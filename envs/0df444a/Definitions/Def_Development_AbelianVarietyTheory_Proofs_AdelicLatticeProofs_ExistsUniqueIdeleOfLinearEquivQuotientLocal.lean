-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
-- name    : Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T12:36:40.263649+00:00
-- url     : https://prove2.me/theorems/3187e5e0-190f-476c-8abb-90594789e6ee
-- title:
--   Exists Unique Idele Of Linear Equiv Quotient Local
-- statement:
--   Definitions and structural lemmas for Exists Unique Idele Of Linear Equiv Quotient Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUniqueIdeleOfLinearEquivQuotientLocal.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationAlgebraMapEqCount
import Theorems.Thm_GlobalTheory_AdicValuationCountFactors_valuation_eq_exp_neg_count

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped nonZeroDivisors IsDedekindDomain.FiniteAdeleRing
noncomputable section
namespace GlobalTheory.Idele
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]
theorem valuation_eq_exp_neg_count (v : HeightOneSpectrum R) {x : K} (hx : x ≠ 0) :
    v.valuation K x = exp (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ x)) := by
  first
  | exact @_root_.GlobalTheory.AdicValuationCountFactors.valuation_eq_exp_neg_count
  | exact _root_.GlobalTheory.AdicValuationCountFactors.valuation_eq_exp_neg_count
  | (apply _root_.GlobalTheory.AdicValuationCountFactors.valuation_eq_exp_neg_count <;> assumption)
  | (intros; apply _root_.GlobalTheory.AdicValuationCountFactors.valuation_eq_exp_neg_count <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AdicValuationCountFactors.valuation_eq_exp_neg_count <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AdicValuationCountFactors.valuation_eq_exp_neg_count ..)
theorem le_of_count_le {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, FractionalIdeal.count K v J ≤ FractionalIdeal.count K v I) :
    I ≤ J := by
  have hIJ : I * J⁻¹ ≠ 0 := mul_ne_zero hI (inv_ne_zero hJ)
  have h1 : I * J⁻¹ ≤ 1 := by
    rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hIJ]
    refine finprod_induction (fun L : FractionalIdeal R⁰ K => L ≤ 1) le_rfl ?_ ?_
    · intro a b ha hb
      calc a * b ≤ 1 * b := by gcongr
        _ ≤ 1 := by simpa using hb
    · intro v
      have h0 : 0 ≤ FractionalIdeal.count K v (I * J⁻¹) := by
        rw [FractionalIdeal.count_mul K v hI (inv_ne_zero hJ), FractionalIdeal.count_inv]
        linarith [h v]
      obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h0
      rw [hn, zpow_natCast, ← FractionalIdeal.coeIdeal_pow]
      exact FractionalIdeal.coeIdeal_le_one
  calc I = I * J⁻¹ * J := by rw [mul_assoc, inv_mul_cancel₀ hJ, mul_one]
    _ ≤ 1 * J := by gcongr
    _ = J := one_mul J
theorem eq_of_count_eq {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, FractionalIdeal.count K v I = FractionalIdeal.count K v J) :
    I = J :=
  le_antisymm (le_of_count_le hI hJ fun v => (h v).ge) (le_of_count_le hJ hI fun v => (h v).le)
theorem mem_iff_valuation_le {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) (x : K) :
    x ∈ I ↔ ∀ v : HeightOneSpectrum R,
      v.valuation K x ≤ exp (-FractionalIdeal.count K v I) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [FractionalIdeal.zero_mem]
  have hx' : FractionalIdeal.spanSingleton R⁰ x ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.2 hx
  rw [← FractionalIdeal.spanSingleton_le_iff_mem]
  simp_rw [fun v : HeightOneSpectrum R => valuation_eq_exp_neg_count v hx, exp_le_exp, neg_le_neg_iff]
  exact ⟨fun h v => FractionalIdeal.count_mono K v hx' h, le_of_count_le hx' hI⟩
theorem exists_mem_valuation_eq {I : FractionalIdeal R⁰ K} (hI : I ≠ 0)
    (v : HeightOneSpectrum R) :
    ∃ y ∈ I, v.valuation K y = exp (-FractionalIdeal.count K v I) := by
  classical
  by_contra hne
  push Not at hne
  have hv : (v.asIdeal : FractionalIdeal R⁰ K) ≠ 0 := by simpa using v.ne_bot
  have hle : I ≤ (v.asIdeal : FractionalIdeal R⁰ K) * I := by
    intro y hy
    have hy' := (mem_iff_valuation_le hI y).1 hy
    refine (mem_iff_valuation_le (mul_ne_zero hv hI) y).2 fun w => ?_
    rw [FractionalIdeal.count_mul K w hv hI, FractionalIdeal.count_maximal]
    split_ifs with hw
    · subst hw
      have := lt_of_le_of_ne (hy' v) (hne y hy)
      rcases eq_or_ne (v.valuation K y) 0 with h0 | h0
      · simp [h0]
      rw [← exp_log h0, exp_lt_exp] at this
      rw [← exp_log h0, exp_le_exp]
      omega
    · simpa using hy' w
  have := FractionalIdeal.count_mono K v hI hle
  rw [FractionalIdeal.count_mul K v hv hI, FractionalIdeal.count_self] at this
  omega
def localIdeal (v : HeightOneSpectrum R) (I : FractionalIdeal R⁰ K) :
    Submodule (v.adicCompletionIntegers K) (v.adicCompletion K) :=
  Submodule.span _ (algebraMap K (v.adicCompletion K) '' (I : Set K))
theorem valued_algebraMap (v : HeightOneSpectrum R) (x : K) :
    Valued.v (algebraMap K (v.adicCompletion K) x) = v.valuation K x :=
  valuedAdicCompletion_eq_valuation' v x
theorem mem_localIdeal_iff {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) (v : HeightOneSpectrum R)
    (x : v.adicCompletion K) :
    x ∈ localIdeal v I ↔ Valued.v x ≤ exp (-FractionalIdeal.count K v I) := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      rw [valued_algebraMap]
      exact (mem_iff_valuation_le hI y).1 hy v
    | zero => simp
    | add x y _ _ hx hy => exact (Valuation.map_add _ x y).trans (max_le hx hy)
    | smul a x _ hx =>
      have ha : Valued.v (a : v.adicCompletion K) ≤ 1 := a.2
      change Valued.v ((a : v.adicCompletion K) * x) ≤ _
      rw [map_mul]
      exact (mul_le_of_le_one_left' ha).trans hx
  · intro hx
    obtain ⟨y, hy, hvy⟩ := exists_mem_valuation_eq hI v
    rw [← valued_algebraMap] at hvy
    have hy0 : Valued.v (algebraMap K (v.adicCompletion K) y) ≠ 0 := by rw [hvy]; exact exp_ne_zero
    have hy1 : algebraMap K (v.adicCompletion K) y ≠ 0 := by
      intro h; rw [h] at hy0; simp at hy0
    have hm : x / algebraMap K (v.adicCompletion K) y ∈ v.adicCompletionIntegers K := by
      rw [mem_adicCompletionIntegers, map_div₀, div_le_one₀ (zero_lt_iff.2 hy0), hvy]
      exact hx
    have : x = (⟨_, hm⟩ : v.adicCompletionIntegers K) • algebraMap K (v.adicCompletion K) y := by
      change x = x / _ * _
      rw [div_mul_cancel₀ _ hy1]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, hy, rfl⟩)
theorem localIdeal_zero (v : HeightOneSpectrum R) :
    localIdeal v (0 : FractionalIdeal R⁰ K) = ⊥ := by
  rw [localIdeal, Submodule.span_eq_bot]
  rintro _ ⟨y, hy, rfl⟩
  rw [(FractionalIdeal.mem_zero_iff R⁰).1 hy, map_zero]
@[simp] theorem adele_mul_apply (a b : 𝔸ᶠ[R, K]) (v : HeightOneSpectrum R) :
    (a * b) v = a v * b v := rfl
@[simp] theorem adele_add_apply (a b : 𝔸ᶠ[R, K]) (v : HeightOneSpectrum R) :
    (a + b) v = a v + b v := rfl
@[simp] theorem adele_sub_apply (a b : 𝔸ᶠ[R, K]) (v : HeightOneSpectrum R) :
    (a - b) v = a v - b v := rfl
@[simp] theorem adele_one_apply (v : HeightOneSpectrum R) : (1 : 𝔸ᶠ[R, K]) v = 1 := rfl
@[simp] theorem adele_zero_apply (v : HeightOneSpectrum R) : (0 : 𝔸ᶠ[R, K]) v = 0 := rfl
theorem adele_algebraMap_apply (x : K) (v : HeightOneSpectrum R) :
    algebraMap K 𝔸ᶠ[R, K] x v = algebraMap K (v.adicCompletion K) x := rfl
theorem adele_smul_apply (r : R) (a : 𝔸ᶠ[R, K]) (v : HeightOneSpectrum R) :
    (r • a) v = algebraMap K (v.adicCompletion K) (algebraMap R K r) * a v := by
  rw [Algebra.smul_def]; rfl
def adelicIdeal (I : FractionalIdeal R⁰ K) : Submodule R 𝔸ᶠ[R, K] where
  carrier := {a | ∀ v, a v ∈ localIdeal v I}
  add_mem' ha hb v := add_mem (ha v) (hb v)
  zero_mem' v := zero_mem _
  smul_mem' r a ha v := by
    rw [adele_smul_apply]
    exact (localIdeal v I).smul_mem (algebraMap R (v.adicCompletionIntegers K) r) (ha v)
theorem mem_adelicIdeal {I : FractionalIdeal R⁰ K} {a : 𝔸ᶠ[R, K]} :
    a ∈ adelicIdeal I ↔ ∀ v, a v ∈ localIdeal v I := Iff.rfl
theorem mem_adelicIdeal_iff {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) {a : 𝔸ᶠ[R, K]} :
    a ∈ adelicIdeal I ↔ ∀ v, Valued.v (a v) ≤ exp (-FractionalIdeal.count K v I) := by
  simp_rw [mem_adelicIdeal, mem_localIdeal_iff hI]
theorem algebraMap_mem_adelicIdeal {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) (x : K) :
    algebraMap K 𝔸ᶠ[R, K] x ∈ adelicIdeal I ↔ x ∈ I := by
  simp_rw [mem_adelicIdeal_iff hI, mem_iff_valuation_le hI, adele_algebraMap_apply,
    valued_algebraMap]
theorem idele_apply_mul_inv (t : 𝔸ᶠ[R, K]ˣ) (v : HeightOneSpectrum R) :
    (t : 𝔸ᶠ[R, K]) v * ((t⁻¹ : 𝔸ᶠ[R, K]ˣ) : 𝔸ᶠ[R, K]) v = 1 := by
  rw [← adele_mul_apply, Units.mul_inv, adele_one_apply]
theorem idele_apply_ne_zero (t : 𝔸ᶠ[R, K]ˣ) (v : HeightOneSpectrum R) :
    (t : 𝔸ᶠ[R, K]) v ≠ 0 := left_ne_zero_of_mul_eq_one (idele_apply_mul_inv t v)
def ord_vw (t : 𝔸ᶠ[R, K]ˣ) (v : HeightOneSpectrum R) : ℤ := -log (Valued.v ((t : 𝔸ᶠ[R, K]) v))
theorem valued_idele (t : 𝔸ᶠ[R, K]ˣ) (v : HeightOneSpectrum R) :
    Valued.v ((t : 𝔸ᶠ[R, K]) v) = exp (-ord_vw t v) := by
  rw [ord_vw, neg_neg, exp_log]
  simpa using idele_apply_ne_zero t v
theorem ord_vw_mul (t s : 𝔸ᶠ[R, K]ˣ) (v : HeightOneSpectrum R) :
    ord_vw (t * s) v = ord_vw t v + ord_vw s v := by
  have := valued_idele (t * s) v
  rw [Units.val_mul, adele_mul_apply, map_mul, valued_idele, valued_idele, ← exp_add,
    exp_inj] at this
  omega
theorem ord_vw_one (v : HeightOneSpectrum R) : ord_vw (1 : 𝔸ᶠ[R, K]ˣ) v = 0 := by
  have := ord_vw_mul (1 : 𝔸ᶠ[R, K]ˣ) 1 v
  rw [one_mul] at this
  omega
theorem ord_vw_eventually_zero (t : 𝔸ᶠ[R, K]ˣ) : ∀ᶠ v in Filter.cofinite, ord_vw t v = 0 := by
  filter_upwards [(FiniteAdeleRing.isUnit_iff.1 t.isUnit).2] with v hv
  simp [ord_vw, hv]
def idealOf (t : 𝔸ᶠ[R, K]ˣ) : FractionalIdeal R⁰ K :=
  ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^ ord_vw t v
theorem idealOf_ne_zero (t : 𝔸ᶠ[R, K]ˣ) : idealOf t ≠ 0 := by
  refine finprod_induction (fun L : FractionalIdeal R⁰ K => L ≠ 0) one_ne_zero
    (fun _ _ => mul_ne_zero) fun v => zpow_ne_zero _ ?_
  simpa using v.ne_bot
theorem count_idealOf (t : 𝔸ᶠ[R, K]ˣ) (v : HeightOneSpectrum R) :
    FractionalIdeal.count K v (idealOf t) = ord_vw t v :=
  FractionalIdeal.count_finprod K v _ (ord_vw_eventually_zero t)
theorem idealOf_one : idealOf (1 : 𝔸ᶠ[R, K]ˣ) = 1 :=
  eq_of_count_eq (idealOf_ne_zero _) one_ne_zero fun v => by
    rw [count_idealOf, ord_vw_one, FractionalIdeal.count_one]
theorem idealOf_mul (t s : 𝔸ᶠ[R, K]ˣ) : idealOf (t * s) = idealOf t * idealOf s :=
  eq_of_count_eq (idealOf_ne_zero _) (mul_ne_zero (idealOf_ne_zero _) (idealOf_ne_zero _))
    fun v => by
      rw [FractionalIdeal.count_mul K v (idealOf_ne_zero _) (idealOf_ne_zero _), count_idealOf,
        count_idealOf, count_idealOf, ord_vw_mul]
scoped instance mulActionFractionalIdeal : MulAction 𝔸ᶠ[R, K]ˣ (FractionalIdeal R⁰ K) where
  smul t I := idealOf t * I
  one_smul I := by change idealOf 1 * I = I; rw [idealOf_one, one_mul]
  mul_smul t s I := by
    change idealOf (t * s) * I = idealOf t * (idealOf s * I); rw [idealOf_mul, mul_assoc]
theorem smul_def (t : 𝔸ᶠ[R, K]ˣ) (I : FractionalIdeal R⁰ K) : t • I = idealOf t * I := rfl
theorem smul_ne_zero (t : 𝔸ᶠ[R, K]ˣ) {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) : t • I ≠ 0 :=
  mul_ne_zero (idealOf_ne_zero t) hI
theorem count_smul (t : 𝔸ᶠ[R, K]ˣ) {I : FractionalIdeal R⁰ K} (hI : I ≠ 0)
    (v : HeightOneSpectrum R) :
    FractionalIdeal.count K v (t • I) = ord_vw t v + FractionalIdeal.count K v I := by
  rw [smul_def, FractionalIdeal.count_mul K v (idealOf_ne_zero _) hI, count_idealOf]
theorem mul_mem_localIdeal_smul (t : 𝔸ᶠ[R, K]ˣ) (I : FractionalIdeal R⁰ K)
    (v : HeightOneSpectrum R) (x : v.adicCompletion K) :
    (t : 𝔸ᶠ[R, K]) v * x ∈ localIdeal v (t • I) ↔ x ∈ localIdeal v I := by
  rcases eq_or_ne I 0 with rfl | hI
  · simp [smul_def, localIdeal_zero, idele_apply_ne_zero]
  rw [mem_localIdeal_iff hI, mem_localIdeal_iff (smul_ne_zero t hI), count_smul t hI, map_mul,
    valued_idele, neg_add, exp_add, mul_le_mul_iff_right₀ (zero_lt_iff.2 exp_ne_zero)]
theorem mul_mem_adelicIdeal_smul (t : 𝔸ᶠ[R, K]ˣ) (I : FractionalIdeal R⁰ K) (a : 𝔸ᶠ[R, K]) :
    (t : 𝔸ᶠ[R, K]) * a ∈ adelicIdeal (t • I) ↔ a ∈ adelicIdeal I := by
  simp_rw [mem_adelicIdeal, adele_mul_apply, mul_mem_localIdeal_smul]
theorem setOf_valued_le_eq (v : HeightOneSpectrum R) (n : ℤ) :
    ∃ c : v.adicCompletion K, Valued.v.restrict c ≠ 0 ∧
      {y : v.adicCompletion K | Valued.v y ≤ exp n} =
        {y | Valued.v.restrict y ≤ Valued.v.restrict c} := by
  obtain ⟨c, hc⟩ := valuedAdicCompletion_surjective K v (exp n)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact exp_ne_zero hc.symm
  refine ⟨c, by simp [hc0], ?_⟩
  ext y
  simp only [Set.mem_setOf_eq, Valuation.restrict_le_iff, hc]
theorem isOpen_valued_le (v : HeightOneSpectrum R) (n : ℤ) :
    IsOpen {y : v.adicCompletion K | Valued.v y ≤ exp n} := by
  obtain ⟨c, hc, h⟩ := setOf_valued_le_eq (K := K) v n
  rw [h]; exact Valued.isOpen_closedBall _ hc
theorem exists_valued_sub_le (v : HeightOneSpectrum R) {a : v.adicCompletion K}
    (ha : Valued.v a ≤ 1) (n : ℕ) :
    ∃ r : R, Valued.v (a - algebraMap K (v.adicCompletion K) (algebraMap R K r)) ≤
      exp (-(n : ℤ)) := by
  have ho : IsOpen {y : v.adicCompletion K | Valued.v (a - y) ≤ exp (-(n : ℤ))} :=
    (isOpen_valued_le (K := K) v (-(n : ℤ))).preimage (continuous_const.sub continuous_id)
  obtain ⟨x, hx⟩ := (denseRange_algebraMap K v).exists_mem_open ho ⟨a, by simp⟩
  have hx : Valued.v (a - algebraMap K (v.adicCompletion K) x) ≤ exp (-(n : ℤ)) := hx
  have h1 : exp (-(n : ℤ)) ≤ (1 : ℤᵐ⁰) := by rw [← exp_zero, exp_le_exp]; omega
  have hx1 : v.valuation K x ≤ 1 := by
    rw [← valued_algebraMap, ← sub_sub_cancel a (algebraMap K (v.adicCompletion K) x)]
    exact (Valuation.map_sub _ _ _).trans (max_le ha (hx.trans h1))
  obtain ⟨r, hr⟩ := v.exists_valuation_sub_lt_of_integer hx1 (Units.mk0 _ (exp_ne_zero (a := -(n : ℤ))))
  refine ⟨r, ?_⟩
  rw [← valued_algebraMap, map_sub, Valuation.map_sub_swap] at hr
  rw [← sub_add_sub_cancel a (algebraMap K (v.adicCompletion K) x)]
  exact (Valuation.map_add _ _ _).trans (max_le hx hr.le)
theorem exists_sub_mem_adelicIdeal_of_integral {I : FractionalIdeal R⁰ K} (hI : I ≠ 0)
    {a : 𝔸ᶠ[R, K]} (ha : ∀ v, Valued.v (a v) ≤ 1) :
    ∃ r : R, a - algebraMap K 𝔸ᶠ[R, K] (algebraMap R K r) ∈ adelicIdeal I := by
  classical
  have hfin := Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors I)
  let e : HeightOneSpectrum R → ℕ := fun v => (FractionalIdeal.count K v I).toNat
  choose x hx using fun v => exists_valued_sub_le v (ha v) (e v)
  obtain ⟨r, hr⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := hfin.toFinset)
    (fun v => v.asIdeal) e (fun v _ => v.prime)
    (fun v _ w _ h h' => h (HeightOneSpectrum.ext h')) (fun v => x v)
  refine ⟨r, (mem_adelicIdeal_iff hI).2 fun v => ?_⟩
  rw [adele_sub_apply, adele_algebraMap_apply]
  have hr1 : Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) ≤ 1 := by
    rw [valued_algebraMap]; exact v.valuation_le_one r
  by_cases hv : v ∈ hfin.toFinset
  · have h2 := (v.intValuation_le_pow_iff_mem _ _).2 (hr v hv)
    rw [← v.valuation_of_algebraMap (K := K)] at h2
    change v.valuation K (algebraMap R K (r - x v)) ≤ _ at h2
    rw [← valued_algebraMap, map_sub, map_sub, Valuation.map_sub_swap] at h2
    rw [← sub_add_sub_cancel (a v) (algebraMap K (v.adicCompletion K) (algebraMap R K (x v)))]
    refine ((Valuation.map_add _ _ _).trans (max_le (hx v) h2)).trans ?_
    rw [exp_le_exp]
    simp only [e]
    omega
  · have : FractionalIdeal.count K v I = 0 := by simpa using hv
    rw [this]
    exact (Valuation.map_sub _ _ _).trans (max_le (ha v) hr1)
theorem exists_mul_integral (a : 𝔸ᶠ[R, K]) :
    ∃ b : R, b ≠ 0 ∧ ∀ v, Valued.v ((algebraMap K 𝔸ᶠ[R, K] (algebraMap R K b) * a) v) ≤ 1 := by
  classical
  have hfin := Filter.eventually_cofinite.1 a.2
  choose b hb0 hb using fun v : HeightOneSpectrum R =>
    adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v (a v)
  have hle : ∀ (v : HeightOneSpectrum R) (r : R),
      Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) ≤ 1 := fun v r => by
    rw [valued_algebraMap]; exact v.valuation_le_one r
  refine ⟨∏ v ∈ hfin.toFinset, b v,
    Finset.prod_ne_zero_iff.2 fun v _ => nonZeroDivisors.ne_zero (hb0 v), fun v => ?_⟩
  rw [adele_mul_apply, adele_algebraMap_apply]
  by_cases hv : v ∈ hfin.toFinset
  · rw [← Finset.prod_erase_mul _ _ hv, map_mul (algebraMap R K),
      map_mul (algebraMap K (v.adicCompletion K)), mul_assoc, map_mul]
    refine mul_le_one' (hle v _) ?_
    rw [mul_comm]
    exact hb v
  · have : a.1 v ∈ v.adicCompletionIntegers K := by simpa using hv
    rw [map_mul]
    exact mul_le_one' (hle v _) (show Valued.v (a v) ≤ 1 from this)
theorem exists_sub_mem_adelicIdeal {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) (a : 𝔸ᶠ[R, K]) :
    ∃ x : K, a - algebraMap K 𝔸ᶠ[R, K] x ∈ adelicIdeal I := by
  obtain ⟨b, hb0, hb⟩ := exists_mul_integral a
  have hb1 : algebraMap R K b ≠ 0 := by simpa using hb0
  let t := FiniteAdeleRing.unitEmbedding R K (Units.mk0 _ hb1)
  obtain ⟨r, hr⟩ := exists_sub_mem_adelicIdeal_of_integral (smul_ne_zero t hI) hb
  refine ⟨algebraMap R K r / algebraMap R K b, ?_⟩
  rw [← mul_mem_adelicIdeal_smul t]
  convert hr using 1
  simp only [t, FiniteAdeleRing.unitEmbedding_apply, Units.val_mk0]
  rw [mul_sub, ← map_mul, mul_div_cancel₀ _ hb1]
def quotEquivAdelic {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) :
    (K ⧸ (I : Submodule R K)) ≃ₗ[R] (𝔸ᶠ[R, K] ⧸ adelicIdeal I) :=
  LinearEquiv.ofBijective
    (Submodule.mapQ (I : Submodule R K) (adelicIdeal I)
      ((Algebra.linearMap K 𝔸ᶠ[R, K]).restrictScalars R)
      fun x hx => (algebraMap_mem_adelicIdeal hI x).2 hx) <| by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro q hq
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      rw [Submodule.Quotient.mk_eq_zero]
      exact (algebraMap_mem_adelicIdeal hI x).1 ((Submodule.Quotient.mk_eq_zero _).1 hq)
    · intro q
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      obtain ⟨x, hx⟩ := exists_sub_mem_adelicIdeal hI a
      refine ⟨Submodule.Quotient.mk x, ?_⟩
      exact ((Submodule.Quotient.eq _).2 hx).symm
@[simp] theorem quotEquivAdelic_mk {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) (x : K) :
    quotEquivAdelic hI (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (algebraMap K 𝔸ᶠ[R, K] x) := rfl
def adelicMulEquiv (t : 𝔸ᶠ[R, K]ˣ) {I J : FractionalIdeal R⁰ K} (h : J = t • I) :
    (𝔸ᶠ[R, K] ⧸ adelicIdeal I) ≃ₗ[R] (𝔸ᶠ[R, K] ⧸ adelicIdeal J) :=
  Submodule.Quotient.equiv _ _ (Units.mulLeftLinearEquiv R 𝔸ᶠ[R, K] t) <| by
    subst h
    ext a
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact (mul_mem_adelicIdeal_smul t I c).2 hc
    · intro ha
      refine ⟨(t⁻¹ : 𝔸ᶠ[R, K]ˣ) * a, ?_, by simp⟩
      rw [← mul_mem_adelicIdeal_smul t]
      simpa using ha
def mulEquiv (t : 𝔸ᶠ[R, K]ˣ) {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (h : J = t • I) :
    (K ⧸ (I : Submodule R K)) ≃ₗ[R] (K ⧸ (J : Submodule R K)) :=
  (quotEquivAdelic hI).trans <| (adelicMulEquiv t h).trans
    (quotEquivAdelic (h ▸ smul_ne_zero t hI)).symm
end GlobalTheory.Idele
namespace GlobalTheory
open NumberField GlobalTheory.Idele
end GlobalTheory


