-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
-- name    : GroundTheory_PAdicHodge_TiltValuation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T07:21:22.35781+00:00
-- url     : https://prove2.me/theorems/cd07b5e0-b013-48e5-b1c0-8992c637a32a
-- title:
--   Tilt Valuation
-- statement:
--   Definitions and structural lemmas for Tilt Valuation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TiltValuation.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_surjective_frobenius

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.PAdicHodge
open Filter Topology NNReal
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]
section Integers
variable {K' : Type*} [NormedField K'] [IsUltrametricDist K']
theorem mem_span_singleton_iff_norm_le {a x : normInteger K'} :
    x ∈ Ideal.span {a} ↔ ‖(x : K')‖ ≤ ‖(a : K')‖ := by
  simpa using mem_span_singleton_pow_iff (a := a) (x := x) 1
end Integers
omit [Fact p.Prime] [IsPerfectoidField K p] in

theorem mk_eq_mk_iff_norm_sub_le {a b : normInteger K} :
    Ideal.Quotient.mk (Ideal.span {(p : normInteger K)}) a =
        Ideal.Quotient.mk (Ideal.span {(p : normInteger K)}) b ↔
      ‖(a : K) - b‖ ≤ ‖(p : K)‖ := by
  rw [Ideal.Quotient.eq, mem_span_singleton_iff_norm_le]
  simp
omit [Fact p.Prime] [IsPerfectoidField K p] in

theorem mk_eq_zero_iff_norm_le {a : normInteger K} :
    Ideal.Quotient.mk (Ideal.span {(p : normInteger K)}) a = 0 ↔ ‖(a : K)‖ ≤ ‖(p : K)‖ := by
  rw [← map_zero (Ideal.Quotient.mk (Ideal.span {(p : normInteger K)})),
    mk_eq_mk_iff_norm_sub_le]
  simp
@[simp]
theorem untilt_zero : PreTilt.untilt (0 : PreTilt (normInteger K) p) = 0 :=
  Perfection.teichmuller_zero
theorem untilt_mul (x y : PreTilt (normInteger K) p) :
    (x * y).untilt = x.untilt * y.untilt :=
  map_mul _ x y
theorem coeff_eq_mk_untilt (x : PreTilt (normInteger K) p) (n : ℕ) :
    PreTilt.coeff n x = Ideal.Quotient.mk (Ideal.span {(p : normInteger K)})
      (((frobeniusEquiv (PreTilt (normInteger K) p) p).symm^[n] x).untilt) := by
  rw [PreTilt.mk_untilt_eq_coeff_zero, PreTilt.coeff_iterate_frobeniusEquiv_symm, zero_add]
theorem norm_untilt_iterate_pow (x : PreTilt (normInteger K) p) (n : ℕ) :
    ‖((((frobeniusEquiv (PreTilt (normInteger K) p) p).symm^[n] x).untilt : normInteger K) : K)‖
      ^ p ^ n = ‖((x.untilt : normInteger K) : K)‖ := by
  rw [← norm_pow, ← SubmonoidClass.coe_pow, PreTilt.untilt_iterate_frobeniusEquiv_symm_pow]
theorem val_eq_nnnorm_untilt (x : PreTilt (normInteger K) p) :
    PreTilt.val K NormedField.valuation (normInteger K) normInteger_integers p x =
      ‖((x.untilt : normInteger K) : K)‖₊ := by
  by_cases hx : x = 0
  · subst hx; simp
  obtain ⟨n, hn⟩ : ∃ n, PreTilt.coeff n x ≠ 0 :=
    not_forall.1 fun h => hx <| Perfection.ext h
  change PreTilt.valAux K _ _ p x = _
  rw [PreTilt.valAux_eq normInteger_integers hn, coeff_eq_mk_untilt,
    ModP.preVal_mk normInteger_integers (by rwa [← coeff_eq_mk_untilt])]
  ext
  push_cast
  rw [NormedField.valuation_apply, coe_nnnorm]
  exact norm_untilt_iterate_pow x n
theorem untilt_eq_zero_iff {x : PreTilt (normInteger K) p} :
    ((x.untilt : normInteger K) : K) = 0 ↔ x = 0 := by
  rw [← nnnorm_eq_zero, ← val_eq_nnnorm_untilt, PreTilt.map_eq_zero]
theorem norm_untilt_add_le (x y : PreTilt (normInteger K) p) :
    ‖(((x + y).untilt : normInteger K) : K)‖ ≤
      max ‖((x.untilt : normInteger K) : K)‖ ‖((y.untilt : normInteger K) : K)‖ := by
  have := (PreTilt.val K NormedField.valuation (normInteger K) normInteger_integers p).map_add x y
  simp only [val_eq_nnnorm_untilt] at this
  exact_mod_cast this
theorem norm_untilt_neg (x : PreTilt (normInteger K) p) :
    ‖(((-x).untilt : normInteger K) : K)‖ = ‖((x.untilt : normInteger K) : K)‖ := by
  have := (PreTilt.val K NormedField.valuation (normInteger K) normInteger_integers p).map_neg x
  simp only [val_eq_nnnorm_untilt] at this
  exact congrArg NNReal.toReal this
theorem norm_untilt_le_one (x : PreTilt (normInteger K) p) :
    ‖((x.untilt : normInteger K) : K)‖ ≤ 1 :=
  mem_normInteger.1 (x.untilt).2
variable (K p) in

def tiltNorm : MulRingNorm (PreTilt (normInteger K) p) where
  toFun x := ‖((x.untilt : normInteger K) : K)‖
  map_zero' := by simp
  add_le' x y := (norm_untilt_add_le x y).trans
    (max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _))
  neg' x := norm_untilt_neg x
  map_one' := by simp
  map_mul' x y := by simp [untilt_mul]
  eq_zero_of_map_eq_zero' x h := untilt_eq_zero_iff.1 (norm_eq_zero.1 h)
instance normedCommRing_preTilt : NormedCommRing (PreTilt (normInteger K) p) where
  __ := RingNorm.toNormedRing
    { tiltNorm K p with mul_le' := fun x y => (map_mul (tiltNorm K p) x y).le }
  mul_comm := mul_comm
theorem preTilt_norm_def (x : PreTilt (normInteger K) p) :
    ‖x‖ = ‖((x.untilt : normInteger K) : K)‖ := rfl
instance : NormMulClass (PreTilt (normInteger K) p) :=
  ⟨fun x y => map_mul (tiltNorm K p) x y⟩
instance : NormOneClass (PreTilt (normInteger K) p) :=
  ⟨map_one (tiltNorm K p)⟩
instance : IsUltrametricDist (PreTilt (normInteger K) p) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm norm_untilt_add_le
theorem preTilt_norm_le_one (x : PreTilt (normInteger K) p) : ‖x‖ ≤ 1 :=
  norm_untilt_le_one x
theorem norm_untilt_add_sub_le (x y : PreTilt (normInteger K) p) :
    ‖(((x + y).untilt : normInteger K) : K) - (x.untilt + y.untilt)‖ ≤ ‖(p : K)‖ := by
  have h := (mk_eq_mk_iff_norm_sub_le (p := p) (a := (x + y).untilt)
    (b := x.untilt + y.untilt)).1 (by simp)
  simpa using h
theorem coeff_eq_zero_iff_norm_le (x : PreTilt (normInteger K) p) (n : ℕ) :
    PreTilt.coeff n x = 0 ↔ ‖x‖ ≤ ‖(p : K)‖ ^ p ^ n := by
  rw [coeff_eq_mk_untilt, mk_eq_zero_iff_norm_le, preTilt_norm_def, ← norm_untilt_iterate_pow x n]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _)
    (pow_ne_zero n (Fact.out : p.Prime).ne_zero)).symm
theorem exists_mk_untilt_eq (a : normInteger K) :
    ∃ x : PreTilt (normInteger K) p, Ideal.Quotient.mk (Ideal.span {(p : normInteger K)})
      x.untilt = Ideal.Quotient.mk _ a := by
  obtain ⟨x, hx⟩ : ∃ x : PreTilt (normInteger K) p, PreTilt.coeff 0 x = Ideal.Quotient.mk _ a :=
    Perfection.coeff_surjective (IsPerfectoidField.surjective_frobenius (K := K) p) 0 _
  exact ⟨x, by rw [PreTilt.mk_untilt_eq_coeff_zero]; exact hx⟩
theorem untilt_add_of_natCast_eq_zero (hp : (p : K) = 0) (x y : PreTilt (normInteger K) p) :
    (x + y).untilt = x.untilt + y.untilt := by
  have := norm_untilt_add_sub_le x y
  rw [hp, norm_zero, norm_le_zero_iff, sub_eq_zero] at this
  exact Subtype.ext (by simpa using this)
instance completeSpace_preTilt : CompleteSpace (PreTilt (normInteger K) p) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  by_cases hp : (p : K) = 0
  ·
    have hsub : ∀ x y : PreTilt (normInteger K) p,
        (x - y).untilt = x.untilt - y.untilt := fun x y => by
      rw [eq_sub_iff_add_eq, ← untilt_add_of_natCast_eq_zero hp, sub_add_cancel]
    have hiso : ∀ x y : PreTilt (normInteger K) p,
        dist ((x.untilt : normInteger K) : K) (y.untilt) = dist x y := fun x y => by
      rw [dist_eq_norm, dist_eq_norm, preTilt_norm_def, hsub]; rfl
    have := IsPerfectoidField.completeSpace (K := K) p
    have hv : CauchySeq fun m => ((u m).untilt : K) := by
      refine Metric.cauchySeq_iff.2 fun ε hε => ?_
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu ε hε
      exact ⟨N, fun m hm n hn => by rw [hiso]; exact hN m hm n hn⟩
    obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hv
    have ha1 : ‖a‖ ≤ 1 := le_of_tendsto' ha.norm fun m => norm_untilt_le_one (u m)
    obtain ⟨L, hL⟩ := exists_mk_untilt_eq (p := p) ⟨a, mem_normInteger.2 ha1⟩
    rw [mk_eq_mk_iff_norm_sub_le, hp, norm_zero, norm_le_zero_iff, sub_eq_zero] at hL
    refine ⟨L, tendsto_iff_dist_tendsto_zero.2 ?_⟩
    have := tendsto_iff_dist_tendsto_zero.1 ha
    refine this.congr fun m => ?_
    rw [← hiso, hL]
  · set r := ‖(p : K)‖ with hr
    have hr0 : 0 < r := norm_pos_iff.2 hp
    have hr1 : r < 1 := IsPerfectoidField.norm_natCast_lt_one
    have hN : ∀ n : ℕ, ∃ N, ∀ m ≥ N, PreTilt.coeff n (u m) = PreTilt.coeff n (u N) := by
      intro n
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 hu (r ^ p ^ n) (by positivity)
      refine ⟨N, fun m hm => ?_⟩
      have := (coeff_eq_zero_iff_norm_le (u m - u N) n).2
        (by rw [← dist_eq_norm]; exact (hN m hm).le)
      rwa [map_sub, sub_eq_zero] at this
    choose N hN using hN
    let c : ℕ → ModP (normInteger K) p := fun n => PreTilt.coeff n (u (N n))
    have hcp : ∀ n, c (n + 1) ^ p = c n := by
      intro n
      simp only [c]
      rw [← hN (n + 1) (max (N n) (N (n + 1))) (le_max_right _ _), PreTilt.coeff_pow_p,
        hN n _ (le_max_left _ _)]
    let L : PreTilt (normInteger K) p := ⟨c, hcp⟩
    have hL : ∀ n, PreTilt.coeff n L = c n := fun n => rfl
    refine ⟨L, Metric.tendsto_atTop.2 fun ε hε => ?_⟩
    obtain ⟨n, hn⟩ : ∃ n : ℕ, r ^ p ^ n < ε := by
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hr1
      exact ⟨n, (pow_le_pow_of_le_one hr0.le hr1.le
        (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le).trans_lt hn⟩
    refine ⟨N n, fun m hm => ?_⟩
    rw [dist_eq_norm]
    refine lt_of_le_of_lt ((coeff_eq_zero_iff_norm_le _ n).1 ?_) hn
    rw [map_sub, hL, hN n m hm, sub_self]
theorem preTilt_dvd_iff_norm_le {x y : PreTilt (normInteger K) p} : x ∣ y ↔ ‖y‖ ≤ ‖x‖ := by
  constructor
  · rintro ⟨c, rfl⟩
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (preTilt_norm_le_one c)
  intro hxy
  by_cases hx : x = 0
  · subst hx
    rw [norm_zero, norm_le_zero_iff] at hxy
    rw [hxy]
  set ψ := (frobeniusEquiv (PreTilt (normInteger K) p) p).symm
  have hx0 : ∀ n, (((ψ^[n] x).untilt : normInteger K) : K) ≠ 0 := fun n h => by
    have := norm_untilt_iterate_pow x n
    rw [h, norm_zero, zero_pow (pow_ne_zero n (Fact.out : p.Prime).ne_zero), eq_comm,
      norm_eq_zero, untilt_eq_zero_iff] at this
    exact hx this
  have hle : ∀ n, ‖(((ψ^[n] y).untilt : normInteger K) : K)‖ ≤
      ‖(((ψ^[n] x).untilt : normInteger K) : K)‖ := fun n => by
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _)
      (pow_ne_zero n (Fact.out : p.Prime).ne_zero), norm_untilt_iterate_pow,
      norm_untilt_iterate_pow]
    exact hxy
  let z : ℕ → normInteger K := fun n =>
    ⟨((ψ^[n] y).untilt : K) / (ψ^[n] x).untilt, mem_normInteger.2 (by
      rw [norm_div]; exact div_le_one_of_le₀ (hle n) (norm_nonneg _))⟩
  have hroot : ∀ (w : PreTilt (normInteger K) p) (n : ℕ),
      (((ψ^[n + 1] w).untilt : normInteger K) : K) ^ p = (ψ^[n] w).untilt := fun w n => by
    rw [Function.iterate_succ_apply']
    have := PreTilt.untilt_iterate_frobeniusEquiv_symm_pow (ψ^[n] w) 1
    rw [pow_one] at this
    exact congrArg Subtype.val this
  have hz : ∀ n, z (n + 1) ^ p = z n := fun n => by
    apply Subtype.ext
    simp only [z, SubmonoidClass.coe_pow, div_pow, hroot]
  let Z : PreTilt (normInteger K) p := ⟨fun n => Ideal.Quotient.mk _ (z n),
    fun n => by rw [← map_pow, hz]⟩
  refine ⟨Z, Perfection.ext fun n => ?_⟩
  change PreTilt.coeff n y = PreTilt.coeff n (x * Z)
  rw [map_mul, coeff_eq_mk_untilt, coeff_eq_mk_untilt]
  change _ = _ * Ideal.Quotient.mk _ (z n)
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  simp only [z, Subring.coe_mul]
  rw [mul_div_cancel₀ _ (hx0 n)]
def untiltModHom (ϖ : normInteger K) (hp : ‖(p : K)‖ ≤ ‖(ϖ : K)‖) :
    PreTilt (normInteger K) p →+* normInteger K ⧸ Ideal.span {ϖ} :=
  (Ideal.Quotient.factor (Ideal.span_le.2 (by
    rw [Set.singleton_subset_iff, SetLike.mem_coe, mem_span_singleton_iff_norm_le]
    simpa using hp))).comp (PreTilt.coeff 0)
theorem untiltModHom_apply (ϖ : normInteger K) (hp : ‖(p : K)‖ ≤ ‖(ϖ : K)‖)
    (x : PreTilt (normInteger K) p) :
    untiltModHom ϖ hp x = Ideal.Quotient.mk _ x.untilt := by
  rw [untiltModHom, RingHom.comp_apply, ← PreTilt.mk_untilt_eq_coeff_zero,
    Ideal.Quotient.factor_mk]
theorem untiltModHom_surjective (ϖ : normInteger K) (hp : ‖(p : K)‖ ≤ ‖(ϖ : K)‖) :
    Function.Surjective (untiltModHom (p := p) ϖ hp) := by
  rw [untiltModHom, RingHom.coe_comp]
  exact (Ideal.Quotient.factor_surjective _).comp
    (Perfection.coeff_surjective (IsPerfectoidField.surjective_frobenius (K := K) p) 0)
theorem ker_untiltModHom (ϖ' : PreTilt (normInteger K) p) (ϖ : normInteger K)
    (h : ‖((ϖ'.untilt : normInteger K) : K)‖ = ‖(ϖ : K)‖) (hp : ‖(p : K)‖ ≤ ‖(ϖ : K)‖) :
    RingHom.ker (untiltModHom ϖ hp) = Ideal.span {ϖ'} := by
  ext x
  rw [RingHom.mem_ker, untiltModHom_apply, Ideal.Quotient.eq_zero_iff_mem,
    mem_span_singleton_iff_norm_le, Ideal.mem_span_singleton, preTilt_dvd_iff_norm_le, ← h]
  rfl
def tiltQuotientEquiv (ϖ' : PreTilt (normInteger K) p) (ϖ : normInteger K)
    (h : ‖((ϖ'.untilt : normInteger K) : K)‖ = ‖(ϖ : K)‖) (hp : ‖(p : K)‖ ≤ ‖(ϖ : K)‖) :
    PreTilt (normInteger K) p ⧸ Ideal.span {ϖ'} ≃+* normInteger K ⧸ Ideal.span {ϖ} :=
  (Ideal.quotEquivOfEq (ker_untiltModHom ϖ' ϖ h hp).symm).trans
    (RingHom.quotientKerEquivOfSurjective (untiltModHom_surjective ϖ hp))
end GroundTheory.PAdicHodge
end


