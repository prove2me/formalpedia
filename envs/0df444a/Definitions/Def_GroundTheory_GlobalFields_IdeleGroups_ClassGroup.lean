-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
-- name    : GroundTheory_GlobalFields_IdeleGroups_ClassGroup
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T00:26:36.649924+00:00
-- url     : https://prove2.me/theorems/042ccf21-f352-4e2b-8ab7-5617fbbacf51
-- title:
--   Class Group
-- statement:
--   Definitions and structural lemmas for Class Group, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/ClassGroup.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_ker_mk
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_mk_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_mk_surjective
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding_of_ne
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_mem_standardOpenSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding


set_option autoImplicit false
namespace GroundTheory.Global
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero FractionalIdeal
open scoped NumberField.AdeleRing nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
def primeIdealUnit (v : HeightOneSpectrum (𝓞 K)) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) (coeIdeal_ne_zero.mpr v.ne_bot)
@[simp]
theorem coe_primeIdealUnit (v : HeightOneSpectrum (𝓞 K)) :
    ((primeIdealUnit v : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) :=
  rfl
theorem fractionalIdealUnits_eq_iff {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ} :
    I = J ↔ ∀ v : HeightOneSpectrum (𝓞 K),
      count K v (I : FractionalIdeal (𝓞 K)⁰ K) = count K v (J : FractionalIdeal (𝓞 K)⁰ K) := by
  refine ⟨fun h v ↦ h ▸ rfl, fun h ↦ Units.ext ?_⟩
  rw [← finprod_heightOneSpectrum_factorization' (K := K) I.ne_zero,
    ← finprod_heightOneSpectrum_factorization' (K := K) J.ne_zero]
  exact finprod_congr fun v ↦ by rw [h v]
theorem coe_finprod_primeIdealUnit_zpow (n : HeightOneSpectrum (𝓞 K) → ℤ)
    (hn : ∀ᶠ v in Filter.cofinite, n v = 0) :
    ((∏ᶠ v, primeIdealUnit v ^ n v : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ n v := by
  have hfin : (Function.mulSupport fun v ↦ primeIdealUnit (K := K) v ^ n v).Finite :=
    (Filter.eventually_cofinite.1 hn).subset fun v hv h ↦ hv (by simp only [h, zpow_zero])
  rw [← Units.coeHom_apply, map_finprod _ hfin]
  exact finprod_congr fun v ↦ by simp [Units.val_zpow_eq_zpow_val]
theorem count_finprod_primeIdealUnit_zpow (n : HeightOneSpectrum (𝓞 K) → ℤ)
    (hn : ∀ᶠ v in Filter.cofinite, n v = 0) (v : HeightOneSpectrum (𝓞 K)) :
    count K v ((∏ᶠ w, primeIdealUnit w ^ n w : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) = n v := by
  rw [coe_finprod_primeIdealUnit_zpow n hn, count_finprod K v n hn]
theorem finprod_primeIdealUnit_zpow_count (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∏ᶠ v, primeIdealUnit v ^ count K v (I : FractionalIdeal (𝓞 K)⁰ K) = I := by
  rw [fractionalIdealUnits_eq_iff]
  intro v
  exact count_finprod_primeIdealUnit_zpow _ (FractionalIdeal.finite_factors _) v
open Classical in
theorem count_primeIdealUnit (v w : HeightOneSpectrum (𝓞 K)) :
    count K w ((primeIdealUnit v : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      if w = v then 1 else 0 := by
  rw [coe_primeIdealUnit]
  split_ifs with h
  · subst h
    exact count_self K w
  · exact count_maximal_coprime K w (Ne.symm h)
theorem count_spanSingleton (v : HeightOneSpectrum (𝓞 K)) {a : K} (ha : a ≠ 0) :
    count K v (spanSingleton (𝓞 K)⁰ a) = -log (v.valuation K a) := by
  obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at ha
  have hI : spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K n / algebraMap (𝓞 K) K d) =
      spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K d)⁻¹ * ↑(Ideal.span {n} : Ideal (𝓞 K)) := by
    rw [coeIdeal_span_singleton, spanSingleton_mul_spanSingleton, div_eq_mul_inv, mul_comm]
  rw [count_well_defined K v ((spanSingleton_ne_zero_iff).2 ha) hI, map_div₀,
    valuation_of_algebraMap, valuation_of_algebraMap, intValuation_if_neg _ hn0,
    intValuation_if_neg _ hd0, ← exp_sub, log_exp]
  ring
namespace IdeleGroup
def ord (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup K) : ℤ :=
  -log (Valued.v ((x : 𝔸[K]).2 v))
theorem valued_ne_zero (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup K) :
    Valued.v ((x : 𝔸[K]).2 v) ≠ 0 :=
  (Valuation.ne_zero_iff _).2 (finiteProj v x).ne_zero
theorem ord_mul (v : HeightOneSpectrum (𝓞 K)) (x y : IdeleGroup K) :
    ord v (x * y) = ord v x + ord v y := by
  have h : ((x * y : IdeleGroup K) : 𝔸[K]).2 v = (x : 𝔸[K]).2 v * (y : 𝔸[K]).2 v := rfl
  rw [ord, ord, ord, h, map_mul, log_mul (valued_ne_zero v x) (valued_ne_zero v y), neg_add]
@[simp]
theorem ord_one (v : HeightOneSpectrum (𝓞 K)) : ord v (1 : IdeleGroup K) = 0 := by
  have h : ((1 : IdeleGroup K) : 𝔸[K]).2 v = 1 := rfl
  rw [ord, h, map_one, log_one, neg_zero]
theorem ord_inv (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup K) : ord v x⁻¹ = -ord v x := by
  have h := ord_mul v x x⁻¹
  rw [mul_inv_cancel, ord_one] at h
  omega
theorem mem_adicCompletionIntegers_iff_ord_nonneg (v : HeightOneSpectrum (𝓞 K))
    (x : IdeleGroup K) :
    (x : 𝔸[K]).2 v ∈ v.adicCompletionIntegers K ↔ 0 ≤ ord v x := by
  rw [mem_adicCompletionIntegers, ord, neg_nonneg, log_le_iff_le_exp (valued_ne_zero v x),
    exp_zero]
theorem ord_eq_zero_iff (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup K) :
    ord v x = 0 ↔ (x : 𝔸[K]).2 v ∈ v.adicCompletionIntegers K ∧
      ((x⁻¹ : IdeleGroup K) : 𝔸[K]).2 v ∈ v.adicCompletionIntegers K := by
  rw [mem_adicCompletionIntegers_iff_ord_nonneg, mem_adicCompletionIntegers_iff_ord_nonneg,
    ord_inv]
  omega
theorem eventually_ord_eq_zero (x : IdeleGroup K) :
    ∀ᶠ v in Filter.cofinite, ord v x = 0 :=
  ((x : 𝔸[K]).2.2.and ((x⁻¹ : IdeleGroup K) : 𝔸[K]).2.2).mono fun v hv ↦
    (ord_eq_zero_iff v x).2 hv
theorem mem_standardOpenSubgroup_iff_ord {x : IdeleGroup K} :
    x ∈ standardOpenSubgroup K ↔ ∀ v : HeightOneSpectrum (𝓞 K), ord v x = 0 := by
  simp only [mem_standardOpenSubgroup, ord_eq_zero_iff]
theorem ord_finiteEmbedding_self (v : HeightOneSpectrum (𝓞 K)) (a : (v.adicCompletion K)ˣ) :
    ord v (finiteEmbedding v a) = -log (Valued.v (a : v.adicCompletion K)) := by
  rw [ord, ← coe_finiteProj, finiteProj_finiteEmbedding]
theorem ord_finiteEmbedding_of_ne {v w : HeightOneSpectrum (𝓞 K)} (h : w ≠ v)
    (a : (v.adicCompletion K)ˣ) : ord w (finiteEmbedding v a) = 0 := by
  rw [ord, ← coe_finiteProj, finiteProj_finiteEmbedding_of_ne h, Units.val_one, map_one, log_one,
    neg_zero]
theorem ord_diagonal (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ) :
    ord v (diagonal K a) = -log (v.valuation K a) := by
  rw [ord, ← coe_finiteProj, coe_finiteProj_diagonal, valuedAdicCompletion_eq_valuation']
open Classical in

theorem exists_ord_eq_ite (v : HeightOneSpectrum (𝓞 K)) :
    ∃ x : IdeleGroup K, ∀ w, ord w x = if w = v then 1 else 0 := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  have hne : ((π : K) : v.adicCompletion K) ≠ 0 := by
    intro h
    have h' := congrArg Valued.v h
    rw [valuedAdicCompletion_eq_valuation', hπ, map_zero] at h'
    exact exp_ne_zero h'
  refine ⟨finiteEmbedding v (Units.mk0 _ hne), fun w ↦ ?_⟩
  split_ifs with h
  · subst h
    rw [ord_finiteEmbedding_self, Units.val_mk0, valuedAdicCompletion_eq_valuation', hπ, log_exp,
      neg_neg]
  · exact ord_finiteEmbedding_of_ne h _
theorem finite_mulSupport_primeIdealUnit_zpow_ord (x : IdeleGroup K) :
    (Function.mulSupport fun v ↦ primeIdealUnit (K := K) v ^ ord v x).Finite :=
  (Filter.eventually_cofinite.1 (eventually_ord_eq_zero x)).subset fun v hv h ↦
    hv (by simp only [h, zpow_zero])
def toFractionalIdeal : IdeleGroup K →* (FractionalIdeal (𝓞 K)⁰ K)ˣ where
  toFun x := ∏ᶠ v, primeIdealUnit v ^ ord v x
  map_one' := by simp only [ord_one, zpow_zero, finprod_one]
  map_mul' x y := by
    simp only [ord_mul, zpow_add]
    exact finprod_mul_distrib (finite_mulSupport_primeIdealUnit_zpow_ord x)
      (finite_mulSupport_primeIdealUnit_zpow_ord y)
@[simp]
theorem count_toFractionalIdeal (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup K) :
    count K v ((toFractionalIdeal x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) = ord v x :=
  count_finprod_primeIdealUnit_zpow _ (eventually_ord_eq_zero x) v
theorem toFractionalIdeal_eq_iff {x : IdeleGroup K} {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} :
    toFractionalIdeal x = I ↔
      ∀ v : HeightOneSpectrum (𝓞 K), ord v x = count K v (I : FractionalIdeal (𝓞 K)⁰ K) := by
  simp only [fractionalIdealUnits_eq_iff, count_toFractionalIdeal]
theorem ker_toFractionalIdeal :
    (toFractionalIdeal (K := K)).ker = standardOpenSubgroup K := by
  ext x
  rw [MonoidHom.mem_ker, toFractionalIdeal_eq_iff, mem_standardOpenSubgroup_iff_ord]
  simp only [Units.val_one, count_one]
open Classical in

theorem primeIdealUnit_mem_range (v : HeightOneSpectrum (𝓞 K)) :
    primeIdealUnit v ∈ (toFractionalIdeal (K := K)).range := by
  obtain ⟨x, hx⟩ := exists_ord_eq_ite v
  refine ⟨x, toFractionalIdeal_eq_iff.2 fun w ↦ ?_⟩
  rw [hx, count_primeIdealUnit]
theorem toFractionalIdeal_surjective : Function.Surjective (toFractionalIdeal (K := K)) := by
  intro I
  have h : I ∈ (toFractionalIdeal (K := K)).range := by
    rw [← finprod_primeIdealUnit_zpow_count I]
    exact finprod_induction (· ∈ (toFractionalIdeal (K := K)).range) (one_mem _)
      (fun _ _ ↦ mul_mem) fun v ↦ zpow_mem (primeIdealUnit_mem_range v) _
  exact h
theorem toFractionalIdeal_diagonal (a : Kˣ) :
    toFractionalIdeal (diagonal K a) = toPrincipalIdeal (𝓞 K) K a := by
  rw [toFractionalIdeal_eq_iff]
  intro v
  rw [ord_diagonal, coe_toPrincipalIdeal, count_spanSingleton v a.ne_zero]
theorem _root_.GroundTheory.Global.classGroup_mk_eq_one_iff {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} :
    ClassGroup.mk K I = 1 ↔ I ∈ (toPrincipalIdeal (𝓞 K) K).range := by
  rw [ClassGroup.mk_eq_one_iff, mem_principal_ideals_iff]
  constructor
  · intro hI
    obtain ⟨x, hx⟩ := Submodule.IsPrincipal.principal (S := (I : Submodule (𝓞 K) K))
    refine ⟨x, ?_⟩
    symm
    apply Subtype.coe_injective
    simp only [FractionalIdeal.val_eq_coe, hx, coe_spanSingleton]
  · rintro ⟨x, hx⟩
    exact ⟨⟨x, by rw [← hx, coe_spanSingleton]⟩⟩
theorem _root_.GroundTheory.Global.classGroup_mk_surjective :
    Function.Surjective (ClassGroup.mk K : (FractionalIdeal (𝓞 K)⁰ K)ˣ →* ClassGroup (𝓞 K)) :=
  fun c ↦ ClassGroup.induction K (P := fun c ↦ ∃ I, ClassGroup.mk K I = c) (fun I ↦ ⟨I, rfl⟩) c
def toClassGroup : IdeleGroup K →* ClassGroup (𝓞 K) :=
  (ClassGroup.mk K).comp toFractionalIdeal
theorem toClassGroup_apply (x : IdeleGroup K) :
    toClassGroup x = ClassGroup.mk K (toFractionalIdeal x) :=
  rfl
theorem toClassGroup_surjective : Function.Surjective (toClassGroup (K := K)) :=
  classGroup_mk_surjective.comp toFractionalIdeal_surjective
theorem ker_toClassGroup :
    (toClassGroup (K := K)).ker = (diagonal K).range ⊔ standardOpenSubgroup K := by
  apply le_antisymm
  · intro x hx
    rw [MonoidHom.mem_ker, toClassGroup_apply, classGroup_mk_eq_one_iff] at hx
    obtain ⟨a, ha⟩ := hx
    have hu : (diagonal K a)⁻¹ * x ∈ standardOpenSubgroup K := by
      rw [← ker_toFractionalIdeal, MonoidHom.mem_ker, map_mul, map_inv, toFractionalIdeal_diagonal,
        ha, inv_mul_cancel]
    exact Subgroup.mem_sup.2 ⟨diagonal K a, ⟨a, rfl⟩, _, hu, mul_inv_cancel_left _ _⟩
  · refine sup_le ?_ ?_
    · rintro _ ⟨a, rfl⟩
      rw [MonoidHom.mem_ker, toClassGroup_apply, toFractionalIdeal_diagonal,
        classGroup_mk_eq_one_iff]
      exact ⟨a, rfl⟩
    · intro x hx
      rw [← ker_toFractionalIdeal, MonoidHom.mem_ker] at hx
      rw [MonoidHom.mem_ker, toClassGroup_apply, hx, map_one]
def quotientEquivClassGroup :
    IdeleGroup K ⧸ ((diagonal K).range ⊔ standardOpenSubgroup K) ≃* ClassGroup (𝓞 K) :=
  (QuotientGroup.quotientMulEquivOfEq ker_toClassGroup.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ toClassGroup_surjective)
@[simp]
theorem quotientEquivClassGroup_mk (x : IdeleGroup K) :
    quotientEquivClassGroup (QuotientGroup.mk x :
      IdeleGroup K ⧸ ((diagonal K).range ⊔ standardOpenSubgroup K)) =
      ClassGroup.mk K (toFractionalIdeal x) :=
  rfl
end IdeleGroup
namespace IdeleClassGroup
open IdeleGroup
def toClassGroup : IdeleClassGroup K →* ClassGroup (𝓞 K) :=
  QuotientGroup.lift _ IdeleGroup.toClassGroup
    (le_sup_left.trans_eq (ker_toClassGroup (K := K)).symm)
@[simp]
theorem toClassGroup_mk (x : IdeleGroup K) :
    toClassGroup (mk K x) = IdeleGroup.toClassGroup x :=
  rfl
theorem toClassGroup_surjective : Function.Surjective (toClassGroup (K := K)) := by
  intro c
  obtain ⟨x, rfl⟩ := IdeleGroup.toClassGroup_surjective c
  exact ⟨mk K x, rfl⟩
theorem ker_toClassGroup :
    (toClassGroup (K := K)).ker = (standardOpenSubgroup K).map (mk K) := by
  ext c
  obtain ⟨x, rfl⟩ := mk_surjective K c
  rw [MonoidHom.mem_ker, toClassGroup_mk, ← MonoidHom.mem_ker, IdeleGroup.ker_toClassGroup]
  constructor
  · intro hx
    obtain ⟨_, ⟨a, rfl⟩, u, hu, rfl⟩ := Subgroup.mem_sup.1 hx
    exact ⟨u, hu, by rw [map_mul, mk_diagonal]; exact (one_mul (mk K u)).symm⟩
  · rintro ⟨u, hu, h⟩
    have h1 : mk K (x * u⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
    rw [← MonoidHom.mem_ker, ker_mk] at h1
    rw [← inv_mul_cancel_right x u]
    exact mul_mem (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right hu)
instance : ((standardOpenSubgroup K).map (mk K)).Normal :=
  ⟨fun n hn g ↦ by rwa [mul_comm g n, mul_inv_cancel_right]⟩
def quotientEquivClassGroup :
    IdeleClassGroup K ⧸ (standardOpenSubgroup K).map (mk K) ≃* ClassGroup (𝓞 K) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_toClassGroup (K := K)).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ toClassGroup_surjective)
end IdeleClassGroup
end
end GroundTheory.Global


