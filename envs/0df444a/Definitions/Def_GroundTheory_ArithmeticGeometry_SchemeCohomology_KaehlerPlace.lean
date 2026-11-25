-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_KaehlerPlace
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_KaehlerPlace
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T00:37:51.348415+00:00
-- url     : https://prove2.me/theorems/07f5acb4-8186-4cf6-9e44-b23b84c836cf
-- title:
--   Kaehler Place
-- statement:
--   Definitions and structural lemmas for Kaehler Place, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/KaehlerPlace.lean

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceBridge
import Theorems.Thm_GroundTheory_FunctionField_Place_exists_ord_eq_one
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
import Theorems.Thm_GroundTheory_FunctionField_Place_ord_pow
import Theorems.Thm_GroundTheory_FunctionField_Place_valuation_eq_exp_neg_ord
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply


set_option autoImplicit false
namespace GroundTheory.Arith.SchemeCoh
open GroundTheory.FunctionField KaehlerDifferential IntermediateField
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
variable (k) in

def spanDField (x : K) : IntermediateField k K where
  carrier := {y | D k K y ∈ Submodule.span K {D k K x}}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Derivation.leibniz] at *
    exact add_mem (Submodule.smul_mem _ _ hb) (Submodule.smul_mem _ _ ha)
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, map_add] at *
    exact add_mem ha hb
  algebraMap_mem' c := by
    simp only [Set.mem_ofPred_eq, Derivation.map_algebraMap]
    exact zero_mem _
  inv_mem' a ha := by
    simp only [Set.mem_ofPred_eq, Derivation.leibniz_inv] at *
    exact Submodule.smul_mem _ _ ha
theorem D_mem_span_of_mem_adjoin (x : K) {y : K} (hy : y ∈ k⟮x⟯) :
    D k K y ∈ Submodule.span K {D k K x} := by
  have : k⟮x⟯ ≤ spanDField k x := by
    rw [adjoin_le_iff, Set.singleton_subset_iff]
    exact Submodule.subset_span rfl
  exact this hy
theorem span_D_eq_top (x : K) [Algebra.IsSeparable k⟮x⟯ K] :
    Submodule.span K {D k K x} = ⊤ := by
  have : Algebra.FormallyUnramified k⟮x⟯ K := .of_isSeparable _ _
  refine eq_top_iff.mpr fun ω hω ↦ ?_
  clear hω
  obtain ⟨z, rfl⟩ := (exact_mapBaseChange_map k k⟮x⟯ K ω).mp (Subsingleton.elim _ _)
  induction z with
  | zero => simp
  | add a b ha hb => rw [map_add]; exact add_mem ha hb
  | tmul a b =>
    rw [mapBaseChange_tmul]
    refine Submodule.smul_mem _ _ ?_
    have hb : b ∈ Submodule.span k⟮x⟯ (Set.range (D k k⟮x⟯)) := by
      rw [span_range_derivation]; trivial
    induction hb using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨e, rfl⟩ := h
      rw [map_D]
      exact D_mem_span_of_mem_adjoin x e.2
    | zero => simp
    | add _ _ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | smul c _ _ h =>
      rw [map_smul, algebra_compatible_smul K c]
      exact Submodule.smul_mem _ _ h
variable [IsFunctionField k K]
theorem kaehlerDifferential_nontrivial : Nontrivial Ω[K⁄k] := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have : Algebra.FormallyUnramified k K := ⟨h⟩
  have : Algebra.EssFiniteType k K := essFiniteType
  have : Module.Finite k K := Algebra.FormallyUnramified.finite_of_free k K
  have h1 := trdeg_eq_one (k := k) (K := K)
  have : Algebra.IsAlgebraic k K := Algebra.IsAlgebraic.of_finite k K
  rw [_root_.trdeg_eq_zero] at h1
  exact zero_ne_one h1
theorem D_ne_zero_of_isSeparable (x : K) [Algebra.IsSeparable k⟮x⟯ K] : D k K x ≠ 0 := by
  intro h
  have htop := span_D_eq_top (k := k) x
  rw [h, Submodule.span_singleton_eq_bot.mpr rfl] at htop
  have := kaehlerDifferential_nontrivial (k := k) (K := K)
  exact bot_ne_top htop
section Perfect
variable [PerfectField k]
variable (k K) in

theorem exists_isSeparable_adjoin : ∃ x : K, Algebra.IsSeparable k⟮x⟯ K := by
  have : Algebra.EssFiniteType k K := essFiniteType
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k K
  have hcard : s.card = 1 := by
    have h := hs.cardinalMk_eq_trdeg
    rw [trdeg_eq_one, Cardinal.mk_coe_finset] at h
    exact_mod_cast h
  obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hcard
  refine ⟨x, ?_⟩
  convert hsep <;> simp
theorem exists_ord_eq_one_D_ne_zero (v : Place k K) :
    ∃ t : K, v.ord t = 1 ∧ D k K t ≠ 0 := by
  obtain ⟨π, hπ⟩ := v.exists_ord_eq_one
  have hπ0 : π ≠ 0 := fun h ↦ by simp [h, v.ord_zero] at hπ
  by_cases hd : D k K π = 0
  swap
  · exact ⟨π, hπ, hd⟩
  obtain ⟨x, hx⟩ := exists_isSeparable_adjoin k K
  have hdx := D_ne_zero_of_isSeparable (k := k) x
  have hx0 : x ≠ 0 := fun h ↦ hdx (by simp [h])
  set m : ℕ := (2 - v.ord x).toNat + 1 with hm
  have hm1 : 1 ≤ m := by omega
  have hord : v.ord (π ^ m * x) = m + v.ord x := by
    rw [v.ord_mul (pow_ne_zero _ hπ0) hx0, v.ord_pow, hπ, mul_one]
  have hlt : v.valuation (π ^ m * x) < v.valuation π := by
    rw [v.valuation_eq_exp_neg_ord (mul_ne_zero (pow_ne_zero _ hπ0) hx0),
      v.valuation_eq_exp_neg_ord hπ0, hord, hπ, WithZero.exp_lt_exp]
    omega
  refine ⟨π + π ^ m * x, ?_, ?_⟩
  · have hne : π + π ^ m * x ≠ 0 := by
      intro h
      have := Valuation.map_add_eq_of_lt_left v.valuation hlt
      rw [h, map_zero] at this
      exact (v.valuation.ne_zero_iff.mpr hπ0) this.symm
    have h := Valuation.map_add_eq_of_lt_left v.valuation hlt
    rw [v.valuation_eq_exp_neg_ord hne, v.valuation_eq_exp_neg_ord hπ0, hπ] at h
    have := WithZero.exp_injective h
    omega
  · rw [map_add, hd, zero_add, Derivation.leibniz, Derivation.leibniz_pow, hd]
    simp only [smul_zero, add_zero]
    exact smul_ne_zero (pow_ne_zero _ hπ0) hdx
end Perfect
section Order
variable [PerfectField k]
noncomputable def kaehlerCoeff (t : K) (ω : Ω[K⁄k]) : K :=
  haveI := Classical.propDecidable
  if h : ∃ c : K, c • D k K t = ω then h.choose else 0
noncomputable def kaehlerUniformizer (v : Place k K) : K :=
  (exists_ord_eq_one_D_ne_zero v).choose
noncomputable def kaehlerOrd (v : Place k K) (ω : Ω[K⁄k]) : ℤ :=
  v.ord (kaehlerCoeff (kaehlerUniformizer v) ω)
end Order
end GroundTheory.Arith.SchemeCoh


