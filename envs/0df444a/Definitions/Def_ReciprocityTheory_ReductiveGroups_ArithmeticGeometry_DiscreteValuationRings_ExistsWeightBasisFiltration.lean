-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsWeightBasisFiltration
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsWeightBasisFiltration
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:20:25.135513+00:00
-- url     : https://prove2.me/theorems/2a74efa2-39e9-49f1-85fc-1f059eed6273
-- title:
--   Exists Weight Basis Filtration
-- statement:
--   Definitions and structural lemmas for Exists Weight Basis Filtration, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExistsWeightBasisFiltration.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Mathlib.AlgebraicGeometry.ValuativeCriterion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace ReciprocityTheory.ChartRestriction.G.DVR.TWO
open ReciprocityTheory.ChartRestriction.G.Out
variable {F : Type} [Field F] (v : AddValuation F (WithTop ℚ))
theorem exists_weight_basis_filtration {a b : WithTop ℚ} (h : a + b = 0) (ha : a ≤ 0) : 0 ≤ b := by
  rcases eq_or_ne b ⊤ with rfl | hbt
  · exact le_top
  rcases eq_or_ne a ⊤ with rfl | hat
  · simp at h
  lift a to ℚ using hat
  lift b to ℚ using hbt
  norm_cast at h ha ⊢
  linarith
theorem le_zero_of_add_eq_zero_nonneg {a b : WithTop ℚ} (h : a + b = 0) (hb : 0 ≤ b) : a ≤ 0 := by
  rcases eq_or_ne b ⊤ with rfl | hbt
  · simp at h
  rcases eq_or_ne a ⊤ with rfl | hat
  · simp at h
  lift a to ℚ using hat
  lift b to ℚ using hbt
  norm_cast at h hb ⊢
  linarith
def Ov : ValuationSubring F where
  carrier := {x | 0 ≤ v x}
  mul_mem' {a b} ha hb := by
    show 0 ≤ v (a * b)
    rw [AddValuation.map_mul]; exact add_nonneg ha hb
  one_mem' := by show 0 ≤ v 1; rw [AddValuation.map_one]
  add_mem' {a b} ha hb := le_trans (le_min ha hb) (AddValuation.map_add v a b)
  zero_mem' := by show 0 ≤ v 0; rw [AddValuation.map_zero]; exact le_top
  neg_mem' {a} ha := by show 0 ≤ v (-a); rw [AddValuation.map_neg]; exact ha
  mem_or_inv_mem' x := by
    by_cases hx : x = 0
    · left; show 0 ≤ v x; rw [hx, AddValuation.map_zero]; exact le_top
    rcases le_total 0 (v x) with h | h
    · exact Or.inl h
    · right
      show 0 ≤ v x⁻¹
      refine exists_weight_basis_filtration ?_ h
      rw [← AddValuation.map_mul, mul_inv_cancel₀ hx, AddValuation.map_one]
theorem mem_Ov {x : F} : x ∈ Ov v ↔ 0 ≤ v x := Iff.rfl
theorem v_nonneg (r : Ov v) : (0 : WithTop ℚ) ≤ v (r : F) := (mem_Ov v).1 r.2
theorem v_unit (r : (Ov v)ˣ) : v ((r : Ov v) : F) = 0 := by
  have h1 := v_nonneg v (r : Ov v)
  have h2 := v_nonneg v ((r⁻¹ : (Ov v)ˣ) : Ov v)
  have hm : ((r : Ov v) : F) * (((r⁻¹ : (Ov v)ˣ) : Ov v) : F) = 1 := congrArg Subtype.val r.mul_inv
  have hs : v ((r : Ov v) : F) + v (((r⁻¹ : (Ov v)ˣ) : Ov v) : F) = 0 := by
    rw [← AddValuation.map_mul, hm, AddValuation.map_one]
  exact le_antisymm (le_zero_of_add_eq_zero_nonneg hs h2) h1
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  [Algebra (FractionRing V) F]
abbrev algVF : V →+* F := (algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))
theorem v_of_V (hϖ : Irreducible ϖ) (hv : ValOver ϖ F v) (x : V) : (0 : WithTop ℚ) ≤ v (algVF x) ∧
    (¬ IsUnit x → x ≠ 0 → (1 : WithTop ℚ) ≤ v (algVF x)) := by
  by_cases hx0 : x = 0
  · subst hx0
    refine ⟨?_, fun _ h => absurd rfl h⟩
    rw [map_zero, AddValuation.map_zero]
    exact le_top
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  have hH : HasVal ϖ (algebraMap V (FractionRing V) x) (n : ℤ) :=
    ⟨u, by rw [hu, map_mul, map_pow, zpow_natCast, mul_comm]⟩
  have hval : v (algVF x) = (((n : ℤ) : ℚ) : WithTop ℚ) := hv _ _ hH
  rw [hval]
  refine ⟨?_, fun hnu _ => ?_⟩
  · have h0 : (0 : ℚ) ≤ ((n : ℤ) : ℚ) := by positivity
    exact_mod_cast h0
  · rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exact (hnu (by rw [hu, h0, pow_zero, mul_one]; exact u.isUnit)).elim
    · have h1 : (1 : ℚ) ≤ ((n : ℤ) : ℚ) := by exact_mod_cast hpos
      exact_mod_cast h1
def fO (hϖ : Irreducible ϖ) (hv : ValOver ϖ F v) : V →+* Ov v :=
  (algVF (F := F) (V := V)).codRestrict (Ov v).toSubring fun x => (v_of_V v hϖ hv x).1
instance isLocalHom_fO (hϖ : Irreducible ϖ) (hv : ValOver ϖ F v) : IsLocalHom (fO v hϖ hv) where
  map_nonunit x hx := by
    by_contra hxu
    have hx0 : x ≠ 0 := by rintro rfl; simp at hx
    have h1 := (v_of_V v hϖ hv x).2 hxu hx0
    have h0 := v_unit v hx.unit
    rw [IsUnit.unit_spec] at h0
    have : v (algVF x) = 0 := h0
    rw [this] at h1
    exact absurd h1 (by decide)
end ReciprocityTheory.ChartRestriction.G.DVR.TWO


