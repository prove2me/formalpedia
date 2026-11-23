-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:43:22.705236+00:00
-- url     : https://prove2.me/theorems/83597abd-89f3-4356-ae07-40bfd2fd3e32
-- title:
--   Ne Bot Of Norm
-- statement:
--   Definitions and structural lemmas for Ne Bot Of Norm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/NeBotOfNorm.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime
import Theorems.Thm_GlobalTheory_SW_Base_herm_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
namespace GlobalTheory.SW.Nbr
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
noncomputable def co : 𝓞 E ≃+* 𝓞 E := (IsCMField.ringOfIntegersComplexConj E).toRingEquiv
theorem herm_one (x y : Fin n → E) : herm 1 x y = ∑ a, x a * cc (y a) := by
  unfold herm
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Matrix.one_apply]
theorem herm_sl (c : E) (x y : Fin n → E) : herm 1 (c • x) y = c * herm 1 x y := by
  simp [herm_one, Finset.mul_sum, mul_assoc]
theorem herm_al (x x' y : Fin n → E) : herm 1 (x + x') y = herm 1 x y + herm 1 x' y := by
  simp [herm_one, add_mul, Finset.sum_add_distrib]
omit [IsCMField E] in
theorem osmul (c : 𝓞 E) (x : Fin n → E) : c • x = (c : E) • x := rfl
def Int' (x y : Fin n → E) : Prop := IsIntegral ℤ (herm 1 x y)
theorem Int'.add {x x' y : Fin n → E} (h : Int' x y) (h' : Int' x' y) : Int' (x + x') y := by
  unfold Int'
  rw [herm_al]
  exact IsIntegral.add h h'
theorem Int'.smul {x y : Fin n → E} (c : 𝓞 E) (h : Int' x y) : Int' (c • x) y := by
  unfold Int'
  rw [osmul, herm_sl]
  exact IsIntegral.mul c.2 h
theorem int_zero (y : Fin n → E) : Int' 0 y := by
  unfold Int'
  rw [herm_one]
  simpa using isIntegral_zero
def SD (Λ : Lt E n) : Prop := ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, Int' x y
def nbOf (P : Ideal (𝓞 E)) (Λ₀ : Lt E n) : Lt E n where
  carrier := {x | (∀ y ∈ Λ₀, Int' x y) ∧ ∀ c ∈ conjI P, c • x ∈ Λ₀}
  add_mem' := fun ha hb => ⟨fun y hy => (ha.1 y hy).add (hb.1 y hy), fun c hc => by
    rw [smul_add]; exact Λ₀.add_mem (ha.2 c hc) (hb.2 c hc)⟩
  zero_mem' := ⟨fun y _ => int_zero y, fun c _ => by rw [smul_zero]; exact Λ₀.zero_mem⟩
  smul_mem' := fun a x hx => ⟨fun y hy => (hx.1 y hy).smul a, fun c hc => by
    rw [smul_comm]; exact Λ₀.smul_mem a (hx.2 c hc)⟩
end GlobalTheory.SW.Nbr
namespace GlobalTheory.SW
end GlobalTheory.SW


