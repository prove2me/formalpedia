-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NullMeasurableSetShearImage
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_NullMeasurableSetShearImage
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:40:55.785784+00:00
-- url     : https://prove2.me/theorems/11e439f0-d056-4752-b14d-92ec82542b9d
-- title:
--   Null Measurable Set Shear Image
-- statement:
--   Definitions and structural lemmas for Null Measurable Set Shear Image, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NullMeasurableSetShearImage.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
namespace GlobalTheory.UnfoldNormal
def pairGroup {H : Type} [Group H] (Γ N : Subgroup H) (hN : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) :
    Subgroup (H × H) where
  carrier := {p | p.1 ∈ Γ ∧ p.2 ∈ Γ ∧ p.1 * p.2⁻¹ ∈ N}
  mul_mem' := by
    rintro ⟨a, b⟩ ⟨c, d⟩ ⟨ha, hb, hab⟩ ⟨hc, hd, hcd⟩
    refine ⟨Γ.mul_mem ha hc, Γ.mul_mem hb hd, ?_⟩
    have e : a * c * (b * d)⁻¹ = (a * b⁻¹) * (b * (c * d⁻¹) * b⁻¹) := by group
    simp only [Prod.fst_mul, Prod.snd_mul]
    rw [e]
    exact N.mul_mem hab (hN b hb _ hcd)
  one_mem' := ⟨Γ.one_mem, Γ.one_mem, by simp [N.one_mem]⟩
  inv_mem' := by
    rintro ⟨a, b⟩ ⟨ha, hb, hab⟩
    refine ⟨Γ.inv_mem ha, Γ.inv_mem hb, ?_⟩
    have e : a⁻¹ * b⁻¹⁻¹ = a⁻¹ * (a * b⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    simp only [Prod.fst_inv, Prod.snd_inv]
    rw [e]
    exact hN _ (Γ.inv_mem ha) _ (N.inv_mem hab)
def shear {H : Type} [Group H] (N : Subgroup H) (p : N × H) : H × H := ((p.1 : H) * p.2, p.2)
end GlobalTheory.UnfoldNormal
namespace GlobalTheory.UnfoldNormal
variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H]
  [MeasurableSpace H] [BorelSpace H]
def shearEquiv : H × H ≃ᵐ H × H where
  toFun p := (p.1 * p.2, p.2)
  invFun p := (p.1 * p.2⁻¹, p.2)
  left_inv p := by simp
  right_inv p := by simp
  measurable_toFun := (measurable_fst.mul measurable_snd).prodMk measurable_snd
  measurable_invFun := (measurable_fst.mul measurable_snd.inv).prodMk measurable_snd
end GlobalTheory.UnfoldNormal


