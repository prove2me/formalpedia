-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_SPicDefs
-- name    : GroundTheory_ProfiniteCohomology_RestrictedRamification_SPicDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:46:18.98991+00:00
-- url     : https://prove2.me/theorems/dec59ac8-c709-49b0-b927-86cb0f6a7089
-- title:
--   SPic Defs
-- statement:
--   Definitions and structural lemmas for SPic Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/SPicDefs.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.ProfCoh
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {F : Type*} [Field F] [NumberField F]
noncomputable def ordAt (v : HeightOneSpectrum (𝓞 F)) (x : Fˣ) : ℤ :=
  -Multiplicative.toAdd (v.valuationOfNeZero x)
theorem ordAt_mul (v : HeightOneSpectrum (𝓞 F)) (x y : Fˣ) :
    ordAt v (x * y) = ordAt v x + ordAt v y := by
  simp only [ordAt, map_mul, toAdd_mul, neg_add]
theorem ordAt_one (v : HeightOneSpectrum (𝓞 F)) : ordAt v (1 : Fˣ) = 0 := by
  simp [ordAt]
theorem ordAt_eq_zero_iff (v : HeightOneSpectrum (𝓞 F)) (x : Fˣ) :
    ordAt v x = 0 ↔ v.valuation F (x : F) = 1 := by
  rw [ordAt, neg_eq_zero, ← valuationOfNeZero_eq, ← WithZero.coe_one, WithZero.coe_inj,
    ← toAdd_one]
  exact Multiplicative.toAdd.injective.eq_iff
theorem finite_ordAt_ne_zero (x : Fˣ) : {v : HeightOneSpectrum (𝓞 F) | ordAt v x ≠ 0}.Finite := by
  refine ((Support.finite (𝓞 F) (x : F)).union (Support.finite (𝓞 F) ((x⁻¹ : Fˣ) : F))).subset ?_
  intro v hv
  have hv' : v.valuation F (x : F) ≠ 1 := fun h => hv ((ordAt_eq_zero_iff v x).2 h)
  rcases lt_or_gt_of_ne hv' with h | h
  · right
    change 1 < v.valuation F ((x⁻¹ : Fˣ) : F)
    rw [Units.val_inv_eq_inv_val, map_inv₀]
    exact one_lt_inv₀ (lt_of_le_of_ne zero_le (((map_ne_zero (v.valuation F)).2 x.ne_zero)).symm)
      |>.2 h
  · left
    exact h
variable (S : Set (HeightOneSpectrum (𝓞 F)))
abbrev sDivisor := {v : HeightOneSpectrum (𝓞 F) // v ∉ S} →₀ ℤ
noncomputable def divS : Additive Fˣ →+ sDivisor S where
  toFun x := Finsupp.ofSupportFinite (fun v => ordAt v.1 (Additive.toMul x)) (by
    refine ((finite_ordAt_ne_zero (Additive.toMul x)).preimage
      Subtype.val_injective.injOn).subset ?_
    intro v hv
    exact hv)
  map_zero' := by
    ext v
    simp [Finsupp.ofSupportFinite_coe, ordAt_one]
  map_add' x y := by
    ext v
    simp [Finsupp.ofSupportFinite_coe, toMul_add, ordAt_mul]
abbrev sPic := sDivisor S ⧸ (divS S).range
noncomputable abbrev sPicMk : sDivisor S →+ sPic S := QuotientAddGroup.mk' (divS S).range
end GroundTheory.ProfCoh


