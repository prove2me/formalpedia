-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_QExpansionMonoWCoeffZero
-- name    : ReciprocityTheory_DualLattices_QExpansionMonoWCoeffZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:08:13.147833+00:00
-- url     : https://prove2.me/theorems/17442aa5-affe-4b25-88bb-d5bd1b1159b8
-- title:
--   QExpansion Mono WCoeff Zero
-- statement:
--   Definitions and structural lemmas for QExpansion Mono WCoeff Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/QExpansionMonoWCoeffZero.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_Eisenstein4CoeffBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.PGsh
open UpperHalfPlane hiding I
open Complex ModularForm ModularFormClass MatrixGroups EisensteinSeries
def monoIdx (w : ℕ) : Finset ℕ :=
  (Finset.range (w + 1)).filter fun a => 4 * a ≤ w ∧ 6 ∣ w - 4 * a
def monoB (w a : ℕ) : ℕ := (w - 4 * a) / 6
noncomputable def monoW (w a : ℕ) : ModularForm 𝒮ℒ (w : ℤ) :=
  if h : 4 * a + 6 * monoB w a = w then
    ModularForm.mcast (by omega) ((E₄.pow a).mul (E₆.pow (monoB w a)))
  else 0
noncomputable def monoSpanF (w : ℕ) : Submodule ℂ (ℍ → ℂ) :=
  Submodule.span ℂ (Set.range fun a : monoIdx w => (⇑(monoW w a) : ℍ → ℂ))
noncomputable def coeLin (k : ℤ) : ModularForm 𝒮ℒ k →ₗ[ℂ] (ℍ → ℂ) where
  toFun f := ⇑f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
end ReciprocityTheory.PGsh


