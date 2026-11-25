-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_DegreeDecomposition
-- name    : GroundTheory_GlobalFields_CyclotomicCharacters_DegreeDecomposition
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T00:35:23.119045+00:00
-- url     : https://prove2.me/theorems/1e57165a-34d8-45b6-946a-b1662d8e72d8
-- title:
--   Degree Decomposition
-- statement:
--   Definitions and structural lemmas for Degree Decomposition, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/DegreeDecomposition.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Degree
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ClosedSubgroups
import Theorems.Thm_GroundTheory_Global_Cyclotomic_padicEquiv_apply
import Theorems.Thm_GroundTheory_Global_Cyclotomic_padicEquiv_symm_apply
import Theorems.Thm_GroundTheory_Global_Cyclotomic_val_unitsPadicEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.Cyclotomic.padicEquiv_apply
attribute [local simp] GroundTheory.Global.Cyclotomic.padicEquiv_symm_apply
attribute [local simp] GroundTheory.Global.Cyclotomic.val_unitsPadicEquiv_apply


set_option autoImplicit false
open NumberField IntermediateField Filter Topology
open scoped GroundTheory.LocalField.Abstract Pointwise
namespace GroundTheory.Global
namespace Cyclotomic
open GroundTheory.LocalField.Abstract
local notation "ℚ̄" => AlgebraicClosure ℚ
section Lift
noncomputable abbrev ringOfIntegersIncl (L : IntermediateField ℚ ℚ̄) : 𝓞 L →+* 𝓞 ℚ̄ :=
  RingOfIntegers.mapRingHom (algebraMap L ℚ̄)
end Lift
section Cyclotomic
end Cyclotomic
section Component
end Component
section Image
variable (q : Nat.Primes) (P : Ideal (𝓞 ℚ̄))
def decompositionComponentImage : AddSubgroup ℤ_[q] where
  carrier := (fun σ => Multiplicative.toAdd (degreeComponent q σ)) ''
    (MulAction.stabilizer Gal(ℚ̄/ℚ) P)
  add_mem' := by
    rintro _ _ ⟨σ, hσ, rfl⟩ ⟨τ, hτ, rfl⟩
    exact ⟨σ * τ, mul_mem hσ hτ, by simp⟩
  zero_mem' := ⟨1, one_mem _, by simp⟩
  neg_mem' := by
    rintro _ ⟨σ, hσ, rfl⟩
    exact ⟨σ⁻¹, inv_mem hσ, by simp⟩
def decompositionDegreeImage : AddSubgroup ℤ̂ where
  carrier := (fun σ => Multiplicative.toAdd (degree σ)) '' (MulAction.stabilizer Gal(ℚ̄/ℚ) P)
  add_mem' := by
    rintro _ _ ⟨σ, hσ, rfl⟩ ⟨τ, hτ, rfl⟩
    exact ⟨σ * τ, mul_mem hσ hτ, by simp⟩
  zero_mem' := ⟨1, one_mem _, by simp⟩
  neg_mem' := by
    rintro _ ⟨σ, hσ, rfl⟩
    exact ⟨σ⁻¹, inv_mem hσ, by simp⟩
end Image
end Cyclotomic
end GroundTheory.Global


