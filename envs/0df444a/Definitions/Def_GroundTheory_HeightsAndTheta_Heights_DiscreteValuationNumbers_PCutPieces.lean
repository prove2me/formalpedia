-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PCutPieces
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PCutPieces
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:20:07.782539+00:00
-- url     : https://prove2.me/theorems/a6c7e620-4175-494e-a278-f8c2dee50d8b
-- title:
--   PCut Pieces
-- statement:
--   Definitions and structural lemmas for PCut Pieces, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PCutPieces.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
namespace CutPieces
variable {F : Type*} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
theorem weightedHomogeneousSubmodule_le_total (m : K → ℕ) :
    weightedHomogeneousSubmodule F (blockWeight ι) m ≤
      weightedHomogeneousSubmodule F (fun _ : (Σ k, ι k) => (1 : ℕ)) (∑ k, m k) := by
  intro f hf
  rw [mem_weightedHomogeneousSubmodule] at hf ⊢
  intro d hd
  rw [← hf hd, Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum]
  simp only [Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [blockWeight, Pi.single_apply]
instance finiteDimensional [∀ k, Fintype (ι k)] (m : K → ℕ) :
    FiniteDimensional F (weightedHomogeneousSubmodule F (blockWeight ι) m) := by
  have : Module.Finite F
      (weightedHomogeneousSubmodule F (fun _ : (Σ k, ι k) => (1 : ℕ)) (∑ k, m k)) :=
    Module.Finite.iff_fg.mpr (weightedHomogeneousSubmodule_fg (R := F) (w := fun _ => 1) (hw := fun _ => one_ne_zero) (n := _))
  exact Submodule.finiteDimensional_of_le (weightedHomogeneousSubmodule_le_total m)
attribute [local instance] MvPolynomial.weightedGradedAlgebra
end CutPieces
end
end GroundTheory.Heights₂.Heights.NumbersDVR


