-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousAeval
-- name    : GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousAeval
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:36.172705+00:00
-- url     : https://prove2.me/theorems/cfac8fbb-ae9a-4e24-bd0d-e04cb9ce582f
-- title:
--   Is Weighted Homogeneous Aeval
-- statement:
--   Definitions and structural lemmas for Is Weighted Homogeneous Aeval, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousAeval.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
namespace SmallSections
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
def formSubst {P : ArithVariety n} (D : AddBlockData P)
    (g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ)
    (c : (k : ι) → Fin (n k + 1)) : Coord D.extSizes → MvPolynomial (Coord n) ℤ
  | ⟨none, j⟩ => g c j
  | ⟨some k, i⟩ => X ⟨k, i⟩
end SmallSections
end
end GroundTheory.Heights₂.Heights


