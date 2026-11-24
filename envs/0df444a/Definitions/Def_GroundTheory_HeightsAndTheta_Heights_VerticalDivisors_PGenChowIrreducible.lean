-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGenChowIrreducible
-- name    : GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGenChowIrreducible
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:44:41.908101+00:00
-- url     : https://prove2.me/theorems/45720fe0-16fc-4b95-bec2-b4f23ef186e5
-- title:
--   PGen Chow Irreducible
-- statement:
--   Definitions and structural lemmas for PGen Chow Irreducible, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenChowIrreducible.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
namespace GenChowIrreducible
variable {n e : ℕ}
def parVar (e n : ℕ) (ij : Fin (e + 1) × Fin n) : Fin n ⊕ Par e n :=
  Fin.cases (motive := fun _ => Fin n ⊕ Par e n) (.inl ij.2) (fun i => .inr (.inl (i, ij.2))) ij.1
end GenChowIrreducible
end
end GroundTheory.Heights₂.Heights.Vertical


