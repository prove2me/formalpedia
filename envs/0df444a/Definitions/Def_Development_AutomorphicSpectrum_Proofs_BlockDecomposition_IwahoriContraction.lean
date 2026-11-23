-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriContraction
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriContraction
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:32:33.705802+00:00
-- url     : https://prove2.me/theorems/c2b4b63e-6275-44b9-b4eb-5551d7c2aa2e
-- title:
--   Iwahori Contraction
-- statement:
--   Definitions and structural lemmas for Iwahori Contraction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriContraction.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix Topology MatrixGroups
noncomputable section
namespace GlobalTheory.CompanionTheory.IwContract
open PositivityTheory.Rg.Tf.Loc
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}
def Near (r : ValueGroupWithZero F) (c : GL (Fin n) F) : Prop :=
  c ∈ GlobalTheory.SmGL.iwahori F (Fin n) ∧ ∀ i j, i ≠ j → valuation F (c.val i j) ≤ r
end GlobalTheory.CompanionTheory.IwContract


