-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HasCompactSupportPhiU
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_HasCompactSupportPhiU
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T23:44:33.187384+00:00
-- url     : https://prove2.me/theorems/b17b9eb8-b09d-4945-a0dc-b4837a12cdb1
-- title:
--   Has Compact Support Phi U
-- statement:
--   Definitions and structural lemmas for Has Compact Support Phi U, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/HasCompactSupportPhiU.lean

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LocalIntegralGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ComplexConjugate Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL
namespace GlobalTheory.SingleBlock
section Alg
variable {F : Type} [Field F] {r t : ℕ} {O : Subring F} {ϖ : F} {P : Subgroup (GL (Fin r) F)}
def suppSet (t : ℕ) (O : Subring F) (ϖ : F) (P : Subgroup (GL (Fin r) F)) :
    Set (Matrix (Fin r ⊕ Fin t) (Fin r) F) :=
  {x | toRows₁ x ∈ Jset P ∧ toRows₂ x ∈ IIset O ϖ}
end Alg
section Top
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {r t : ℕ}
  {O : Subring F} {ϖ : F} {P : Subgroup (GL (Fin r) F)}
variable [MeasurableSpace F] [BorelSpace F]
end Top
end GlobalTheory.SingleBlock


