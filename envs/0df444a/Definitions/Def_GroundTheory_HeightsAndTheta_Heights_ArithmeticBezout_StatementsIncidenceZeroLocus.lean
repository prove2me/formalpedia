-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncidenceZeroLocus
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncidenceZeroLocus
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:44:11.727863+00:00
-- url     : https://prove2.me/theorems/ca7545da-1a43-4f9d-bf6a-853b486ce1cc
-- title:
--   Statements Incidence Zero Locus
-- statement:
--   Definitions and structural lemmas for Statements Incidence Zero Locus, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsIncidenceZeroLocus.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
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
def IncidenceZeroLocus.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (Q : Ideal (MvPolynomial (Fin n) F)), IsHomogIdeal Q →
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra F Ω] (v : Fin k × Fin n → Ω),
      (∀ g ∈ incIdeal Q k, aeval v g = 0) →
        ∃ y : Fin n → Ω, y ≠ 0 ∧ (∀ q ∈ Q, aeval y q = 0) ∧ ∀ i, ∑ j, v (i, j) * y j = 0
section Inhabitants
attribute [local instance] MvPolynomial.gradedAlgebra
def linearFormX0 (Ω : Type*) [Zero Ω] [One Ω] : Fin 1 × Fin 2 → Ω := fun ij => if ij.2 = 0 then 1 else 0
end Inhabitants
end
end GroundTheory.Heights₂.Heights


