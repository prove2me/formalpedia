-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSectionDegreeSum
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSectionDegreeSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:59:08.449266+00:00
-- url     : https://prove2.me/theorems/aa33e937-ee60-44de-a7c7-9ebb9feaf0df
-- title:
--   St Section Degree Sum
-- statement:
--   Definitions and structural lemmas for St Section Degree Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSectionDegreeSum.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
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
def SectionDegreeSum.Statement : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (n e δ : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 2) × Fin n) F) (u : Fin n → F),
    IsProjPrime I → IsChowForm I (e + 2) f → IsMultiHomog δ f → linForm u ∉ I →
      ∃ (g : Ideal (MvPolynomial (Fin n) F) → MvPolynomial (Fin (e + 1) × Fin n) F)
        (δW : Ideal (MvPolynomial (Fin n) F) → ℕ),
        (∀ W ∈ (divCycle I u).support,
          IsProjPrime W ∧ IsChowForm W (e + 1) (g W) ∧ IsMultiHomog (δW W) (g W)) ∧
        δ = ∑ W ∈ (divCycle I u).support, divCycle I u W * δW W
end
end GroundTheory.Heights₂.Heights


