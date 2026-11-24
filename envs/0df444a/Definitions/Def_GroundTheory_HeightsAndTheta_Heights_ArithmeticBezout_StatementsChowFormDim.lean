-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChowFormDim
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChowFormDim
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:34.888415+00:00
-- url     : https://prove2.me/theorems/995919e5-b74b-40ae-bbe3-f3762c641feb
-- title:
--   Statements Chow Form Dim
-- statement:
--   Definitions and structural lemmas for Statements Chow Form Dim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsChowFormDim.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
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
def ChowFormDimLe.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin k × Fin n) F),
    IsProjPrime I → IsChowForm I k f → ringKrullDim (MvPolynomial (Fin n) F ⧸ I) ≤ k
end
end GroundTheory.Heights₂.Heights


