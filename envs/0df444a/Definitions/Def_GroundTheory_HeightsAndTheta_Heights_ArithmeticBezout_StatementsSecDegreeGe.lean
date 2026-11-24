-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSecDegreeGe
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSecDegreeGe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:46:38.52581+00:00
-- url     : https://prove2.me/theorems/62f80ea5-0cd2-475a-a055-69f349eda4e5
-- title:
--   Statements Sec Degree Ge
-- statement:
--   Definitions and structural lemmas for Statements Sec Degree Ge, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsSecDegreeGe.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
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
def SecDegreeGe.Statement : Prop :=
  ∀ (k E : Type) [Field k] [PerfectField k] [Field E] [Algebra k E] (n e δ : ℕ)
    (Q : Ideal (MvPolynomial (Fin n) k)) (g : MvPolynomial (Fin (e + 1) × Fin n) k)
    (y : Vertical.Par e n → E),
    IsProjPrime Q → IsChowForm Q (e + 1) g → IsMultiHomog δ g →
      eval (fun j => y (.inr j)) (Vertical.specRest (algebraMap k E) g y) ≠ 0 →
        Module.Finite E (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y) ∧
          δ ≤ Module.finrank E (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y)
end
end GroundTheory.Heights₂.Heights


