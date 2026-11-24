-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSecFiniteUnit
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSecFiniteUnit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:00.695731+00:00
-- url     : https://prove2.me/theorems/b8e02fde-d734-4e02-8c90-6e497086e538
-- title:
--   Statements Sec Finite Unit
-- statement:
--   Definitions and structural lemmas for Statements Sec Finite Unit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsSecFiniteUnit.lean

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
def SecFiniteUnit.Statement : Prop :=
  ∀ (k R : Type) [Field k] [CommRing R] [Algebra k R] (n e δ : ℕ)
    (Q : Ideal (MvPolynomial (Fin n) k)) (g : MvPolynomial (Fin (e + 1) × Fin n) k)
    (y : Vertical.Par e n → R), IsChowForm Q (e + 1) g → IsMultiHomog δ g →
      IsUnit (eval (fun j => y (.inr j)) (Vertical.specRest (algebraMap k R) g y)) →
        Module.Finite R (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap k R))) y)
end
end GroundTheory.Heights₂.Heights


