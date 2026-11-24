-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSecDegreeLe
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSecDegreeLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:46:54.592547+00:00
-- url     : https://prove2.me/theorems/47e60038-433f-480c-b90c-a0eb13e85ebc
-- title:
--   Statements Sec Degree Le
-- statement:
--   Definitions and structural lemmas for Statements Sec Degree Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsSecDegreeLe.lean

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
def SecDegreeLe.Statement : Prop :=
  ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (n e δ : ℕ)
    (Q : Ideal (MvPolynomial (Fin n) k)) (g : MvPolynomial (Fin (e + 1) × Fin n) k)
    (y : Vertical.Par e n → E),
    IsProjPrime Q → IsChowForm Q (e + 1) g → IsMultiHomog δ g →
      Module.Finite E (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y) →
      IsDomain (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y) →
      Algebra.IsSeparable E (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y) →
      Vertical.specRest (algebraMap k E) g y ≠ 0 →
        Module.finrank E (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y) ≤ δ
namespace SecDegreeLe
abbrev pointSecAlg : Type :=
  Vertical.SecAlg ((⊥ : Ideal (MvPolynomial (Fin 1) ℚ)).map (MvPolynomial.map (algebraMap ℚ ℚ)))
    (fun _ : Vertical.Par 0 1 => (1 : ℚ))
end SecDegreeLe
end
end GroundTheory.Heights₂.Heights


