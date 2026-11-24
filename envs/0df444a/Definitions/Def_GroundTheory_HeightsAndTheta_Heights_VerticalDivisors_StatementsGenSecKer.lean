-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsGenSecKer
-- name    : GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsGenSecKer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:43:53.539042+00:00
-- url     : https://prove2.me/theorems/16c8e6ec-f64d-492f-8696-f3f8683b0469
-- title:
--   Statements Gen Sec Ker
-- statement:
--   Definitions and structural lemmas for Statements Gen Sec Ker, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/StatementsGenSecKer.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
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
def GenSecKer.Statement : Prop :=
  ∀ (k : Type) [Field k] (n e : ℕ) (Q : Ideal (MvPolynomial (Fin n) k))
    (g : MvPolynomial (Fin (e + 1) × Fin n) k), IsProjPrime Q → IsChowForm Q (e + 1) g →
      RingHom.ker ((Ideal.Quotient.mk
          (secIdeal (Q.map (MvPolynomial.map (algebraMap k (GenParField k e n)))) (genPar k e n))).comp
        (MvPolynomial.map (algebraMap k (GenParField k e n)))) = Q
end
end GroundTheory.Heights₂.Heights.Vertical


