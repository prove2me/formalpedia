-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RelevantMonotoneOfParts
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_RelevantMonotoneOfParts
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T15:14:19.096077+00:00
-- url     : https://prove2.me/theorems/15e33684-27e5-4a35-8dba-8b1e00760896
-- title:
--   Relevant Monotone Of Parts
-- statement:
--   Definitions and structural lemmas for Relevant Monotone Of Parts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RelevantMonotoneOfParts.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerFourthCondition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P
namespace C2x4
variable {m : ℕ}
def Cond (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) : Prop :=
  ∀ a b : Fin m, a < b → w b < w a →
    ((b.val = a.val + 1 ↔ (w a).val = (w b).val + 1) ∧ (b.val = a.val + 1 → d a = d b))
def IsCut (w : Equiv.Perm (Fin m)) (c : Fin m) : Prop := ∀ x y : Fin m, x ≤ c → c < y → w x < w y
open Classical in

noncomputable def blk (w : Equiv.Perm (Fin m)) (a : Fin m) : ℕ :=
  (Finset.univ.filter (fun c : Fin m => c < a ∧ IsCut w c)).card
end C2x4
open C2x4
end Formalism.FourierDecayAlt.P


