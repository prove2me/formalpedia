-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagSpanVanishing
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagSpanVanishing
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T16:09:25.224493+00:00
-- url     : https://prove2.me/theorems/1db989b3-798b-4f41-86bf-746402498ec2
-- title:
--   Flag Span Vanishing
-- statement:
--   Definitions and structural lemmas for Flag Span Vanishing, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FlagSpanVanishing.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LinearChangeOfVariablesBis
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
namespace FlagSpanVanishing
open C2x5 C2x7
variable {k r : ℕ}
def wpart (s : B.Mat k r) : B.Mat k r := fun i j =>
  if r ≤ i.val ∧ i.val ≤ r + k ∧ r ≤ j.val ∧ j.val ≤ r + k then s i j else if i = j then 1 else 0
end FlagSpanVanishing
namespace FlagSpanVanishing
open C2x5 C2x7
variable {k r : ℕ}
end FlagSpanVanishing
open C2x5 C2x7 FlagSpanVanishing
end Formalism.FourierDecayAlt.P


