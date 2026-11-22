-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:17:12.56372+00:00
-- url     : https://prove2.me/theorems/dc4b56e8-ee62-4a97-825e-a7c7c7599ab0
-- title:
--   Markov
-- statement:
--   Definitions and structural lemmas for Markov, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Markov.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.Markov
open Polynomial Real Finset
noncomputable def th (n k : ℕ) : ℝ := (2 * k + 1) * π / (2 * n)
noncomputable def rot (a b : ℝ) : ℕ → ℝ[X] × ℝ[X]
  | 0 => (1, 0)
  | m + 1 => (C a * X * (rot a b m).1 + C b * ((1 - X ^ 2) * (rot a b m).2),
              C b * (rot a b m).1 + C a * X * (rot a b m).2)
end Formalism.FourierDecayAlt.P.Markov
namespace Formalism.FourierDecayAlt.P
open Polynomial
end Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P.Markov
open Polynomial
end Formalism.FourierDecayAlt.P.Markov
namespace Formalism.FourierDecayAlt.P
open Polynomial
end Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


