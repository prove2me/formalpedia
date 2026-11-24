-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_NoExceptionalOfNoRealZero
-- name    : Formalism_GL3MeanSquares_HookFormulaTorsion_NoExceptionalOfNoRealZero
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T18:33:42.532837+00:00
-- url     : https://prove2.me/theorems/a2ad7d1a-4570-43ac-b2c3-1bc3a2d1fbc7
-- title:
--   No Exceptional Of No Real Zero
-- statement:
--   Definitions and structural lemmas for No Exceptional Of No Real Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/NoExceptionalOfNoRealZero.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_WeightedSumIntegralFormula
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.HermitianLattices.GL2b2
namespace PfN
section A
open Complex
noncomputable def tt (k : ℕ) (s : ℂ) : ℂ :=
  ((8 * (k : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - ((8 * (k : ℝ) + 3 : ℝ) : ℂ) ^ (-s) -
    ((8 * (k : ℝ) + 5 : ℝ) : ℂ) ^ (-s) + ((8 * (k : ℝ) + 7 : ℝ) : ℂ) ^ (-s)
noncomputable def tr (k : ℕ) (σ : ℝ) : ℝ :=
  (8 * (k : ℝ) + 1) ^ (-σ) - (8 * (k : ℝ) + 3) ^ (-σ) - (8 * (k : ℝ) + 5) ^ (-σ) +
    (8 * (k : ℝ) + 7) ^ (-σ)
end A
section B
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition Formalism.HermitianLattices.ZeroFreeRegionGL2
end B
end PfN
end Formalism.HermitianLattices.GL2b2


