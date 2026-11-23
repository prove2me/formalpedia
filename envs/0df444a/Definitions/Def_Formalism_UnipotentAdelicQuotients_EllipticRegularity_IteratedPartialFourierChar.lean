-- Prove2me | Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_IteratedPartialFourierChar
-- name    : Formalism_UnipotentAdelicQuotients_EllipticRegularity_IteratedPartialFourierChar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:34:36.464106+00:00
-- url     : https://prove2.me/theorems/e9d8074d-43a5-4d1c-9352-c8a30d76a44b
-- title:
--   Iterated Partial Fourier Char
-- statement:
--   Definitions and structural lemmas for Iterated Partial Fourier Char, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/IteratedPartialFourierChar.lean

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable def eL {d : ℕ} (ξ : E d) : E d →L[ℝ] ℂ :=
  (-(2 * (Real.pi : ℂ) * Complex.I)) • (Complex.ofRealCLM.comp (innerSL ℝ ξ))
end ZetaZeros.D.EllReg


