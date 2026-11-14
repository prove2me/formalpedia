-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_ScalarIdentities
-- name    : ConsistentSubmodular_Deterministic_Certificates_ScalarIdentities
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:06:27.885811+00:00
-- url     : https://prove2.me/theorems/13aa28ad-18a7-4ed2-87f3-d4d344f1ae95
-- title:
--   Exit-segment square identity for the $3/4$ certificate: $4R\big(L+(1-y)^2R+yG-\tfrac34(L+G)\big)$
-- statement:
--   This file contains no definitions. It proves one polynomial identity in the real variables $L,G,R,y$ (the remaining variables declared are unused):
--   $$4R\Big(L+(1-y)^2R+yG-\tfrac34\,(L+G)\Big)=\big(2R(1-y)-G\big)^2+R\,(L+G)-G^2 .$$
--   The left side is $4R$ times the excess over the level $\tfrac34(L+G)$ of the quantity $L+(1-y)^2R+yG$. The latter is the value along an exit segment parametrized by $y$, with a baseline $L$, a residual $R$ and a gain $G$. The identity is checked by `ring`.
--
--   It rewrites the safety margin of an exit segment as a perfect square plus a term independent of $y$, so that the margin is controlled at its minimum over $y$ in the verification of the $3/4$ certificates of Section 3 and Appendix B.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/ScalarIdentities.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib

namespace ConsistentSubmodular

variable (H P c α β L G R y A δ w q d d₀ kpar u z T Pt g a η n b : ℝ)

theorem exit_square_identity :
    4 * R * (L + (1 - y) ^ 2 * R + y * G - (3 : ℝ) / 4 * (L + G)) =
      (2 * R * (1 - y) - G) ^ 2 + R * (L + G) - G ^ 2 := by
  ring

end ConsistentSubmodular


