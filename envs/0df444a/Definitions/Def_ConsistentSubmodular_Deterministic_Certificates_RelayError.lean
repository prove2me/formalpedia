-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_RelayError
-- name    : ConsistentSubmodular_Deterministic_Certificates_RelayError
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:08:18.995209+00:00
-- url     : https://prove2.me/theorems/411aec2e-33ef-42ac-8876-d222bb842acc
-- title:
--   Relay error polynomial $b^2-b(2A+2w-D)+D(A+w)$ for forward relays
-- statement:
--   The file defines a single real-valued function used to measure the error of a credit-to-edge estimate for forward relays between stages of an atomic profile.
--
--   - `relayError` $A\,D\,b\,w$, for real parameters $A,D,b,w$:
--   $$\mathrm{relayError}(A,D,b,w)=b^2-b\,(2A+2w-D)+D\,(A+w).$$
--   It is a monic quadratic in $b$ with linear coefficient $-(2A+2w-D)$ and constant term $D(A+w)$; the parameters stand for the designated mass $A$, the deficit budget $D$, the baseline $b$, and the residual $w$.
--
--   The error vanishes or has a controlled sign exactly where the relay edge meets the safety level $3/4$, and its sign is analysed by quadratic bounds between endpoints.
--
--   These definitions serve the safety analysis of forward relays in the deterministic $3/4$ certificate construction (Appendix B).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/RelayError.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_ScalarGeometry

namespace ConsistentSubmodular

def relayError (A D b w : ℝ) : ℝ :=
  b ^ 2 - b * (2 * A + 2 * w - D) + D * (A + w)

end ConsistentSubmodular


