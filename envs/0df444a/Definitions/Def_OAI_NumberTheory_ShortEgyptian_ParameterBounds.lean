-- Prove2me | Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
-- name    : OAI_NumberTheory_ShortEgyptian_ParameterBounds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:20:59.814742+00:00
-- url     : https://prove2.me/theorems/e35e50cc-86f9-48bf-b2c4-d6cc9fd44e3f
-- title:
--   Explicit constants for reciprocal phase-sum estimates after $r$ differencing steps
-- statement:
--   For a natural number $r$ the file defines two natural numbers:
--
--   1. **Size constant.**
--
--      $$K_r=\bigl(18\cdot 3^{\,r+3}\bigr)^{4}\,\bigl((r+2)!\bigr)^{2}\,2^{2r};$$
--
--   2. **Power exponent.**
--
--      $$P_r=2^{r}\,(2r+4).$$
--
--   They quantify how long a summation range must be for $r$ steps of van der Corput differencing to save a factor $T$ in an exponential sum of reciprocals. In the surrounding development, with $e(x)=\exp(2\pi i x)$, it is shown that if $T\ge 1$, $U\ge K_r\,T^{P_r}$, $Z\ge 0$ with $U^{2r+3}\le Z^2\le U^{2r+5}$, and $p,q$ are integers with $U\le p$ and $q\le 2U$, then
--
--   $$\Bigl|\sum_{p\le n\le q}e\Bigl(\frac{Z}{n}\Bigr)\Bigr|\le\frac{8U}{T}.$$
--
--   The same constants, taken at a larger index, also appear in the size conditions under which the construction of short expansions is carried out.
--
--   **Formalization Note** The Lean names are `reciprocalConstantNat` and `reciprocalPower`; both are natural numbers and are cast to the reals where they are used.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/ParameterBounds.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/ParameterBounds.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ShortEgyptianFractions mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing

namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

def reciprocalConstantNat (r : ℕ) : ℕ :=
  (18 * 3 ^ (r + 3)) ^ 4 * (r + 2).factorial ^ 2 * 2 ^ (2 * r)

def reciprocalPower (r : ℕ) : ℕ := 2 ^ r * (2 * r + 4)

end ShortEgyptian

end OAI


