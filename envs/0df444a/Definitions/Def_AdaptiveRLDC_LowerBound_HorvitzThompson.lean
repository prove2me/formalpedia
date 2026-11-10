-- Prove2me | Definitions.Def_AdaptiveRLDC_LowerBound_HorvitzThompson
-- name    : AdaptiveRLDC_LowerBound_HorvitzThompson
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T14:56:27.622872+00:00
-- url     : https://prove2.me/theorems/f1f6645c-3238-4ed8-b5af-f6f1c6460c04
-- title:
--   Horvitz–Thompson estimator and discrete derivative
-- statement:
--   For $p\in(0,1]$, finite set weights $\mu$, and a binary vector $x$, let $x_S=\prod_{i\in S}x_i$, including $x_\varnothing=1$. Define
--   $$R_{\mu,p}(x)=\sum_S\mu(S)p^{-|S|}x_S.$$
--   The discrete derivative in coordinate $i$ is $f(x^{i\to1})-f(x^{i\to0})$, independent of the original coordinate value. This estimator and its actual coefficients are shared by the capped optimization and the bias statement.
-- source:
--   Guy Goldberg, Tom Gur, Sidhant Saraogi, Lower Bounds for Adaptive Relaxed Locally Decodable Codes via the Capped Horvitz–Thompson Estimator, STOC 2027 submission #1071 (October 2026), Definitions 4.1 and 4.3, printed p.16, PDF p.17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1071.pdf; sha256 fc1b12e269801cef0033faea9f18d9873b62d5b18dbd21242a4daefc43048a5b. Title-page date November 3, 2026; submission status does not assert acceptance.

import Mathlib
import Definitions.Def_AdaptiveRLDC_LowerBound_FiniteWeights

open scoped BigOperators
noncomputable section

namespace AdaptiveRLDC.LowerBound

open Classical

/-- Definition 4.1: the empty monomial is one. -/
def monomial {n : ℕ} (x : Cube n) (S : Sets n) : ℝ :=
  ∏ i ∈ S, if x i then (1 : ℝ) else 0

def htTerm {n : ℕ} (μ : Sets n → ℝ) (p : ℝ) (x : Cube n) (S : Sets n) : ℝ :=
  μ S / p ^ S.card * monomial x S

def ht {n : ℕ} (μ : Sets n → ℝ) (p : ℝ) (x : Cube n) : ℝ := ∑ S, htTerm μ p x S

/-- Definition 4.3: the value ignores the original i-th coordinate. -/
def discreteDerivative {n : ℕ} (f : Cube n → ℝ) (i : Fin n) (x : Cube n) : ℝ :=
  f (Function.update x i true) - f (Function.update x i false)

end AdaptiveRLDC.LowerBound


