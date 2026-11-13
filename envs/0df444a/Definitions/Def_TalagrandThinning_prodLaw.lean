-- Prove2me | Definitions.Def_TalagrandThinning_prodLaw
-- name    : TalagrandThinning_prodLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:40:09.428012+00:00
-- url     : https://prove2.me/theorems/cbcc03ef-07e1-4680-a04a-18469bb7be87
-- title:
--   The product measure $\mu_s$ on the cube and its expectation
-- statement:
--   For $0<s<1$ the **product measure** $\mu_s$ on $\{0,1\}^N$ includes each element of $[N]$ independently with probability $s$:
--
--   $$\mu_s(\{A\}) = s^{|A|}(1-s)^{N-|A|}\qquad(A\subseteq[N]).$$
--
--   The expectation of a real function $f$ on the cube under $\mu_s$ is $\mathbb E_{\mu_s}f=\sum_{A}\mu_s(\{A\})f(A)$.
--
--   $\mu_t$ is the law of the thinning mask $X_t$ and $\mu_p$ the law of the dominating random set $X_p$.
--
--   **Formalization Note** The weight is written as $\prod_i (s \text{ if } i\in A \text{ else } 1-s)$, which equals $s^{|A|}(1-s)^{N-|A|}$. The measure is the finite sum of weighted point masses. The definition is total in $s$; every statement assumes $0<s<1$, as the paper does.
-- source:
--   Fang & Wang, A Note on a Result of Chen Li: the Thinning Problem via the Kernel Method, arXiv:2609.18458 (held version dated Sep 12, 2026, sha256 68a0f38d…), §1.1, p.2 (µ_s); §2, p.3 (𝔼_{µ_s})

import Mathlib
import Definitions.Def_TalagrandThinning_Cube

set_option autoImplicit false

open MeasureTheory

namespace TalagrandThinning

/-- The product weight `s^{|A|}(1-s)^{N-|A|}` of a point of the cube
(arXiv:2609.18458, held version dated Sep 12, 2026, sha256 68a0f38d…, §1.1, p.2).

**Formalization Note** Written as the product over coordinates of `s` (if `i ∈ A`) or `1 - s`
(if `i ∉ A`), which equals `s^{|A|}(1-s)^{N-|A|}`. -/
noncomputable def weight {N : ℕ} (s : ℝ) (x : Cube N) : ℝ :=
  ∏ i, if x i then s else 1 - s

/-- The product measure `µ_s` on the cube: `µ_s(A) = s^{|A|}(1-s)^{N-|A|}` for `A ⊆ [N]`
(arXiv:2609.18458, held version dated Sep 12, 2026, sha256 68a0f38d…, §1.1, p.2, "For 0 < s < 1, let µ_s be the product measure").

**Formalization Note** `µ_s` is the finite sum of point masses `∑_x µ_s({x}) δ_x`, with
`µ_s({x}) = weight s x`. The paper defines it for `0 < s < 1`; the Lean definition is total, and
every statement that uses it assumes `0 < s < 1` (outside `[0,1]` the weights are not
probabilities). Each coordinate is in the random set with probability `s`. -/
noncomputable def prodLaw (N : ℕ) (s : ℝ) : Measure (Cube N) :=
  ∑ x : Cube N, ENNReal.ofReal (weight s x) • Measure.dirac x

/-- The expectation `E_{µ_s} f = ∑_x µ_s({x}) f(x)` of a real function on the cube under `µ_s`
(arXiv:2609.18458, held version dated Sep 12, 2026, sha256 68a0f38d…, §2, p.3, as used in (2.1) and (2.6)).

**Formalization Note** A finite weighted sum, so it is defined for every real `f` (no
integrability side condition is needed on a finite cube). -/
noncomputable def expect {N : ℕ} (s : ℝ) (f : Cube N → ℝ) : ℝ :=
  ∑ x : Cube N, weight s x * f x

end TalagrandThinning


