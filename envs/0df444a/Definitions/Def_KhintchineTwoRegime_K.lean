-- Prove2me | Definitions.Def_KhintchineTwoRegime_K
-- name    : KhintchineTwoRegime_K
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:35.422741+00:00
-- url     : https://prove2.me/theorems/30f67342-eb15-4ed6-895c-d82e889bff93
-- title:
--   Rademacher first moment $K_n(\omega)=\mathbb E|\sum_i\omega_i\epsilon_i|$
-- statement:
--   Let $\epsilon_1,\dots,\epsilon_n$ be independent Rademacher random variables (each equal to $\pm1$ with probability $1/2$) and let $\omega\in\mathbb R^n$. The **first absolute moment** of the Rademacher sum is
--   $$
--   K_n(\omega)=\mathbb E\Bigl|\sum_{i=1}^n\omega_i\epsilon_i\Bigr| = 2^{-n}\sum_{\epsilon\in\{-1,1\}^n}\Bigl|\sum_{i=1}^n\omega_i\epsilon_i\Bigr|,
--   $$
--   the average size of the linear form $\omega\cdot x$ on the Hamming cube. Every inequality of the mission is a lower bound on $K_n$.
--
--   **Formalization Note** The expectation is the uniform average over the $2^n$ sign vectors $\epsilon:\{0,\dots,n-1\}\to\{\mathrm{true},\mathrm{false}\}$, with true read as $+1$ and false as $-1$. This is the exact form of the platform theorem `ModernOnlineLearning.LowerBounds.theorem_A_14_p1` (Szarek's sharp bound), which the mission reuses.
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), §1, p.1

import Mathlib

namespace KhintchineTwoRegime

/-- The Rademacher first moment `K_n(ω) = E|∑ᵢ ωᵢ εᵢ|` (Fang–Wang, *A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions*, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), §1, p.1).

**Formalization Note** The expectation over independent Rademacher signs `ε₁, …, εₙ` is the
uniform average over all `2ⁿ` sign vectors `ε : Fin n → Bool`, with `true ↦ +1` and
`false ↦ −1`. This is the exact form used by the platform theorem
`ModernOnlineLearning.LowerBounds.theorem_A_14_p1`. Coordinates are 0-based: the paper's `ω₁`
is `ω 0`. -/
noncomputable def K (n : ℕ) (ω : Fin n → ℝ) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹ * ∑ ε : Fin n → Bool, |∑ i, (if ε i then (1 : ℝ) else -1) * ω i|

end KhintchineTwoRegime


