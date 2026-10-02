-- Prove2me | Definitions.Def_SennottDP_Tauberian_PowerSeries
-- name    : SennottDP_Tauberian_PowerSeries
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T12:45:37.069966+00:00
-- url     : https://prove2.me/theorems/994161f2-4a01-49e9-bd8b-2ada9c26b085
-- title:
--   Power series with nonnegative terms, radius of convergence, partial sums, Abel and Cesàro means
-- statement:
--   Let $u_0, u_1, u_2, \dots$ be a sequence of nonnegative terms $u_n \in [0, \infty]$. For $\alpha \in [0,\infty)$ the **power series**
--   $$U(\alpha) = \sum_{n=0}^{\infty} \alpha^n u_n \in [0, \infty]$$
--   always has a sum, possibly $+\infty$, because its partial sums increase. Its **radius of convergence** is
--   $$R = \Big(\limsup_{n\to\infty} u_n^{1/n}\Big)^{-1} \in [0, \infty],$$
--   with $0^{-1} = \infty$ and $\infty^{-1} = 0$.
--
--   The **partial sums** are $w_n = \sum_{k=0}^{n-1} u_k$ (so $w_0 = 0$), the **Cesàro means** are $w_n / n$ for $n \ge 1$, and the **Abel means** are $(1-\alpha)U(\alpha)$ for $\alpha \in [0,1)$. All of these take values in $[0,\infty]$.
--
--   These are the objects compared by the Tauberian theorem of Appendix A.4: the Cesàro means as $n \to \infty$ and the Abel means as $\alpha \to 1^-$.
--
--   **Formalization Note** Terms are `ℝ≥0∞`-valued and `α : ℝ≥0`; `U` is an `ℝ≥0∞` `tsum` and `0^0 = 1`, so `U(0) = u_0`. The radius uses the `ℝ≥0∞` `limsup` of `u_n ^ (1/n)` (real exponent; the `n = 0` term is irrelevant) and the `ℝ≥0∞` inverse. `cesaroMean u n = w_n / n` takes the value `0` at `n = 0`, and `abelMean u α = (1 - α) U(α)` uses truncated subtraction, which is exact for `α < 1`; both are only used through limits along `n → ∞` and `α → 1⁻`.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 279, Section A.3, (A.20)–(A.21); p. 282, Theorem A.4.2 (w_n)

import Mathlib

open scoped ENNReal NNReal

namespace SennottDP.Tauberian

/-- Sennott (1999), §A.3, p. 279, (A.20): the power series with nonnegative terms
`U(α) = ∑_{n=0}^∞ α^n u_n`, for `α ∈ [0, ∞)` and a sequence `u_n ∈ [0, ∞]`.
The sum is taken in `[0, ∞]`, so it always exists (it may be `∞`). At `α = 0` the
convention `0^0 = 1` gives `U(0) = u_0`. -/
noncomputable def U (u : ℕ → ℝ≥0∞) (α : ℝ≥0) : ℝ≥0∞ :=
  ∑' n, (α : ℝ≥0∞) ^ n * u n

/-- Sennott (1999), §A.3, p. 279, (A.21): the radius of convergence
`R = (lim sup_{n→∞} u_n^{1/n})^{-1} ∈ [0, ∞]`, with `0⁻¹ = ∞` and `∞⁻¹ = 0`.
(The value of `u_0^{1/0}` is irrelevant to the `lim sup`.) -/
noncomputable def radius (u : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  (Filter.limsup (fun n : ℕ => u n ^ ((n : ℝ)⁻¹)) Filter.atTop)⁻¹

/-- Sennott (1999), p. 282, Theorem A.4.2: the partial sums `w_n = ∑_{k=0}^{n-1} u_k`
(the book uses `n ≥ 1`; `w 0 = 0` is the empty sum). -/
noncomputable def w (u : ℕ → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range n, u k

/-- The Cesàro mean `w_n / n ∈ [0, ∞]` of Theorem A.4.2. Its value at `n = 0` (`0 / 0 = 0`
in `ℝ≥0∞`) plays no role: it is only used through limits as `n → ∞`. -/
noncomputable def cesaroMean (u : ℕ → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  w u n / n

/-- The Abel mean `(1 - α) U(α) ∈ [0, ∞]` of Theorem A.4.2, used for `α ∈ [0, 1)`
(where `1 - α > 0`, so `(1 - α) · ∞ = ∞`); only its behaviour as `α → 1⁻` matters. -/
noncomputable def abelMean (u : ℕ → ℝ≥0∞) (α : ℝ≥0) : ℝ≥0∞ :=
  (1 - (α : ℝ≥0∞)) * U u α

end SennottDP.Tauberian


