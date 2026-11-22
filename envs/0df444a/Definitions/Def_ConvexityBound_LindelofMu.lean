-- Prove2me | Definitions.Def_ConvexityBound_LindelofMu
-- name    : ConvexityBound_LindelofMu
-- status  : Definition
-- author  : @emmgaml
-- created : 2026-11-22T15:22:09.126254+00:00
-- url     : https://prove2.me/theorems/aea46808-722d-4cfa-88a4-ad12024faf3d
-- title:
--   The Lindelöf $\mu$-function: order of growth of a function on the vertical line $\operatorname{Re}(s)=\sigma$
-- statement:
--   **The Lindelöf $\mu$-function.** Let $f$ be a complex-valued function of a complex variable and let $\sigma\in\mathbb R$. The *Lindelöf function* of $f$ measures the order of growth of $f$ on the vertical line $\operatorname{Re}(s)=\sigma$:
--
--   $$\mu(\sigma)=\mu_f(\sigma):=\inf\bigl\{\,k\in\mathbb R_{\ge0}\ :\ f(\sigma+it)=O\bigl(|t|^{k}\bigr)\ \text{as}\ |t|\to\infty\,\bigr\}\ \in[0,\infty],$$
--
--   where $f(\sigma+it)=O(|t|^k)$ as $|t|\to\infty$ means that there are constants $C,T$ with $|f(\sigma+it)|\le C|t|^k$ for all real $t$ with $|t|\ge T$, and where $\mu(\sigma)=\infty$ if no such exponent $k$ exists.
--
--   `ConvexityBound.lindelofMu f σ` is this quantity.
--
--   For example $\mu(\sigma)=0$ whenever $f$ is bounded on the line $\operatorname{Re}(s)=\sigma$ (in particular for a Dirichlet series in its half-plane of absolute convergence), and $\mu_f\equiv1$ for $f(s)=s$. For the Riemann zeta function the Lindelöf hypothesis is the statement $\mu_\zeta(\tfrac12)=0$.
--
--   This is the function $\mu(\sigma)$ of the classical theory of functions of finite order in a strip. The source recalls it in §B.1.1.1, equation (B.1.1.2), and uses its convexity (Lemma B.1.1.1) to deduce the convexity bound for finite Hecke $L$-functions (Proposition B.1.1.3).
--
--   **Formalization Note.** $f$ is a total function `ℂ → ℂ`; only its values on the line matter. "As $|t|\to\infty$" is the cocompact filter of $\mathbb R$, so both directions $t\to\pm\infty$ are controlled. The value lies in `ℝ≥0∞` and is `⊤` exactly when $f$ satisfies no polynomial bound on the line, so there is no junk value. As in (B.1.1.2) of the source, the infimum is over exponents $k\ge0$; thus $\mu\ge0$, and a function which decays on the line still has $\mu=0$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 589, §B.1.1.1 and equation (B.1.1.2) in Lemma B.1.1.1; classical reference: E. C. Titchmarsh, The Theory of Functions, Oxford University Press, 1939, Ch. 9, §9.41 (as cited by the paper at that spot)

import Mathlib

/-!
# The Lindelöf `μ`-function (order of growth on vertical lines)

For a function `f : ℂ → ℂ` and a real number `σ`, the Lindelöf function `μ(σ) = μ_f(σ)` is the
infimum of the real numbers `k ≥ 0` such that

`f(σ + i t) = O(|t| ^ k)` as `|t| → ∞`.

This is the function `μ(σ)` of E. C. Titchmarsh, *The Theory of Functions*, §9.41, in the form
of A. M. Masullo, *The Music of the Primes*, (B.1.1.2), p. 589, where the infimum is taken over
non-negative exponents (so that `μ ≥ 0`, and `μ(σ) = 0` whenever `f` is bounded on the line
`Re s = σ`).

`ConvexityBound.lindelofMu f σ` takes values in `[0, ∞]`: it is `∞` exactly when `f` satisfies no
polynomial bound on the line `Re s = σ`, so there is no junk value.
-/

open Filter Asymptotics
open scoped ENNReal NNReal

namespace ConvexityBound

/-- The Lindelöf `μ`-function of `f` at the abscissa `σ`: the infimum, in `[0, ∞]`, of the
exponents `k ≥ 0` with `f(σ + i t) = O(|t| ^ k)` as `|t| → ∞` (i.e. along the cocompact filter of
`ℝ`).  It equals `∞` if there is no such exponent. -/
noncomputable def lindelofMu (f : ℂ → ℂ) (σ : ℝ) : ℝ≥0∞ :=
  sInf ((fun k : ℝ≥0 => (k : ℝ≥0∞)) ''
    {k : ℝ≥0 | (fun t : ℝ => f ((σ : ℂ) + (t : ℂ) * Complex.I)) =O[cocompact ℝ]
      fun t : ℝ => |t| ^ (k : ℝ)})

end ConvexityBound


