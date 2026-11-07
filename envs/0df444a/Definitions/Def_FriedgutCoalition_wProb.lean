-- Prove2me | Definitions.Def_FriedgutCoalition_wProb
-- name    : FriedgutCoalition_wProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:33:41.724368+00:00
-- url     : https://prove2.me/theorems/35439c51-2773-4629-82f0-7fb77c44b788
-- title:
--   Product-distribution probabilities $\Pr_{x\sim\sigma^n}[P(x)]$, the uniform distribution $U_r$ and the $p$-biased bit $\mu_p$
-- statement:
--   Let $\Sigma$ be a finite alphabet, $\iota$ a finite set of coordinates and $\sigma:\Sigma\to\mathbb R$ a weight function. For an event $P$ on $\Sigma^\iota$,
--
--   $$\Pr_{x\sim\sigma^\iota}[P(x)]=\sum_{x\in\Sigma^\iota}[P(x)]\prod_{i\in\iota}\sigma(x_i).$$
--
--   When $\sigma$ is a distribution this is the probability of $P$ under the product distribution $\sigma^\iota$, in which each coordinate is drawn independently from $\sigma$.
--
--   Two distributions are used throughout:
--
--   1. the uniform distribution $U_r$ on $[r]=\{1,\dots,r\}$, with weight $1/r$ on each value, so that $U_r^n$ is the uniform distribution on $[r]^n$;
--   2. the $p$-biased bit $\mu_p$ on $\{0,1\}$, which equals $1$ with probability $p$ and $0$ with probability $1-p$, so that $\mu_p^n$ sets each of $n$ bits to $1$ independently with probability $p$.
--
--   These are the probability spaces in which all of the paper's finite-alphabet quantities are computed.
--
--   **Formalization Note** A distribution is a weight function into $\mathbb R$; the theorems state nonnegativity and total mass one where the paper says "distribution". $[r]$ is `Fin r`, so the uniform weights at $r=0$ are the zero function, and statements that need a uniform distribution assume $r\ge1$. $\{0,1\}$ is `Bool`, with `true` the value $1$.
-- source:
--   Chattopadhyay, Gurumukhani, A Resolution of Friedgut's Conjecture on Influential Coalitions, arXiv:2609.16401 (held file sha256 51f298ff…), §2 notation, p.4 (U^r_n); §2.1, p.5 (σⁿ, µ_p)

import Mathlib

namespace FriedgutCoalition

/-!
# Product-distribution probabilities on a finite alphabet

E. Chattopadhyay, M. Gurumukhani, *A Resolution of Friedgut's Conjecture on Influential Coalitions*,
arXiv:2609.16401 (held file sha256 51f298ff…), §2.1, p.5 (the product distribution `σⁿ`), §2 notation
p.4 (`Uⁿ_r`), §2.1 p.5 (`µ_p`).

**Formalization Note.** A distribution `σ` on a finite alphabet `α` is a weight function `α → ℝ`. The
hypotheses "`σ ≥ 0`, `∑ σ = 1`" are stated by the theorems that need them, exactly where the paper says
"distribution". `wProb σ P` is `Pr_{x ∼ σ^ι}[P x]`, an exact finite sum. The alphabet `[r] = {1, …, r}`
is `Fin r`, so `unif r` is the uniform distribution on `[r]`; at `r = 0` it is the zero function (Lean's
`1 / 0 = 0`), and statements that need a uniform distribution say `0 < r`. The output alphabet
`{0, 1}` is `Bool`, and `bern p` is `µ_p` on one bit: `true` (the paper's `1`) has probability `p`.
-/

/-- `Pr_{x ∼ σ^ι}[P x] = ∑_x [P x] ∏_i σ(x_i)`, the probability of an event under the product of the
weights `σ`. -/
noncomputable def wProb {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (σ : α → ℝ) (P : (ι → α) → Prop) : ℝ := by
  classical
  exact ∑ x : ι → α, if P x then ∏ i, σ (x i) else 0

/-- The uniform distribution `U_r` on `[r]`, as weights `1 / r` on `Fin r`. -/
noncomputable def unif (r : ℕ) : Fin r → ℝ := fun _ => 1 / (r : ℝ)

/-- The `p`-biased distribution `µ_p` on one bit: `true` with probability `p`, `false` with
probability `1 − p`. -/
noncomputable def bern (p : ℝ) : Bool → ℝ := fun c => if c then p else 1 - p

end FriedgutCoalition


