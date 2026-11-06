-- Prove2me | Definitions.Def_MethodFulfillment_magF
-- name    : MethodFulfillment_magF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:10:14.206903+00:00
-- url     : https://prove2.me/theorems/280620c1-05a4-4228-94ce-e2e37a70eb27
-- title:
--   Magician's threshold rule and CDF recursion (Appendix D)
-- statement:
--   Given consumption probabilities $\mu^1,\mu^2,\dots\in[0,1]$ and a level $\gamma$, the magician of Appendix D computes a sequence of functions $F^t=F_{W^t}$ of $l\in\{0,1,2,\dots\}$ (the CDF of the number $W^t$ of units used before period $t$):
--
--   1. $F^1(l)=1$ for every $l\ge0$, and $F^t(-1)=0$;
--   2. the **threshold** is $\theta^t=\min\{l: F^t(l)\ge\gamma\}$;
--   3. the **availability probability** with $l$ units used is
--   $$a^{tl}=\begin{cases}1 & l<\theta^t,\\[2pt] \dfrac{\gamma-F^t(\theta^t-1)}{F^t(\theta^t)-F^t(\theta^t-1)} & l=\theta^t,\\[2pt] 0 & l>\theta^t;\end{cases}$$
--   4. $F^{t+1}(l)=a^{tl}\mu^t F^t(l-1)+(1-a^{tl}\mu^t)F^t(l)$.
--
--   This is a deterministic recursion in $(\mu,\gamma)$; the magician makes its inventory available in period $t$ with probability $a^{tW^t}$. The helper definitions `prev`, `theta` and `aCoef` are $F(l-1)$, $\theta$ and $a^{tl}$.
--
--   **Formalization Note** Indices are 0-based: the Lean function at $t$ is the paper's $F^{t+1}$, and the Lean input $\mu_t$ is the paper's $\mu^{t+1}$. The threshold is the infimum of a set of natural numbers; for $\gamma\le1$ the set is nonempty, because $F^{t+1}(l)=1$ for $l\ge t$. A division by zero returns $0$.
-- source:
--   Amil, Makhdoumi & Wei, Multi-Item Order Fulfillment Revisited: LP Formulation and Prophet Inequality, manuscript (PDF sha256 197c13b9…), Appendix D, p.58

import Mathlib

namespace MethodFulfillment

/-- `prev F l = F (l - 1)`, with `F (-1) = 0` (the "otherwise" row of the recursion in Appendix D,
p.58, of Amil, Makhdoumi & Wei, manuscript, PDF sha256 197c13b9…). -/
def prev (F : ℕ → ℝ) (l : ℕ) : ℝ :=
  if l = 0 then 0 else F (l - 1)

/-- The magician's threshold `θ = min {l : F(l) ≥ γ}` (Appendix D, p.58).

**Formalization Note.** `sInf` on `ℕ`. For the recursion `magF` with `γ ≤ 1` the set is nonempty,
because `magF μ γ t l = 1` for `l ≥ t`; the junk value `sInf ∅ = 0` only occurs for `γ > 1`. -/
noncomputable def theta (F : ℕ → ℝ) (γ : ℝ) : ℕ :=
  sInf {l : ℕ | γ ≤ F l}

/-- The magician's availability probability given `l` units used,
`a^{tl} = P(A^t = 1 | W^t = l)` (Appendix D, p.58): `1` below the threshold `θ`,
`(γ − F(θ − 1)) / (F(θ) − F(θ − 1))` at the threshold, `0` above it. -/
noncomputable def aCoef (F : ℕ → ℝ) (γ : ℝ) (l : ℕ) : ℝ :=
  if l < theta F γ then 1
  else if l = theta F γ then
    (γ - prev F (theta F γ)) / (F (theta F γ) - prev F (theta F γ))
  else 0

/-- The magician's CDF recursion of Appendix D (Amil, Makhdoumi & Wei, manuscript, PDF sha256
197c13b9…, p.58), as a deterministic function of the consumption probabilities `μ` and the level
`γ`:
`F_{W^{t+1}}(l) = a^{tl} μ^t F_{W^t}(l − 1) + (1 − a^{tl} μ^t) F_{W^t}(l)`, with `F_{W^1} ≡ 1`.

**Formalization Note.** Indices are shifted to 0-based time: `magF μ γ t` is the paper's
`F_{W^{t+1}}`, and `μ t` is the paper's `μ^{t+1}`. So `magF μ γ 0 = 1` everywhere (no unit used
before the first period; the paper's "t = 0" row), and `magF μ γ (t+1)` is computed from
`magF μ γ t`, its threshold and its availability probabilities. `prev` supplies `F(−1) = 0`.
A division by zero in `aCoef` returns `0`. -/
noncomputable def magF (μ : ℕ → ℝ) (γ : ℝ) : ℕ → ℕ → ℝ
  | 0 => fun _ => 1
  | t + 1 => fun l =>
      aCoef (magF μ γ t) γ l * μ t * prev (magF μ γ t) l +
        (1 - aCoef (magF μ γ t) γ l * μ t) * magF μ γ t l

end MethodFulfillment


