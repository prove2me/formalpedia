-- Prove2me | Definitions.Def_TalagrandConc_OnePoint_Basic
-- name    : TalagrandConc_OnePoint_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:36:51.548994+00:00
-- url     : https://prove2.me/theorems/3030dbb4-77e8-4c6f-a884-e30d653d8dca
-- title:
--   Hamming distance $f(A,x)$ to a set, its weighted form, and the constants $a(t)$, $a(\alpha,t)$ of §§2.1–2.2
-- statement:
--   Let $(\Omega,\Sigma,\mu)$ be a probability space, $N\ge 0$ an integer, and write points of the product $\Omega^N$ as $x=(x_1,\dots,x_N)$. This module fixes the objects of Sections 2.1–2.2 of Talagrand's paper.
--
--   1. **Hamming distance to a set** (Eq. (2.1.1)). For $A\subseteq\Omega^N$ and $x\in\Omega^N$,
--   $$f(A,x)=\min\big\{\operatorname{card}\{i\le N:\ x_i\neq y_i\}\ :\ y\in A\big\}\in\{0,1,\dots,N\}\cup\{+\infty\},$$
--   with the convention $f(\emptyset,x)=+\infty$ (infimum of the empty set).
--
--   2. **Weighted Hamming distance** (Eq. (2.1.7), Remark 2.1.3). For weights $a=(a_i)_{i\le N}$,
--   $$f_a(A,x)=\inf\Big\{\sum_{i\le N,\ x_i\neq y_i} a_i\ :\ y\in A\Big\},$$
--   again $+\infty$ when $A=\emptyset$.
--
--   3. **The constant of Lemma 2.1.2**: $a(t)=\tfrac12+\tfrac{e^t+e^{-t}}{4}$.
--
--   4. **The constant of Proposition 2.2.1** (Eq. (2.2.2)): for $\alpha>0$ and $t>0$,
--   $$a(\alpha,t)=\frac{\alpha^{\alpha}}{(\alpha+1)^{\alpha+1}}\,\frac{(e^t-e^{-t/\alpha})^{1+\alpha}}{(1-e^{-t/\alpha})(e^t-1)^{\alpha}},$$
--   and $a(\alpha,0)=1$, its limit as $t\downarrow 0$.
--
--   5. **Exponential moment integrand**: $e^{tz}$ for $t\in\mathbb R$ and $z\in[0,+\infty]$, with $e^{t\cdot\infty}=+\infty$ for $t>0$ and $e^{0\cdot\infty}=1$.
--
--   These are the only objects needed to state the one-point control inequalities: $f(A,\cdot)$ is the quantity whose exponential moments are bounded, and $a(t)$, $a(\alpha,t)$ are the per-coordinate factors that the induction on $N$ produces.
--
--   **Formalization Note** Distances are valued in $[0,\infty]$ (`ℝ≥0∞`), so $f(\emptyset,x)=+\infty$ rather than a junk $0$. Formula (2.2.2) is $0/0$ at $t=0$; the definition uses the value $1$ there, which is the value of the variational form (2.2.3) at $t=0$. The integrand $e^{tz}$ is computed through `EReal.exp`.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 81, Eq. (2.1.1); p. 82, Lemma 2.1.2; p. 84, Remark 2.1.3, Eq. (2.1.7); p. 85, Eq. (2.2.2)

import Mathlib

namespace TalagrandConc.OnePoint

open scoped ENNReal Classical

/-- Talagrand (1995), Eq. (2.1.1), p. 81: the Hamming distance from `x ∈ Ω^N` to a set `A ⊆ Ω^N`,
`f(A, x) = min { card {i ≤ N ; x_i ≠ y_i} ; y ∈ A }`.
It takes values in `ℝ≥0∞`; for `A = ∅` the infimum is `⊤ = +∞`. -/
noncomputable def hammingDistToSet {Ω : Type*} {N : ℕ} (A : Set (Fin N → Ω))
    (x : Fin N → Ω) : ℝ≥0∞ :=
  ⨅ y ∈ A, ((Finset.univ.filter (fun i => x i ≠ y i)).card : ℝ≥0∞)

/-- Talagrand (1995), Eq. (2.1.7), p. 84 (Remark 2.1.3): the weighted Hamming distance
`f(A, x) = inf { Σ { a_i : i ≤ N ; x_i ≠ y_i } : y ∈ A }` for weights `a : Fin N → ℝ`.
It takes values in `ℝ≥0∞`; for `A = ∅` the infimum is `⊤ = +∞`. -/
noncomputable def weightedHammingDistToSet {Ω : Type*} {N : ℕ} (a : Fin N → ℝ)
    (A : Set (Fin N → Ω)) (x : Fin N → Ω) : ℝ≥0∞ :=
  ⨅ y ∈ A, ∑ i ∈ Finset.univ.filter (fun i => x i ≠ y i), ENNReal.ofReal (a i)

/-- Talagrand (1995), p. 82, Lemma 2.1.2: `a(t) = 1/2 + (e^t + e^{-t})/4`. -/
noncomputable def aOne (t : ℝ) : ℝ :=
  1 / 2 + (Real.exp t + Real.exp (-t)) / 4

/-- Talagrand (1995), Eq. (2.2.2), p. 85:
`a(α, t) = α^α / (α+1)^(α+1) · (e^t − e^{−t/α})^(1+α) / ((1 − e^{−t/α}) (e^t − 1)^α)`.
The formula is `0/0` at `t = 0`; there it is given its limit value `1` (the value of the
paper's variational form (2.2.3) at `t = 0`). Intended for `α > 0`, `t ≥ 0`. -/
noncomputable def aAlpha (α t : ℝ) : ℝ :=
  if t = 0 then 1 else
    α ^ α / (α + 1) ^ (α + 1) *
      ((Real.exp t - Real.exp (-t / α)) ^ (1 + α) /
        ((1 - Real.exp (-t / α)) * (Real.exp t - 1) ^ α))

/-- The exponential moment integrand `e^{t z}` for `t : ℝ` and an extended distance
`z : ℝ≥0∞`, computed in `EReal` (so `e^{t·∞} = ∞` for `t > 0` and `e^{0·∞} = 1`). -/
noncomputable def expMul (t : ℝ) (z : ℝ≥0∞) : ℝ≥0∞ :=
  EReal.exp ((t : EReal) * (z : EReal))

end TalagrandConc.OnePoint


