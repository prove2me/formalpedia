-- Prove2me | Definitions.Def_OptHedgeGames_Notation
-- name    : OptHedgeGames_Notation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:38:52.485037+00:00
-- url     : https://prove2.me/theorems/ac14700f-63ee-4a21-9ff8-678e71c3a10f
-- title:
--   Exponential tilt $E_p[z]$, variance $\mathrm{Var}_p$, seminorm $\|\cdot\|_p$, oscillation, $\ell_1$ norm and KL divergence
-- statement:
--   Fix $n$ and vectors in $\mathbb R^n$, indexed by the actions $a\in[n]$. For a probability vector $p$ and $z\in\mathbb R^n$ this module defines the following notions.
--
--   1. The **exponential tilt** of $p$ by $z$: $E_p[z](a)=p(a)e^{z(a)}/\sum_c p(c)e^{z(c)}$.
--   2. The **variance** of $v$ under $p$ and the **variance seminorm**:
--   $$
--   \mathrm{Var}_p(v)=\sum_a p(a)\big(v(a)-\langle p,v\rangle\big)^2,\qquad \|v\|_p=\sqrt{\mathrm{Var}_p(v)}.
--   $$
--   3. The **oscillation** $\mathrm{osc}(z)=\max_a z(a)-\min_a z(a)$ and the **$\ell_1$ norm** $\|v\|_1=\sum_a|v(a)|$.
--   4. The **Kullback–Leibler divergence** $\mathrm{KL}(p\|q)=\sum_{a:p(a)>0}p(a)\log\frac{p(a)}{q(a)}$.
--
--   The Optimistic Hedge update is an exponential tilt, and its analysis measures every loss vector in the seminorm $\|\cdot\|_p$ of the current strategy.
--
--   **Formalization Note** Probability vectors are points of `stdSimplex ℝ (Fin n)`, where the denominator of the tilt is positive. A term with $p(a)=0$ of the KL sum is $0$ in Lean, so the sum over all actions is the restricted sum. The norm $\|\cdot\|_\infty$ of the paper is Mathlib's supremum norm on `Fin n → ℝ`.
-- source:
--   Dagan, Eisen, Erez & Koren, Optimistic Hedge in General-Sum Games, STOC 2027 submission manuscript (sha256 383e3793…), §2 Notation, p.4; Appendix A, p.43

import Mathlib

namespace OptHedgeGames

/-- The **exponential tilt** `E_p[z]` of `p` by `z`: the vector with entries
`E_p[z](a) = p(a) e^{z(a)} / Σ_c p(c) e^{z(c)}`
(Dagan, Eisen, Erez & Koren, *Optimistic Hedge in General-Sum Games*, STOC 2027 submission
manuscript (sha256 383e3793…), §2, Notation, p.4).

**Formalization Note** Real division; for `p ∈ stdSimplex ℝ (Fin n)` the denominator is positive,
so the junk value of `x / 0` is never reached on the paper's domain. -/
noncomputable def tilt {n : ℕ} (p z : Fin n → ℝ) : Fin n → ℝ :=
  fun a => p a * Real.exp (z a) / ∑ c, p c * Real.exp (z c)

/-- The **variance** of `v` with respect to `p`, `Var_p(v) = Σ_a p(a)(v(a) − ⟨p, v⟩)²`
(manuscript sha256 383e3793…, §2, Notation, p.4). -/
noncomputable def var {n : ℕ} (p v : Fin n → ℝ) : ℝ :=
  ∑ a, p a * (v a - ∑ c, p c * v c) ^ 2

/-- The **variance seminorm** `∥v∥_p = √Var_p(v)`
(manuscript sha256 383e3793…, §2, Notation, p.4). -/
noncomputable def vnorm {n : ℕ} (p v : Fin n → ℝ) : ℝ :=
  Real.sqrt (var p v)

/-- The **oscillation** `osc(z) = max_a z(a) − min_a z(a)`
(manuscript sha256 383e3793…, §2, Notation, p.4).

**Formalization Note** `⨆`/`⨅` over the finite type `Fin n`: for `n ≥ 1` these are the maximum and
the minimum. At `n = 0` the value is the junk `0`; there is no probability vector at `n = 0`, so no
statement of the mission reads it. -/
noncomputable def osc {n : ℕ} (z : Fin n → ℝ) : ℝ :=
  (⨆ a, z a) - ⨅ a, z a

/-- The **`ℓ₁` norm** `∥v∥₁ = Σ_a |v(a)|` of a vector (manuscript sha256 383e3793…, used in (33),
p.18, and Lemma A.2, p.44).

**Formalization Note** The `ℓ∞` norm `∥v∥_∞` of the paper is Mathlib's norm `‖v‖` on `Fin n → ℝ`,
the supremum norm. -/
noncomputable def l1Norm {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  ∑ a, |v a|

/-- The **Kullback–Leibler divergence** of probability vectors,
`KL(p ∥ q) = Σ_{a : p(a) > 0} p(a) log (p(a)/q(a))`, for `q(a) > 0` whenever `p(a) > 0`
(manuscript sha256 383e3793…, Appendix A, p.43).

**Formalization Note** A sum over all of `Fin n`: a term with `p(a) = 0` is `0 * _ = 0` in Lean, so
this is the paper's restricted sum. `Real.log` is the natural logarithm. -/
noncomputable def kl {n : ℕ} (p q : Fin n → ℝ) : ℝ :=
  ∑ a, p a * Real.log (p a / q a)

end OptHedgeGames


