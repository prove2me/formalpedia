-- Prove2me | Definitions.Def_ActiveCtxSearch_Errors
-- name    : ActiveCtxSearch_Errors
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:40:53.323+00:00
-- url     : https://prove2.me/theorems/cded695d-963b-42bc-985b-e4216bced2d3
-- title:
--   Classification error, excess error, $\eta_b$, $\varphi$, $\wp$ and the balancing action $b^*$
-- statement:
--   A non-homogeneous linear classifier is $\hat v(\cdot)=\langle\cdot,\hat w\rangle-\hat\beta$, given by the pair $(\hat w,\hat\beta)$.
--
--   1. Under a joint law $Q$ of (context, label), $\mathrm{err}(v\mid Q)=\Pr_{(x,y)\sim Q}[y\neq\operatorname{sgn}(v(x))]$; on a finite data list $D$ the empirical loss is $\sum_{(x,y)\in D}\mathbf 1\{y\neq\operatorname{sgn}(\langle x,w\rangle-\beta)\}$.
--   2. Under the query point $b$,
--   $$\mathrm{err}_b(\hat v)=\Pr_{x\sim P_X,\ \xi\sim P_\xi}\big[\operatorname{sgn}(v(x)+\xi-b)\neq\operatorname{sgn}(\hat v(x))\big],$$
--   the Bayes classifier is $v_b^*(\cdot)=\langle\cdot,w^*\rangle-\mu^*-b$, i.e. the pair $(w^*,\mu^*+b)$, and the excess error is $\Delta\mathrm{err}_b(\hat v)=\mathrm{err}_b(\hat v)-\mathrm{err}_b(v_b^*)$.
--   3. $\eta_b(x)=\Pr[y=1\mid x,b]=\Pr_\xi[v(x)+\xi\ge b]$, $F_\xi(t)=\Pr[\xi\le t]$ and $\varphi(\Delta)=F_\xi(0)-F_\xi(-\Delta)$.
--   4. The label-balance function is $\wp(b)=\Pr_{x\sim P_X,\xi\sim P_\xi}[v(x)+\xi\ge b]$, the probability of positive feedback under the action $b$, and the **label-balancing action** is
--   $$b^*=\sup\{b:\wp(b)\ge 1/2\},$$
--   the unique $b$ with $\wp(b)=1/2$ under (A2)–(A3).
--
--   These are the quantities in which every lemma of the mission is stated.
--
--   **Formalization Note** The source's text writes $\wp(b)=\Pr_x[v(x)\ge b]$ without the noise, but Figure 2 ($\wp(b)=\mathbb E_x[y\mid x,w^*,\mu^*,b]$), the proofs of Lemmas 1 and 4, and the quantity Algorithm 2 estimates are the label probability, which is the reading used. The supremum is a real number for every instance, so $b^*$ involves no choice.
-- source:
--   Chen, Liu & Wang, Active Learning for Contextual Search with Binary Feedback, arXiv:2110.01072v2, §3.1, p.10 (b*); Figure 2, p.11 (℘); §3.2, p.12, Eqs. (3), (4); Appendix A, p.28, Eqs. (27), (28); Lemma 9, p.29 (err(v|Q))

import Mathlib
import Definitions.Def_ActiveCtxSearch_Stream

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

namespace ActiveCtxSearch

variable {d : ℕ}

/-- The error `err(v|Q) = Pr_{(x,y)∼Q}[y ≠ sgn(v(x))]` of the non-homogeneous linear classifier
`v(·) = ⟨·, w⟩ − β`, given as the pair `c = (w, β)`, under a joint law `Q` of (context, label)
(arXiv:2110.01072v2, Lemma 9, p.29). -/
noncomputable def clsErr (Q : Measure (E d × ℤ)) (c : E d × ℝ) : ℝ :=
  Q.real {p | p.2 ≠ sgn (⟪p.1, c.1⟫ - c.2)}

/-- The empirical 0-1 loss `Σ_{(x,y) ∈ D} 1{y ≠ sgn(⟨x, w⟩ − β)}` of the classifier `c = (w, β)` on a
finite list `D` of (context, label) pairs (arXiv:2110.01072v2, Algorithm 3, lines 3 and 14, p.13;
Lemma 9, p.29). -/
noncomputable def empLoss (D : List (E d × ℤ)) (c : E d × ℝ) : ℕ :=
  D.countP (fun p => decide (p.2 ≠ sgn (⟪p.1, c.1⟫ - c.2)))

namespace Problem

/-- The error `err_b(v̂) = Pr_{x∼P_X, ξ∼P_ξ}[sgn(v(x) + ξ − b) ≠ sgn(v̂(x))]` of the classifier
`v̂(·) = ⟨·, ŵ⟩ − β̂`, given as `c = (ŵ, β̂)`, under the query point `b`
(arXiv:2110.01072v2, Eq. (3), p.12). -/
noncomputable def err (I : Problem d) (b : ℝ) (c : E d × ℝ) : ℝ :=
  (I.PX.prod I.Pξ).real {z | sgn (I.v z.1 + z.2 - b) ≠ sgn (⟪z.1, c.1⟫ - c.2)}

/-- The Bayes classifier `v*_b(·) = ⟨·, w*⟩ − μ* − b` at the query point `b`, as the pair
`(w*, μ* + b)` (arXiv:2110.01072v2, p.12). -/
noncomputable def bayes (I : Problem d) (b : ℝ) : E d × ℝ := (I.w, I.μ + b)

/-- The excess error `Δerr_b(v̂) = err_b(v̂) − err_b(v*_b)` (arXiv:2110.01072v2, Eq. (4), p.12). -/
noncomputable def excessErr (I : Problem d) (b : ℝ) (c : E d × ℝ) : ℝ :=
  I.err b c - I.err b (I.bayes b)

/-- The conditional label probability `η_b(x) = Pr[y = 1 | x, b] = Pr_{ξ∼P_ξ}[v(x) + ξ ≥ b]`
(arXiv:2110.01072v2, Eq. (27), p.28). -/
noncomputable def eta (I : Problem d) (b : ℝ) (x : E d) : ℝ := I.Pξ.real {ξ | b ≤ I.v x + ξ}

/-- The noise distribution function `F_ξ(t) = Pr[ξ ≤ t]`. -/
noncomputable def cdfξ (I : Problem d) (t : ℝ) : ℝ := I.Pξ.real (Set.Iic t)

/-- The link `φ(Δ) = F_ξ(0) − F_ξ(−Δ)` (arXiv:2110.01072v2, Eq. (28), p.28). -/
noncomputable def phi (I : Problem d) (Δ : ℝ) : ℝ := I.cdfξ 0 - I.cdfξ (-Δ)

/-- The label-balance function `℘(b) = Pr_{x∼P_X, ξ∼P_ξ}[v(x) + ξ ≥ b]`, the probability of the
feedback `y = 1` under the action `b` (arXiv:2110.01072v2, Figure 2, p.11: `℘(b) = E_x[y | x, w*, μ*, b]`;
proof of Lemma 2, p.17; Lemma 4, p.18).

**Formalization Note** The text of pp.10–12 and 17–18 writes `℘(b) = Pr_x[v(x) ≥ b]`, without the noise.
Figure 2, the proofs of Lemmas 1 and 4 (`1/2 = Pr_x[y = 1 | b*]`, `Pr[y = 1 | x, b̂] = φ(Δ_{b*}(x) − s)`) and the
quantity Algorithm 2 estimates are the label probability, which is the reading used here. -/
noncomputable def labelProb (I : Problem d) (b : ℝ) : ℝ :=
  (I.PX.prod I.Pξ).real {z | b ≤ I.v z.1 + z.2}

/-- The label-balancing action `b*`, the value with `℘(b*) = 1/2` (arXiv:2110.01072v2, §3.1, p.10).

**Formalization Note** It is defined as `sup {b : ℘(b) ≥ 1/2}`, which is a real number for every
instance (`℘` decreases from `1` to `0`). Under (A2)–(A3) `℘` is continuous and strictly decreasing
near its median, so this is the unique `b` with `℘(b) = 1/2` (p.10: "such a value of `b*` exists and is
unique"); the definition does not depend on a choice. -/
noncomputable def bStar (I : Problem d) : ℝ := sSup {b | 1 / 2 ≤ I.labelProb b}

end Problem

end ActiveCtxSearch


