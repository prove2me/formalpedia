-- Prove2me | Definitions.Def_CovariateSAA_Optim
-- name    : CovariateSAA_Optim
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:27:39.770189+00:00
-- url     : https://prove2.me/theorems/d2ec229b-3914-4e7b-8648-ad62ac81035e
-- title:
--   Minimum value, minimizer set and deviation $\mathbb D(A,B)$ of sets
-- statement:
--   For a real function $h$ and a set $Z$, the module defines the **minimum value** $\min_{z\in Z} h(z)$, written as the infimum of $h(Z)$, and the **set of minimizers**
--   $$
--   \operatorname*{arg\,min}_{z\in Z} h(z) = \{\, z\in Z : h(z)\le h(z') \text{ for all } z'\in Z \,\}.
--   $$
--   For sets $A, B$ of a metric space it defines the **deviation** of $A$ from $B$,
--   $$
--   \mathbb D(A,B) := \sup_{v\in A} \operatorname{dist}(v,B), \qquad \operatorname{dist}(v,B) := \inf_{w\in B}\|v-w\|.
--   $$
--
--   These are the optimal value $v^*(x)$ and solution set $S^*(x)$ of the true problem (1), their ER-SAA counterparts $\hat v^{ER}_n(x)$ and $\hat S^{ER}_n(x)$ of (4), the minimum and argmin of Lemma 10, and the distance $\mathbb D(\hat S^{ER}_n(x), S^*(x))$ in which Theorem 5 measures convergence of solution sets.
--
--   **Formalization Note** The minimum is `sInf (h '' Z)`; it equals the minimum whenever the minimum is attained, which is the case wherever the paper uses it (lower semicontinuous $h$ on a nonempty compact $Z$, or a nonempty set of minimizers). The deviation is the real supremum of $\operatorname{dist}(\cdot,B)$ over $A$; it is the paper's value for bounded $A$ and nonempty $B$, and $0$ for $A=\emptyset$.
-- source:
--   Kannan, Bayraksan & Luedtke, Data-Driven Sample Average Approximation with Covariate Information, arXiv:2207.13554v1, (1) p.5, (4) p.6, Notation p.8 (𝔻(A,B), dist(v,B)), Lemma 10 p.28

import Mathlib

namespace CovariateSAA

/-- The minimum value `min_{z ∈ Z} h(z)` used throughout Kannan, Bayraksan & Luedtke,
*Data-Driven Sample Average Approximation with Covariate Information*, arXiv:2207.13554v1:
`v*(x)` in (1), p.5, `v̂^ER_n(x)` in (4), p.6, and `min_{w ∈ W} h(w)` in Lemma 10, p.28.

**Formalization Note** It is `sInf (h '' Z)`. Where the minimum is attained (as in the paper's
statements: `h` lower semicontinuous on a nonempty compact `Z`, or the minimizer set nonempty)
this is the minimum; Lean's `sInf` of an empty or unbounded-below set of reals is `0`, a value
the paper's statements never use. -/
noncomputable def minVal {E : Type*} (h : E → ℝ) (Z : Set E) : ℝ :=
  sInf (h '' Z)

/-- The set of minimizers `arg min_{z ∈ Z} h(z) = {z ∈ Z : h(z) ≤ h(z') for all z' ∈ Z}`
(arXiv:2207.13554v1: `S*(x)`, p.5; `Ŝ^ER_n(x)`, p.6; `W*`, Lemma 10, p.28). -/
def argminSet {E : Type*} (h : E → ℝ) (Z : Set E) : Set E :=
  {z | z ∈ Z ∧ ∀ z' ∈ Z, h z ≤ h z'}

/-- The deviation of `A` from `B` (arXiv:2207.13554v1, Notation, p.8):
`𝔻(A, B) := sup_{v ∈ A} dist(v, B)` with `dist(v, B) := inf_{w ∈ B} ‖v − w‖`.

**Formalization Note** `dist(v, B)` is `Metric.infDist v B` and the supremum is the real
`sSup` of the image of `A`. For `A` bounded and `B` nonempty (the only case the paper uses:
`A ⊆ 𝒵` compact and `B = S*(x) ≠ ∅`) the image is bounded above and this is the paper's
supremum; for `A = ∅` Lean returns `0`. -/
noncomputable def deviation {E : Type*} [PseudoMetricSpace E] (A B : Set E) : ℝ :=
  sSup ((fun v => Metric.infDist v B) '' A)

end CovariateSAA


