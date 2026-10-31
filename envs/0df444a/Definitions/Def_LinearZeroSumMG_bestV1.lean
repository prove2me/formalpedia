-- Prove2me | Definitions.Def_LinearZeroSumMG_bestV1
-- name    : LinearZeroSumMG_bestV1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:51:50.056008+00:00
-- url     : https://prove2.me/theorems/062edd1d-cae1-4b92-ae07-6acaac088b9c
-- title:
--   Best-response values $V^{*,\nu}_h$, $Q^{*,\nu}_h$, $V^{\pi,*}_h$, $Q^{\pi,*}_h$
-- statement:
--   When P1 best-responds to a policy $\nu$ of P2, and when P2 best-responds to a policy $\pi$ of P1,
--   $$
--   V^{*,\nu}_h(x)=\max_\pi V^{\pi,\nu}_h(x),\quad Q^{*,\nu}_h(x,a,b)=\max_\pi Q^{\pi,\nu}_h(x,a,b),\quad
--   V^{\pi,*}_h(x)=\min_\nu V^{\pi,\nu}_h(x),\quad Q^{\pi,*}_h(x,a,b)=\min_\nu Q^{\pi,\nu}_h(x,a,b).
--   $$
--   The duality gap $V^{*,\nu}_1(x_1)-V^{\pi,*}_1(x_1)$ measures how far $(\pi,\nu)$ is from a Nash equilibrium.
--
--   **Formalization Note** The maximum and minimum range over measurable stochastic Markov policies and are written as a supremum and an infimum. For a nonempty action set and a policy $\nu$ (resp. $\pi$), the family is nonempty and bounded by $H$ in absolute value, so these are genuine suprema and infima. They are not defined through a max–min Bellman recursion; that the suprema are attained is not part of the definition.
-- source:
--   Xie, Chen, Wang & Yang, Learning Zero-Sum Simultaneous-Move Markov Games Using Function Approximation and Correlated Equilibrium, arXiv:2002.07066v3, §2.2.1, p.6

import Mathlib
import Definitions.Def_LinearZeroSumMG_IsPolicy
import Definitions.Def_LinearZeroSumMG_Vval

namespace LinearZeroSumMG

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] [Fintype A]

/-- **Best-response values `V^{*,ν}_h`, `Q^{*,ν}_h`, `V^{π,*}_h`, `Q^{π,*}_h`.**
Xie, Chen, Wang & Yang, *Learning Zero-Sum Simultaneous-Move Markov Games Using Function
Approximation and Correlated Equilibrium*, arXiv:2002.07066v3, §2.2.1, p.6: "we introduce the value
and Q functions when P1 plays the best response to a fixed policy `ν` of P2:
`V^{*,ν}_h(x) = max_π V^{π,ν}_h(x)` and `Q^{*,ν}_h(x, a, b) = max_π Q^{π,ν}_h(x, a, b)`. Analogously,
when P2 plays the best response to P1's policy `π`, we define `V^{π,*}_h(x) = min_ν V^{π,ν}_h(x)` and
`Q^{π,*}_h(x, a, b) = min_ν Q^{π,ν}_h(x, a, b)`."

`bestV1 G ν h x = V^{*,ν}_h(x)`; the companions `bestQ1`, `bestV2`, `bestQ2` follow.

**Formalization Note** The maximum and minimum range over the stochastic Markov policies of
`IsPolicy` (measurable in the state). They are written as `⨆`/`⨅` in `ℝ` over that subtype. When `A`
is nonempty and `ν` is a policy, the subtype is nonempty and the family is bounded by `H` in absolute
value (rewards lie in `[−1, 1]`), so these are genuine suprema and infima; that they are attained is
not part of the definition. They are not defined through a max–min Bellman recursion. -/
noncomputable def bestV1 (G : MarkovGame S A) (ν : ℕ → S → A → ℝ) (h : ℕ) (x : S) : ℝ :=
  ⨆ π : {π : ℕ → S → A → ℝ // IsPolicy π}, Vval G π.1 ν h x

/-- `Q^{*,ν}_h(x, a, b) = max_π Q^{π,ν}_h(x, a, b)` (arXiv:2002.07066v3, §2.2.1, p.6). -/
noncomputable def bestQ1 (G : MarkovGame S A) (ν : ℕ → S → A → ℝ) (h : ℕ) (x : S) (a b : A) : ℝ :=
  ⨆ π : {π : ℕ → S → A → ℝ // IsPolicy π}, Qval G π.1 ν h x a b

/-- `V^{π,*}_h(x) = min_ν V^{π,ν}_h(x)` (arXiv:2002.07066v3, §2.2.1, p.6). -/
noncomputable def bestV2 (G : MarkovGame S A) (π : ℕ → S → A → ℝ) (h : ℕ) (x : S) : ℝ :=
  ⨅ ν : {ν : ℕ → S → A → ℝ // IsPolicy ν}, Vval G π ν.1 h x

/-- `Q^{π,*}_h(x, a, b) = min_ν Q^{π,ν}_h(x, a, b)` (arXiv:2002.07066v3, §2.2.1, p.6). -/
noncomputable def bestQ2 (G : MarkovGame S A) (π : ℕ → S → A → ℝ) (h : ℕ) (x : S) (a b : A) : ℝ :=
  ⨅ ν : {ν : ℕ → S → A → ℝ // IsPolicy ν}, Qval G π ν.1 h x a b

end LinearZeroSumMG


