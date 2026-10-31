-- Prove2me | Definitions.Def_LinearZeroSumMG_Vval
-- name    : LinearZeroSumMG_Vval
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:50:51.831227+00:00
-- url     : https://prove2.me/theorems/89bf70bb-75c4-415b-ba40-8e4f6dce23e8
-- title:
--   Value and action-value functions $V^{\pi,\nu}_h$, $Q^{\pi,\nu}_h$ and the operator $\mathbb P_h V$
-- statement:
--   For a function $V:\mathcal S\to\mathbb R$, write
--   $$
--   [\mathbb P_hV](x,a,b)=\int V(x')\,\mathrm d\mathbb P_h(x'\mid x,a,b).
--   $$
--   For a fixed pair of policies $(\pi,\nu)$, the **value** and **action-value** functions are defined backwards from $V^{\pi,\nu}_{H+1}\equiv Q^{\pi,\nu}_{H+1}\equiv0$ by
--   $$
--   Q^{\pi,\nu}_h(x,a,b)=r_h(x,a,b)+[\mathbb P_hV^{\pi,\nu}_{h+1}](x,a,b),\qquad
--   V^{\pi,\nu}_h(x)=\sum_{a,b}\pi_h(x)(a)\,\nu_h(x)(b)\,Q^{\pi,\nu}_h(x,a,b),
--   $$
--   for $h=H,H-1,\dots,1$. They are the expected sums $\mathbb E[\sum_{t=h}^Hr_t(x_t,a_t,b_t)]$ from step $h$ when P1 plays $\pi$ and P2 plays $\nu$ independently.
--
--   **Formalization Note** The paper defines the values as trajectory expectations; for a fixed Markov policy pair they equal this backward recursion. Both functions are $0$ for $h>H$.
-- source:
--   Xie, Chen, Wang & Yang, Learning Zero-Sum Simultaneous-Move Markov Games Using Function Approximation and Correlated Equilibrium, arXiv:2002.07066v3, §2.2.1, p.6

import Mathlib
import Definitions.Def_LinearZeroSumMG_MarkovGame

namespace LinearZeroSumMG

open MeasureTheory ProbabilityTheory

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] [Fintype A]

/-- **The conditional-expectation shorthand `[ℙ_h V](x, a, b)`.**
Xie, Chen, Wang & Yang, *Learning Zero-Sum Simultaneous-Move Markov Games Using Function
Approximation and Correlated Equilibrium*, arXiv:2002.07066v3, §2.2.1, p.6:
"`[ℙ_h V](x, a, b) := 𝔼_{x'∼ℙ_h(·|x,a,b)}[V(x')] = ∫ V(x') dℙ_h(x'|x, a, b)`." -/
noncomputable def transOp (G : MarkovGame S A) (h : ℕ) (V : S → ℝ) (x : S) (a b : A) : ℝ :=
  ∫ y, V y ∂(G.P h (x, a, b))

/-- **The value function `V^{π,ν}_h` of a fixed policy pair.**
arXiv:2002.07066v3, §2.2.1, p.6: "For a fixed pair of policies `(π, ν)` for both players, the value
and Q (a.k.a. action-value) functions … `V^{π,ν}_h(x) := 𝔼[∑_{t=h}^H r_t(x_t, a_t, b_t) | x_h = x]`,
`Q^{π,ν}_h(x, a, b) := 𝔼[∑_{t=h}^H r_t(x_t, a_t, b_t) | x_h = x, a_h = a, b_h = b]`, where the
expectation is over `a_t ∼ π_t(x_t)`, `b_t ∼ ν_t(x_t)` and `x_{t+1} ∼ ℙ_t(·|x_t, a_t, b_t)`. It is
convenient to set `V^{π,ν}_{H+1}(x) ≡ Q^{π,ν}_{H+1}(x) ≡ 0` for the terminal reward."

Here `V^{π,ν}_h` is computed by the backward recursion
`V^{π,ν}_h(x) = ∑_{a,b} π_h(x)(a) ν_h(x)(b) [r_h(x, a, b) + (ℙ_h V^{π,ν}_{h+1})(x, a, b)]` for `h ≤ H`,
and `V^{π,ν}_h ≡ 0` for `h > H`.

**Formalization Note** The paper defines the values as expectations over trajectories; for a fixed
Markov policy pair these equal the backward recursion used here (the two players randomize
independently, `a ∼ π_h(x)` and `b ∼ ν_h(x)`). Steps are 1-based; the recursion is also defined at
`h = 0`, a value that is never used. -/
noncomputable def Vval (G : MarkovGame S A) (π ν : ℕ → S → A → ℝ) (h : ℕ) : S → ℝ :=
  if h ≤ G.H then
    fun x => ∑ a, ∑ b, π h x a * ν h x b *
      (G.r h x a b + ∫ y, Vval G π ν (h + 1) y ∂(G.P h (x, a, b)))
  else fun _ => 0
termination_by G.H + 1 - h
decreasing_by omega

/-- **The action-value function `Q^{π,ν}_h` of a fixed policy pair** (arXiv:2002.07066v3, §2.2.1,
p.6): `Q^{π,ν}_h(x, a, b) = r_h(x, a, b) + (ℙ_h V^{π,ν}_{h+1})(x, a, b)` for `h ≤ H`, and
`Q^{π,ν}_h ≡ 0` for `h > H` (in particular `Q^{π,ν}_{H+1} ≡ 0`). -/
noncomputable def Qval (G : MarkovGame S A) (π ν : ℕ → S → A → ℝ) (h : ℕ) (x : S) (a b : A) : ℝ :=
  if h ≤ G.H then G.r h x a b + transOp G h (Vval G π ν (h + 1)) x a b else 0

end LinearZeroSumMG


