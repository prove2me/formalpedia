-- Prove2me | Definitions.Def_StructBandit_IsDUSol
-- name    : StructBandit_IsDUSol
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:34:09.277978+00:00
-- url     : https://prove2.me/theorems/7c147f13-14d9-4e89-9bb7-0060a80618b7
-- title:
--   The deep update $\mathsf{DU}(Q;\epsilon)$, problem (20)
-- statement:
--   The **deep update** returns the minimizer $(\eta'_\epsilon(Q),\mu_\epsilon(Q))$ of
--
--   $$
--   \sum_{x\in X}\eta(x)^2+\sum_{x\in X}\|\mu(x)\|_2^2
--   $$
--
--   over $\eta\ge0$ and dual-feasible $\mu(x)=(\alpha(x),\beta(x),\lambda(x))\in\mathbb R_+\times\mathbb R\times\mathcal K^\star$ subject to
--
--   1. $1\le\mathrm{Dual}(\eta,x,Q;\mu(x))$ for all $x\in\tilde X_d(Q)$;
--   2. $\sum_{x\in\tilde X(Q)}\eta(x)\Delta(x,Q)\le C(Q)+\epsilon$;
--   3. $\eta(x)\ge\epsilon/(2\sum_{x\in\tilde X(Q)}\Delta(x,Q))$ for all $x\in\tilde X(Q)$;
--   4. $\eta(x)\ge\lambda(x')(r,x)+\beta(x')+\alpha(x')r\mathbb 1(x=x')+\epsilon/(2\sum_{x\in\tilde X(Q)}\Delta(x,Q))$ for all $x'\in\tilde X_d(Q)$, $x\in\tilde X(Q)$, $r\in\mathfrak R$.
--
--   It is DUSA's continuous selection of an $\epsilon$-suboptimal exploration rate with matching dual certificates. The module also defines $\|\eta\|_\infty$ over the suboptimal arms, $\max_{x\in\tilde X(Q)}\eta(x)$, used in (22).
--
--   **Formalization Note** A predicate `IsDUSol S Q ε η µ`. The page types $\mu(x)\in\mathcal K^\star\times\mathbb R_+\times\mathbb R$ and writes $\lambda(r,x)(x')$; as elsewhere in the paper this is $\alpha\in\mathbb R_+$, $\beta\in\mathbb R$, $\lambda\in\mathcal K^\star$, and the $(r,x)$ entry of $\lambda(x')$.
-- source:
--   Van Parys & Golrezaei, Optimal Learning for Structured Bandits, arXiv:2007.07302v3, Algorithm 3, Eq. (20), p.27; ‖η′_ε(P)‖∞, p.28

import Mathlib
import Definitions.Def_StructBandit_lowerBound
import Definitions.Def_StructBandit_PPrime
import Definitions.Def_StructBandit_dualFn

open scoped BigOperators

namespace StructBandit

/-- The threshold `ε / (2 ∑_{x∈X̃(Q)} ∆(x,Q))` of the last two constraint families of (20). The sum is
`0` only when `X̃(Q) = ∅`, and then both families are empty. -/
noncomputable def duThreshold {R : Finset ℝ} {X : Type*} [Fintype X] [Nonempty X]
    (Q : R → X → ℝ) (ε : ℝ) : ℝ :=
  ε / (2 * ∑ x ∈ subArms Q, gap Q x)

open Classical in
/-- Feasibility in the deep update (20) (arXiv:2007.07302v3, Algorithm 3, p.27):
1. `η(x) ≥ 0` and `µ(x) = (α(x),β(x),λ(x))` dual feasible for every `x ∈ X`;
2. `1 ≤ Dual(η,x,Q;µ(x))` for all `x ∈ X̃d(Q)`;
3. `∑_{x∈X̃(Q)} η(x)∆(x,Q) ≤ C(Q) + ε` (`C` the primal (6));
4. `η(x) ≥ ε/(2∑_{x∈X̃(Q)}∆(x,Q))` for all `x ∈ X̃(Q)`;
5. `η(x) ≥ λ(x′)(r,x) + β(x′) + α(x′) r 𝟙(x = x′) + ε/(2∑_{x∈X̃(Q)}∆(x,Q))` for all `x′ ∈ X̃d(Q)`,
   `x ∈ X̃(Q)` and `r ∈ R`.

**Formalization Note.** The page types `µ(x) ∈ K⋆ × ℝ₊ × ℝ` and writes `λ(r,x)(x′)`; as everywhere else
in the paper (pp.22, 24) this is `α(x) ∈ ℝ₊`, `β(x) ∈ ℝ`, `λ(x) ∈ K⋆`, and `λ(r,x)(x′)` is the `(r,x)`
entry of `λ(x′)`. The last family holds for every `r ∈ R`. -/
def IsDUFeasible {R : Finset ℝ} {X : Type*} [Fintype X] [Nonempty X] (S : Set (R → X → ℝ))
    (Q : R → X → ℝ) (ε : ℝ) (η : X → ℝ) (μs : X → DualVec R X) : Prop :=
  (∀ x, 0 ≤ η x) ∧ (∀ x, IsDualFeasible S (μs x)) ∧
    (∀ x ∈ deceitArms S Q, (1 : EReal) ≤ dualFn η x Q (μs x)) ∧
    ((∑ x ∈ subArms Q, η x * gap Q x : ℝ) : EReal) ≤ lowerBound S Q + ((ε : ℝ) : EReal) ∧
    (∀ x ∈ subArms Q, duThreshold Q ε ≤ η x) ∧
    (∀ x' ∈ deceitArms S Q, ∀ x ∈ subArms Q, ∀ r : R,
      (μs x').2.2 r x + (μs x').2.1 + (μs x').1 * (r : ℝ) * (if x = x' then 1 else 0)
        + duThreshold Q ε ≤ η x)

/-- The objective `∑_{x∈X} η(x)² + ∑_{x∈X} ‖µ(x)‖₂²` of (20), with
`‖µ(x)‖₂² = α(x)² + β(x)² + ∑_{r,y} λ(x)(r,y)²`. -/
def duObjective {R : Finset ℝ} {X : Type*} [Fintype X] (η : X → ℝ) (μs : X → DualVec R X) : ℝ :=
  ∑ x, η x ^ 2 + ∑ x, ((μs x).1 ^ 2 + (μs x).2.1 ^ 2 + ∑ r, ∑ y, (μs x).2.2 r y ^ 2)

/-- **The deep update** `DU(Q;ε) = (η′_ε(Q), µ_ε(Q))` (arXiv:2007.07302v3, Algorithm 3, Eq. (20),
p.27): `(η, µ)` is feasible for (20) and minimizes its objective over the feasible set.

**Formalization Note.** A predicate: `IsDUSol S Q ε η µ` says `(η, µ)` is the argmin of (20). The
objective is strictly convex, so there is at most one such pair; Proposition 4 asserts existence and
continuity on `𝒫′`. -/
def IsDUSol {R : Finset ℝ} {X : Type*} [Fintype X] [Nonempty X] (S : Set (R → X → ℝ))
    (Q : R → X → ℝ) (ε : ℝ) (η : X → ℝ) (μs : X → DualVec R X) : Prop :=
  IsDUFeasible S Q ε η μs ∧
    ∀ η₂ μs₂, IsDUFeasible S Q ε η₂ μs₂ → duObjective η μs ≤ duObjective η₂ μs₂

/-- `‖η‖_∞` over the suboptimal arms, `max_{x∈X̃(Q)} η(x)` (p.28: "`‖η′_ε(P)‖_∞ = max_{x∈X̃(P)} η′(x,P)`"),
`0` when `X̃(Q) = ∅`. -/
noncomputable def maxOnSub {R : Finset ℝ} {X : Type*} [Fintype X] [Nonempty X]
    (Q : R → X → ℝ) (η : X → ℝ) : ℝ :=
  if h : (subArms Q).Nonempty then (subArms Q).sup' h η else 0

end StructBandit


