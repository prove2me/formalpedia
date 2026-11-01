-- Prove2me | Definitions.Def_StructBandit_shallowUpdate
-- name    : StructBandit_shallowUpdate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:33:43.327167+00:00
-- url     : https://prove2.me/theorems/3f928b0c-7627-47ed-a919-6c0f880be8f2
-- title:
--   The dual-constrained bound $\overline C(Q;\mu)$ and the shallow update $\mathsf{SU}(Q,\eta';\mu,\epsilon)$
-- statement:
--   With one dual vector $\mu(x)$ per arm, let $\overline C(Q;\mu):=\inf_{\eta\ge0}\sum_{x\in\tilde X(Q)}\eta(x)\Delta(x,Q)$ subject to $1\le\overline{\mathrm{Dual}}(\eta,x,Q;\mu(x))$ for all $x\in\tilde X_d(Q)$, where $\overline{\mathrm{Dual}}(\eta,x,Q;\mu):=\max_{\rho\ge0}\mathrm{Dual}(\eta,x,Q;\rho\mu)$ is the dual-test function. The **shallow update** returns
--
--   $$
--   \eta_\epsilon(Q):=\arg\min_{\eta\ge0}\sum_{x\in X}(\eta(x)-\eta'(x))^2\quad\text{s.t.}\quad 1\le\overline{\mathrm{Dual}}(\eta,x,Q;\mu(x))\ \forall x\in\tilde X_d(Q),\ \ \sum_{x\in\tilde X(Q)}\eta(x)\Delta(x,Q)\le\overline C(Q;\mu)+2\epsilon,
--   $$
--
--   and $+\infty$ if there is no feasible solution.
--
--   DUSA calls it in every exploration round to set its target exploration rates.
--
--   **Formalization Note** The output is an `Option` (`none` = $+\infty$, also returned when no minimizer exists). The minimizer is unique when it exists.
-- source:
--   Van Parys & Golrezaei, Optimal Learning for Structured Bandits, arXiv:2007.07302v3, Eq. (18), p.25; Algorithm 2, Eq. (19), p.26

import Mathlib
import Definitions.Def_StructBandit_PPrime
import Definitions.Def_StructBandit_dualFn

open scoped BigOperators

namespace StructBandit

/-- **The dual-constrained lower bound** `C̄(Q;µ)` (arXiv:2007.07302v3, Eq. (18), p.25):
`C̄(Q;µ) := inf_{η≥0} ∑_{x∈X̃(Q)} η(x)∆(x,Q)` s.t. `1 ≤ Dual‾(η,x,Q;µ(x))` for all `x ∈ X̃d(Q)`; an
infimum in `EReal`, `+∞` if infeasible. Here `µ : X → DualVec` carries one dual vector per arm.

**Formalization Note.** The constraint is the dual-test function `Dual‾` of (17) (`dualSup`, the
supremum over `ρ ≥ 0`), not `Dual` at `ρ = 1`: the bars on `C̄` and `Dual‾` are printed in (18), (19), and
the proof of Lemma 11 (p.72) relies on the homogeneity of `Dual‾` in `η` (Lemma 18). -/
noncomputable def lowerBoundDual {R : Finset ℝ} {X : Type*} [Fintype X] [Nonempty X]
    (S : Set (R → X → ℝ)) (Q : R → X → ℝ) (μs : X → DualVec R X) : EReal :=
  ⨅ (η : X → ℝ) (_ : ∀ x, 0 ≤ η x) (_ : ∀ x ∈ deceitArms S Q, (1 : EReal) ≤ dualSup η x Q (μs x)),
    ((∑ x ∈ subArms Q, η x * gap Q x : ℝ) : EReal)

/-- Feasibility in the shallow update (19): `η ≥ 0`, `1 ≤ Dual‾(η,x,Q;µ(x))` for all `x ∈ X̃d(Q)`, and
`∑_{x∈X̃(Q)} η(x)∆(x,Q) ≤ C̄(Q;µ) + 2ε`. -/
def IsSUFeasible {R : Finset ℝ} {X : Type*} [Fintype X] [Nonempty X] (S : Set (R → X → ℝ))
    (Q : R → X → ℝ) (μs : X → DualVec R X) (ε : ℝ) (η : X → ℝ) : Prop :=
  (∀ x, 0 ≤ η x) ∧ (∀ x ∈ deceitArms S Q, (1 : EReal) ≤ dualSup η x Q (μs x)) ∧
    ((∑ x ∈ subArms Q, η x * gap Q x : ℝ) : EReal) ≤ lowerBoundDual S Q μs + ((2 * ε : ℝ) : EReal)

/-- `η` solves the shallow update problem (19): it is feasible and minimizes `∑_{x∈X}(η(x) − η′(x))²`
over the feasible set. -/
def IsSUSol {R : Finset ℝ} {X : Type*} [Fintype X] [Nonempty X] (S : Set (R → X → ℝ))
    (Q : R → X → ℝ) (η' : X → ℝ) (μs : X → DualVec R X) (ε : ℝ) (η : X → ℝ) : Prop :=
  IsSUFeasible S Q μs ε η ∧
    ∀ η₂, IsSUFeasible S Q μs ε η₂ → ∑ x, (η x - η' x) ^ 2 ≤ ∑ x, (η₂ x - η' x) ^ 2

open Classical in
/-- **The shallow update** `SU(Q,η′;µ,ε)` (arXiv:2007.07302v3, Algorithm 2, Eq. (19), p.26): the
minimizer `η_ε(Q)` of (19); "if no feasible solution exists, we simply set `η_ε(Q) := +∞`".

**Formalization Note.** The output is an `Option`: `some η` is the minimizer, `none` stands for `+∞`
and is returned whenever (19) has no minimizer. The minimizer is unique when it exists (the objective is
strictly convex and the feasible set is convex, `Dual` being concave), so the choice made by
`Classical.choose` is the minimizer. -/
noncomputable def shallowUpdate {R : Finset ℝ} {X : Type*} [Fintype X] [Nonempty X]
    (S : Set (R → X → ℝ)) (Q : R → X → ℝ) (η' : X → ℝ) (μs : X → DualVec R X) (ε : ℝ) :
    Option (X → ℝ) :=
  if h : ∃ η, IsSUSol S Q η' μs ε η then some h.choose else none

end StructBandit


