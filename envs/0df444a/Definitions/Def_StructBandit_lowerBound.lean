-- Prove2me | Definitions.Def_StructBandit_lowerBound
-- name    : StructBandit_lowerBound
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:32:36.094173+00:00
-- url     : https://prove2.me/theorems/786d9740-e487-451f-85d3-8deae9a73194
-- title:
--   Deceitful distributions, the distance $\mathrm{Dist}$ and the lower bound $C(P)$
-- statement:
--   For $P$ and an arm $x'$, the **deceitful distributions** are
--
--   $$
--   \mathrm{Deceit}(x',P):=\Big\{Q\in\mathcal P:\ Q(x^\star(P))=P(x^\star(P)),\ \sum_r rQ(r,x')>\sum_r rQ(r,x^\star(P))\Big\}.
--   $$
--
--   The **distance function** is $\mathrm{Dist}(\eta,x',P):=\inf_{Q\in\mathrm{Deceit}(x',P)}\sum_{x\in\tilde X(P)}\eta(x)I(P(x),Q(x))$, and $+\infty$ when $\mathrm{Deceit}(x',P)=\emptyset$. The **regret lower bound function** is
--
--   $$
--   C(P):=\inf_{\eta\ge0}\ \sum_{x\in\tilde X(P)}\eta(x)\Delta(x,P)\quad\text{s.t.}\quad 1\le\mathrm{Dist}(\eta,x,P)\ \ \forall x\in\tilde X(P).
--   $$
--
--   $C(P)\log T$ is the Graves–Lai lower bound on the regret of uniformly good policies; Theorem 3 compares DUSA with it.
--
--   **Formalization Note** All three are extended reals; an infimum over an empty set is $+\infty$. $C$ is defined by the primal program (6), not by its dual.
-- source:
--   Van Parys & Golrezaei, Optimal Learning for Structured Bandits, arXiv:2007.07302v3, Eqs. (4), (6), (7), pp.11–12

import Mathlib
import Definitions.Def_StructBandit_IsStructureSet
import Definitions.Def_StructBandit_infoDist

open scoped BigOperators

namespace StructBandit

/-- **Deceitful reward distributions** `Deceit(x′,P)` (arXiv:2007.07302v3, Eq. (4), p.11): the
distributions `Q ∈ S` that agree with `P` on the optimal arms of `P`, `Q(x⋆(P)) = P(x⋆(P))`, and under
which arm `x′` earns more than the arms of `x⋆(P)`. -/
def Deceit {R : Finset ℝ} {X : Type*} [Fintype X] [Nonempty X] (S : Set (R → X → ℝ)) (x' : X)
    (P : R → X → ℝ) : Set (R → X → ℝ) :=
  {Q | Q ∈ S ∧ (∀ x ∈ optArms P, ∀ r, Q r x = P r x) ∧ ∀ x ∈ optArms P, mean Q x < mean Q x'}

/-- **The distance function** `Dist(η,x′,P)` (arXiv:2007.07302v3, Eq. (7), p.12): if `Deceit(x′,P)` is
non-empty, `Dist(η,x′,P) := inf_{Q ∈ Deceit(x′,P)} ∑_{x∈X̃(P)} η(x) I(P(x),Q(x))`; otherwise `+∞`.

**Formalization Note.** Computed in `EReal`: the infimum over the empty set is `⊤`, which is the
page's "otherwise `Dist = ∞`". `P(x)` is the column `r ↦ P(r,x)`. A term `η(x) · I` with `η(x) = 0` and
`I = +∞` is `0` (`EReal` has `0 · ⊤ = 0`). -/
noncomputable def distFn {R : Finset ℝ} {X : Type*} [Fintype X] [Nonempty X]
    (S : Set (R → X → ℝ)) (η : X → ℝ) (x' : X) (P : R → X → ℝ) : EReal :=
  ⨅ Q ∈ Deceit S x' P,
    ∑ x ∈ subArms P, ((η x : ℝ) : EReal) * infoDist (fun r => P r x) (fun r => Q r x)

/-- **The regret lower bound function** `C(P)` (arXiv:2007.07302v3, Eq. (6), p.12):
`C(P) := inf_{η ≥ 0} ∑_{x∈X̃(P)} η(x) ∆(x,P)` subject to `1 ≤ Dist(η,x,P)` for all `x ∈ X̃(P)`.

**Formalization Note.** An infimum in `EReal`, `+∞` when the constraints are infeasible; `η` ranges
over all nonnegative functions `X → ℝ`. This is the primal (6), not the dual (16). -/
noncomputable def lowerBound {R : Finset ℝ} {X : Type*} [Fintype X] [Nonempty X]
    (S : Set (R → X → ℝ)) (P : R → X → ℝ) : EReal :=
  ⨅ (η : X → ℝ) (_ : ∀ x, 0 ≤ η x) (_ : ∀ x ∈ subArms P, (1 : EReal) ≤ distFn S η x P),
    ((∑ x ∈ subArms P, η x * gap P x : ℝ) : EReal)

end StructBandit


