-- Prove2me | Definitions.Def_StructBandit_PPrime
-- name    : StructBandit_PPrime
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:32:37.19595+00:00
-- url     : https://prove2.me/theorems/cc9eb5da-d848-46d8-bf59-d01d2b6af783
-- title:
--   $\mathrm{Rew}_{\max}$, deceitful arms $\tilde X_d(P)$ and the set $\mathcal P'$ of Assumption 1
-- statement:
--   The **maximum reward** of arm $x$ is $\mathrm{Rew}_{\max}(x,P):=\max\{\sum_r rQ(r,x): Q\in\mathcal P,\ Q(x^\star(P))=P(x^\star(P))\}$. A suboptimal arm is **deceitful** if $\mathrm{Rew}_{\max}(x,P)>\mathrm{Rew}^\star(P)$; these arms form $\tilde X_d(P)$.
--
--   **Assumption 1** singles out the distributions $P\in\mathcal P$ that
--
--   1. have a unique optimal arm,
--   2. satisfy $\mathrm{Rew}_{\max}(x,P)\ne\mathrm{Rew}^\star(P)$ for every suboptimal arm $x\in\tilde X(P)$,
--   3. lie in $\mathrm{int}(\mathcal P)$.
--
--   They form $\mathcal P'$, the set of true distributions to which Theorem 3 applies.
--
--   **Formalization Note** $\mathrm{Rew}_{\max}$ is a supremum in `EReal` ($-\infty$ if infeasible). Condition 2 is printed "for any $x\in X$"; at an optimal arm it always fails ($Q=P$ is feasible and fixes the optimal column), so it is read over suboptimal arms, as the paper's own discussion on pp.19–20 does.
-- source:
--   Van Parys & Golrezaei, Optimal Learning for Structured Bandits, arXiv:2007.07302v3, Eq. (8), p.13; X̃d p.14; Assumption 1, p.19

import Mathlib
import Definitions.Def_StructBandit_IsStructureSet

open scoped BigOperators

namespace StructBandit

/-- **The maximum reward** `Rewmax(x,P)` (arXiv:2007.07302v3, Eq. (8), p.13):
`Rewmax(x,P) := max ∑_{r∈R} r Q(r,x)` over `Q ∈ S` with `Q(x⋆(P)) = P(x⋆(P))`.

**Formalization Note.** A supremum in `EReal` (the page's "max"); it is `⊥ = −∞` when no `Q ∈ S`
agrees with `P` on `x⋆(P)`, which can happen only for `P ∉ S`. -/
noncomputable def rewMax {R : Finset ℝ} {X : Type*} [Fintype X] [Nonempty X]
    (S : Set (R → X → ℝ)) (x : X) (P : R → X → ℝ) : EReal :=
  ⨆ Q ∈ {Q : R → X → ℝ | Q ∈ S ∧ ∀ y ∈ optArms P, ∀ r, Q r y = P r y}, ((mean Q x : ℝ) : EReal)

open Classical in
/-- The **deceitful** suboptimal arms `X̃d(P) := {x ∈ X̃(P) : Rewmax(x,P) > Rew⋆(P)}` (p.13–14). The
non-deceitful ones are `X̃n(P) = X̃(P) ∖ X̃d(P)`. -/
noncomputable def deceitArms {R : Finset ℝ} {X : Type*} [Fintype X] [Nonempty X]
    (S : Set (R → X → ℝ)) (P : R → X → ℝ) : Finset X :=
  (subArms P).filter (fun x => ((rewStar P : ℝ) : EReal) < rewMax S x P)

/-- **The set `S′` of Assumption 1** (arXiv:2007.07302v3, p.19): the reward distributions `P ∈ S` that
1. have a unique optimal arm,
2. satisfy `Rewmax(x,P) ≠ Rew⋆(P)` for every suboptimal arm `x ∈ X̃(P)`, and
3. lie in the interior of `S` (App. B, p.40, see `relInt`).

**Formalization Note.** Condition 2 is printed "for any `x ∈ X`". At an optimal arm `x = x⋆(P)` it
always fails (`Q = P` is feasible in (8) and every feasible `Q` fixes the column of `x⋆(P)`, so
`Rewmax(x⋆(P),P) = Rew⋆(P)`), which would make `S′` empty. It is read over the suboptimal arms, as
the paper's gloss (p.19) and its counterexample (p.20) do. -/
def PPrime {R : Finset ℝ} {X : Type*} [Fintype X] [Nonempty X] (S : Set (R → X → ℝ)) :
    Set (R → X → ℝ) :=
  {P | P ∈ S ∧ (∃ x₀, optArms P = {x₀}) ∧
    (∀ x ∈ subArms P, rewMax S x P ≠ ((rewStar P : ℝ) : EReal)) ∧ P ∈ relInt S}

end StructBandit


