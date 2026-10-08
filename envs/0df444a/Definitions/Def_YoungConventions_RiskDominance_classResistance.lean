-- Prove2me | Definitions.Def_YoungConventions_RiskDominance_classResistance
-- name    : YoungConventions_RiskDominance_classResistance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T18:02:41.432165+00:00
-- url     : https://prove2.me/theorems/33338b08-5cc7-406c-b1bb-5a430ae140a8
-- title:
--   Least resistance $r_{ij}$ between two sets of states
-- statement:
--   For sets of states $A$ and $B$ (in the paper, two distinct recurrent communication classes $H_i$ and $H_j$), consider all directed paths of successor steps that begin in $A$ and end in $B$. The **least resistance** from $A$ to $B$ is
--   $$r_{AB}=\min\{\text{total resistance of a path from a state of }A\text{ to a state of }B\}.$$
--   For classes $H_i,H_j$ this is the number $r_{ij}$ of the paper.
--
--   **Formalization Note** Resistances are natural numbers and the minimum is the infimum on $\mathbb N$. For nonempty $A,B$ a path always exists ($m$ steps of experimentation lead from any state to any state), so the convention $\inf\emptyset=0$ is never used for recurrent classes.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §6, pp. 68–69

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_History
import Definitions.Def_YoungConventions_RiskDominance_PathResistance

namespace YoungConventions.RiskDominance

/-- **Least resistance `r_ij` from one set of states to another.** Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §6, pp. 68–69 (PDF pp.
13–14): "Given any two distinct classes `Hᵢ` and `H_j` consider all directed paths that begin in
`Hᵢ` and end in `H_j`. There is at least one such path, because the perturbed process `P^ε` is
irreducible. Among all such paths, find one with least total resistance, and let this resistance be
denoted by `r_ij`."

`classResistance u k A B` is the least total resistance of a path of successor steps from a state of
`A` to a state of `B`.

**Formalization Note.** Resistances are natural numbers, so the least element is `sInf` on `ℕ`.
For any two nonempty sets the set of path resistances is nonempty (`m` successor steps lead from any
state to any state), so the junk value `sInf ∅ = 0` is never used for recurrent classes. -/
noncomputable def classResistance {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] {m : ℕ} [NeZero m]
    (u : ι → ((i : ι) → S i) → ℝ) (k : ℕ) (A B : Set (YoungConventions.AdaptivePlay.History S m)) : ℕ :=
  sInf {r : ℕ | ∃ a ∈ A, ∃ b ∈ B, PathResistance u k a b r}

end YoungConventions.RiskDominance


