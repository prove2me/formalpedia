-- Prove2me | Definitions.Def_ReplParity_IsReplicable
-- name    : ReplParity_IsReplicable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:37:39.456635+00:00
-- url     : https://prove2.me/theorems/ba1eea1c-a084-4f19-ba3f-e7d5598964fb
-- title:
--   Definition 2.1 — $\rho$-replicable on every labeled distribution
-- statement:
--   A learner $A$ receives a sample $S\sim D^m$ of a size $m$ fixed in advance and a random seed $r$ independent of $S$. It is **$\rho$-replicable on every labeled distribution** if for every labeled distribution $D$,
--   $$\Pr_{S,S'\sim D^m,\,r}\big[A(S;r)\ne A(S';r)\big]\le\rho,$$
--   where $S$ and $S'$ are independent and the seed $r$ is shared by the two runs. Outputs are compared exactly, as elements of the output set.
--
--   This is the replicability notion of Impagliazzo, Lei, Pitassi and Sorrell, with the quantifier over all labeled distributions, not only realizable ones.
--
--   **Formalization Note** The domain is finite, the seed is uniform on a finite set $\Omega$ (for the goal, the bit strings of a fixed length), and $D$ ranges over every distribution on $X\times\mathbb F_2$.
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), Definition 2.1, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_ReplParity_prIID

namespace ReplParity

/-- **ρ-replicable on every labeled distribution (Definition 2.1).** Shen, Zhong, *Replicable
Parity Learning: Cubic Sample Complexity and a Geometric Characterization*, STOC 2027 submission
(manuscript sha256 40424491…), Definition 2.1, p.10 (PDF p.12): "A learner A is ρ-replicable on
every labeled distribution if for every labeled distribution D, Pr_{S,S′∼D^m, r}[A(S; r) ≠ A(S′; r)]
≤ ρ, where S and S′ are independent and the seed r is shared by the two runs. Outputs are compared
exactly, as elements of the output set."

A learner with sample size `m`, seeds in the finite type `Ω` (uniform) and outputs in `β` is a
function `A : (Fin m → X × ZMod 2) → Ω → β`.

**Formalization Note.** `X` is finite and labels are `ZMod 2`; `D` ranges over every `PMF` on
`X × ZMod 2`; outputs are compared with `≠` in `β`. -/
def IsReplicable {X Ω β : Type*} [Fintype X] [Fintype Ω] {m : ℕ}
    (A : (Fin m → X × ZMod 2) → Ω → β) (ρ : ℝ) : Prop :=
  ∀ D : PMF (X × ZMod 2), prIID2 D m (fun S S' r => A S r ≠ A S' r) ≤ ρ

end ReplParity


