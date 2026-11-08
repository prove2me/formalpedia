-- Prove2me | Definitions.Def_FairFacilityLoc_groupScore
-- name    : FairFacilityLoc_groupScore
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:13:51.505226+00:00
-- url     : https://prove2.me/theorems/0beb54f8-ed2b-4158-9460-3a72d94eb3a3
-- title:
--   The scores of the Score-Balanced mechanism and the winning sets
-- statement:
--   For $d\le3$ and a weight vector $a\in K_j$, the mass on a set $S$ of agents is $A_j(S;a)=\sum_{i\in S\cap G_j}a_i$, and
--   $$\sigma_j(S;a)=A_j(G_j;a)\bigl(A_j(S;a)-b_dA_j(N\setminus S;a)\bigr),\qquad \sigma_j(S)=\max_{a\in K_j}\sigma_j(S;a).$$
--   For $d\ge4$, $\sigma_h(S)=|S\cap G_h|$ and $\sigma_j(S)=0$ for every $j\ne h$.
--
--   In every dimension, $S$ is **winning** if $\max_j\sigma_j(S)\ge\max_j\sigma_j(N\setminus S)$.
--
--   **Formalization Note** Scores may be negative. The maximum over $K_j$ is a real supremum, which is a maximum because a weight set is compact and nonempty.
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), (2.3), §2.2, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_FairFacilityLoc_penalty
import Definitions.Def_FairFacilityLoc_WeightSelection
import Definitions.Def_FairFacilityLoc_heaviestGroup

open scoped NNReal

namespace FairFacilityLoc

/-- The **mass** `A_j(S; a) = ∑_{i ∈ S ∩ G_j} a_i` of a weight vector `a ∈ ℝ^G_{≥0}` on a set `S` of agents
(Yan, Zhou, manuscript, sha256 642a1268…, §2.2, p.16, PDF p.18). -/
noncomputable def groupMass {n : ℕ} {G : Finset (Fin n)} (a : ↥G → ℝ≥0) (S : Finset (Fin n)) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : ↥G => (i : Fin n) ∈ S), (a i : ℝ)

/-- The **score of `S` for the weight vector `a`**, (2.3), p.16, PDF p.18:
`σ_j(S; a) = A_j(G_j; a) (A_j(S; a) − b A_j(N ∖ S; a))`.

**Formalization Note.** `Sᶜ` is the complement in `N`, and `groupMass` only counts members of `G`. Scores
can be negative. -/
noncomputable def vectorScore {n : ℕ} {G : Finset (Fin n)} (b : ℝ) (a : ↥G → ℝ≥0) (S : Finset (Fin n)) :
    ℝ :=
  groupMass a G * (groupMass a S - b * groupMass a Sᶜ)

/-- The **score of `S` for group `j`** in dimension `d`, §2.2, p.16, PDF p.18. For `d ≤ 3`,
`σ_j(S) = max_{a ∈ K_j} σ_j(S; a)`. For `d ≥ 4`, `σ_h(S) = |S ∩ G_h|` and `σ_j(S) = 0` for `j ≠ h`.

**Formalization Note.** `sSup` is the printed `max`: `K_j` is a weight set, so it is compact and nonempty,
and `σ_j(S; a)` is continuous in `a`. -/
noncomputable def groupScore (d : ℕ) (K : WeightSelection) {n m : ℕ} (G : GroupStructure n m) (j : Fin m)
    (S : Finset (Fin n)) : ℝ :=
  if d ≤ 3 then
    sSup ((fun a => vectorScore (penalty d) a S) '' K.K G j)
  else if j = heaviestGroup G then
    ((S ∩ G.G j).card : ℝ)
  else
    0

/-- The **largest score** `max_j σ_j(S)` of a set `S` of agents, §2.2, p.16, PDF p.18.

**Formalization Note.** A real supremum over the finite nonempty `Fin m`, hence a maximum. Scores can be
negative, so it is not a supremum with `0`. -/
noncomputable def maxGroupScore (d : ℕ) (K : WeightSelection) {n m : ℕ} (G : GroupStructure n m)
    (S : Finset (Fin n)) : ℝ :=
  ⨆ j : Fin m, groupScore d K G j S

/-- **Winning sets**, §2.2, p.16, PDF p.18: `S` is winning if `max_j σ_j(S) ≥ max_j σ_j(N ∖ S)`. -/
def IsWinning (d : ℕ) (K : WeightSelection) {n m : ℕ} (G : GroupStructure n m)
    (S : Finset (Fin n)) : Prop :=
  maxGroupScore d K G Sᶜ ≤ maxGroupScore d K G S

end FairFacilityLoc


