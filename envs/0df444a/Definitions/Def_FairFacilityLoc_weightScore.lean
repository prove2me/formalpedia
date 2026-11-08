-- Prove2me | Definitions.Def_FairFacilityLoc_weightScore
-- name    : FairFacilityLoc_weightScore
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:10:40.706445+00:00
-- url     : https://prove2.me/theorems/1b8abdba-e28b-400f-bb92-38f790fc0352
-- title:
--   Mass and score of a weight vector on the agents
-- statement:
--   A weight vector is regarded as a vector $a\in\mathbb R^N$ (zero off its group). Its mass on a set $S$ of agents is $A(S;a)=\sum_{i\in S}a_i$, and
--   $$\sigma(S;a)=A(N;a)\bigl(A(S;a)-b\,A(N\setminus S;a)\bigr),\qquad \sigma_W(S)=\max_{a\in W}\sigma(S;a)$$
--   for a family $W$. A linear group with weight $w_j$ is the vector $w_j\mathbf 1_{G_j}$.
--
--   **Formalization Note** $W$ is a finite family, nonempty in every statement.
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), §3.3, p.47 (PDF p.49)

import Mathlib

namespace FairFacilityLoc

/-- The **mass** `A(S; a) = ∑_{i ∈ S} a_i` of a weight vector `a ∈ ℝ^N` on a set `S` of agents (Yan, Zhou,
manuscript, sha256 642a1268…, §3.3, p.47, PDF p.49). `mass a Finset.univ` is the total mass `A(N; a)`. -/
def mass {n : ℕ} (a : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ i ∈ S, a i

/-- The **score** `σ(S; a) = A(N; a) (A(S; a) − b A(N ∖ S; a))` of a set for a weight vector, §3.3, p.47, PDF
p.49. -/
def weightScore {n : ℕ} (b : ℝ) (a : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  mass a Finset.univ * (mass a S - b * mass a Sᶜ)

/-- The **largest score** `σ_W(S) = max_{a ∈ W} σ(S; a)` over a family, §3.3, p.47, PDF p.49.

**Formalization Note.** `W` is a finite family (`Finset`). Every statement has a vector of positive mass in
`W`, so `W` is nonempty and `sSup` is a maximum. -/
noncomputable def maxWeightScore {n : ℕ} (b : ℝ) (W : Finset (Fin n → ℝ)) (S : Finset (Fin n)) : ℝ :=
  sSup ((fun a => weightScore b a S) '' (W : Set (Fin n → ℝ)))

end FairFacilityLoc


