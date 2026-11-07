-- Prove2me | Definitions.Def_StableVotingDistortion_IsGStable
-- name    : StableVotingDistortion_IsGStable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:03:41.187362+00:00
-- url     : https://prove2.me/theorems/51bae94f-6b0d-430f-a346-62a71f08f8a4
-- title:
--   Activation functions and $g$-stable lotteries (Definition 3)
-- statement:
--   An **activation function** is a continuous, non-decreasing $g:[0,1]\to[0,1]$. For a lottery $D$ write
--   $$H(D)=\max_{a\in C}\ \mathbb E_{v\sim V}[g(\mathrm{rank}_v(a;D))],$$
--   the maximum running over all candidates, zero mass included, with the attacker's rank taken as a random copy.
--
--   A **$g$-stable lottery** is a lottery minimizing $H$, that is, a solution of $\arg\min_D\max_{D^\dagger}\mathbb E_{v\sim V,\,a\sim D^\dagger}[g(\mathrm{rank}_v(a;D))]$.
--
--   These are the voting rules of the mission: $g(r)=r^k$ recovers stable $k$-lotteries.
--
--   **Formalization Note** A lottery is a point of `stdSimplex ℝ C`, and full support is not assumed. $g$ is a function on $\mathbb R$ constrained only on $[0,1]$.
-- source:
--   Cai, Frank, Hastings, Ramakrishnan, Wang, Ye, Stable Voting Rules on the Edge of Optimal Metric Distortion, arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Definition 3, p.10; proof of Theorem 4, p.11

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_StableVotingDistortion_voterMean
import Definitions.Def_StableVotingDistortion_activation

set_option autoImplicit false

open PctDistortion

namespace StableVotingDistortion

/-- An **activation function**: `g : [0, 1] → [0, 1]`, continuous and non-decreasing.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Definition 3, p.10: "Fix a continuous, non-decreasing function g : [0, 1] → [0, 1]."

**Formalization Note.** `g` is a function `ℝ → ℝ`, constrained only on `[0, 1]`. -/
structure IsActivation (g : ℝ → ℝ) : Prop where
  /-- `g` is continuous on `[0, 1]`. -/
  continuousOn : ContinuousOn g (Set.Icc 0 1)
  /-- `g` is non-decreasing on `[0, 1]`. -/
  monotoneOn : MonotoneOn g (Set.Icc 0 1)
  /-- `g` maps `[0, 1]` into `[0, 1]`. -/
  mapsTo : Set.MapsTo g (Set.Icc 0 1) (Set.Icc 0 1)

/-- `H(D) = max_{a ∈ C} E_{v ∼ V}[g(rank_v(a; D))]`, the attacker's best value against `D`. The
maximum runs over all candidates, zero mass included.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), proof of Theorem 4, p.11: "Let H(D) = max_{a∈C} E_{v∼V}[g(rank_v(a; D))]." -/
noncomputable def maxActivation {V C : Type} [Fintype V] [Fintype C] [Nonempty C] (g : ℝ → ℝ)
    (E : Election V C) (D : C → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun a => voterMean (fun v => activation g E D v a))

/-- `D` is a **`g`-stable lottery** of the election `E`: `D` is a lottery minimizing `H` over all
lotteries.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Definition 3, p.10: "Given an election, a g-stable lottery, denoted D_g, is a solution to the
following minimax optimization: arg min_D max_{D†} E_{v∼V, a∼D†}[g(rank_v(a; D))]. (9)"; p.11: "Since
the objective defining D_g is linear in D†, its maximum over D† equals H(D). Thus, D_g minimizes H(D)."

**Formalization Note.** A lottery is a point of `stdSimplex ℝ C`; full support is not assumed. -/
def IsGStable {V C : Type} [Fintype V] [Fintype C] [Nonempty C] (g : ℝ → ℝ)
    (E : Election V C) (D : C → ℝ) : Prop :=
  D ∈ stdSimplex ℝ C ∧ ∀ D' ∈ stdSimplex ℝ C, maxActivation g E D ≤ maxActivation g E D'

end StableVotingDistortion


