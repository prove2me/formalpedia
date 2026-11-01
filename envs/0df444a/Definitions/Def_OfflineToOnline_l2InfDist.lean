-- Prove2me | Definitions.Def_OfflineToOnline_l2InfDist
-- name    : OfflineToOnline_l2InfDist
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:33:15.518407+00:00
-- url     : https://prove2.me/theorems/fd4d4bca-59fe-4c2b-9e66-d01b21940ff4
-- title:
--   Euclidean distance $d_2(v,S)$ to a set
-- statement:
--   The **Euclidean distance** of a vector $v\in\mathbb R^d$ from a set $S\subseteq\mathbb R^d$ is
--
--   $$
--   d_2(v,S)=\inf_{s\in S}\|v-s\|_2=\inf_{s\in S}\Big(\sum_{j=1}^d (v_j-s_j)^2\Big)^{1/2}.
--   $$
--
--   Lemma 1 bounds this distance for the average payoff of a Blackwell game.
--
--   **Formalization Note** Vectors are `Fin d → ℝ`, whose Mathlib norm is the sup norm, so the Euclidean norm is written out. The infimum over an empty set is $0$; statements using it assume $S$ nonempty.
-- source:
--   Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, Online Learning via Offline Greedy Algorithms: Applications in Market Design and Optimization, arXiv:2102.11050v4, Lemma 1 and (5), p.46

import Mathlib

namespace OfflineToOnline

/-- The Euclidean distance `d₂(v, S) = inf_{s ∈ S} ‖v − s‖₂` of a vector from a set, used in
Lemma 1, p.46.

Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, arXiv:2102.11050v4, Lemma 1 and (5), p.46.

Formalization Note: vectors live in `Fin d → ℝ`, whose Mathlib norm is the sup norm, so the
Euclidean norm is written out as `√(∑_j (v_j − s_j)²)`. The infimum over an empty `S` is `0`; the
theorems using it assume `S` nonempty. -/
noncomputable def l2InfDist {d : ℕ} (v : Fin d → ℝ) (S : Set (Fin d → ℝ)) : ℝ :=
  ⨅ s : S, Real.sqrt (∑ j, (v j - (s : Fin d → ℝ) j) ^ 2)

end OfflineToOnline


