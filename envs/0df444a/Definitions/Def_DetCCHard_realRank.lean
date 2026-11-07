-- Prove2me | Definitions.Def_DetCCHard_realRank
-- name    : DetCCHard_realRank
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:35:01.558696+00:00
-- url     : https://prove2.me/theorems/523e02e7-d791-4381-b8f7-4255e3dd93f1
-- title:
--   Rank of a Boolean table
-- statement:
--   The **rank** of a Boolean table $M : X \times Y \to \{0,1\}$ is the rank over $\mathbb R$ of its $0/1$ matrix. It appears in Lemma 5.4 ($\operatorname{rank}(R_0) = p_0$) and in the rank bound (iii) of the amplifier.
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), Lemma 5.4 and Theorem 5.3 (iii), p.17

import Mathlib

namespace DetCCHard

/-- The **rank** of a Boolean table `M : X × Y → {0, 1}` (Gaspers–He–Mackenzie, arXiv:2508.05597,
held version sha256 ad552d13…a4a03, Lemma 5.4 and Theorem 5.3 (iii), p.17): the rank over `ℝ` of
its `0/1` matrix. -/
noncomputable def realRank {X Y : Type} [Fintype X] [Fintype Y] (M : X → Y → Bool) : ℕ :=
  Matrix.rank (Matrix.of fun x y => if M x y then (1 : ℝ) else 0)

end DetCCHard


