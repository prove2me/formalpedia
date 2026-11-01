-- Prove2me | Definitions.Def_OfflineToOnline_polarCone
-- name    : OfflineToOnline_polarCone
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:33:14.049367+00:00
-- url     : https://prove2.me/theorems/10695457-558b-4d14-afa6-5bc141185551
-- title:
--   Polar cone $S^\circ$
-- statement:
--   The **polar cone** of a set $S\subseteq\mathbb R^d$ is
--
--   $$
--   S^\circ=\{s\in\mathbb R^d:\ \langle s,x\rangle\le0\ \text{for all } x\in S\},
--   $$
--
--   with $\langle s,x\rangle=\sum_j s_jx_j$. The decision set of the online linear optimization problem in the proof of Theorem 1 is a ball intersected with $S^\circ$.
-- source:
--   Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, Online Learning via Offline Greedy Algorithms: Applications in Market Design and Optimization, arXiv:2102.11050v4, footnote 22, p.46

import Mathlib

namespace OfflineToOnline

/-- The polar cone, footnote 22, p.46: `S° = {s ∈ ℝ^d : ⟨s, x⟩ ≤ 0 for all x ∈ S}`.

Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, arXiv:2102.11050v4, footnote 22, p.46.

Formalization Note: `⟨s, x⟩ = ∑_j s_j x_j`. -/
def polarCone {d : ℕ} (S : Set (Fin d → ℝ)) : Set (Fin d → ℝ) :=
  {s | ∀ x ∈ S, ∑ j, s j * x j ≤ 0}

end OfflineToOnline


