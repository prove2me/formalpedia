-- Prove2me | Definitions.Def_FourierRankQLB_supportFn
-- name    : FourierRankQLB_supportFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:39:21.165092+00:00
-- url     : https://prove2.me/theorems/1050e6e1-2fa1-4e11-91dc-419b85c5380d
-- title:
--   The support function $h_K(c)$
-- statement:
--   For compact $K\subseteq\mathbb R^n$ and $c\in\mathbb R^n$,
--   $$
--   h_K(c)=\max_{x\in K}c^Tx .
--   $$
--   It is the optimal value of the linear optimization problem over $K$.
--
--   **Formalization Note** It is the real supremum of the image, which is the maximum on a nonempty compact set. Every statement of the mission applies it to such a set.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, §2.1, p.13

import Mathlib
import Definitions.Def_FourierRankQLB_Ambient

namespace FourierRankQLB

/-- The support function `h_K(c) = max_{x ∈ K} cᵀx`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, §2.1, p. 13.

**Formalization Note.** The paper defines `h_K` for compact `K`. It is written as a real supremum,
which equals the maximum on a nonempty compact set. On an empty or unbounded set the value is the
junk `0`, so every statement here applies it only to nonempty compact sets. -/
noncomputable def supportFn {n : ℕ} (K : Set (Ambient n)) (c : Ambient n) : ℝ :=
  sSup ((fun x => inner ℝ c x) '' K)

end FourierRankQLB


