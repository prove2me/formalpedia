-- Prove2me | Definitions.Def_SteinerNav_aspectRatio
-- name    : SteinerNav_aspectRatio
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:46:52.265198+00:00
-- url     : https://prove2.me/theorems/f023f6de-6f77-4211-abc4-c4ebd4bb0a8e
-- title:
--   Minimum distance $\sigma$, diameter $D$, aspect ratio $\Delta=D/\sigma$ and the annulus count $L=1+\lfloor\log_2\Delta\rfloor$
-- statement:
--   Let $P\subset\mathbb R^d$ be a finite set with at least two points.
--
--   1. $\sigma=\min_{p\neq p'\in P}\|p-p'\|$ is the smallest pairwise distance.
--   2. $D=\operatorname{diam}(P)=\max_{p\neq p'\in P}\|p-p'\|$ is the largest pairwise distance.
--   3. The **aspect ratio** of $P$ is
--   $$\Delta(P)=\frac{D}{\sigma}=\frac{\max_{x\neq y}\|x-y\|}{\min_{x\neq y}\|x-y\|}\ \ge 1 .$$
--   4. The number of annuli is $L=1+\lfloor\log_2\Delta\rfloor$.
--
--   The aspect ratio controls the length of greedy routes, and $L$ is the number of dyadic distance scales around a source used by the construction.
--
--   **Formalization Note** $\sigma$ and $D$ are the infimum and supremum of the finite set of off-diagonal distances. They are the minimum and maximum when $|P|\ge 2$; for $|P|\le 1$ the set is empty and both are $0$, so every theorem using them assumes $|P|\ge 2$, the paper's standing assumption.
-- source:
--   Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, Sparse α-Navigable Graphs in Euclidean Space via Steiner Points, STOC 2027 submission (manuscript sha256 e396eee6…), §3 "Notation", p.5; §4.1, p.7 (σ, D, L)

import Mathlib
import Definitions.Def_SteinerNav_Covers

namespace SteinerNav

/-- `σ = min_{p ≠ p′ ∈ P} ‖p − p′‖` (Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), §4.1, p.7).

**Formalization Note** An `sInf` over the finite set of off-diagonal distances; it is that minimum as
soon as `2 ≤ |P|` and the junk value `0` otherwise. Every use carries `2 ≤ P.card`. -/
noncomputable def minDist {d : ℕ} (P : Finset (Pt d)) : ℝ :=
  sInf {r : ℝ | ∃ x ∈ P, ∃ y ∈ P, x ≠ y ∧ r = dist x y}

/-- `D = diam(P) = max_{p ≠ p′ ∈ P} ‖p − p′‖` (Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), §3, p.5, and §4.1, p.7).

**Formalization Note** An `sSup` over the finite set of off-diagonal distances, so the maximum when
`2 ≤ |P|` and the junk value `0` otherwise. -/
noncomputable def maxDist {d : ℕ} (P : Finset (Pt d)) : ℝ :=
  sSup {r : ℝ | ∃ x ∈ P, ∃ y ∈ P, x ≠ y ∧ r = dist x y}

/-- The aspect ratio `Δ(P) = D/σ`, the largest over the smallest pairwise distance (Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), §3, p.5).
Meaningful for `2 ≤ |P|`, where it is at least `1`. -/
noncomputable def aspectRatio {d : ℕ} (P : Finset (Pt d)) : ℝ :=
  maxDist P / minDist P

/-- The number of annuli `L = 1 + ⌊log₂ Δ⌋` (Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), §4.1, p.7). -/
noncomputable def annulusCount {d : ℕ} (P : Finset (Pt d)) : ℕ :=
  1 + ⌊Real.logb 2 (aspectRatio P)⌋₊

end SteinerNav


