-- Prove2me | Definitions.Def_OnlineCAP_octant
-- name    : OnlineCAP_octant
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:23:39.113364+00:00
-- url     : https://prove2.me/theorems/c33f320d-fc9e-4169-8d1f-a28d43cfcb93
-- title:
--   Octant of a given orientation in ℝ³
-- statement:
--   An **orientation** is a choice $\sigma\in\{\le,\ge\}^3$ of one inequality per coordinate. The **octant** of orientation $\sigma$ with vertex $q\in\mathbb R^3$ is
--   $$\{s\in\mathbb R^3 : s_i\ \sigma_i\ q_i\text{ for } i=1,2,3\}.$$
--   The dominance ranges $(-\infty,q_x]\times(-\infty,q_y]\times(-\infty,q_z]$ of Appendix A are the orientation $(\le,\le,\le)$.
--
--   **Formalization Note** Orientations are maps `Fin 3 → Bool` (`true` for $\le$); octants are closed.
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), Theorem 4.8, p.19; Appendix A, p.27

import Mathlib

namespace OnlineCAP

/-- **Octant of a given orientation in ℝ³.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), Theorem 4.8, p.19 and Appendix A, p.27 (PDF
p.27): "standard 3D dominance ranges of the form Qq = (−∞, qx] × (−∞, qy] × (−∞, qz] defined by a
query vertex q"; an octant of another orientation reverses some of the three inequalities.

For an orientation `σ : Fin 3 → Bool` and a vertex `q ∈ ℝ³`, `octant σ q` is the set of
`s ∈ ℝ³` with `s_i ≤ q_i` when `σ i = true` and `s_i ≥ q_i` when `σ i = false`. The dominance
ranges are `σ ≡ true`.

**Formalization Note.** Points of ℝ³ are `Fin 3 → ℝ`. Closed octants, as in Appendix A. -/
def octant (σ : Fin 3 → Bool) (q : Fin 3 → ℝ) : Set (Fin 3 → ℝ) :=
  {s | ∀ i, if σ i then s i ≤ q i else q i ≤ s i}

end OnlineCAP


