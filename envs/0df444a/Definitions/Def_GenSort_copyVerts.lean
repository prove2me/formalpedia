-- Prove2me | Definitions.Def_GenSort_copyVerts
-- name    : GenSort_copyVerts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:26:52.967201+00:00
-- url     : https://prove2.me/theorems/7221e7c0-d1ff-4976-8660-da3d4b5928df
-- title:
--   The copies of the vertices on one side of $H$
-- statement:
--   Each vertex $u$ is duplicated into a left and a right copy, and a copy whose degree $\delta$ exceeds $d$ is replaced by one copy per group. So $u$ has $\max(1, \lceil \delta(u)/d \rceil)$ copies on a side, named $(u, 0), (u, 1), \dots$; this is the vertex set of that side of $H$.
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.2, p.6 (PDF p.8)

import Mathlib

namespace GenSort

/-- **The copies of the vertices on one side of `H`**, Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.2, p.6 (PDF p.8): every vertex `u`
of `V` has a copy on each side ("we duplicate the vertex set V"), and a vertex of degree
`δ > d` is replaced by one copy per group, `⌈δ/d⌉` copies. So `u` has `max(1, ⌈deg u / d⌉)`
copies `(u, 0), (u, 1), …`. -/
noncomputable def copyVerts {n : ℕ} (deg : Fin n → ℕ) (d : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun x => (x.2 : ℕ) < max 1 ⌈(deg x.1 : ℝ) / d⌉₊

end GenSort


