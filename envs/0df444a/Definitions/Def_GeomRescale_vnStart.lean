-- Prove2me | Definitions.Def_GeomRescale_vnStart
-- name    : GeomRescale_vnStart
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:17:00.983982+00:00
-- url     : https://prove2.me/theorems/7cd70c78-4e9d-4c8f-bb38-f29134db2617
-- title:
--   Lines 1–3 of Algorithm 1
-- statement:
--   Algorithm 1 starts with $\mu' := \mu$, $W' := W$, $g_1$ the vertex of $B(f_\mu)$ of a chosen order, $x_1 := 1$, $y := g_1/\|g_1\|_Q$ and $k := 2$.
--
--   An arbitrary vertex of $B(f_\mu)$ is the greedy vector of an arbitrary order, by the description of the vertices on p.4.
--
--   **Formalization Note** The step is charged $n$ evaluations and $c(n) + n^2$ operations, on top of the counters on entry.
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Algorithm 1, lines 1–3, p.8

import Mathlib
import Definitions.Def_SchrijverSFM_Alg_Setting
import Definitions.Def_GeomRescale_fR
import Definitions.Def_GeomRescale_enlarge
import Definitions.Def_GeomRescale_unitQ
import Definitions.Def_GeomRescale_sortCost
import Definitions.Def_GeomRescale_VN

namespace GeomRescale

/-- Lines 1–3 of Algorithm 1 (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Algorithm 1, p.8): `μ′ := μ`, `W′ := W`, `g₁` is the vertex of
`B(f_μ)` of the order `σ`, `x₁ := 1`, `y := g₁/‖g₁‖_Q`, `k := 2`.

**Formalization Note.** "An arbitrary vertex" is an arbitrary order `σ`, by p.4: "for any ordering …
the following point is a vertex of `B(f)`, and every vertex is of this form". `e`, `o` are the
values of the counters on entry. The charge is `n` evaluations (the prefix values of `f`) and
`c(n) + n²` operations (the sort, `‖g₁‖_Q` and `y`). -/
noncomputable def vnStart {n : ℕ} (f : Finset (Fin n) → ℤ) (μ : ℤ) (W : Finset (Fin n))
    (Q : Matrix (Fin n) (Fin n) ℝ) (σ : Equiv.Perm (Fin n)) (e o : ℕ) : VN n :=
  let g := SchrijverSFM.Alg.greedy (enlarge (fR f) (μ : ℝ)) σ
  { μ := μ
    W := W
    data := [(g, 1)]
    y := unitQ Q g
    evals := e + n
    ops := o + sortCost n + n ^ 2 }

end GeomRescale


