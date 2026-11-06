-- Prove2me | Definitions.Def_MemQueryFeas_IsHaarGr
-- name    : MemQueryFeas_IsHaarGr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:34:09.953357+00:00
-- url     : https://prove2.me/theorems/e4e6e885-f33f-4887-bceb-2561b8f00acc
-- title:
--   Haar uniform law on $\mathrm{Gr}(k,d)$
-- statement:
--   A probability measure $\nu$ on linear maps of $\mathbb R^d$ is the **Haar uniform law $\mathrm{Unif}(\mathrm{Gr}(k,d))$** (transported to projections) if, under $\nu$, almost every map is the orthogonal projection onto a $k$-dimensional subspace and the law is invariant under conjugation $p\mapsto UpU^{-1}$ by every orthogonal map $U$. This is the platform's definition of a uniform random projection (`IsUniformProjection`) applied to the identity map; it characterizes the unique rotation-invariant law on $\mathrm{Gr}(k,d)$.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), §3.1, p.7 (PDF p.8); p.25

import Mathlib
import Definitions.Def_MemQueryFeas_Op
import Definitions.Def_HighDimProb_Isoperimetry_UniformProjection

open MeasureTheory

namespace MemQueryFeas

/-- **The Haar uniform law `Unif(Gr(k, d))`.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), §3.1, p.7 (PDF p.8): "`E_1, …, E_P` iid
`∼ Unif(Gr(d̃, d))`"; p.25: "the Haar uniform measure".

`IsHaarGr k ν`: `ν` is a probability law on projections, concentrated on rank-`k` orthogonal
projections and invariant under conjugation by every orthogonal map of `ℝ^d`, i.e. the identity is
a uniform random projection under `ν` in the sense of the platform's
`HighDimProb.Isoperimetry.IsUniformProjection`.

**Formalization Note.** These conditions characterize the unique `O(d)`-invariant probability law on
`Gr(k,d)` (transported to projections). -/
def IsHaarGr {d : ℕ} (k : ℕ) (ν : Measure (Op d)) : Prop :=
  IsProbabilityMeasure ν ∧ HighDimProb.Isoperimetry.IsUniformProjection ν k id

end MemQueryFeas


