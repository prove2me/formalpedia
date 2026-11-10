-- Prove2me | Definitions.Def_GreedNorm_prev
-- name    : GreedNorm_prev
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:44:39.984905+00:00
-- url     : https://prove2.me/theorems/298aef8e-543b-425e-a700-87398ddecfe7
-- title:
--   $\mathrm{prev}(i)$
-- statement:
--   For $i\in[m]$, $\mathrm{prev}(i)$ is the largest element of $\mathrm{POS}$ that is at most $i$ (it exists since $1\in\mathrm{POS}$).
--
--   **Formalization Note** Written as the supremum in $\mathbb N$ of $\{\ell\in\mathrm{POS}:\ell\le i\}$, which is its maximum when the set is nonempty.
-- source:
--   Gan–Huang–Umboh, Greed is All You Need: An Approximation Algorithm Framework for Nested Norm Covering and Packing Problems, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), §2, p.5 (PDF 7)

import Mathlib
import Definitions.Def_GreedNorm_POS

namespace GreedNorm

/-- **`prev(i)`**: the largest element of `POS_{m,ϵ}` that is at most `i`.
Gan–Huang–Umboh, *Greed is All You Need: An Approximation Algorithm Framework for Nested Norm
Covering and Packing Problems*, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), §2, p.5 (PDF 7): "For each i ∈ [m], define prev(i) to be the largest element of POS that is
at most i."

**Formalization Note** Indices are 1-based natural numbers. The value is the supremum (in `ℕ`) of
`{ℓ ∈ POS | ℓ ≤ i}`, which is its maximum when the set is nonempty; for `1 ≤ i` and `m ≥ 1`
it is nonempty because `1 ∈ POS`. -/
noncomputable def prev (m : ℕ) (ε : ℝ) (i : ℕ) : ℕ := by
  classical
  exact ((POS m ε).filter (fun ℓ => ℓ ≤ i)).sup id

end GreedNorm


