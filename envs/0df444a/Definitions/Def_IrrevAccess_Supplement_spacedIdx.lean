-- Prove2me | Definitions.Def_IrrevAccess_Supplement_spacedIdx
-- name    : IrrevAccess_Supplement_spacedIdx
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:56:37.961931+00:00
-- url     : https://prove2.me/theorems/b962f913-f25d-4968-adae-a4ad2d750b8e
-- title:
--   Index law with spacing $s$: $N(sj,1)$
-- statement:
--   For $s\in\mathbb R$ the **spaced index** gives task $j$ the index law $N(s\,j,1)$; the instance with this index is $I_s$, and $I=I_1$.
--
--   **Formalization Note** Tasks are $\{0,\dots,k-1\}$, task $j$ being the paper's task $j+1$, so its law is $N(s(j+1),1)$; for $s=1$ this is the base mission's `IrrevAccess.gaussIdx`.
-- source:
--   Chen–Fang, The Price of Irreversible Experiment Access, STOC 2027 submission (manuscript, sha256 ba610425…9726), §4.5, p.18 (PDF 20)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace IrrevAccess.Supplement

/-- **Index law with spacing `s`: `N(s j, 1)`.** Chen–Fang, *The Price of Irreversible Experiment Access*, STOC 2027 submission (manuscript, sha256 ba610425…9726), §4.5, p.18 (PDF 20): "let I_s, for s > 0,
denote the instance obtained from I by giving the index diagnostic the law N(sj, 1), so that
I = I_1."

**Formalization Note** Tasks are `Fin k = {0, …, k−1}`; task `j` is the paper's task `j + 1 ∈ [k]`,
so its index law is `N(s (j + 1), 1)`, exactly as the base `IrrevAccess.gaussIdx k` (which is the
case `s = 1`). -/
noncomputable def spacedIdx (k : ℕ) (s : ℝ) : Fin k → Measure ℝ :=
  fun j => gaussianReal (s * ((j : ℕ) + 1 : ℝ)) 1

end IrrevAccess.Supplement


