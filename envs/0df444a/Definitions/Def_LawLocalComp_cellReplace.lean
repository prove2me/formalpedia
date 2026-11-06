-- Prove2me | Definitions.Def_LawLocalComp_cellReplace
-- name    : LawLocalComp_cellReplace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:13:19.139885+00:00
-- url     : https://prove2.me/theorems/a6dccefe-51a0-4618-96de-bfe7a366df8a
-- title:
--   Replacement of every cell by its conditional mean
-- statement:
--   Given a labelling of the atoms of $X$ by cells, the **cell replacement** moves the mass of every atom to the conditional mean of its cell. The result is $\mathbb E[X\mid\text{cell}(X)]$: one atom per cell of positive mass, carrying the cell's mass, with coincident means merged.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), §3, p.5; Lemma 7.2, p.13

import Mathlib
import Definitions.Def_LawLocalComp_cellMean
import Definitions.Def_LawLocalComp_lawOfW

namespace LawLocalComp

/-- **Replace every cell by its conditional mean.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), §3, p.5; Lemma 7.2, p.13.

`cellReplace X key` moves the mass of every atom `x` to the conditional mean of its cell `key x`.
Its law is `E[X | key X]`, with one atom per cell of positive mass (coincident means merge). -/
noncomputable def cellReplace (X : Law) (key : ℝ → ℤ) : Law :=
  lawOfW (∑ x ∈ X.w.support, Finsupp.single (cellMean X key (key x)) (X.w x))

end LawLocalComp


