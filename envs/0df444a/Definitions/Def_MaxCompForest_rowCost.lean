-- Prove2me | Definitions.Def_MaxCompForest_rowCost
-- name    : MaxCompForest_rowCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:11.104795+00:00
-- url     : https://prove2.me/theorems/9aef467b-3205-46b0-855b-8f6f3066428d
-- title:
--   Weighted assignment cost of a row set
-- statement:
--   For positive weights $w_v$, a pseudometric $\rho$ on the row labels and a nonempty set $C$ of row labels,
--   $$
--   \sum_v w_v\min_{z\in C}\rho(v,z)^2 .
--   $$
--   The row optimum $\mathrm{OPT}^{\mathrm{row}}_m$ of the paper is the minimum of this cost, with $\rho$ the Euclidean distance between rows, over $1\le|C|\le m$.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), §2.1 p.7, Lemma C.1 p.36

import Mathlib

namespace MaxCompForest

variable {V : Type*} [Fintype V]

/-- **The weighted assignment cost** `∑_v w_v min_{z ∈ C} ρ(v,z)²` of a nonempty set `C` of rows.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), §2.1 p.7, Lemma C.1 p.36.

**Formalization Note.** The minimum is `Finset.inf'`, so nonemptiness is an argument. The paper's
`OPTrow_m` is the minimum of this quantity over `1 ≤ |C| ≤ m`; statements give the set `C`
explicitly, or compare with every such `C`. -/
noncomputable def rowCost (W : V → ℝ) (ρ : V → V → ℝ) (C : Finset V) (hC : C.Nonempty) : ℝ :=
  ∑ v, W v * C.inf' hC (fun z => ρ v z ^ 2)

end MaxCompForest


