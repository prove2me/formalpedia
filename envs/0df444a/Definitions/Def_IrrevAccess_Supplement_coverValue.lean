-- Prove2me | Definitions.Def_IrrevAccess_Supplement_coverValue
-- name    : IrrevAccess_Supplement_coverValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:56:05.623228+00:00
-- url     : https://prove2.me/theorems/be453abf-d9d6-4e90-9c2d-b06da95c7d09
-- title:
--   Value of a covering allocation program
-- statement:
--   For a finite index set $\iota$ of weights, a family $S$ of constraints and coefficients $a_{c,i}\in\mathbb R$, the **covering value** is
--   $$
--   \mathrm{cov}(S,a)=\inf\Big\{\sum_{i}z_i:\ z\ge 0,\ \sum_i z_i\,a_{c,i}\ge 1\ \text{for every }c\in S\Big\}\in[0,\infty].
--   $$
--   An empty constraint family has value $0$ and an infeasible program has value $+\infty$, as in the paper's programs (5), (6), (11), (12) and (17)–(20). When the program is feasible the infimum is attained (a linear program), so it is the paper's minimum.
--
--   All allocation programs of the supplement are instances of this one definition.
-- source:
--   Chen–Fang, The Price of Irreversible Experiment Access, STOC 2027 submission (manuscript, sha256 ba610425…9726), §4.1, p.11 (PDF 13), programs (5)–(6); §4.4, p.14 (PDF 16), programs (11)–(12)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace IrrevAccess.Supplement

/-- **Value of a covering allocation program.** Chen–Fang, *The Price of Irreversible Experiment Access*, STOC 2027 submission (manuscript, sha256 ba610425…9726), §4.1, p.11 (PDF 13), programs (5)–(6),
and §4.4, p.14 (PDF 16), programs (11)–(12): "min_{z≥0} { Σ_e z_e : Σ_e z_e d_e(b, b') ≥ 1 for every
b' … }. An empty family of constraints has value zero; an infeasible program has value +∞."

`coverValue S a` is the infimum of `Σ_i z_i` over weight vectors `z ≥ 0` (indexed by the finite type
`ι`) satisfying `Σ_i z_i · a c i ≥ 1` for every constraint `c ∈ S`.

**Formalization Note** Values in `[0, ∞]`: the infimum over an empty feasible set is `⊤ = +∞`
(an infeasible program), and an empty constraint family `S = ∅` admits `z = 0`, so its value is
`0`. When the program is feasible the infimum is attained (a linear program), so it is the paper's
minimum. -/
noncomputable def coverValue {ι κ : Type} [Fintype ι] (S : Set κ) (a : κ → ι → ℝ) : ℝ≥0∞ :=
  ⨅ (z : ι → ℝ) (_ : ∀ i, 0 ≤ z i) (_ : ∀ c ∈ S, 1 ≤ ∑ i, z i * a c i), ENNReal.ofReal (∑ i, z i)

end IrrevAccess.Supplement


