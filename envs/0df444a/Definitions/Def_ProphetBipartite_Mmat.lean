-- Prove2me | Definitions.Def_ProphetBipartite_Mmat
-- name    : ProphetBipartite_Mmat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:14.877477+00:00
-- url     : https://prove2.me/theorems/e9e59b2f-3ee1-44db-87c8-a57505da0fcc
-- title:
--   The matrices $M$ and $Q$ of (10)
-- statement:
--   Fix independent value laws $F_e$ on $\mathbb R_+$, $v\sim F=\prod_eF_e$, and an optimal matching selector $\mathrm{opt}$. For $i\in L$, $j\in R$ let $\chi^{(i,j)}_{\mathrm{opt}}(v)$ be the value $v_e$ of the edge $e$ of $\mathrm{opt}(v)$ joining $i$ and $j$ if there is one, and $0$ otherwise (display (4)). The $n\times m$ matrices of display (10) are
--
--   $$
--   M_{i,j}=\mathbb E_v\big[\chi^{(i,j)}_{\mathrm{opt}}(v)\big],\qquad Q_{i,j}=\Pr_v\big[(i,j)\in\mathrm{opt}(v)\big].
--   $$
--
--   $M$ records the expected contribution of the pair $(i,j)$ to the prophet's matching and $Q$ the probability that the prophet uses it. Both enter the lower bound (11) on the policy and the identity (12) for the prophet.
--
--   **Formalization Note** In a multigraph $\chi^{(i,j)}_{\mathrm{opt}}(v)$ is the sum of $v_e$ over the edges of $\mathrm{opt}(v)$ from $i$ to $j$, of which there is at most one. $M_{i,j}$ is a real (Bochner) integral; every statement that uses it assumes finite means, so the integrand is integrable. `Qmat` is defined in the same module.
-- source:
--   Gravin, Wang, Prophet inequality for bipartite matching: merits of being simple and non adaptive, arXiv:1902.06243v1, (4) p.6, (10) p.8

import Mathlib

open MeasureTheory
open scoped NNReal

namespace ProphetBipartite

/-- **The matrix `M` of (10).** Gravin & Wang, arXiv:1902.06243v1, (4) p.6 and (10) p.8:
`M_{i,j} = E_v[χ^{(i,j)}_opt(v)]`, where `χ^{(i,j)}_opt(v)` is the value `v_e` of the edge `e` of
`opt(v)` between `i` and `j` if there is one, and `0` otherwise. The values are drawn from
`F = ∏_e F_e`, the product `Measure.pi μ` of the laws `μ e` of the edge values.

**Formalization Note.** In a multigraph several parallel edges join `i` and `j`; `χ^{(i,j)}_opt` sums
`v_e` over the edges of `opt v` from `i` to `j`, of which there is at most one because `opt v` is a
matching. `M_{i,j}` is a real (Bochner) integral: with finite means of the edge values the
integrand is integrable, and every statement using `Mmat` assumes finite means. -/
noncomputable def Mmat {L R E : Type*} [Fintype E] [DecidableEq L] [DecidableEq R]
    (left : E → L) (right : E → R) (opt : (E → ℝ≥0) → Finset E) (μ : E → Measure ℝ≥0)
    (i : L) (j : R) : ℝ :=
  ∫ v, ∑ e ∈ (opt v).filter (fun e => left e = i ∧ right e = j), (v e : ℝ) ∂(Measure.pi μ)

/-- **The matrix `Q` of (10).** Gravin & Wang, arXiv:1902.06243v1, (4) p.6 and (10) p.8:
`Q_{i,j} = Pr_v[(i, j) ∈ opt(v)]`, the probability that the optimal matching contains an edge
between `i` and `j`, for `v ∼ ∏_e F_e`. -/
noncomputable def Qmat {L R E : Type*} [Fintype E]
    (left : E → L) (right : E → R) (opt : (E → ℝ≥0) → Finset E) (μ : E → Measure ℝ≥0)
    (i : L) (j : R) : ℝ :=
  (Measure.pi μ).real {v | ∃ e ∈ opt v, left e = i ∧ right e = j}

end ProphetBipartite


