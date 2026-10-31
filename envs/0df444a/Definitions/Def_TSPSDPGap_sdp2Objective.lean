-- Prove2me | Definitions.Def_TSPSDPGap_sdp2Objective
-- name    : TSPSDPGap_sdp2Objective
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:37:52.127091+00:00
-- url     : https://prove2.me/theorems/ba9185ca-87c1-4944-a780-6da2294ba4c5
-- title:
--   Objective of the de Klerk–Sotirov SDP (2) on $n+1$ vertices
-- statement:
--   Let $D$ be an $(n+1)\times(n+1)$ cost matrix and $r,s\in[n+1]$. Put $\alpha=[n+1]\setminus\{r\}$ and $\beta=[n+1]\setminus\{s\}$, each listed in increasing order. The **objective of SDP (2)** at $Y\in\mathbb R^{n^2\times n^2}$ is
--   $$
--   \operatorname{trace}\Bigl(\bigl(D[\beta]\otimes\tfrac12 C^{(n+1)}_1[\alpha]+\operatorname{Diag}(\bar c)\bigr)Y\Bigr),\qquad \bar c=\operatorname{vec}\bigl(C_1[\alpha,\{r\}]\,D[\{s\},\beta]\bigr),
--   $$
--   where $M[\alpha]$ is the principal submatrix on $\alpha$, $C_1[\alpha,\{r\}]D[\{s\},\beta]$ is the $\alpha\times\beta$ matrix with entries $(C^{(n+1)}_1)_{ar}D_{sb}$, and $\operatorname{vec}$ stacks the columns of a matrix. This is the symmetry-reduced relaxation of de Klerk and Sotirov, written as an SDP for instances on $n+1$ vertices.
--
--   **Formalization Note** Vertices are `Fin (n+1)` (0-based); $\alpha$ and $\beta$ are enumerated by `Fin.succAbove r` and `Fin.succAbove s`. `Matrix.vec` stacks columns, so $\bar c$ is indexed by (β-index, α-index), matching the Kronecker index of $D[\beta]\otimes C_1[\alpha]$. The unadorned $C_1$ in $\bar c$ is read as $C^{(n+1)}_1$, the only size for which $C_1[\alpha,\{r\}]$ is defined. A sanity check in `Solutions/verification` evaluates the objective at the lift of a permutation and recovers the tour cost.
-- source:
--   Gutekunst & Williamson, SDP Relaxations of the TSP and Their Integrality Gaps, arXiv:1907.09054v1, SDP (2), p.7

import Mathlib
import Definitions.Def_TSPSDPGap_circBasis

open scoped Kronecker

namespace TSPSDPGap

/-- **The objective of SDP (2) (de Klerk–Sotirov) on `n + 1` vertices.**
Gutekunst & Williamson, *SDP Relaxations of the TSP and Their Integrality Gaps*,
arXiv:1907.09054v1, §2.2, p.7: "min trace((D[β] ⊗ ½C^{(n+1)}_1[α] + Diag(c̄))Y) … where
s, r ∈ [n + 1] and α = [n + 1]\r and β = [n + 1]\s, and where c̄ = vec(C_1[α, {r}]D[{s}, β])."

For an `(n + 1) × (n + 1)` cost matrix `D` and indices `r, s`, the value is
`trace((D[β] ⊗ ½ C^{(n+1)}_1[α] + Diag(c̄)) Y)`, where `M[α]` is the principal submatrix on
`α`, `C_1[α,{r}] D[{s},β]` is the `α × β` matrix with entries `C^{(n+1)}_1(a, r) · D(s, b)`, and
`vec` stacks its columns.

**Formalization Note.** Vertices are `Fin (n + 1)` (0-based). `α = [n+1]∖r` and
`β = [n+1]∖s`, listed increasingly, are `Fin.succAbove r` and `Fin.succAbove s`. `vec` is
Mathlib's `Matrix.vec` (column stacking, indexed `(column, row)`), so `c̄` is indexed
`(β-index, α-index)`, the same order as the Kronecker index of `D[β] ⊗ C_1[α]`. The unadorned
`C_1` in `c̄` is read as `C^{(n+1)}_1`, the only size for which `C_1[α, {r}]` is defined. -/
noncomputable def sdp2Objective (n : ℕ) (D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (r s : Fin (n + 1)) (Y : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ) : ℝ :=
  Matrix.trace
    (((D.submatrix s.succAbove s.succAbove) ⊗ₖ
        ((1 / 2 : ℝ) • (circBasis (n + 1) 1).submatrix r.succAbove r.succAbove) +
      Matrix.diagonal (Matrix.vec (Matrix.of fun (a : Fin n) (b : Fin n) =>
        circBasis (n + 1) 1 (r.succAbove a) r * D s (s.succAbove b)))) * Y)

end TSPSDPGap


