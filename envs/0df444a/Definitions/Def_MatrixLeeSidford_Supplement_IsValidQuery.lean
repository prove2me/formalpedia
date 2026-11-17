-- Prove2me | Definitions.Def_MatrixLeeSidford_Supplement_IsValidQuery
-- name    : MatrixLeeSidford_Supplement_IsValidQuery
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T15:18:43.852718+00:00
-- url     : https://prove2.me/theorems/1e8945bb-6df6-4186-9a5f-520b8ef33b46
-- title:
--   Valid queries of a call, (V1)–(V3) (Definition 8.3)
-- statement:
--   Consider a call of Center that starts at $y^\circ$, and let $(y_j,G_j)$ be the query state of its query $j$. Query $j$ is **valid** if:
--
--   1. **(V1)** the call starts at a point $y^\circ$ with $\lambda_c(y^\circ)\le1/10$, and $y_j\in B(y^\circ)$;
--   2. **(V2)** $G_j$ is warm at $y_j$: $\Delta_{y_j}(G_j)\le\eta_w$;
--   3. **(V3)** $G_j$ is accurate at $y_j$, $\Delta_{y_j}(G_j)\le\eta$, if query $j$ is a y-query or the last G-query after a y-step.
--
--   Validity is the condition under which the data structures' estimates are guaranteed to be accurate; Theorem 9.6 shows that it propagates through a centering call.
--
--   **Formalization Note** Validity also records that query $j$ is reached (no earlier update failed), $y_j\in\Omega$ and $G_j\succ0$: the domain on which $\lambda_c$, $\nabla^2F$ and $\Delta$ are defined ($B(y^\circ)\subseteq\Omega$ by Lemma 3.2, and the maintained weight lies in $\mathbb S^m_{++}$). The cases of the standalone query, which lies outside every call, are omitted.
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Definition 8.3, (V1)–(V3), pp.55–56

import Mathlib
import Definitions.Def_MatrixLeeSidford_dualRegion
import Definitions.Def_MatrixLeeSidford_Supplement_weightGap
import Definitions.Def_MatrixLeeSidford_Supplement_newtonDec
import Definitions.Def_MatrixLeeSidford_Supplement_phaseBall
import Definitions.Def_MatrixLeeSidford_Supplement_centerState

open Matrix

namespace MatrixLeeSidford.Supplement

/-- **Validity of query `j` of a call of Center** (Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), Definition 8.3, (V1)–(V3), pp.55–56). Query `j`,
made at the query state `(y_j, G_j)`, is valid if
(V1) the call starts at a point `y°` with `λ_c(y°) ≤ 1/10`, and `y_j ∈ B(y°)`;
(V2) `G_j` is warm at `y_j`: `Δ_{y_j}(G_j) ≤ η_w`;
(V3) `G_j` is accurate at `y_j`, `Δ_{y_j}(G_j) ≤ η`, if query `j` is a y-query (`j mod (N_G+1) = 0`) or the
last G-query after a y-step (`j mod (N_G+1) = N_G`).

**Formalization Note** Validity also records that query `j` is reached (no earlier `UpdateWeight` failed),
that `y_j` is feasible and that `G_j ≻ 0` — the domain on which `λ_c`, `∇²F` and `Δ` are defined (Dweight's
member `G ∈ S^m_{++}`, Algorithm 5, p.56; `B(y°) ⊆ Ω` by Lemma 3.2, p.57). The standalone-query cases of
(V1)/(V3) concern queries outside a call and do not arise here. The parameters `α, γ_y, γ_G, N_G` are those of
`centerState`. -/
def IsValidQuery {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (s : ℕ) (α γy γG η ηw : ℝ) (NG : ℕ) (c y₀ : EuclideanSpace ℝ (Fin m))
    (G₀ : Matrix (Fin m) (Fin m) ℝ)
    (ans : ℕ → EuclideanSpace ℝ (Fin m) × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin m) ℝ)
    (j : ℕ) : Prop :=
  ∃ y G, centerState α γy γG NG c y₀ G₀ ans j = some (y, G) ∧
    y ∈ dualRegion A C ∧ G.PosDef ∧
    -- (V1)
    (newtonDec A C c y₀ ≤ 1 / 10 ∧ y ∈ phaseBall A C y₀) ∧
    -- (V2)
    weightGap A C s y G ≤ ηw ∧
    -- (V3)
    ((j % (NG + 1) = 0 ∨ j % (NG + 1) = NG) → weightGap A C s y G ≤ η)

end MatrixLeeSidford.Supplement


