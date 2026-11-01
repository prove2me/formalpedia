-- Prove2me | Definitions.Def_ProphetBipartite_vaddRun
-- name    : ProphetBipartite_vaddRun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:15.021986+00:00
-- url     : https://prove2.me/theorems/50470334-9d6b-4504-b7c3-fe8a7a1ffac3
-- title:
--   The vertex-additive policy $\mathrm{V\text{-}add}(l,r)$ and its run
-- statement:
--   A **vertex-additive policy** $\mathrm{V\text{-}add}(l,r)$ is given by prices $l=(l_i)_{i\in L}$ on the left vertices and $r=(r_j)_{j\in R}$ on the right vertices. When an edge $e(t)=(i,j)$ arrives with value $v_{e(t)}$, the policy accepts it if and only if
--
--   1. both $i$ and $j$ are available, i.e. not covered by a previously accepted edge, and
--   2. $v_{e(t)}\ge l_i+r_j$.
--
--   Otherwise the edge is rejected. Accepting an edge covers both its endpoints. Running the policy along an order $\sigma$ on a value profile $v$ produces
--
--   - the set $\mathcal A(v)$ of accepted edges (a matching),
--   - the final sets $X_L(v)\subseteq L$, $X_R(v)\subseteq R$ of covered vertices,
--   - the collected value $\mathrm{V\text{-}add}(l,r)(v)=\sum_{e\in\mathcal A(v)}v_e$.
--
--   The policy is static: the prices never change, and the decision for an edge uses only the prices, the coverage so far and the edge's own value.
--
--   **Formalization Note** Prices are in $\mathbb R_{\ge0}$ (the proof of Theorem 3.1 uses nonnegative prices). Ties $v_e=l_i+r_j$ are accepted. The run is a left fold over the list $\sigma$; the module also defines `vaddAccepted`, `vaddCoveredL`, `vaddCoveredR` and `vaddValue`.
-- source:
--   Gravin, Wang, Prophet inequality for bipartite matching: merits of being simple and non adaptive, arXiv:1902.06243v1, §3, p.5; 𝒜(v), X_L(v), X_R(v) p.5

import Mathlib

open scoped NNReal

namespace ProphetBipartite

/-- The state of a run of a vertex-additive policy: the covered left vertices, the covered right
vertices and the accepted edges so far. -/
structure RunState (L R E : Type*) where
  /-- Left vertices covered by accepted edges. -/
  coveredL : Finset L
  /-- Right vertices covered by accepted edges. -/
  coveredR : Finset R
  /-- Accepted edges. -/
  accepted : Finset E

/-- **One step of `V-add(l, r)`.** Gravin & Wang, arXiv:1902.06243v1, §3, p.5: a vertex-additive
policy with prices `l = (l₁, …, l_n)`, `r = (r₁, …, r_m)` "accepts a new arriving edge
`e(t) = (i, j)` with value `v_{e(t)}` if and only if (1) vertices `i, j` are available, i.e., both
`i ∈ L`, `j ∈ R` are not covered by previously accepted edges; (2) edge's value exceeds the sum of
its vertex thresholds `v_{e(t)} ≥ l_i + r_j`." Accepting covers both endpoints; otherwise the state
is unchanged.

**Formalization Note.** Ties are accepted (`l_i + r_j ≤ v_e`), as the printed "≥". Prices are in
`ℝ≥0`: p.5 says "positive real vectors", and the proof of Theorem 3.1 (p.9) finds "non negative
price vectors", so prices equal to `0` are allowed. -/
noncomputable def vaddStep {L R E : Type*} [DecidableEq L] [DecidableEq R] [DecidableEq E]
    (left : E → L) (right : E → R) (l : L → ℝ≥0) (r : R → ℝ≥0) (v : E → ℝ≥0)
    (s : RunState L R E) (e : E) : RunState L R E :=
  if left e ∉ s.coveredL ∧ right e ∉ s.coveredR ∧ l (left e) + r (right e) ≤ v e then
    { coveredL := insert (left e) s.coveredL
      coveredR := insert (right e) s.coveredR
      accepted := insert e s.accepted }
  else s

/-- **The run of `V-add(l, r)` on the arrival order `σ` and the value profile `v`.** Gravin & Wang,
arXiv:1902.06243v1, §3, p.5. The edges of `σ` are processed in order, starting with nothing covered
and nothing accepted. The run uses only the prices, the order and the realized values of the
edges that have arrived. -/
noncomputable def vaddRun {L R E : Type*} [DecidableEq L] [DecidableEq R] [DecidableEq E]
    (left : E → L) (right : E → R) (l : L → ℝ≥0) (r : R → ℝ≥0) (σ : List E) (v : E → ℝ≥0) :
    RunState L R E :=
  σ.foldl (vaddStep left right l r v) ⟨∅, ∅, ∅⟩

/-- The set `𝒜(v)` of edges accepted by `V-add(l, r)` (p.5). -/
noncomputable def vaddAccepted {L R E : Type*} [DecidableEq L] [DecidableEq R] [DecidableEq E]
    (left : E → L) (right : E → R) (l : L → ℝ≥0) (r : R → ℝ≥0) (σ : List E) (v : E → ℝ≥0) :
    Finset E :=
  (vaddRun left right l r σ v).accepted

/-- The final set `X_L(v)` of covered left vertices (p.5). -/
noncomputable def vaddCoveredL {L R E : Type*} [DecidableEq L] [DecidableEq R] [DecidableEq E]
    (left : E → L) (right : E → R) (l : L → ℝ≥0) (r : R → ℝ≥0) (σ : List E) (v : E → ℝ≥0) :
    Finset L :=
  (vaddRun left right l r σ v).coveredL

/-- The final set `X_R(v)` of covered right vertices (p.5). -/
noncomputable def vaddCoveredR {L R E : Type*} [DecidableEq L] [DecidableEq R] [DecidableEq E]
    (left : E → L) (right : E → R) (l : L → ℝ≥0) (r : R → ℝ≥0) (σ : List E) (v : E → ℝ≥0) :
    Finset R :=
  (vaddRun left right l r σ v).coveredR

/-- The value `V-add(l, r)` collects on `v`: the total value `∑_{e∈𝒜(v)} v_e` of the accepted
edges (pp.4–5). -/
noncomputable def vaddValue {L R E : Type*} [DecidableEq L] [DecidableEq R] [DecidableEq E]
    (left : E → L) (right : E → R) (l : L → ℝ≥0) (r : R → ℝ≥0) (σ : List E) (v : E → ℝ≥0) :
    ℝ≥0 :=
  ∑ e ∈ vaddAccepted left right l r σ v, v e

end ProphetBipartite


