-- Prove2me | Definitions.Def_MarkovEntanglementExact_Supplement_tvEntanglement
-- name    : MarkovEntanglementExact_Supplement_tvEntanglement
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:45:16.971168+00:00
-- url     : https://prove2.me/theorems/5d0d8738-7c68-59b2-ab58-11fcff8e2b2e
-- title:
--   Measure of Markov entanglement w.r.t. the total variation distance
-- statement:
--   For a transition matrix $P$ on $X_A\times X_B$, the **measure of Markov entanglement with respect to the total variation distance** is
--   $$E(P)=\min_{P'\in\mathcal P_{\mathrm{SEP}}}\|P-P'\|_{TV},\qquad\|P-P'\|_{TV}=\max_x\tfrac12\sum_y|P(x,y)-P'(x,y)|,$$
--   where $\mathcal P_{\mathrm{SEP}}$ is the set of separable transition matrices $\sum_jx_jP^{(j)}_A\otimes P^{(j)}_B$ (Definition 1) that are themselves transition matrices. It vanishes exactly when $P$ is separable, and it is the measure of Theorem 3.
--
--   **Formalization Note** Written as `sInf` over `IsSeparable Q ∧ IsTransitionMatrix Q`; the set is nonempty and bounded below, and the minimum is attained.
-- source:
--   Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Definition 3, Eq. (4), p.14, and Definition 4, p.15

import Mathlib
import Definitions.Def_markov_entanglement

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglementExact.Supplement

variable {SA SB : Type*} [Fintype SA] [Fintype SB] [DecidableEq SA] [DecidableEq SB]

/-- The measure of Markov entanglement of a two-agent transition matrix `P` with respect to the
total variation distance: `E(P) = min_{P' ∈ P_SEP} ‖P − P'‖_TV` (Definition 3, Eq. (4), with the
distance of Definition 4). `P_SEP` is the set of separable transition matrices: matrices of the
form `Σ_j x_j P^(j)_A ⊗ P^(j)_B` that are themselves transition matrices.

Source: Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Definition 3, Eq. (4),
p.14; Definition 4 and the display after it, p.15; `P_SEP` as transition matrices, §3.3, p.12.

**Formalization Note.** `P_SEP` is `IsSeparable Q ∧ IsTransitionMatrix Q`: `IsSeparable` alone
allows signed combinations with negative entries, while p.12 requires every element of `P_SEP` to
be a transition matrix. The paper's `min` is written `sInf`; the set is nonempty (any
`P_A ⊗ P_B`) and bounded below by `0`, and the infimum is attained (the feasible set is compact),
so the two agree. -/
noncomputable def tvEntanglement (P : Matrix (SA × SB) (SA × SB) ℝ) : ℝ :=
  sInf {d : ℝ | ∃ Q : Matrix (SA × SB) (SA × SB) ℝ,
    IsSeparable Q ∧ IsTransitionMatrix Q ∧ d = tvDist P Q}

end MarkovEntanglementExact.Supplement


