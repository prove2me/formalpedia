-- Prove2me | Definitions.Def_GenEmpLik_Coverage_Supplement_Hadamard
-- name    : GenEmpLik_Coverage_Supplement_Hadamard
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T23:13:12.540347+00:00
-- url     : https://prove2.me/theorems/80ed8bca-91d0-4bfa-88c6-8c36e7474d4e
-- title:
--   Definition 4 — tangent Hadamard differentiability with whole-space derivative
-- statement:
--   Let $\mathcal P\subset\mathcal M$ lie in a normed real space, let $P\in\mathcal P$, and let $B\subset\mathcal M$ be the tangent set. The functional $T$ is Hadamard differentiable at $P$ tangentially to $B$ with derivative $dT$ when, for every $v\in B$ and every sequence of nonzero real scales $t_n\to0$ and directions $v_n\in\mathcal M$ converging in norm to $v$, with $P+t_nv_n\in\mathcal P$,
--   $$\frac{T(P+t_nv_n)-T(P)}{t_n}\longrightarrow dT(v).$$
--   Here $dT$ is linear and continuous on all of $\mathcal M$, the extension required by Theorem 10. The sequence form is the primary definition in Definition 4; its compact-uniform reformulation (24) is not asserted as a separate theorem item. This notion permits an arbitrary infinite-dimensional domain and tangent set.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, pp. 22–23, Definition 4; 23, Theorem 10

import Mathlib
import Definitions.Def_GenEmpLik_Coverage_Supplement_functionalDomain

open Filter
open scoped Topology

namespace GenEmpLik.Coverage.Supplement

/-- Definition 4, pp. 22–23, in its sequence form. Directions H_n range over
all M, not just B; scales are nonzero and may approach zero from either side.
The derivative is linear and continuous on the whole M, as required by Theorem 10. -/
def HadamardAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M D B : Set E) (T : E → ℝ) (P : E) (dT : E → ℝ) : Prop :=
  P ∈ D ∧ B ⊆ M ∧
  dT 0 = 0 ∧
  (∀ v ∈ M, ∀ w ∈ M, dT (v + w) = dT v + dT w) ∧
  (∀ a : ℝ, ∀ v ∈ M, dT (a • v) = a * dT v) ∧
  ContinuousOn dT M ∧
  ∀ v ∈ B, ∀ (t : ℕ → ℝ) (vseq : ℕ → E),
    (∀ n, t n ≠ 0) → Tendsto t atTop (𝓝 0) →
    (∀ n, vseq n ∈ M) → Tendsto vseq atTop (𝓝 v) →
    (∀ n, P + t n • vseq n ∈ D) →
    Tendsto (fun n => (T (P + t n • vseq n) - T P) / t n) atTop (𝓝 (dT v))

end GenEmpLik.Coverage.Supplement


