-- Prove2me | Definitions.Def_TwoStageMatch_DualAssignment
-- name    : TwoStageMatch_DualAssignment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:31:40.025922+00:00
-- url     : https://prove2.me/theorems/9438f781-4510-47c8-9a82-b7b850948c95
-- title:
--   The randomized dual assignment for (LP-1) in the proof of Theorem 1
-- statement:
--   Fix the optimal $x^*$ of a run of Algorithm 1, a realization $\tilde D_2=A$, a first-stage matching $M_1$ with matched supplies $S_1$, and a dual $(\hat\alpha,\hat\beta)$ of the residual matching LP on $G[A,S\setminus S_1]$. With the levels and slacks of the structural decomposition of $x^*$, the dual assignment for (LP-1) is
--
--   1. $\alpha_i=\hat\alpha_i$ for $i\in A$;
--   2. $\alpha_i=c^{(l)}$ for $i\in D^{(l)}$, $l=0,1,\dots,L$;
--   3. $\beta_j=w_j\big(\sum_{i\in N(j)}x^*_{ij}\big)^2+\hat\beta_j\,\mathbb 1\{j\in S\setminus S_1\}$ for $j\in S$.
--
--   It is random through $M_1$; the proof of Theorem 1 shows it is feasible in expectation up to the factor $3/4$ and that its objective equals the algorithm's weight in expectation.
--
--   **Formalization Note** $\hat\alpha$ is a function on $D_1\cup D_2$ of which only the values on $A$ are used, and $\hat\beta_j$ for $j\in S_1$ is multiplied by $0$. The square is $(\sum_i x^*_{ij})^2=y_j^{*2}$.
-- source:
--   Y. Feng, R. Niazadeh, A. Saberi, Two-stage Stochastic Matching and Pricing with Applications to Ride Hailing, arXiv:2210.11648v1 [cs.DS] (preprint, 21 Oct 2022), https://arxiv.org/abs/2210.11648v1, proof of Theorem 1, p.15 (dual assignment)

import Mathlib
import Definitions.Def_TwoStageMatch_Instance
import Definitions.Def_TwoStageMatch_Decomposition

open Finset

namespace TwoStageMatch

/-!
# The randomized dual assignment of the proof of Theorem 1

Feng, Niazadeh & Saberi, arXiv:2210.11648v1, proof of Theorem 1, pp.14–15.

Fix the fractional first-stage matching `x*` of a run, a realization `D̃₂ = A`, a first-stage
matching `M₁` with matched supplies `S₁`, and a dual `(α̂, β̂)` of the residual matching LP on
`G[D̃₂, S \ S₁]`. The assignment for (LP-1) is
* `α_i = α̂_i` for `i ∈ D̃₂`;
* `α_i = c⁽ˡ⁾` for `i ∈ D⁽ˡ⁾`, `l = 0, 1, …, L`;
* `β_j = w_j (Σ_{i ∈ N(j)} x*_{ij})² + β̂_j 𝟙{j ∈ S \ S₁}` for `j ∈ S`.

**Formalization Note.** `α̂` is a function on `D₁ ⊕ D₂` (only its values on `D̃₂` are used) and
`β̂` a function on `S` (its values on `S₁` are multiplied by `0`). In the statements that use
this assignment `(α̂, β̂)` depends on `M₁` and `A`.
-/

variable {D₁ D₂ S : Type*} [Fintype D₁] [Fintype S] [DecidableEq D₁] [DecidableEq S]

/-- The demand duals `α`: the level slack `c⁽ˡ⁾` on `i ∈ D⁽ˡ⁾ ⊆ D₁`, and `α̂_i` on `D₂`. -/
noncomputable def dualAlpha (I : Instance D₁ D₂ S) (x : D₁ → S → ℝ) (αh : D₁ ⊕ D₂ → ℝ) :
    D₁ ⊕ D₂ → ℝ
  | Sum.inl i => levelSlack I.w x (levelD x i)
  | Sum.inr i => αh (Sum.inr i)

/-- The supply duals `β_j = w_j (Σ_{i ∈ N(j)} x_{ij})² + β̂_j 𝟙{j ∈ S \ S₁}`, where `S₁` is the set
of supplies matched by `M₁`. -/
noncomputable def dualBeta (I : Instance D₁ D₂ S) (x : D₁ → S → ℝ)
    (M : Finset ((D₁ ⊕ D₂) × S)) (βh : S → ℝ) (j : S) : ℝ :=
  I.w j * (load x j) ^ 2 + if j ∈ Finset.univ \ matchedSupply M then βh j else 0

end TwoStageMatch


