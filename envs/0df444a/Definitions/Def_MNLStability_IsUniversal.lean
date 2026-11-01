-- Prove2me | Definitions.Def_MNLStability_IsUniversal
-- name    : MNLStability_IsUniversal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:30:58.223609+00:00
-- url     : https://prove2.me/theorems/b1e506e9-2a4d-4128-a070-f94b5a77dffa
-- title:
--   $I$-universal families of inventory vectors
-- statement:
--   Fix the weights, prices, the law of $M$, the capacity $C$, an accuracy $\varepsilon$ and a set of products $I$. A list $\mathcal U_I$ of inventory vectors is **$I$-universal** when for every vector $U$ with at most $C$ units there is $V\in\mathcal U_I$ such that $U^{\hookleftarrow}=U\hookleftarrow_I V$ satisfies:
--
--   1. $\mathbb E[X_i^{U^{\hookleftarrow}}]\ge\mathbb E[X_i^U]$ for every product $i\notin I$;
--   2. $\sum_{i\in I}r_i\,\mathbb E[X_i^{U^{\hookleftarrow}}]\ge(1-\varepsilon)\sum_{i\in I}r_i\,\mathbb E[X_i^U]$;
--   3. $\|U^{\hookleftarrow}\|_1\le\|U\|_1$.
--
--   Universal families let the algorithm enumerate the part of an unknown optimal vector that lives in one weight class.
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), §4.1, p.18 (definition of I-universal); §3.2, p.16

import Mathlib
import Definitions.Def_MNLStability_expX
import Definitions.Def_MNLStability_opt
import Definitions.Def_MNLStability_swap

namespace MNLStability

variable {n : ℕ}

/-- A list `F` of inventory vectors is `I`-universal (SSRN:3498325, §4.1, p.18) for the weights
`wts`, prices `r`, law `pM`, capacity `C` and accuracy `ε` when, for every vector `U` with at most
`C` units, some `V ∈ F` makes `U' = U ↩_I V` satisfy:
1. `E[X_i^{U'}] ≥ E[X_i^U]` for every product `i ∉ I`;
2. `Σ_{i ∈ I} r_i E[X_i^{U'}] ≥ (1 − ε) · Σ_{i ∈ I} r_i E[X_i^U]`;
3. `‖U'‖₁ ≤ ‖U‖₁`. -/
def IsUniversal (wts : Weights n) (r : Fin n → ℝ) (pM : ℕ →₀ ℝ) (C : ℕ) (ε : ℝ)
    (I : Finset (Fin n)) (F : List (Fin n → ℕ)) : Prop :=
  ∀ U : Fin n → ℕ, norm1 U ≤ C → ∃ V ∈ F,
    (∀ i, i ∉ I → expX wts pM U i ≤ expX wts pM (swap I U V) i) ∧
    (1 - ε) * ∑ i ∈ I, r i * expX wts pM U i ≤ ∑ i ∈ I, r i * expX wts pM (swap I U V) i ∧
    norm1 (swap I U V) ≤ norm1 U

end MNLStability


