-- Prove2me | Definitions.Def_IntroDelayAMDP_Supplement_alg2Inner
-- name    : IntroDelayAMDP_Supplement_alg2Inner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:47:38.175116+00:00
-- url     : https://prove2.me/theorems/288d40d8-2b93-4094-b257-e30db4b02b78
-- title:
--   Algorithm 2 — the inner removal loop
-- statement:
--   The inner loop of **Algorithm 2**: starting from $R_j=R$ with $m_j=|R|$ fixed, while some $i\in R_j$ has $\|\phi_i\|^2_{\Lambda_j^{-1}}>2d\log(1+1/\lambda)$ with $\Lambda_j=\lambda I+\frac1{m_j}\sum_{i\in R_j}\phi_i\phi_i^\top$, remove one such $i$ (chosen by the removal rule) and recompute $\Lambda_j$. It returns the final $R_j$.
--
--
--   **Formalization Note** The loop runs with fuel $|R|+1$; since each round removes an index, the fuel never binds.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Algorithm 2, lines 4–5, p.17

import Mathlib
import Definitions.Def_IntroDelayAMDP_Supplement_RemovalRule

namespace IntroDelayAMDP.Supplement

open Matrix

open Classical in
/-- **The inner loop of Algorithm 2** (lines 4–5, printed p.17, PDF p.19, of
Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)): "while some `i ∈ R_j` has
`‖ϕ_i‖²_{Λ_j^{-1}} > 2d log(1 + 1/λ)` do Remove one such `i` from `R_j`, and recompute
`Λ_j ← λI + (1/m_j) ∑_{i∈R_j} ϕ_iϕ_iᵀ` with `m_j` fixed."
`alg2Inner rule ϕ λ r m_j fuel R` runs this loop from `R_j = R` with `r = 2d log(1 + 1/λ)`, removing the index
chosen by `rule` among the violating ones, and returns the final `R_j`.

**Formalization Note.** Every round removes one index, so `fuel = |R| + 1` rounds always reach the end of
the loop; the fuel never binds. -/
noncomputable def alg2Inner {d : ℕ} (rule : RemovalRule d) (ϕ : ℕ → Fin d → ℝ) (lam r : ℝ) (mj : ℕ) :
    ℕ → Finset ℕ → Finset ℕ
  | 0, R => R
  | fuel + 1, R =>
    let Λ : Matrix (Fin d) (Fin d) ℝ := lam • 1 + (1 / (mj : ℝ)) • ∑ i ∈ R, Matrix.vecMulVec (ϕ i) (ϕ i)
    let V := R.filter (fun i => r < ϕ i ⬝ᵥ (Λ⁻¹ *ᵥ ϕ i))
    if V.Nonempty then alg2Inner rule ϕ lam r mj fuel (R.erase (rule.choose ϕ R V)) else R

end IntroDelayAMDP.Supplement


