-- Prove2me | Definitions.Def_SolomonRWRE_DiffEq_TwoSided
-- name    : SolomonRWRE_DiffEq_TwoSided
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:30:47.937678+00:00
-- url     : https://prove2.me/theorems/ff7a5b91-189d-425b-a46d-6c4172c58d82
-- title:
--   §4, proof of Theorem (4.4), p. 29 — two-sided i.i.d. family {σ_j}_{j∈ℤ} and S_n = Σ_{j=−∞}^n σ_j ⋯ σ_n
-- statement:
--   In the proof of Theorem (4.4) the driving sequence is extended to both sides: "without loss of generality we may assume that $\sigma_j$ is the $j$th coordinate function on the probability space $([0,\infty]^{\mathbb Z},\mathcal F,P)$ … and $P$ is the product measure."
--
--   1. **Two-sided family.** $\{\sigma_j\}_{j\in\mathbb Z}$ is a family of measurable, nonnegative, mutually independent random variables, each with the law of $\sigma_1$.
--   2. **The two-sided series.** For $n\in\mathbb Z$,
--   $$
--   S_n=\sum_{j=-\infty}^{n}\sigma_j\cdots\sigma_n\in[0,\infty].
--   $$
--
--   $S_n$ dominates $Z_n$ (computed from $\sigma_1,\dots,\sigma_n$). Unlike $Z_n$, it is the image of $S_1$ under a shift of the sequence, which is what lets an ergodic theorem be applied.
--
--   **Formalization Note** This is a different object from the one-sided family of `System`: the index set is $\mathbb Z$ and all $\sigma_j$, $j\le 0$ included, are i.i.d. The values are real. The paper's coordinates live in $[0,\infty]$, but $\sigma$ is a real random variable, so they take the value $\infty$ with probability $0$. $S_n$ is a series in $[0,\infty]$, so no summability hypothesis is needed to write it.
-- source:
--   Solomon, Random Walks in a Random Environment, Ann. Probab. 3(1):1–31 (1975), DOI 10.1214/aop/1176996444, p. 29, proof of Theorem (4.4), third paragraph

import Mathlib
import Definitions.Def_SolomonRWRE_DiffEq_System

open MeasureTheory ProbabilityTheory

namespace SolomonRWRE.DiffEq

/-- **The two-sided i.i.d. family** of the proof of Theorem (4.4), p. 29: "Without loss of
generality we may assume that `σ_j` is the `j`th coordinate function on the probability space
`([0, ∞]^Z, 𝓕, P)` … and `P` is the product measure."

**Formalization Note.** This is a different object from `IsIIDNonneg`: the family is indexed
by `ℤ`, and all of `σ_j`, `j ∈ ℤ`, are independent, nonnegative and identically distributed.
The values are real (the paper's `[0, ∞]` coordinates take the value `∞` with probability `0`).
`Z` is applied to its restriction `n ↦ σ n` to `ℕ`, which uses `σ_1, …, σ_n` only. -/
structure IsIIDNonnegZ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (σ : ℤ → Ω → ℝ) :
    Prop where
  meas : ∀ n, Measurable (σ n)
  nonneg : ∀ n ω, 0 ≤ σ n ω
  indep : iIndepFun σ P
  ident : ∀ n, IdentDistrib (σ n) (σ 1) P P

/-- **`S_n = Σ_{j=−∞}^n σ_j ⋯ σ_n`** (proof of Theorem (4.4), p. 29), in `[0, ∞]`.
The term with index `m` is `σ_{n−m} ⋯ σ_n`, i.e. `j = n − m`. -/
noncomputable def S {Ω : Type*} (σ : ℤ → Ω → ℝ) (n : ℤ) (ω : Ω) : ENNReal :=
  ∑' m : ℕ, ∏ l ∈ Finset.range (m + 1), ENNReal.ofReal (σ (n - l) ω)

end SolomonRWRE.DiffEq


