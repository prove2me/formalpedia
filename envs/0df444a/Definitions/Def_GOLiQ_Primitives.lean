-- Prove2me | Definitions.Def_GOLiQ_Primitives
-- name    : GOLiQ_Primitives
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:50:20.368057+00:00
-- url     : https://prove2.me/theorems/a7d51771-5833-4dce-957c-9776eabb695c
-- title:
--   Random primitives: i.i.d. unit-mean $U_n$, $V_n$ and the coordinate draws $Z_k$
-- statement:
--   On a probability space $(\Omega,P)$:
--
--   1. $U_1,U_2,\dots$ and $V_1,V_2,\dots$ are i.i.d. sequences of nonnegative random variables with $\mathbb E[U_n]=\mathbb E[V_n]=1$; with fee $p$ and rate $\mu$, interarrival times are $U_n/\lambda(p)$ and service times $V_n/\mu$;
--   2. $Z_1,Z_2,\dots$ are i.i.d. and uniform on $\{1,2\}$; $Z_k$ is the coordinate drawn in iteration $k$ of Algorithm 1;
--   3. all of these variables are mutually independent.
--
--   These primitives drive the queue under every policy and the GOLiQ algorithm.
--
--   **Formalization Note** Indices start at $1$; the values at index $0$ are not used. Independence is the mutual independence of the family indexed by (sequence, index).
-- source:
--   Chen, Liu, Hong, An Online Learning Approach to Dynamic Pricing and Capacity Sizing in Service Systems, arXiv:2009.02911v3, §3.1, p.11; Algorithm 1, p.32

import Mathlib

open MeasureTheory ProbabilityTheory

namespace GOLiQ

/-- **The random primitives of the queue and of the algorithm**
(Chen, Liu, Hong, arXiv:2009.02911v3, §3.1, p.11, and Algorithm 1, p.32).

On a probability space `(Ω, P)`:

* `U₁, U₂, …` and `V₁, V₂, …` are i.i.d. sequences of nonnegative random variables with unit means,
  `E[Uₙ] = E[Vₙ] = 1`; the interarrival times are `Uₙ/λ(p)` and the service times `Vₙ/µ` (p.11);
* `Z₁, Z₂, …` are i.i.d., uniform on `{1, 2}` (the coordinate draws "randomly draw `Z ∈ {1, 2}`" of
  Algorithm 1, p.32);
* the three sequences are independent of each other ("two independent i.i.d. sequences", p.11; the
  draw `Z` is external randomization).

**Formalization Note.** Indices start at `1` as in the paper; the values `U 0`, `V 0`, `Z 0` are not
used and are unconstrained. Mutual independence of all the variables is `iIndepFun` over the index
set `Fin 3 × ℕ` (sequence, index − 1). Nonnegativity of `Uₙ`, `Vₙ` holds because they are scaled
times. -/
structure Primitives (Ω : Type*) [MeasurableSpace Ω] where
  /-- The probability measure. -/
  P : Measure Ω
  isProbabilityMeasure : IsProbabilityMeasure P
  /-- `Uₙ`: interarrival time of customer `n` is `Uₙ / λ`. -/
  U : ℕ → Ω → ℝ
  /-- `Vₙ`: service time is `Vₙ / µ`. -/
  V : ℕ → Ω → ℝ
  /-- `Zₖ ∈ {1, 2}`: the coordinate drawn in iteration `k` of Algorithm 1. -/
  Z : ℕ → Ω → ℝ
  measurable_U : ∀ n, Measurable (U n)
  measurable_V : ∀ n, Measurable (V n)
  measurable_Z : ∀ n, Measurable (Z n)
  /-- All of `U₁, U₂, …, V₁, V₂, …, Z₁, Z₂, …` are mutually independent. -/
  indep : iIndepFun (fun i : Fin 3 × ℕ => (![U, V, Z] i.1) (i.2 + 1)) P
  identDistrib_U : ∀ n, IdentDistrib (U (n + 1)) (U 1) P P
  identDistrib_V : ∀ n, IdentDistrib (V (n + 1)) (V 1) P P
  identDistrib_Z : ∀ n, IdentDistrib (Z (n + 1)) (Z 1) P P
  U_nonneg : ∀ n ω, 0 ≤ U (n + 1) ω
  V_nonneg : ∀ n ω, 0 ≤ V (n + 1) ω
  integrable_U : Integrable (U 1) P
  integrable_V : Integrable (V 1) P
  /-- `E[Uₙ] = 1`. -/
  mean_U : ∫ ω, U 1 ω ∂P = 1
  /-- `E[Vₙ] = 1`. -/
  mean_V : ∫ ω, V 1 ω ∂P = 1
  Z_mem : ∀ n ω, Z (n + 1) ω = 1 ∨ Z (n + 1) ω = 2
  Z_uniform : P {ω | Z 1 ω = 1} = 1 / 2

end GOLiQ


