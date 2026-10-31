-- Prove2me | Definitions.Def_UnbiasedTimeAvg_ChainModel
-- name    : UnbiasedTimeAvg_ChainModel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:20:29.623156+00:00
-- url     : https://prove2.me/theorems/b42229bf-92d5-42f0-b1d9-65f0249c6fa2
-- title:
--   The standing model: a Markov chain $X_{i+1}=g(X_i,U_i)$ with i.i.d. noise and square-integrable $f(X_i)$
-- statement:
--   The paper's standing assumptions (p.2, p.4 and §2.1). On a probability space $(\Omega,P)$:
--
--   1. $(U_i)_{i\in\mathbb Z}$ are independent and identically distributed random variables with values in a measurable space $F'$;
--   2. $g:F\times F'\to F$ is measurable (for the product σ-algebra) and $f:F\to\mathbb R$ is measurable;
--   3. the chain $X_0=x_0$ (deterministic), $X_{i+1}=g(X_i,U_i)$ satisfies $\mathbb E\big[f(X_i)^2\big]<\infty$ for every $i\ge0$.
--
--   `ChainModel P U g f x₀` is the conjunction of these conditions. Every theorem of the mission is stated under it.
--
--   **Formalization Note** The probability measure is supplied separately as `[IsProbabilityMeasure P]`. "Independent and identically distributed" is mutual independence of the family `U` (`iIndepFun`) together with equality of all marginal laws (`IdentDistrib`).
-- source:
--   N. Kahalé, Unbiased time-average estimators for Markov chains, arXiv:2209.09581v1 (20 Sep 2022), p.2 (Markov chain, deterministic X_0, measurable f, f(X_i) square-integrable), p.4 ((1.1), i.i.d. U_i, measurable g), §2.1 p.4 (U_i, i ∈ ℤ)

import Mathlib
import Definitions.Def_UnbiasedTimeAvg_coupledChain

open MeasureTheory ProbabilityTheory

namespace UnbiasedTimeAvg

/-- **The standing model of the paper: a Markov chain driven by i.i.d. noise.**
Kahalé, arXiv:2209.09581v1, p.2 ("a Markov chain `(X_i, i ≥ 0)` with state-space `F` and
deterministic initial value `X₀`. Let `f` be a deterministic real-valued measurable function on `F`
such that `f(X_i)` is square-integrable for `i ≥ 0`"), p.4 ((1.1): i.i.d. `U_i` with values in a
measurable space `F′` and a measurable `g : F × F′ → F` with `X_{i+1} = g(X_i, U_i)`), and §2.1, p.4
(the sequence is extended to i.i.d. `U_i`, `i ∈ ℤ`).

`ChainModel P U g f x₀` says, on the probability space `(Ω, P)`:
1. every `U_i`, `i ∈ ℤ`, is measurable, the family `(U_i)_{i ∈ ℤ}` is mutually independent, and
   all `U_i` have the same law;
2. `g` is jointly measurable and `f` is measurable;
3. `f(X_i)` is square-integrable for every `i ≥ 0`, where `X_i = X_{i,0}` is the chain started
   from the deterministic point `x₀` at time `0`.

**Formalization Note.** The probability measure is the instance argument
`[IsProbabilityMeasure P]` of each theorem. The chain is `coupledChain g x₀ U i 0`. -/
structure ChainModel {Ω F F' : Type*} [MeasurableSpace Ω] [MeasurableSpace F]
    [MeasurableSpace F'] (P : Measure Ω) (U : ℤ → Ω → F') (g : F → F' → F) (f : F → ℝ)
    (x₀ : F) : Prop where
  measurable_U : ∀ i, Measurable (U i)
  iIndep_U : iIndepFun U P
  identDistrib_U : ∀ i j, IdentDistrib (U i) (U j) P P
  measurable_g : Measurable (Function.uncurry g)
  measurable_f : Measurable f
  memLp_f : ∀ i : ℕ, MemLp (fun ω => f (coupledChain g x₀ U i 0 ω)) 2 P

end UnbiasedTimeAvg


