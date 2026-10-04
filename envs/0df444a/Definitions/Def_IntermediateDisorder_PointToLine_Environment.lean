-- Prove2me | Definitions.Def_IntermediateDisorder_PointToLine_Environment
-- name    : IntermediateDisorder_PointToLine_Environment
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T04:04:07.302461+00:00
-- url     : https://prove2.me/theorems/20ea96dc-4ce8-44db-81d8-7dcbbb904255
-- title:
--   The random environment, the simple random walk, and the partition functions $Z_n^\omega(\beta)$ and $\mathfrak z_n^\omega(\beta)$
-- statement:
--   This file fixes the directed polymer model in dimension $1+1$.
--
--   **Environment.** Let $(\Omega,\mathcal F,Q)$ be a probability space and $\omega=(\omega(i,x))_{(i,x)\in\mathbb N\times\mathbb Z}$ a family of real random variables on it. The environment satisfies the **standard assumptions** if
--
--   1. the variables $\omega(i,x)$ are mutually independent;
--   2. they all have the law of the reference variable $\omega(1,0)$;
--   3. $\omega(1,0)$ is square integrable, with $Q[\omega(1,0)]=0$ and $Q[\omega(1,0)^2]=1$.
--
--   **Polymer.** $S$ is the symmetric simple random walk on $\mathbb Z$ started at $S_0=0$: an $n$-step path is a sequence of steps $s_1,\dots,s_n\in\{-1,+1\}$, all $2^n$ sequences being equally likely, and $S_i=s_1+\dots+s_i$. The energy of the path in the environment $\omega$ is $H_n^\omega(S)=\sum_{i=1}^n\omega(i,S_i)$. The **point-to-line partition function** and the **modified partition function** (4) are
--
--   $$Z_n^\omega(\beta)=\mathbf P\big[e^{\beta H_n^\omega(S)}\big]=\frac1{2^n}\sum_{s\in\{\pm1\}^n}e^{\beta H_n^\omega(S)},\qquad \mathfrak z_n^\omega(\beta)=\mathbf P\Big[\prod_{i=1}^n\big(1+\beta\,\omega(i,S_i)\big)\Big].$$
--
--   For a fixed environment both are finite averages over the $2^n$ paths. The intermediate disorder regime evaluates them at $\beta n^{-1/4}$.
--
--   **Formalization Note** A step sequence is a map $\{0,\dots,n-1\}\to\mathrm{Bool}$, with `true` read as $+1$; the step indexed by $j$ is taken at time $j+1$, so the environment is read at times $1,\dots,n$ only, never at time $0$. The environment is indexed by $\mathbb N\times\mathbb Z$; the variables at time $0$ are never used. Mean zero and variance one are the paper's standing assumption of Section 5 (p. 29); they are bundled in the structure `IsStdEnvironment`, and square integrability is stated explicitly so that neither integral is a junk value.
-- source:
--   Alberts, Khanin, Quastel, The intermediate disorder regime for directed polymers in dimension 1+1, arXiv:1202.4398v3, p. 2 (model, Z_n^ω), p. 6 eq. (4) (modified partition function), p. 29 (standing assumption: mean zero, variance one)

import Mathlib

namespace IntermediateDisorder.PointToLine

open MeasureTheory ProbabilityTheory

/-- The standing assumptions on the random environment: `ω (i, x)`, `(i, x) ∈ ℕ × ℤ`, is a family
of real random variables on `(Ω, Q)` that are mutually independent, all distributed like the
reference variable `ω (1, 0)`, square integrable, with mean zero and variance one
(Alberts–Khanin–Quastel, p. 2 and the standing assumption of §5, p. 29).
Only the variables with time index `i ≥ 1` are ever read by the polymer. -/
structure IsStdEnvironment {Ω : Type*} [MeasurableSpace Ω] (ω : ℕ × ℤ → Ω → ℝ)
    (Q : Measure Ω) : Prop where
  measurable : ∀ p, Measurable (ω p)
  indep : iIndepFun ω Q
  identDistrib : ∀ p, IdentDistrib (ω p) (ω (1, 0)) Q Q
  memLp_two : MemLp (ω (1, 0)) 2 Q
  mean_zero : ∫ a, ω (1, 0) a ∂Q = 0
  second_moment : ∫ a, ω (1, 0) a ^ 2 ∂Q = 1

/-- A step of the simple random walk: `true ↦ +1`, `false ↦ -1`. -/
def stepZ (b : Bool) : ℤ := if b then 1 else -1

/-- Position `S_i = s_1 + ⋯ + s_i` after `i` steps of the walk whose step sequence is `s`
(steps indexed by `Fin n`, the `j`-th step is taken at time `j + 1`); `S_0 = 0`. -/
def walkPos {n : ℕ} (s : Fin n → Bool) (i : ℕ) : ℤ :=
  ∑ j : Fin n, if (j : ℕ) < i then stepZ (s j) else 0

/-- The energy `H_n^ω(S) = ∑_{i=1}^n ω(i, S_i)` of the `n`-step path with steps `s`. -/
def energy {Ω : Type*} (ω : ℕ × ℤ → Ω → ℝ) {n : ℕ} (s : Fin n → Bool) (a : Ω) : ℝ :=
  ∑ m : Fin n, ω ((m : ℕ) + 1, walkPos s ((m : ℕ) + 1)) a

/-- The point-to-line partition function `Z_n^ω(β) = P[exp(β H_n^ω(S))]`: the average over the
`2^n` equally likely step sequences of the simple random walk started at `0`. -/
noncomputable def partitionFunction {Ω : Type*} (ω : ℕ × ℤ → Ω → ℝ) (n : ℕ) (β : ℝ)
    (a : Ω) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹ * ∑ s : Fin n → Bool, Real.exp (β * energy ω s a)

/-- The modified partition function (4): `𝔷_n^ω(β) = P[∏_{i=1}^n (1 + β ω(i, S_i))]`. -/
noncomputable def modifiedPartitionFunction {Ω : Type*} (ω : ℕ × ℤ → Ω → ℝ) (n : ℕ) (β : ℝ)
    (a : Ω) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹ *
    ∑ s : Fin n → Bool, ∏ m : Fin n, (1 + β * ω ((m : ℕ) + 1, walkPos s ((m : ℕ) + 1)) a)

end IntermediateDisorder.PointToLine


