-- Prove2me | Definitions.Def_QuantumCycleColoring_FourColor_DependentProcess
-- name    : QuantumCycleColoring_FourColor_DependentProcess
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T17:59:18.670987+00:00
-- url     : https://prove2.me/theorems/dead5237-befb-49df-9475-fb3d8870e41d
-- title:
--   Stationary and $k$-dependent processes on $\mathbb Z$
-- statement:
--   Let $(Y_t)_{t\in\mathbb Z}$ be random labels, each a measurable map from a probability space $(\Omega,\mu)$ to a measurable space $S$.
--
--   1. The process is **stationary** if it is invariant under integer shifts: $(Y_{t+1})_{t\in\mathbb Z}$ and $(Y_t)_{t\in\mathbb Z}$ have the same law as random elements of $S^{\mathbb Z}$ with the product $\sigma$-algebra.
--   2. The process is **$k$-dependent** if for any two index sets $U,V\subseteq\mathbb Z$ at distance larger than $k$ (every $u\in U$, $v\in V$ have $|u-v|>k$), the random vectors $(Y_i)_{i\in U}$ and $(Y_i)_{i\in V}$ are independent.
--
--   Every one-way one-round anonymous algorithm on the line produces a stationary $1$-dependent output process; Lemma 6.2 is a statement about such processes with values in $\{0,1\}$.
--
--   **Formalization Note** Measurability of every $Y_t$ is part of stationarity, so that the two laws are push-forwards along measurable maps.
-- source:
--   Tom Gur, Longcheng Li, STOC 2027 submission #515 (October 2026), §3.3, paragraph "Finite dependence" (p.20)

import Mathlib

/-!
# Stationary and 1-dependent processes on the integer line

Tom Gur, Longcheng Li, *Impossibility of One-Way One-Round Quantum 4-Coloring via Matrix-Space
Stability*, STOC 2027 submission #515 (October 2026), §3.3, paragraph "Finite dependence", p.20.

A process is a family `Y : ℤ → Ω → S` of measurable random labels on a probability space.
-/

namespace QuantumCycleColoring.FourColor

open MeasureTheory ProbabilityTheory

variable {Ω S : Type} [MeasurableSpace Ω] [MeasurableSpace S]

/-- p.20: the process `(Y_t)_{t ∈ ℤ}` is stationary if it is invariant under integer shifts:
every `Y_t` is measurable and `(Y_{t+1})_{t∈ℤ}` and `(Y_t)_{t∈ℤ}` are equal in law (as random
elements of `S^ℤ` with the product σ-algebra). -/
def IsStationaryProcess (μ : Measure Ω) (Y : ℤ → Ω → S) : Prop :=
  (∀ t, Measurable (Y t)) ∧
    μ.map (fun ω (t : ℤ) => Y (t + 1) ω) = μ.map (fun ω (t : ℤ) => Y t ω)

/-- p.20: the process is `k`-dependent if for any two index sets `U, V ⊆ ℤ` at distance larger
than `k` (every `u ∈ U`, `v ∈ V` have `|u − v| > k`), the random vectors `(Y_i)_{i∈U}` and
`(Y_i)_{i∈V}` are independent. -/
def IsKDependent (k : ℕ) (μ : Measure Ω) (Y : ℤ → Ω → S) : Prop :=
  ∀ U V : Set ℤ, (∀ u ∈ U, ∀ v ∈ V, (k : ℤ) < |u - v|) →
    IndepFun (fun ω (i : U) => Y i ω) (fun ω (j : V) => Y j ω) μ

end QuantumCycleColoring.FourColor


