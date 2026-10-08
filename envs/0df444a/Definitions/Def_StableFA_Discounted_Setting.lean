-- Prove2me | Definitions.Def_StableFA_Discounted_Setting
-- name    : StableFA_Discounted_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T08:21:23.07427+00:00
-- url     : https://prove2.me/theorems/8b088159-706d-4241-b790-a73156ff0c13
-- title:
--   §3, pp. 5 and 7 — the averager (k_i, β_i, β_ij), its mapping M_A, and compatible operators
-- statement:
--   This file sets up the function-approximation side of approximate value iteration for a finite Markov decision process with states $1,\dots,n$. Value functions are vectors $V\in\mathbb R^n$.
--
--   1. **Averager.** An averager $A$ on $n$ states consists of real constants $k_i$, nonnegative weights $\beta_i$ and nonnegative weights $\beta_{ij}$ ($i,j=1,\dots,n$) such that for every $i$
--   $$\beta_i+\sum_{j=1}^n\beta_{ij}=1 .$$
--   The weights are fixed numbers: they may depend on how the approximator is set up, but not on the target values.
--
--   2. **The mapping $M_A$.** The mapping associated with $A$ sends a vector $Y$ of target values to the vector $\hat Y=M_A(Y)$ of fitted values,
--   $$\hat Y_i=\beta_i k_i+\sum_{j=1}^n\beta_{ij}Y_j .$$
--   Each fitted value is thus a weighted average of target values and a predetermined constant. Examples are $k$-nearest-neighbour, kernel averaging and linear or bilinear interpolation on a mesh.
--
--   3. **Compatible operators.** Two operators $M_F$ and $T$ on $\mathbb R^n$ are *compatible* if for every initial guess $x_0$ the sequence $(M_F\circ T)^k(x_0)$, $k=0,1,2,\dots$, converges to some point $x^*$ of $\mathbb R^n$.
--
--   These are the objects of Gordon's stability theory: compatibility of the approximator with the value backup is what makes approximate value iteration converge, and averagers are the class of approximators for which it always holds in the discounted case.
--
--   **Formalization Note** The averager is indexed by the state set: $M_A$ acts on whole value functions $\mathbb R^n\to\mathbb R^n$. The paper's approximator fits targets at a sample $X_0$ of states; an approximator that ignores the value at a state $j\notin X_0$ is the special case $\beta_{ij}=0$ for all $i$. In `Compatible MF T` the iterated map is `MF ∘ T` (fit after the backup), as on the page; the limit must exist for every initial guess, and may depend on it, as the page's definition allows.
-- source:
--   Gordon, Stable Function Approximation in Dynamic Programming, Tech. Rep. CMU-CS-95-103, Carnegie Mellon University (1995), p. 5 (definitions of the mapping associated with A, and of compatible operators) and p. 7 (definition of averager)

import Mathlib
import Definitions.Def_BertsekasSSPModel

namespace StableFA.Discounted

open Filter Topology

/-- An averager (Gordon 1995, p. 7), indexed by the `n` states of a finite MDP: for each
state `i` there is a constant `k i`, a nonnegative weight `βc i` on that constant (the
paper's `β_i`) and nonnegative weights `β i j` (the paper's `β_ij`) on the target values,
with `βc i + ∑ j, β i j = 1`. The weights are fixed data and do not depend on the targets. -/
structure Averager (n : ℕ) where
  /-- the predetermined constants `k_i` -/
  k : Fin n → ℝ
  /-- the weight `β_i` on the constant `k_i` -/
  βc : Fin n → ℝ
  /-- the weight `β_ij` of target value `Y_j` in fitted value `Ŷ_i` -/
  β : Fin n → Fin n → ℝ
  βc_nonneg : ∀ i, 0 ≤ βc i
  β_nonneg : ∀ i j, 0 ≤ β i j
  sum_eq_one : ∀ i, βc i + ∑ j, β i j = 1

/-- The mapping `M_A` associated with the averager `A` (pp. 5 and 7): it sends a vector of
target values `Y` to the vector of fitted values `Ŷ_i = β_i k_i + ∑_j β_ij Y_j`. -/
def Averager.apply {n : ℕ} (A : Averager n) (Y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => A.βc i * A.k i + ∑ j, A.β i j * Y j

/-- Two operators `M_F` and `T` on `ℝ^n` are compatible (p. 5) if repeated application of
`M_F ∘ T` converges to some point from every initial guess `x₀`. -/
def Compatible {n : ℕ} (MF T : (Fin n → ℝ) → (Fin n → ℝ)) : Prop :=
  ∀ x₀ : Fin n → ℝ, ∃ x : Fin n → ℝ, Tendsto (fun k => (MF ∘ T)^[k] x₀) atTop (𝓝 x)

end StableFA.Discounted


