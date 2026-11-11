-- Prove2me | Definitions.Def_FracColorLocal_KrFree_Dichotomy
-- name    : FracColorLocal_KrFree_Dichotomy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T07:11:42.155196+00:00
-- url     : https://prove2.me/theorems/94fa5da9-21b1-4498-b8dd-9dcc1d63dca2
-- title:
--   b(A), D_θ and the witness conditions (5.1)–(5.2)
-- statement:
--   Let $G$ be a finite graph with positive vertex weights $w$ and positive vertex parameters $\theta_v$. Put
--
--   $$b(A)=\sum_{v\in A}\theta_v w(v),\qquad D_\theta=\sum_v\theta_v w(v)\Lambda_v=\sum_{xy\in E(G)}w(x)w(y)(\theta_x+\theta_y),\qquad e_w(A,B)=\sum_{x\in A}\sum_{y\in B\cap N(x)}w(x)w(y),$$
--
--   where $e_w$ counts ordered pairs (an edge with both ends in $A\cap B$ is counted in both directions). Sets $A,B\subseteq V$, an integer $p\ge 1$ and a real $\rho$ satisfy (5.1) and (5.2) when
--
--   $$w(A),\,w(B)\le\rho 2^p,\qquad b(B)\le\rho^2 2^{2p},\qquad e_w(A,B)>24\big(p\,b(A)+\rho^2 2^{-p}\big).$$
--
--   **Formalization Note** `IsWitness G w θ A B p ρ` is the conjunction of these four inequalities, with `mass` and `crossMass` (= $e_w$) from the referenced weighted-graph definitions; $p$ is a natural number and $2^{-p}$ is the integer power `(2:ℝ) ^ (-(p:ℤ))`. The integer $p\ge 1$ and the requirement $\rho\in\{\theta_v\}$, where needed, are stated in the theorems.
-- source:
--   Davies, Dhawan, Methuku, Nguyen, Seo, Fractional colorings of K_r-free graphs with local demands, arXiv:2611.04297 (PDF sha256 b3f2dcce…), p. 20 (PDF 21), §5.1, (5.1), (5.2)

import Mathlib
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph

namespace FracColorLocal.KrFree

open OAI.CliqueFreeIndependence.WeightedGraph

variable {V : Type*} [Fintype V]

/-- `b(A) := ∑_{v ∈ A} θ_v w(v)` (§5.1). -/
noncomputable def bMass (θ w : V → ℝ) (A : Finset V) : ℝ := ∑ v ∈ A, θ v * w v

/-- `D_θ := ∑_v θ_v w(v) Λ_v` with `Λ_v = w(N(v))` (§5.1). -/
noncomputable def dTheta (G : SimpleGraph V) (w θ : V → ℝ) : ℝ :=
  ∑ v, θ v * w v * neighborMass G w v

/-- `(A, B, p, ρ)` satisfy (5.1) and (5.2):
`w(A), w(B) ≤ ρ 2^p`, `b(B) ≤ ρ² 2^{2p}`, and `e_w(A, B) > 24 (p b(A) + ρ² 2^{-p})`,
where `e_w(A, B) = crossMass G w A B` counts ordered pairs (an edge inside `A ∩ B` twice). -/
def IsWitness (G : SimpleGraph V) (w θ : V → ℝ) (A B : Finset V) (p : ℕ) (ρ : ℝ) : Prop :=
  mass w A ≤ ρ * 2 ^ p ∧ mass w B ≤ ρ * 2 ^ p ∧ bMass θ w B ≤ ρ ^ 2 * 2 ^ (2 * p) ∧
    24 * ((p : ℝ) * bMass θ w A + ρ ^ 2 * (2 : ℝ) ^ (-(p : ℤ))) < crossMass G w A B

end FracColorLocal.KrFree


