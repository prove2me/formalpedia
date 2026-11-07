-- Prove2me | Definitions.Def_HZTractability_IsNormAddEq
-- name    : HZTractability_IsNormAddEq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:07:10.349033+00:00
-- url     : https://prove2.me/theorems/c432259a-ba88-4b32-9172-f06f17f4a4d2
-- title:
--   Normalized additive $\varepsilon$-equilibrium (Definition 2.2)
-- statement:
--   Consider an HZ market with buyers $i$, goods $j$ and utilities $u_{ij}$; buyer $i$'s utility for a bundle $x_i$ is $U_i(x_i)=\sum_j u_{ij}x_{ij}$. An allocation $x\ge 0$ is **feasible** if every buyer receives total quantity one and every good is fully allocated:
--   $$
--   \sum_j x_{ij}=1\ \text{for every buyer } i,\qquad \sum_i x_{ij}=1\ \text{for every good } j .
--   $$
--   Prices $p\ge 0$ are **normalized** if $\min_j p_j=0$. For $\varepsilon\ge 0$, a pair $(p,x)$ with normalized prices and a feasible allocation is a **normalized additive $\varepsilon$-equilibrium** if, for every buyer $i$,
--   $$
--   p\cdot x_i\le 1+\varepsilon,\qquad U_i(x_i)\ge V_i(p)-\varepsilon,
--   $$
--   where $V_i(p)$ is the budget-**one** optimal utility of (OptBundle). The case $\varepsilon=0$ is an exact equilibrium.
--
--   This is the solution concept of the mission's goal (Theorem 1.1) and of every robustness estimate. It allows expenditure on zero-utility goods and imposes no minimum-expenditure tie-breaking.
--
--   **Formalization Note** $U_i(x_i)\ge V_i(p)-\varepsilon$ is written as $U_i(x_i)\ge \sum_j u_{ij}y_j-\varepsilon$ for every budget-one unit bundle $y$; with $\min_j p_j=0$ the maximum is attained, so this is the same condition. Buyers and goods are arbitrary finite types; $N$ buyers, $N$ goods and $u_{ij}\in[0,1]$ are stated where they are needed.
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), Definition 2.2, p.7 (PDF p.9); feasibility, normalization and (OptBundle), §2.2, p.7

import Mathlib
import Definitions.Def_HZTractability_IsUnitBundle

namespace HZTractability

/-- **Normalized additive ε-equilibrium** (Panageas–Shein–Taherijam–Vazirani, *Exploring the
Tractability Frontier of Hylland–Zeckhauser Models*, arXiv:2610.35848, held version, sha256
74b7bf9f…, Definition 2.2, p.7 (PDF 9)): "a pair p, x ≥ 0 with min_j p_j = 0 and feasible x such
that, for every buyer i, p · x_i ≤ 1 + ε, U_i(x_i) ≥ V_i(p) − ε."

In the HZ market with buyers `B`, goods `G` and utilities `u` (§2.2, p.7): `x ≥ 0`, `p ≥ 0`, some
price is zero (`min_j p_j = 0`), `x` is feasible (every row sum and every column sum is exactly
one), every buyer spends at most `1 + ε`, and every buyer's utility `U_i(x_i) = ∑_j u_ij x_ij` is at
least `V_i(p) − ε`, where `V_i(p)` is the budget-**one** optimal utility of (OptBundle).

**Formalization Note** `U_i(x_i) ≥ V_i(p) − ε` is written as `∑_j u_ij y_j − ε ≤ U_i(x_i)` for
every budget-one unit bundle `y` (`IsUnitBundle`); since `min_j p_j = 0` the maximum in (OptBundle)
is attained, so this is the same condition and no supremum junk value enters. Buyers and goods are
arbitrary finite types; Definition 2.2 has `|B| = |G| = N ≥ 1` and `u_ij ∈ [0, 1]` (p.7), which
are stated where they are needed. Definition 2.2 is for `ε ≥ 0`; the predicate is stated for every
real `ε`. -/
def IsNormAddEq {B G : Type} [Fintype B] [Fintype G] (u : B → G → ℝ) (ε : ℝ)
    (x : B → G → ℝ) (p : G → ℝ) : Prop :=
  (∀ i j, 0 ≤ x i j) ∧ (∀ j, 0 ≤ p j) ∧ (∃ j, p j = 0) ∧
  (∀ i, ∑ j, x i j = 1) ∧ (∀ j, ∑ i, x i j = 1) ∧
  (∀ i, ∑ j, p j * x i j ≤ 1 + ε) ∧
  ∀ i y, IsUnitBundle p y → ∑ j, u i j * y j - ε ≤ ∑ j, u i j * x i j

end HZTractability


