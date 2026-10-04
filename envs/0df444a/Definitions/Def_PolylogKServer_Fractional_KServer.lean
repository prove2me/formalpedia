-- Prove2me | Definitions.Def_PolylogKServer_Fractional_KServer
-- name    : PolylogKServer_Fractional_KServer
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T05:48:35.52698+00:00
-- url     : https://prove2.me/theorems/3ec7598a-bd87-458f-aec7-5ca30f308412
-- title:
--   Online fractional k-server algorithms on an HST and their competitiveness
-- statement:
--   Let $T$ be a rooted weighted tree whose leaves are the points of a finite metric space $M$ (through a bijection $e$), with $W(v)$ the length of the edge from $v$ to its parent.
--
--   1. A **fractional k-server state** is $x:M\to\mathbb R$ with $0\le x_m\le 1$ for every leaf $m$ (the probability of having a server at $m$) and $\sum_m x_m=k$.
--   2. For a node $v$, $x_v=\sum_{m\in T(v)}x_m$ is the amount of server mass on the leaves of the subtree rooted at $v$. Changing the state from $x$ to $x'$ costs
--   $$
--   \sum_{v\neq r}W(v)\,|x'_v-x_v| .
--   $$
--   3. An **online fractional k-server algorithm** chooses its state after each request as a function of the requests seen so far.
--   4. For an initial configuration $C_0$ of $k$ servers on distinct points, such an algorithm is **$c$-competitive on $T$ from $C_0$** if it starts at the indicator of the points of $C_0$, every state it reaches is a fractional k-server state, after each request at a point $r$ it has a full server at $r$ ($x_r=1$), and there is a constant $a$, independent of the request sequence, such that on every request sequence $\rho$ its total movement cost is at most $c\cdot\mathrm{OPT}(C_0,\rho)+a$, where $\mathrm{OPT}(C_0,\rho)$ is the optimal **integral** offline k-server cost of serving $\rho$ from $C_0$ in $M$.
--
--   This is the fractional relaxation that the paper solves on weighted HSTs (Theorem 6) and then rounds to a randomized algorithm on HSTs (Theorem 7).
--
--   **Formalization Note** The benchmark is `KServer.offlineCost` from the published definition `KServer_model`. The paper allows $\sum_m x_m\le k$ in principle and notes (p. 36, footnote 8) that one may always keep exactly $k$; exactly $k$ is used here, in all three statements that use this definition.
-- source:
--   Bansal, Buchbinder, Mądry, Naor, A Polylogarithmic-Competitive Algorithm for the k-Server Problem, arXiv:1110.1580v1, p. 6 (fractional view on an HST, movement cost Σ_j W(j)|k_t(j) − k_{t−1}(j)|), p. 36 (Σ_i x^t_i = k, footnote 8)

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_PolylogKServer_HST_Tree

/-!
# The fractional k-server problem on a (weighted) HST

Bansal, Buchbinder, Mądry, Naor, *A Polylogarithmic-Competitive Algorithm for the k-Server
Problem*, arXiv:1110.1580v1, §1.2, p. 6 (fractional view, movement cost
`∑_j W(j) |k_t(j) − k_{t−1}(j)|`), p. 36 (`∑_i x^t_i = k`, footnote 8).

The leaves of the tree `T` are the points of a finite metric space `M`, through a bijection
`e : M ≃ T.Leaf`. A fractional state is `x : M → ℝ`, `x m` being the probability of having a
server at the leaf `e m`. The cost of a fractional algorithm is compared with the optimal
**integral** offline k-server cost `KServer.offlineCost` on `M`.
-/

namespace PolylogKServer.Fractional

open Finset PolylogKServer.HST

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A fractional k-server state (p. 6, p. 36): `0 ≤ x m ≤ 1` (a probability) for every leaf,
and the total amount of servers is exactly `k`. -/
def IsFracState (k : ℕ) {M : Type} [Fintype M] (x : M → ℝ) : Prop :=
  (∀ m, 0 ≤ x m ∧ x m ≤ 1) ∧ ∑ m, x m = k

/-- `x_v = k_t(v)`: the amount of servers that `x` has on the leaves of the subtree `T(v)`. -/
noncomputable def subtreeMass (T : WTree V) {M : Type} [Fintype M] (e : M ≃ T.Leaf)
    (x : M → ℝ) (v : V) : ℝ := by
  classical
  exact ∑ m, if T.IsAnc v (e m : V) then x m else 0

/-- The movement cost of changing the fractional state `x` to `x'` (p. 6):
`∑_{v ≠ root} W(v) |x'_v − x_v|`. -/
noncomputable def fracMoveCost (T : WTree V) {M : Type} [Fintype M] (e : M ≃ T.Leaf)
    (x x' : M → ℝ) : ℝ :=
  ∑ v ∈ univ.filter (fun v => v ≠ T.root),
    T.W v * |subtreeMass T e x' v - subtreeMass T e x v|

/-- The fractional state of an integral configuration `C₀`: one unit of server mass on each
point occupied by `C₀`. -/
noncomputable def indicatorState {k : ℕ} {M : Type} (C₀ : KServer.Config k M) : M → ℝ := by
  classical
  exact fun m => if m ∈ Set.range C₀ then 1 else 0

/-- An **online fractional k-server algorithm** on `M`: its state after serving the requests `l`
is `state l`, a function of the request prefix only; `state []` is its initial state. -/
structure FracKServerAlg (k : ℕ) (M : Type) where
  state : List M → M → ℝ

/-- The total movement cost of `F` on the request sequence `ρ`. -/
noncomputable def FracKServerAlg.cost {k : ℕ} {M : Type} [Fintype M] (F : FracKServerAlg k M)
    (T : WTree V) (e : M ≃ T.Leaf) (ρ : List M) : ℝ :=
  ∑ t ∈ range ρ.length, fracMoveCost T e (F.state (ρ.take t)) (F.state (ρ.take (t + 1)))

/-- `F` is a **`c`-competitive fractional k-server algorithm on `T` from `C₀`**:
1. it starts at the indicator state of `C₀`;
2. every state it reaches is a fractional k-server state;
3. it serves every request: after a request at `r`, there is one full server at `r`
   (`p^t_r = 1`, p. 6);
4. there is a constant `a`, fixed before the request sequence, such that its movement cost on
   every request sequence `ρ` is at most `c` times the optimal integral offline k-server cost
   from `C₀` on `M`, plus `a`. -/
def FracKServerAlg.IsCompetitiveFrom {k : ℕ} {M : Type} [MetricSpace M] [Fintype M]
    (F : FracKServerAlg k M) (T : WTree V) (e : M ≃ T.Leaf) (C₀ : KServer.Config k M)
    (c : ℝ) : Prop :=
  F.state [] = indicatorState C₀ ∧
  (∀ l, IsFracState k (F.state l)) ∧
  (∀ l r, F.state (l ++ [r]) r = 1) ∧
  ∃ a : ℝ, ∀ ρ : List M, F.cost T e ρ ≤ c * KServer.offlineCost C₀ ρ + a

end PolylogKServer.Fractional


