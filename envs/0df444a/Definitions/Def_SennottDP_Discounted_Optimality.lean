-- Prove2me | Definitions.Def_SennottDP_Discounted_Optimality
-- name    : SennottDP_Discounted_Optimality
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T06:54:45.776601+00:00
-- url     : https://prove2.me/theorems/41863107-2821-46f9-945f-52553e651d3d
-- title:
--   The discount optimality operator, the sets $B_i(\alpha)$ and limit points of stationary policies
-- statement:
--   For $W : S \to [0,\infty]$, the **discount optimality operator** is
--   $$(TW)(i) = \min_{a \in A_i} \Big\{ C(i,a) + \alpha \sum_j P_{ij}(a) W(j) \Big\}, \qquad i \in S,$$
--   a minimum over the finite set $A_i$. A stationary policy $f$ **realizes** the minimum if $f(i)$ attains it in every state $i$. The **discount optimality equation** (4.9) is $W = TW$; with $W = V_\alpha$ the quantity in braces is the auxiliary function $U_\alpha(i,a) = C(i,a) + \alpha \sum_j P_{ij}(a) V_\alpha(j)$ of (4.8), and
--   $$B_i(\alpha) = \{ b \in A_i : U_\alpha(i,b) = \min_a U_\alpha(i,a) \}.$$
--
--   A policy $\theta$ is **concentrated on the optimal actions** if (i) for every initial state $i$ the distribution $\theta(\cdot \mid i)$ is concentrated on $B_i(\alpha)$, and (ii) for $n \ge 1$, whenever $h_n$ is a history of positive probability under $\theta$ (from its initial state) with current state $i_n$, the distribution $\theta(\cdot \mid h_n)$ is concentrated on $B_{i_n}(\alpha)$.
--
--   A stationary policy $f$ is a **limit point** of a sequence $(f_r)$ of stationary policies if there is a subsequence $f_{r_k}$ such that for each state $i$, $f_{r_k}(i) = f(i)$ for all sufficiently large $k$ (how large may depend on $i$).
--
--   **Formalization Note** "Concentrated on" is encoded as: every action of nonzero probability belongs to the set. A history of positive probability is one whose probability under the joint law of the preceding definition is nonzero.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 62 (4.6), (4.8), $B_i(\alpha)$; p. 63 (4.9); p. 67, Proposition 4.4.1 (i)–(ii); pp. 288–289, Definition B.1

import Mathlib
import Definitions.Def_SennottDP_Discounted_Criteria

open scoped ENNReal NNReal

namespace SennottDP.Discounted

variable {S : Type} [Countable S] {Act : Type}

/-- The one-step quantity `C(i,a) + α ∑_j P_{ij}(a) W(j)` for a function `W : S → [0, ∞]`.
With `W = V_α` it is the auxiliary function `U_α(i,a)` of (4.8), p. 62; with `W = v_{α,n-1}` it is
`u_{α,n}(i,a)` of (3.1), p. 36. -/
noncomputable def bellmanQ (M : MDC S Act) (α : ℝ≥0) (W : S → ℝ≥0∞) (i : S) (a : Act) : ℝ≥0∞ :=
  (M.C i a : ℝ≥0∞) + (α : ℝ≥0∞) * ∑' j, M.P i a j * W j

/-- The right side of the discount optimality equation (4.9), p. 63:
`min_{a ∈ A_i} { C(i,a) + α ∑_j P_{ij}(a) W(j) }` (a minimum over the finite nonempty set `A_i`). -/
noncomputable def bellman (M : MDC S Act) (α : ℝ≥0) (W : S → ℝ≥0∞) (i : S) : ℝ≥0∞ :=
  (M.A i).inf' (M.A_nonempty i) (bellmanQ M α W i)

/-- A stationary policy `f` realizes the minimum in `min_a { C(i,a) + α ∑_j P_{ij}(a) W(j) }`:
for each state `i`, `f(i)` is an action achieving the minimum (Sennott (1999), p. 62, Corollary
4.1.3; p. 63, Theorem 4.1.4 with `W = V_α`; (3.2), p. 37, with `W = v_{α,n-1}`). -/
def Realizes (M : MDC S Act) (f : StationaryPolicy M) (α : ℝ≥0) (W : S → ℝ≥0∞) : Prop :=
  ∀ i, bellmanQ M α W i (f.1 i) = bellman M α W i

open Classical in
/-- Sennott (1999), p. 62: `B_i(α) = {b ∈ A_i | U_α(i,b) = min_a U_α(i,a)}`, where
`U_α(i,a) = C(i,a) + α ∑_j P_{ij}(a) V_α(j)` is (4.8). -/
noncomputable def optActions (M : MDC S Act) (α : ℝ≥0) (i : S) : Finset Act :=
  (M.A i).filter (fun b => bellmanQ M α (valueFn M α) i b = bellman M α (valueFn M α) i)

/-- Sennott (1999), Proposition 4.4.1, p. 67, conditions (i)–(ii) on a policy `θ`:
(i) for every initial state `i`, the distribution `θ(a | i)` is concentrated on `B_i(α)`;
(ii) for `n ≥ 1`, if `h_n` is a history under `θ` (a history of positive probability under `θ`
from its initial state `i_0`) with current state `i_n`, then `θ(a | h_n)` is concentrated on
`B_{i_n}(α)`. -/
def ConcentratedOnOptActions (M : MDC S Act) (α : ℝ≥0) (θ : Policy M) : Prop :=
  (∀ (i : S) (a : Act), θ.dist 0 (fun _ => i) (fun k => Fin.elim0 k) a ≠ 0 →
      a ∈ optActions M α i) ∧
    (∀ n : ℕ, 1 ≤ n → ∀ (s : Fin (n + 1) → S) (as : Fin n → Act),
      histProb M θ (s 0) n s as ≠ 0 →
        ∀ a : Act, θ.dist n s as a ≠ 0 → a ∈ optActions M α (s (Fin.last n)))

/-- Sennott (1999), Definition B.1, pp. 288–289: a stationary policy `f` is a limit point of the
sequence of stationary policies `(f_r)` if there is a subsequence `f_{r_k}` such that, for each
state `i`, `f_{r_k}(i) = f(i)` for all sufficiently large `k` (how large may depend on `i`). -/
def IsLimitPoint (M : MDC S Act) (fs : ℕ → StationaryPolicy M) (f : StationaryPolicy M) : Prop :=
  ∃ r : ℕ → ℕ, StrictMono r ∧ ∀ i, ∀ᶠ k in Filter.atTop, (fs (r k)).1 i = f.1 i

end SennottDP.Discounted


