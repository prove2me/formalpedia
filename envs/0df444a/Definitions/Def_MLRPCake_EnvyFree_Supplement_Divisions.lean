-- Prove2me | Definitions.Def_MLRPCake_EnvyFree_Supplement_Divisions
-- name    : MLRPCake_EnvyFree_Supplement_Divisions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T05:01:53.816258+00:00
-- url     : https://prove2.me/theorems/8b0c3713-cc3b-436c-b83a-bc4dad862516
-- title:
--   §2, pp. 6–7 — allocations in any order, cake divisions, envy-freeness, Pareto optimality, social, egalitarian and Nash welfare
-- statement:
--   This file extends the published model of contiguous cake division (instance $\langle [n], \{f_i\}_i\rangle$ on the cake $[0,1]$, values $v_i(a,b)=\int_a^b f_i$) by the objects of the paper's companion results.
--
--   1. **Allocations in any order.** An allocation is given by cut points $0=x_0\le x_1\le\dots\le x_n=1$ together with a permutation $\sigma$ of the agents: agent $i$ receives the interval $[x_{\sigma(i)}, x_{\sigma(i)+1}]$. Its own value is $v_i(I_i)=v_i(x_{\sigma(i)},x_{\sigma(i)+1})$. Empty pieces are allowed.
--   2. **Envy-freeness.** $v_i(I_i)\ge v_i(I_j)$ for all agents $i,j$.
--   3. **Cake divisions.** Each agent $i$ receives a bundle $D_i$, a finite union of closed intervals in $[0,1]$; distinct bundles overlap only in a null set (shared endpoints), and the bundles cover $[0,1]$. The value of a bundle is $v_i(D_i)=\int_{D_i} f_i$.
--   4. **Pareto optimality.** A value profile $(u_1,\dots,u_n)$ is Pareto optimal if no cake division $D$ satisfies $v_i(D_i)\ge u_i$ for all $i$ with strict inequality for some agent.
--   5. **Welfare.** For an allocation $I$,
--   $$\mathrm{SW}(I)=\sum_{i=1}^n v_i(I_i),\qquad \mathrm{EW}(I)=\min_{i} v_i(I_i),\qquad \mathrm{NSW}(I)=\Big(\prod_{i=1}^n v_i(I_i)\Big)^{1/n}.$$
--
--   These objects are used by Lemma 5, Theorem 2, Lemma 7 and Theorems 3–5.
--
--   **Formalization Note** Agents are $0,\dots,n-1$ (agent $i$ is the paper's agent $i+1$). The egalitarian welfare is the infimum over the finite index set, used only for $n\ge 1$; the Nash welfare uses the real power $1/n$ of a nonnegative product.
-- source:
--   Barman & Rathi, Fair Cake Division Under Monotone Likelihood Ratios, arXiv:2006.00481v3, pp. 6–7, §2 (Allocations and Cake Divisions; Envy-Freeness; Pareto Optimality; Social, Egalitarian and Nash Social Welfare)

import Mathlib
import Definitions.Def_MLRPCake_EnvyFree_Model

namespace MLRPCake.EnvyFree.Supplement
open MeasureTheory MLRPCake.EnvyFree

variable {n : ℕ}

/-- §2, p. 6: an allocation in which the pieces may be assigned to the agents in any order.
The cut points `0 = x 0 ≤ x 1 ≤ … ≤ x n = 1` are those of the published `IsAllocation`; the
permutation `σ` assigns the `(σ i)`-th interval `[x (σ i), x (σ i + 1)]` (0-based) to agent `i`.
This is agent `i`'s value for its own piece. -/
noncomputable def pieceVal (f : Fin n → ℝ → ℝ) (x : ℕ → ℝ) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    ℝ :=
  val f i (x (σ i)) (x ((σ i : ℕ) + 1))

/-- §2, p. 6: envy-freeness of the allocation `(x, σ)`: every agent `i` values its own piece at
least as much as the piece of any other agent `j`. -/
def IsEnvyFree (f : Fin n → ℝ → ℝ) (x : ℕ → ℝ) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j : Fin n, val f i (x (σ j)) (x ((σ j : ℕ) + 1)) ≤ pieceVal f x σ i

/-- A finite union of closed intervals contained in the cake `[0,1]` (a bundle of a cake
division, §2, p. 6). Empty and degenerate intervals are allowed. -/
def IsFiniteIntervalUnion (S : Set ℝ) : Prop :=
  ∃ (m : ℕ) (a b : Fin m → ℝ), (∀ k, 0 ≤ a k ∧ b k ≤ 1) ∧ S = ⋃ k, Set.Icc (a k) (b k)

/-- §2, p. 6: a cake division `D = {D_1, …, D_n}`: agent `i` receives a finite collection of
intervals `D i`; the bundles are pairwise disjoint (up to the endpoints shared by adjacent
intervals, which carry no value by non-atomicity, p. 5) and their union is the whole cake. -/
def IsCakeDivision (D : Fin n → Set ℝ) : Prop :=
  (∀ i, IsFiniteIntervalUnion (D i)) ∧ (∀ i j, i ≠ j → volume (D i ∩ D j) = 0) ∧
    (⋃ i, D i) = Set.Icc (0:ℝ) 1

/-- Agent `i`'s value `v_i(S) = ∫_S f_i` for a bundle `S ⊆ [0,1]`. -/
noncomputable def bundleVal (f : Fin n → ℝ → ℝ) (i : Fin n) (S : Set ℝ) : ℝ :=
  ∫ t in S, f i t

/-- §2, p. 6: a value profile `u` (agent `i` obtains `u i`) is Pareto optimal over the set of all
cake divisions: no cake division `D` gives every agent at least `u i` and some agent strictly
more. -/
def ParetoOptimal (f : Fin n → ℝ → ℝ) (u : Fin n → ℝ) : Prop :=
  ¬ ∃ D : Fin n → Set ℝ, IsCakeDivision D ∧ (∀ i, u i ≤ bundleVal f i (D i)) ∧
    ∃ k, u k < bundleVal f k (D k)

/-- §2, p. 6: social welfare `SW(I) = ∑_i v_i(I_i)` of the allocation `(x, σ)`. -/
noncomputable def SW (f : Fin n → ℝ → ℝ) (x : ℕ → ℝ) (σ : Equiv.Perm (Fin n)) : ℝ :=
  ∑ i, pieceVal f x σ i

/-- §2, p. 6: egalitarian welfare `EW(I) = min_i v_i(I_i)` of the allocation `(x, σ)` (a minimum
over the finite index set `Fin n`; used only with `n ≥ 1`). -/
noncomputable def EW (f : Fin n → ℝ → ℝ) (x : ℕ → ℝ) (σ : Equiv.Perm (Fin n)) : ℝ :=
  ⨅ i, pieceVal f x σ i

/-- §2, pp. 6–7: Nash social welfare `NSW(I) = (∏_i v_i(I_i))^{1/n}` of the allocation
`(x, σ)`. -/
noncomputable def NSW (f : Fin n → ℝ → ℝ) (x : ℕ → ℝ) (σ : Equiv.Perm (Fin n)) : ℝ :=
  (∏ i, pieceVal f x σ i) ^ ((1:ℝ) / n)

end MLRPCake.EnvyFree.Supplement


