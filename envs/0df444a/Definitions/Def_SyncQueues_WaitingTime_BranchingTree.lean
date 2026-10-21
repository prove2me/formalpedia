-- Prove2me | Definitions.Def_SyncQueues_WaitingTime_BranchingTree
-- name    : SyncQueues_WaitingTime_BranchingTree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:47.747761+00:00
-- url     : https://prove2.me/theorems/497183ce-75b2-4617-9c9a-ee08dd60c64c
-- title:
--   (3.7)–(3.9), pp. 14–15, and §6, p. 21 — the m-ary weighted branching tree, its generation maxima U_r and the endogenous solution W of the high-order Lindley equation
-- statement:
--   This file fixes the limit object of the mission: the weighted branching tree in which every node has exactly $m$ children, and the endogenous solution (3.9) of the high-order Lindley equation (3.3).
--
--   1. **Labels.** Nodes are finite words $\mathbf j=(j_1,\dots,j_r)$ over $\{1,\dots,m\}$; the empty word $\emptyset$ is the root, $\mathbf j|t=(j_1,\dots,j_t)$ is the truncation at level $t$, and $A_r$ is the set of the $m^r$ words of length $r$.
--   2. **Edge marks.** A probability space $(\Omega',\mathcal F',P')$ carries pairs $(\chi_{\mathbf j},\tau_{\mathbf j})$, one per label, that are i.i.d. over labels, with $\chi_{\mathbf j}\sim B$ and $\tau_{\mathbf j}\sim\mathrm{Exp}(\lambda^*)$ independent of each other. Write $X_{\mathbf j}=\chi_{\mathbf j}-\tau_{\mathbf j}$.
--   3. **Path sums and generation maxima.** $S_\emptyset=0$ and
--   $$S_{\mathbf j}=X_{\mathbf j|1}+X_{\mathbf j|2}+\dots+X_{\mathbf j},\qquad U_r=\max_{\mathbf j\in A_r}S_{\mathbf j},\qquad \bigvee_{r=0}^k U_r .$$
--   4. **The endogenous solution (3.9).**
--   $$W=\bigvee_{r=0}^\infty\ \bigvee_{\mathbf j\in A_r} S_{\mathbf j}.$$
--
--   $W$ is the limit in distribution of the stationary waiting time in the main theorem; for $m=1$ it is the supremum $\max_{k\ge0}S_k$ of a random walk, the classical Lindley representation of the M/G/1 waiting time.
--
--   **Formalization Note** Labels are `List (Fin m)`, written root-first; the edge into $\mathbf j$ carries the marks of $\mathbf j$ itself. The marks are indexed by all labels including the root, whose marks are never used. $W$ is a real supremum over all labels, which is the true supremum only when the path sums are bounded above; every statement that uses it asserts or assumes that boundedness. $U_r$ is a maximum over a finite nonempty set when $m\ge1$.
-- source:
--   Olvera-Cravioto & Ruiz-Lacedelli, arXiv:1501.00186v3, pp. 14–15, §3.2, (3.7)–(3.9); p. 21, §6 (definition of $U_r$, $\tilde U_r$)

import Mathlib

namespace SyncQueues.WaitingTime

open MeasureTheory ProbabilityTheory

/-! ### The `m`-ary weighted branching tree and the endogenous solution (3.9)

Olvera-Cravioto & Ruiz-Lacedelli, arXiv:1501.00186v3, §3.2, (3.7)–(3.9), pp. 14–15, and §6, p. 21.
Labels are `List (Fin m)`, written root-first: `[]` is the root `∅`, and `j ++ [i]` is the `i`-th
child of `j`. With every node having exactly `m` children, the set `A_r` of the page is the set of
words of length `r`. -/

/-- The edge marks of the tree: `(χ_j, τ_j)` for `j ∈ U`, i.i.d. over labels, with `χ_j ∼ B` and
`τ_j ∼ Exp(λ*)` independent (`B.prod (expMeasure lamStar)` is the law of the pair). -/
def IsLimitTree {m : ℕ} {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') (B : Measure ℝ)
    (lamStar : ℝ) (χ τ : List (Fin m) → Ω' → ℝ) : Prop :=
  (∀ j, Measurable (χ j) ∧ Measurable (τ j)) ∧
  iIndepFun (fun j ω => (χ j ω, τ j ω)) P' ∧
  ∀ j, P'.map (fun ω => (χ j ω, τ j ω)) = B.prod (expMeasure lamStar)

/-- The path sum `S_j = X_{j|1} + X_{j|2} + ⋯ + X_j` with `X_i = χ_i − τ_i`; the edge of depth
`r + 1` on the path to `j` carries the marks of the prefix `j.take (r + 1)`. `S_∅ = 0`. -/
def pathSum {m : ℕ} {Ω' : Type*} (χ τ : List (Fin m) → Ω' → ℝ) (j : List (Fin m)) (ω : Ω') : ℝ :=
  ∑ r ∈ Finset.range j.length, (χ (j.take (r + 1)) ω - τ (j.take (r + 1)) ω)

/-- `U_r = max_{j ∈ A_r} S_j`, the maximum over the `m^r` words of length `r` (`U_0 = S_∅ = 0`).
For `0 < m` the index type is finite and nonempty, so this real supremum is a maximum. -/
noncomputable def genMax {m : ℕ} {Ω' : Type*} (χ τ : List (Fin m) → Ω' → ℝ) (r : ℕ) (ω : Ω') : ℝ :=
  ⨆ v : Fin r → Fin m, pathSum χ τ (List.ofFn v) ω

/-- `⋁_{r=0}^{k} U_r`, a maximum over the finite range `0, …, k`. -/
noncomputable def genMaxUpTo {m : ℕ} {Ω' : Type*} (χ τ : List (Fin m) → Ω' → ℝ) (k : ℕ)
    (ω : Ω') : ℝ :=
  (Finset.range (k + 1)).sup' Finset.nonempty_range_add_one (fun r => genMax χ τ r ω)

/-- (3.9): the endogenous solution `W = ⋁_{r ≥ 0} ⋁_{j ∈ A_r} S_j` of the high-order Lindley
equation (3.3). This is a real supremum over all labels: it is the true supremum exactly when the
path sums are bounded above, and every statement that uses it asserts or assumes that boundedness. -/
noncomputable def endoW {m : ℕ} {Ω' : Type*} (χ τ : List (Fin m) → Ω' → ℝ) (ω : Ω') : ℝ :=
  ⨆ j : List (Fin m), pathSum χ τ j ω

end SyncQueues.WaitingTime


