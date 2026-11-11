-- Prove2me | Definitions.Def_FullForesight_Randomized_AdditionRobust
-- name    : FullForesight_Randomized_AdditionRobust
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:16:23.922278+00:00
-- url     : https://prove2.me/theorems/a49972e6-cc1e-405d-9c2b-bde8d8ef72f2
-- title:
--   Clairvoyant addition-robust submodular maximization, $\alpha$-addition-robust distributions, LP (1) and payoffs $w_{i,j}$ (§2.3, Definition 2.1)
-- statement:
--   The **clairvoyant addition-robust problem** (§2.3).
--
--   1. An instance is a nonnegative monotone submodular $f$ on the finite subsets of a ground type, a finite set $V_{\mathrm{now}}$ of present elements, future elements $v_1, \dots, v_m$ that are pairwise distinct and not present (the ground set is partitioned into present and future elements) and arrive in this known order, and a budget $\kappa \in \mathbb N$.
--   2. $R_j = \{v_1, \dots, v_j\}$ for $j = 0, \dots, m$, with $R_0 = \emptyset$.
--   3. The benchmark at prefix $j$ is
--   $$f(O_j \cup R_j) = \max\{f(O \cup R_j) : O \subseteq V_{\mathrm{now}},\ |O| \le \kappa\}.$$
--   A family $O_0, \dots, O_m$ of **prefix optimizers** has $O_j \subseteq V_{\mathrm{now}}$, $|O_j| \le \kappa$ and $f(O_j \cup R_j)$ equal to that maximum.
--   4. (Definition 2.1) A random set $S \subseteq V_{\mathrm{now}}$ with $|S| \le \kappa$ surely is **$\alpha$-addition-robust** if
--   $$\mathbb E[f(S \cup R_j)] \ge \alpha\, f(O_j \cup R_j) \qquad (j = 0, \dots, m).$$
--   Its law is a probability distribution $\mu$ on the subsets of $V_{\mathrm{now}}$ giving positive mass only to sets of size at most $\kappa$.
--   5. For prefix optimizers $O$, **LP (1)** maximizes $\rho$ subject to $\sum_i \alpha_i f(O_i \cup R_j) \ge \rho\, f(O_j \cup R_j)$ for all $j$, $\alpha \in \Delta$ (the simplex on $\{0, \dots, m\}$) and $0 \le \rho \le 1$. Its value is $\rho^\star$, the supremum of the feasible $\rho$.
--   6. The **normalized payoffs** are $w_{i,j} = f(O_i \cup R_j)/f(O_j \cup R_j)$.
--
--   **Formalization Note** The ground type `X` is arbitrary with decidable equality and $f$ is defined on all of `Finset X`; a function given only on the subsets of $V_{\mathrm{now}} \cup \{v_1, \dots, v_m\}$ extends by $S \mapsto f(S \cap G)$ without losing monotonicity or submodularity. `prefixSet v j` is $R_j$, `benchmark` the maximum (a `Finset.sup'` over a family containing $\emptyset$), `IsRobustDist` Definition 2.1, `lpValue` is $\rho^\star$ (an `sSup` over a set that contains $0$ and is bounded by $1$), `payoff` is $w_{i,j}$. The simplex is Mathlib's `stdSimplex ℝ (Fin (m+1))`. `payoff` divides by $f(O_j \cup R_j)$, which is positive under Lemma 5's standing assumptions.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission (sha256 ef7bb5aa…), p. 7, §2.3 and Definition 2.1; p. 8, LP (1); p. 23, App. A.4

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_IsSubmodular
import Definitions.Def_SubsamplingSM_Offline_IsMonotoneSetFn

/-!
# Clairvoyant addition-robust submodular maximization (§2.3, Definition 2.1, LP (1))

Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, *Consistent
Submodular Maximization with Full Foresight*, STOC 2027 submission, p. 7 (§2.3, Definition 2.1),
p. 8 (LP (1)), p. 23 (Appendix A.4).

* An instance: a nonnegative monotone submodular `f : Finset X → ℝ`, present elements
  `Vnow : Finset X`, future elements `v 0, …, v (m−1)` (pairwise distinct, none of them present:
  the ground set is partitioned), arriving in index order, and a budget `κ`.
* `prefixSet v j = R_j = {v₁, …, v_j}` for `j = 0, …, m` (`R₀ = ∅`).
* `benchmark f Vnow v κ j = max {f(O ∪ R_j) : O ⊆ Vnow, |O| ≤ κ} = f(O_j ∪ R_j)`.
* `IsRobustDist f Vnow v κ α μ`: `μ` is a probability law on the subsets of `Vnow`, supported on
  sets of size `≤ κ`, with `E_{S∼μ}[f(S ∪ R_j)] ≥ α f(O_j ∪ R_j)` for all `j` (Definition 2.1).
* `IsMaximizerFamily f Vnow v κ O`: `O j ⊆ Vnow`, `|O j| ≤ κ`, `f(O j ∪ R_j)` maximal.
* `lpValue f v O = ρ⋆`: the optimal value of LP (1), the supremum of the feasible `ρ`.
* `payoff f v O i j = w_{i,j} = f(O_i ∪ R_j) / f(O_j ∪ R_j)`.
-/

namespace FullForesight.Randomized

variable {X : Type} [DecidableEq X]

/-- The standing assumptions of §2.3 on `(f, Vnow, v)`: `f ≥ 0` monotone submodular, the
future sequence `v` injective and disjoint from `Vnow`. -/
def IsARInstance {m : ℕ} (f : Finset X → ℝ) (Vnow : Finset X) (v : Fin m → X) : Prop :=
  (∀ S, 0 ≤ f S) ∧ SubsamplingSM.Offline.IsMonotoneSetFn f ∧
    SubsamplingSM.Offline.IsSubmodular f ∧ Function.Injective v ∧ ∀ i, v i ∉ Vnow

/-- `R_j = {v₁, …, v_j}`, `j = 0, …, m`. -/
def prefixSet {m : ℕ} (v : Fin m → X) (j : ℕ) : Finset X :=
  (Finset.univ.filter (fun i : Fin m => (i : ℕ) < j)).image v

/-- `f(O_j ∪ R_j) = max {f(O ∪ R_j) : O ⊆ Vnow, |O| ≤ κ}`. -/
noncomputable def benchmark {m : ℕ} (f : Finset X → ℝ) (Vnow : Finset X) (v : Fin m → X)
    (κ j : ℕ) : ℝ :=
  (Vnow.powerset.filter (fun O => O.card ≤ κ)).sup' ⟨∅, by simp⟩
    (fun O => f (O ∪ prefixSet v j))

/-- `μ` is an `α`-addition-robust distribution (Definition 2.1): a probability law on the subsets
of `Vnow`, supported on sets of size at most `κ`, with
`E_{S∼μ}[f(S ∪ R_j)] ≥ α f(O_j ∪ R_j)` for `j = 0, …, m`. -/
def IsRobustDist {m : ℕ} (f : Finset X → ℝ) (Vnow : Finset X) (v : Fin m → X) (κ : ℕ)
    (α : ℝ) (μ : Finset X → ℝ) : Prop :=
  (∀ S ∈ Vnow.powerset, 0 ≤ μ S) ∧ (∑ S ∈ Vnow.powerset, μ S) = 1 ∧
    (∀ S ∈ Vnow.powerset, 0 < μ S → S.card ≤ κ) ∧
    ∀ j : Fin (m + 1),
      α * benchmark f Vnow v κ j ≤ ∑ S ∈ Vnow.powerset, μ S * f (S ∪ prefixSet v j)

/-- `O_0, …, O_m` is a family of prefix optimizers: `O_j ∈ argmax_{O ⊆ Vnow, |O| ≤ κ} f(O ∪ R_j)`. -/
def IsMaximizerFamily {m : ℕ} (f : Finset X → ℝ) (Vnow : Finset X) (v : Fin m → X) (κ : ℕ)
    (O : Fin (m + 1) → Finset X) : Prop :=
  ∀ j : Fin (m + 1), O j ⊆ Vnow ∧ (O j).card ≤ κ ∧
    f (O j ∪ prefixSet v j) = benchmark f Vnow v κ j

/-- `ρ⋆`, the value of LP (1): the supremum of the `ρ ∈ [0, 1]` for which some `α` in the
simplex `Δ` has `Σ_i α_i f(O_i ∪ R_j) ≥ ρ f(O_j ∪ R_j)` for all `j`. -/
noncomputable def lpValue {m : ℕ} (f : Finset X → ℝ) (v : Fin m → X)
    (O : Fin (m + 1) → Finset X) : ℝ :=
  sSup {ρ : ℝ | 0 ≤ ρ ∧ ρ ≤ 1 ∧ ∃ a ∈ stdSimplex ℝ (Fin (m + 1)),
    ∀ j : Fin (m + 1), ρ * f (O j ∪ prefixSet v j) ≤ ∑ i, a i * f (O i ∪ prefixSet v j)}

/-- The normalized payoffs `w_{i,j} = f(O_i ∪ R_j) / f(O_j ∪ R_j)`. -/
noncomputable def payoff {m : ℕ} (f : Finset X → ℝ) (v : Fin m → X)
    (O : Fin (m + 1) → Finset X) (i j : Fin (m + 1)) : ℝ :=
  f (O i ∪ prefixSet v j) / f (O j ∪ prefixSet v j)

end FullForesight.Randomized


