-- Prove2me | Definitions.Def_FullForesight_Randomized_Model
-- name    : FullForesight_Randomized_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:16:22.480988+00:00
-- url     : https://prove2.me/theorems/4e0bab6b-923f-43dc-9d7a-733ef2f04561
-- title:
--   Clairvoyant consistent submodular maximization: instances, $f(\mathrm{OPT}_t)$, trajectory laws, consistency, approximation (§1.1)
-- statement:
--   The model of §1.1. Elements $x_1, \dots, x_n$ arrive one at a time and the algorithm knows the whole arrival sequence in advance (it is **clairvoyant**).
--
--   1. The arriving elements are the indices $0, 1, \dots, n-1$ of $\mathrm{Fin}\,n$, arriving in index order, and $X_t = \{i : i < t\}$ is the set of the first $t$ arrivals, $t = 0, \dots, n$.
--   2. An **instance** is an integer cardinality bound $k \ge 1$ and a set function $f$ on the subsets of $\mathrm{Fin}\,n$ that is nonnegative, monotone ($A \subseteq B \Rightarrow f(A) \le f(B)$) and submodular ($f(B \cup \{e\}) - f(B) \le f(A \cup \{e\}) - f(A)$ for $A \subseteq B$, $e \notin B$). No normalization $f(\emptyset) = 0$ is assumed.
--   3. The optimum at time $t$ is
--   $$f(\mathrm{OPT}_t) = \max\{f(S) : S \subseteq X_t,\ |S| \le k\}.$$
--   4. A randomized clairvoyant algorithm, run on one instance, produces a random **trajectory** $(\mathrm{ALG}_0, \dots, \mathrm{ALG}_n)$ of sets. Its law is a probability distribution $w$ on the finite set of trajectories $A : \{0, \dots, n\} \to 2^{\mathrm{Fin}\,n}$, and $\mathbb E[f(\mathrm{ALG}_t)] = \sum_A w(A) f(A_t)$.
--   5. The law is **valid** if every trajectory of positive probability has $A_0 = \emptyset$, $A_t \subseteq X_t$ and $|A_t| \le k$ for every $t$.
--   6. It is **$C$-consistent** ($C \in \mathbb R$) if every trajectory of positive probability has $|A_t \triangle A_{t-1}| \le C$ for $t = 1, \dots, n$, where $A \triangle B = (A \setminus B) \cup (B \setminus A)$.
--   7. It is an **$\alpha$-approximation** if $\mathbb E[f(\mathrm{ALG}_t)] \ge \alpha\, f(\mathrm{OPT}_t)$ at every time $t = 0, \dots, n$: the expectation is taken at each fixed time, not simultaneously over times for one realization.
--
--   Because the algorithm sees the whole instance and its computation is unrestricted, "an algorithm with property $P$ exists" is exactly "every instance has a valid law with property $P$". Conversely, every randomized algorithm induces such a law on each instance, so a statement about all valid laws covers all algorithms.
--
--   **Formalization Note** `arrived n t` is $X_t$; `optVal f k t` is $f(\mathrm{OPT}_t)$, a `Finset.sup'` over the nonempty family of feasible sets (it contains $\emptyset$). `TrajLaw n` holds the weights `w`, nonnegative and summing to $1$ over the trajectories `Fin (n+1) → Finset (Fin n)`. `Consistent C` compares `A t.castSucc` and `A t.succ` for `t : Fin n`, i.e. the steps $t = 1, \dots, n$. Monotonicity and submodularity are the published `SubsamplingSM.Offline.IsMonotoneSetFn` and `SubsamplingSM.Offline.IsSubmodular`, which bundle nothing else.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission (sha256 ef7bb5aa…), p. 1, §1.1

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_IsSubmodular
import Definitions.Def_SubsamplingSM_Offline_IsMonotoneSetFn

/-!
# Clairvoyant consistent submodular maximization (§1.1)

Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, *Consistent
Submodular Maximization with Full Foresight*, STOC 2027 submission, p. 1, §1.1.

* The `n` arriving elements are `Fin n`, arriving in index order; `arrived n t = X_t` is the set
  of the first `t` of them (`t = 0, …, n`).
* An instance is a cardinality bound `k ≥ 1` and a nonnegative monotone submodular
  `f : Finset (Fin n) → ℝ` (no normalization `f ∅ = 0`).
* `optVal f k t = max {f S : S ⊆ X_t, |S| ≤ k} = f(OPT_t)`.
* A randomized clairvoyant algorithm, run on one instance, is a probability law of solution
  trajectories `A : Fin (n+1) → Finset (Fin n)` (`A t = ALG_t`), given by nonnegative weights
  summing to one on the finite set of trajectories.
* `Valid`: every trajectory of positive probability has `A 0 = ∅`, `A t ⊆ X_t`, `|A t| ≤ k`.
* `Consistent C`: every trajectory of positive probability has `|A t △ A (t−1)| ≤ C`,
  `t = 1, …, n`.
* `Approx f k α`: `E[f(A t)] ≥ α · optVal f k t` at every time `t = 0, …, n`.
-/

namespace FullForesight.Randomized

/-- `X_t = {x₁, …, x_t}`: the elements of `Fin n` with index `< t`. -/
def arrived (n t : ℕ) : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => (i : ℕ) < t)

/-- An instance of clairvoyant monotone submodular maximization under a cardinality
constraint `k`: `k ≥ 1` and `f ≥ 0` monotone and submodular (diminishing returns). -/
def IsInstance {n : ℕ} (k : ℕ) (f : Finset (Fin n) → ℝ) : Prop :=
  1 ≤ k ∧ (∀ S, 0 ≤ f S) ∧ SubsamplingSM.Offline.IsMonotoneSetFn f ∧
    SubsamplingSM.Offline.IsSubmodular f

/-- `f(OPT_t) = max {f S : S ⊆ X_t, |S| ≤ k}` (the family contains `∅`, so it is nonempty). -/
noncomputable def optVal {n : ℕ} (f : Finset (Fin n) → ℝ) (k t : ℕ) : ℝ :=
  ((Finset.univ : Finset (Finset (Fin n))).filter
      (fun S => S ⊆ arrived n t ∧ S.card ≤ k)).sup'
    ⟨∅, by simp⟩ f

/-- A probability law on solution trajectories `A : Fin (n+1) → Finset (Fin n)`,
`A t = ALG_t`. -/
structure TrajLaw (n : ℕ) where
  /-- the probability of each trajectory -/
  w : (Fin (n + 1) → Finset (Fin n)) → ℝ
  nonneg : ∀ A, 0 ≤ w A
  sum_eq_one : ∑ A, w A = 1

namespace TrajLaw

variable {n : ℕ}

/-- `E[f(ALG_t)]`. -/
def expect (L : TrajLaw n) (f : Finset (Fin n) → ℝ) (t : Fin (n + 1)) : ℝ :=
  ∑ A, L.w A * f (A t)

/-- Feasibility on every realization: `ALG_0 = ∅`, `ALG_t ⊆ X_t`, `|ALG_t| ≤ k`. -/
def Valid (L : TrajLaw n) (k : ℕ) : Prop :=
  ∀ A, 0 < L.w A → A 0 = ∅ ∧ ∀ t : Fin (n + 1), A t ⊆ arrived n t ∧ (A t).card ≤ k

/-- `C`-consistency on every realization: `|ALG_t △ ALG_{t−1}| ≤ C` for `t = 1, …, n`. -/
def Consistent (L : TrajLaw n) (C : ℝ) : Prop :=
  ∀ A, 0 < L.w A → ∀ t : Fin n,
    (((A t.castSucc \ A t.succ) ∪ (A t.succ \ A t.castSucc)).card : ℝ) ≤ C

/-- `α`-approximation: `E[f(ALG_t)] ≥ α f(OPT_t)` at every time `t = 0, …, n`. -/
def Approx (L : TrajLaw n) (f : Finset (Fin n) → ℝ) (k : ℕ) (α : ℝ) : Prop :=
  ∀ t : Fin (n + 1), α * optVal f k t ≤ L.expect f t

end TrajLaw

end FullForesight.Randomized


