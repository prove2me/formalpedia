-- Prove2me | Definitions.Def_FullForesight_Deterministic_Model
-- name    : FullForesight_Deterministic_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-13T15:07:12.173546+00:00
-- url     : https://prove2.me/theorems/b79d28a2-9748-4d0a-9a5c-fe72420e38b2
-- title:
--   Deterministic clairvoyant consistent submodular maximization: solution trajectories, validity, $C$-consistency, $\alpha$-approximation
-- statement:
--   This file fixes what a **deterministic** clairvoyant algorithm is in the model of consistent submodular maximization with full foresight. It is the deterministic counterpart of the randomized model already published for this paper, and reuses its notation.
--
--   **Setting.** Elements $0, 1, \dots, n-1$ arrive in this order, and $X_t = \{i : i < t\}$ is the set of elements that have arrived by time $t \in \{0, \dots, n\}$. An instance is a cardinality bound $k \ge 1$ and a nonnegative monotone submodular function $f$ on subsets of the $n$ elements, and
--   $$f(\mathrm{OPT}_t) = \max\{f(S) : S \subseteq X_t,\ |S| \le k\}.$$
--   A clairvoyant algorithm knows the whole instance in advance.
--
--   **Trajectories.** A deterministic clairvoyant algorithm, run on one instance, produces one solution trajectory $\mathrm{ALG}_0, \mathrm{ALG}_1, \dots, \mathrm{ALG}_n$ of subsets of the elements. The file defines three properties of a trajectory:
--
--   1. **Valid** for the bound $k$: $\mathrm{ALG}_0 = \emptyset$, and $\mathrm{ALG}_t \subseteq X_t$, $|\mathrm{ALG}_t| \le k$ for every $t$.
--   2. **$C$-consistent**: $|\mathrm{ALG}_t \,\triangle\, \mathrm{ALG}_{t-1}| \le C$ for every $t = 1, \dots, n$, where $A \triangle B = (A \setminus B) \cup (B \setminus A)$.
--   3. **$\alpha$-approximate** for $f$ and $k$:
--   $$f(\mathrm{ALG}_t) \ge \alpha\, f(\mathrm{OPT}_t) \qquad (t = 0, \dots, n).$$
--
--   These are the notions used to state Main Result 2 and the deterministic results of Section 3 of the paper.
--
--   **Formalization Note** The trajectory is a function `A : Fin (n+1) → Finset (Fin n)`. The three predicates `IsValid`, `IsConsistent`, `IsApprox` are exactly the predicates `TrajLaw.Valid`, `TrajLaw.Consistent`, `TrajLaw.Approx` of the randomized model applied to the law that puts probability one on `A`. Since a clairvoyant algorithm with unrestricted computation is a per-instance choice of trajectory, "there is a deterministic algorithm" is stated as "every instance has a trajectory", and "no deterministic algorithm" as "some instance has no trajectory".
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission (sha256 ef7bb5aa…56df), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/862.pdf, p. 1 (§1.1, the model), p. 3 (Main Result 2), pp. 10–11 (§3, Theorems 3 and 4)

import Mathlib
import Definitions.Def_FullForesight_Randomized_Model

/-!
# Deterministic clairvoyant consistent submodular maximization (§1.1, §3)

Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, *Consistent
Submodular Maximization with Full Foresight*, STOC 2027 submission, p. 1 (§1.1), p. 3
(Main Result 2), pp. 10–11 (§3, Theorems 3 and 4).

The model is that of `Definitions.Def_FullForesight_Randomized_Model` (arrivals `Fin n` in index
order, `arrived n t = X_t`, instances `IsInstance k f`, `optVal f k t = f(OPT_t)`), with one
change: a deterministic clairvoyant algorithm, run on one instance, is a single solution
trajectory `A : Fin (n+1) → Finset (Fin n)` (`A t = ALG_t`) instead of a probability law of
trajectories.

* `IsValid A k`: `A 0 = ∅`, `A t ⊆ X_t`, `|A t| ≤ k`.
* `IsConsistent A C`: `|A t △ A (t−1)| ≤ C` for `t = 1, …, n`.
* `IsApprox A f k α`: `f(A t) ≥ α · optVal f k t` at every time `t = 0, …, n`.

These are the predicates `TrajLaw.Valid`, `TrajLaw.Consistent`, `TrajLaw.Approx` of the
randomized model for the law that puts probability one on `A`.
-/

namespace FullForesight.Deterministic

open FullForesight.Randomized

/-- Feasibility of a solution trajectory: `ALG_0 = ∅`, `ALG_t ⊆ X_t`, `|ALG_t| ≤ k`. -/
def IsValid {n : ℕ} (A : Fin (n + 1) → Finset (Fin n)) (k : ℕ) : Prop :=
  A 0 = ∅ ∧ ∀ t : Fin (n + 1), A t ⊆ arrived n t ∧ (A t).card ≤ k

/-- `C`-consistency of a solution trajectory: `|ALG_t △ ALG_{t−1}| ≤ C` for `t = 1, …, n`. -/
def IsConsistent {n : ℕ} (A : Fin (n + 1) → Finset (Fin n)) (C : ℝ) : Prop :=
  ∀ t : Fin n, (((A t.castSucc \ A t.succ) ∪ (A t.succ \ A t.castSucc)).card : ℝ) ≤ C

/-- `α`-approximation of a solution trajectory: `f(ALG_t) ≥ α f(OPT_t)` at every time
`t = 0, …, n`. -/
def IsApprox {n : ℕ} (A : Fin (n + 1) → Finset (Fin n)) (f : Finset (Fin n) → ℝ) (k : ℕ)
    (α : ℝ) : Prop :=
  ∀ t : Fin (n + 1), α * optVal f k t ≤ f (A t)

end FullForesight.Deterministic


