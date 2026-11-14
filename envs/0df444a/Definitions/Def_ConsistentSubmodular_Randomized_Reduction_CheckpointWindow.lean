-- Prove2me | Definitions.Def_ConsistentSubmodular_Randomized_Reduction_CheckpointWindow
-- name    : ConsistentSubmodular_Randomized_Reduction_CheckpointWindow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:07:41.553719+00:00
-- url     : https://prove2.me/theorems/9e1d3df8-2ced-4b1b-b7a6-06c26d893aab
-- title:
--   Checkpoint window instance: future prefixes and optimal cores at a checkpoint
-- statement:
--   Let $f$ be an objective on a stream of $n$ elements (element $e\in\{0,\dots,n-1\}$ is the paper's $x_{e+1}$), $\kappa$ a core budget and $c$ a checkpoint time.
--
--   - `future n c j` is the future prefix $\{x_{c+1},\dots,x_{c+j}\}$, i.e. the set of elements $e$ with $c\le e<c+j$.
--   - `optimalCore f P R κ` is a fixed (chosen by the axiom of choice) set $O\subseteq P$ with $|O|\le\kappa$ that maximizes $f(O\cup R)$ among all such sets; its existence is proved by maximizing over the finitely many admissible subsets.
--   - `window f κ c` is the instance of the clairvoyant addition-robust problem at the checkpoint $c$, a window instance with: objective $f$; present elements $V_{\rm now}=X_c=\{x_1,\dots,x_c\}$; core budget $\kappa$; stages $0,\dots,n-c$; arrivals $R_j=$ `future n c j` $=\{x_{c+1},\dots,x_{c+j}\}$ (one future element per stage); and candidate $O_j=$ `optimalCore f X_c R_j κ`. The window axioms (nested arrivals starting at $\emptyset$, disjoint from the present set, candidates contained in the present set, of size at most $\kappa$ and optimal) are verified in the definition.
--
--   The file also proves the existence and defining property of the optimal core, and that the window has one future element per stage (`SingleArrivals`).
--
--   This is the instance on which the addition-robust routine is invoked at each checkpoint in the reduction from clairvoyant addition robustness to consistency (Lemma 1, Appendix A.3).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/Reduction/CheckpointWindow.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Checkpoints

variable {n : ℕ}

/-- The future prefix `{x_{c+1}, ..., x_{c+j}}` after time `c`. -/
def future (n c j : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun e : Fin n => c ≤ e.val ∧ e.val < c + j)

theorem exists_optimalCore (f : Objective n) (P R : Finset (Fin n)) (κ : ℕ) :
    ∃ O, O ⊆ P ∧ O.card ≤ κ ∧
      ∀ O', O' ⊆ P → O'.card ≤ κ → f.value (O' ∪ R) ≤ f.value (O ∪ R) := by
  classical
  obtain ⟨O, hO, hmax⟩ := (P.powerset.filter (fun O => O.card ≤ κ)).exists_max_image
    (fun O => f.value (O ∪ R)) ⟨∅, by simp⟩
  simp only [Finset.mem_filter, Finset.mem_powerset] at hO hmax
  exact ⟨O, hO.1, hO.2, fun O' h1 h2 => hmax O' ⟨h1, h2⟩⟩

/-- A set of at most `κ` elements of `P` maximizing `f(O ∪ R)`. -/
def optimalCore (f : Objective n) (P R : Finset (Fin n)) (κ : ℕ) : Finset (Fin n) :=
  Classical.choose (exists_optimalCore f P R κ)

theorem optimalCore_spec (f : Objective n) (P R : Finset (Fin n)) (κ : ℕ) :
    optimalCore f P R κ ⊆ P ∧ (optimalCore f P R κ).card ≤ κ ∧
      ∀ O', O' ⊆ P → O'.card ≤ κ → f.value (O' ∪ R) ≤ f.value (optimalCore f P R κ ∪ R) :=
  Classical.choose_spec (exists_optimalCore f P R κ)

/-- The instance of the clairvoyant addition-robust problem at the checkpoint
`c`: `V_now = X_c`, budget `κ`, and `V_future = (x_{c+1}, ..., x_n)`, with one
future element per stage. -/
def window (f : Objective n) (κ c : ℕ) : WindowInstance n where
  objective := f
  present := arrivedPrefix n c
  coreBudget := κ
  lastStage := n - c
  arrivals j := future n c j.val
  candidate j := optimalCore f (arrivedPrefix n c) (future n c j.val) κ
  arrivals_zero := by
    ext e
    simp [future]
  arrivals_mono := by
    intro i j hij e he
    simp only [future, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    have : i.val ≤ j.val := hij
    omega
  arrivals_disjoint := by
    intro j
    rw [Finset.disjoint_left]
    intro e he he'
    simp only [future, arrivedPrefix, Finset.mem_filter, Finset.mem_univ, true_and] at he he'
    omega
  candidate_subset j := (optimalCore_spec _ _ _ _).1
  candidate_card j := (optimalCore_spec _ _ _ _).2.1
  candidate_optimal j O hO hcard := (optimalCore_spec _ _ _ _).2.2 O hO hcard

theorem window_singleArrivals (f : Objective n) (κ c : ℕ) : (window f κ c).SingleArrivals := by
  intro (j : Fin (n - c))
  have hj : c + j.val < n := by
    have := j.isLt
    change j.val < n - c at this
    omega
  refine ⟨⟨c + j.val, hj⟩, ?_, ?_⟩
  · simp [window, future]
  · ext e
    simp only [window, future, Fin.val_succ, Fin.val_castSucc, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro he
      by_cases hc : e.val = c + j.val
      · exact Or.inl (Fin.ext hc)
      · exact Or.inr ⟨he.1, by omega⟩
    · rintro (rfl | he)
      · exact ⟨by simp, by simp⟩
      · exact ⟨he.1, by omega⟩

end ConsistentSubmodular.Checkpoints

end


