-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Basic_Model
-- name    : ConsistentSubmodular_Deterministic_Basic_Model
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:07:06.030304+00:00
-- url     : https://prove2.me/theorems/36f3b091-6e81-42c9-8289-585eafce54fd
-- title:
--   Exact buffered optimizer $\mathrm{OPT}(N,Q,k)$ and exact trajectory for a monotone submodular objective
-- statement:
--   Let $f$ be an `Objective n` (nonnegative, monotone, submodular on subsets of `Fin n`), $N,Q\subseteq[n]$ finite sets and $k\in\mathbb N$.
--
--   - `Objective.bufferedOptimizer f N Q k`: a fixed (chosen by the axiom of choice) set $A\subseteq N$ with $|A|\le k$ maximizing $f(Q\cup A)$ over all $B\subseteq N$, $|B|\le k$. Such a maximizer exists because the family of feasible sets is finite and contains $\emptyset$; the set $N$ is the old ground set and $Q$ a fixed buffer added to every candidate.
--   - `Objective.bufferedOptimum f N Q k` $=f\big(Q\cup \text{bufferedOptimizer}(N,Q,k)\big)=\max_{B\subseteq N,\,|B|\le k}f(Q\cup B)$.
--   - `Objective.exactTrajectory f k t` $=\text{bufferedOptimizer}\big(X_t,\emptyset,k\big)$, a set of at most $k$ elements of the arrived prefix $X_t=\{e:e<t\}$ that is optimal for $f$ at time $t$ ($\mathrm{OPT}_t$).
--
--   The file also proves basic facts: monotonicity of the arrived prefix in $t$ and $X_0=\emptyset$, existence and the defining property of the optimizer, nonnegativity of the optimum, the bound $f(A\cup B)\le f(A)+f(B)-f(\emptyset)$, setwise diminishing returns, and the growth bounds $\mathrm{opt}(N,R,k)-\mathrm{opt}(N,Q,k)\le f(R)-f(Q)$ for $Q\subseteq R$ and $\mathrm{opt}(N,Q,k)\le f(Q)+\mathrm{opt}(N,\emptyset,k)-f(\emptyset)$.
--
--   These objects provide the benchmark $f(\mathrm{OPT}_t)$ and the window optimum with buffer (the quantity $P_j=f(O_j\cup R_j)$ in the window instances) used throughout the deterministic construction of Section 3 and Appendix B.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Basic/Model.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {n : ℕ}

@[simp] theorem arrivedPrefix_zero (n : ℕ) : arrivedPrefix n 0 = ∅ := by
  simp [arrivedPrefix]

theorem arrivedPrefix_mono {s t : ℕ} (hst : s ≤ t) :
    arrivedPrefix n s ⊆ arrivedPrefix n t := by
  intro e he
  simp only [arrivedPrefix, Finset.mem_filter, Finset.mem_univ, true_and] at *
  exact lt_of_lt_of_le he hst

namespace Objective

variable (f : Objective n)

/-- An exact finite optimizer on an arbitrary old ground set and fixed buffer. -/
theorem exists_buffered_optimizer (N Q : Finset (Fin n)) (k : ℕ) :
    ∃ A : Finset (Fin n), A ⊆ N ∧ A.card ≤ k ∧
      ∀ B : Finset (Fin n), B ⊆ N → B.card ≤ k →
        f.value (Q ∪ B) ≤ f.value (Q ∪ A) := by
  classical
  let candidates := N.powerset.filter (fun A => A.card ≤ k)
  have hnonempty : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates]
  obtain ⟨A, hA, hmax⟩ := candidates.exists_max_image
    (fun A => f.value (Q ∪ A)) hnonempty
  simp only [candidates, Finset.mem_filter, Finset.mem_powerset] at hA
  refine ⟨A, hA.1, hA.2, ?_⟩
  intro B hBN hBk
  exact hmax B (by simp [candidates, hBN, hBk])

def bufferedOptimizer (N Q : Finset (Fin n)) (k : ℕ) : Finset (Fin n) :=
  Classical.choose (f.exists_buffered_optimizer N Q k)

theorem bufferedOptimizer_spec (N Q : Finset (Fin n)) (k : ℕ) :
    f.bufferedOptimizer N Q k ⊆ N ∧
      (f.bufferedOptimizer N Q k).card ≤ k ∧
      ∀ B : Finset (Fin n), B ⊆ N → B.card ≤ k →
        f.value (Q ∪ B) ≤ f.value (Q ∪ f.bufferedOptimizer N Q k) :=
  Classical.choose_spec (f.exists_buffered_optimizer N Q k)

def bufferedOptimum (N Q : Finset (Fin n)) (k : ℕ) : ℝ :=
  f.value (Q ∪ f.bufferedOptimizer N Q k)

theorem le_bufferedOptimum {N Q A : Finset (Fin n)} {k : ℕ}
    (hAN : A ⊆ N) (hAk : A.card ≤ k) :
    f.value (Q ∪ A) ≤ f.bufferedOptimum N Q k :=
  (f.bufferedOptimizer_spec N Q k).2.2 A hAN hAk

theorem bufferedOptimum_nonnegative (N Q : Finset (Fin n)) (k : ℕ) :
    0 ≤ f.bufferedOptimum N Q k := f.nonnegative _

theorem union_le (A B : Finset (Fin n)) :
    f.value (A ∪ B) ≤ f.value A + f.value B - f.value ∅ := by
  have hsub := f.submodular A B
  have hemp := f.monotone ∅ (A ∩ B) (Finset.empty_subset _)
  linarith

/-- Setwise diminishing returns, including overlapping increments. -/
theorem diminishing_returns {A B : Finset (Fin n)} (hAB : A ⊆ B)
    (E : Finset (Fin n)) :
    f.value (B ∪ E) - f.value B ≤ f.value (A ∪ E) - f.value A := by
  have hs := f.submodular B (A ∪ E)
  have hbase := f.monotone A (B ∩ (A ∪ E)) (by
    intro e he
    exact Finset.mem_inter.mpr ⟨hAB he, Finset.mem_union_left E he⟩)
  have hU : B ∪ (A ∪ E) = B ∪ E := by
    ext e
    simp only [Finset.mem_union]
    constructor
    · rintro (he | he | he)
      · exact Or.inl he
      · exact Or.inl (hAB he)
      · exact Or.inr he
    · rintro (he | he)
      · exact Or.inl he
      · exact Or.inr (Or.inr he)
  rw [hU] at hs
  linarith

/-- A window optimum cannot grow faster than its increasing buffer. -/
theorem bufferedOptimum_growth {N Q R : Finset (Fin n)} {k : ℕ}
    (hQR : Q ⊆ R) :
    f.bufferedOptimum N R k - f.bufferedOptimum N Q k ≤
      f.value R - f.value Q := by
  let A := f.bufferedOptimizer N R k
  have hA := f.bufferedOptimizer_spec N R k
  have hdr := f.diminishing_returns hQR A
  have hmax : f.value (Q ∪ A) ≤ f.bufferedOptimum N Q k :=
    f.le_bufferedOptimum hA.1 hA.2.1
  change f.value (R ∪ A) - f.bufferedOptimum N Q k ≤ _
  linarith

theorem bufferedOptimum_le (N Q : Finset (Fin n)) (k : ℕ) :
    f.bufferedOptimum N Q k ≤
      f.value Q + f.bufferedOptimum N ∅ k - f.value ∅ := by
  have hA := f.bufferedOptimizer_spec N Q k
  have hmax : f.value (f.bufferedOptimizer N Q k) ≤ f.bufferedOptimum N ∅ k := by
    simpa using f.le_bufferedOptimum (Q := ∅) hA.1 hA.2.1
  have hu := f.union_le Q (f.bufferedOptimizer N Q k)
  change f.value (Q ∪ f.bufferedOptimizer N Q k) ≤ _
  linarith

def exactTrajectory (k : ℕ) (t : Fin (n + 1)) : Finset (Fin n) :=
  f.bufferedOptimizer (arrivedPrefix n t.val) ∅ k

end Objective

end ConsistentSubmodular

end


