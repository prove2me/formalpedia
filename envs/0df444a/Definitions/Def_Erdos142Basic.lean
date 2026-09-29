-- Prove2me | Definitions.Def_Erdos142Basic
-- name    : Erdos142Basic
-- status  : Definition
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:20:56.166373+00:00
-- url     : https://prove2.me/theorems/f5f3efdf-ca3f-47bf-92d3-7cb295a6bf89
-- title:
--   Progression-free sets and the counting function $r_k(N)$
-- statement:
--   This file fixes the objects of Erdős Problem #142. Its first four declarations are transcribed verbatim from the [formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/142.lean) entry for this problem, so that the mission's goal is literally the statement recorded there.
--
--   **Progressions.** For a set $s$, a length $l \in \mathbb{N} \cup \{\infty\}$ and elements $a, d$, the predicate `IsAPOfLengthWith` says that $s$ is the arithmetic progression of length $l$ with first term $a$ and common difference $d$: it has exactly $l$ elements and
--
--   $$s \;=\; \{\, a + n d \;:\; n < l \,\}.$$
--
--   `IsAPOfLength` existentially quantifies over $a$ and $d$.
--
--   **Progression-freeness.** `IsAPOfLengthFree` declares $s$ free of progressions of length $l$ when
--
--   $$\forall\, t \subseteq s,\quad t \text{ is an arithmetic progression of length } l \;\Longrightarrow\; l \le 1 .$$
--
--   Progressions of length $0$ and $1$ count as trivial, so **every** set is free of them; the condition has content only for $l \ge 2$.
--
--   **The counting function.** For natural numbers $k$ and $N$,
--
--   $$r_k(N) \;=\; \sup\bigl\{\, |S| \;:\; S \subseteq \{1,\dots,N\},\ S \text{ is free of length-}k\text{ progressions} \,\bigr\}.$$
--
--   This is the function Erdős asked for an asymptotic formula for, and the subject of Roth's theorem, Behrend's construction, Szemerédi's theorem and every modern quantitative bound on progression-free sets.
--
--   **An elementary handle.** The file adds a second formulation for solvers to work with: `HasAP k A` says that the finite set $A$ contains a first term $a$ and a common difference $d > 0$ with $a + id \in A$ for every $i < k$, and `APFree k A` is its negation. This version carries no cardinality side condition and is the form one actually induct on. The mission's first milestone is the bridge between the two formulations.
--
--   Three supporting lemmas are supplied so that the supremum is usable: the empty set is free of progressions of every length, every progression-free subset of $\{1,\dots,N\}$ has at most $r_k(N)$ elements, and $r_k(N) \le N$.
--
--   **Formalization Note.** The ground set is `Finset.Icc 1 N`, that is $\{1,\dots,N\}$, matching the problem statement and the source file rather than `Finset.range N`. The supremum is `sSup` over $\mathbb{N}$; `le_r` and `r_le` are the two facts that make it a genuine maximum. Under the source convention $r_0(N) = r_1(N) = N$, since every set is free of trivial progressions; statements that need to exclude that carry an explicit hypothesis on $k$.
-- source:
--   Google DeepMind, formal-conjectures, FormalConjectures/ErdosProblems/142.lean and FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean (definitions Set.IsAPOfLengthWith, Set.IsAPOfLength, Set.IsAPOfLengthFree, Set.IsAPOfLengthFree.maxCard), https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/142.lean ; Erdős Problem #142, https://www.erdosproblems.com/142 (cited there as [Er80, p.92], [Er81, p.4], [Er97c], [Va99, 1.27])

import Mathlib

namespace Erdos142

variable {α : Type*} [AddCommMonoid α]

/-- A set `s` is an arithmetic progression of length `l` with first term `a` and difference `d`
if `s = {a, a + d, …, a + (l-1)d}` when `l` is finite, and `s = {a, a + d, a + 2d, …}` when
`l = ⊤`. -/
def IsAPOfLengthWith (s : Set α) (l : ℕ∞) (a d : α) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}

/-- A set `s` is an arithmetic progression of length `l`, for some first term and difference. -/
def IsAPOfLength (s : Set α) (l : ℕ∞) : Prop :=
  ∃ a d : α, IsAPOfLengthWith s l a d

/-- A set `s` is free of arithmetic progressions of length `l` if it contains no non-trivial
arithmetic progression of length `l`. -/
def IsAPOfLengthFree (s : Set α) (l : ℕ∞) : Prop :=
  ∀ t ⊆ s, IsAPOfLength t l → l ≤ 1

/-- `r k N` is the largest possible size of a subset of `{1, …, N}` that does not contain
any non-trivial `k`-term arithmetic progression. -/
noncomputable def r (k N : ℕ) : ℕ :=
  sSup {Finset.card S | (S) (_ : S ⊆ Finset.Icc 1 N) (_ : IsAPOfLengthFree (S : Set ℕ) k)}

/-- The elementary form of "contains a non-trivial `k`-term arithmetic progression": there are a
first term `a` and a common difference `d > 0` with `a + i * d ∈ A` for every `i < k`. -/
def HasAP (k : ℕ) (A : Finset ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A

/-- The elementary form of progression-freeness: the negation of `HasAP k A`. -/
def APFree (k : ℕ) (A : Finset ℕ) : Prop :=
  ¬ HasAP k A

/-- The empty set is free of arithmetic progressions of every length. -/
theorem isAPOfLengthFree_empty (k : ℕ) : IsAPOfLengthFree (∅ : Set α) k := by
  rintro t ht ⟨a, d, hcard, -⟩
  rw [Set.subset_empty_iff] at ht
  subst ht
  rw [show ENat.card (↥(∅ : Set α)) = 0 by simp [ENat.card]] at hcard
  simp [← hcard]

/-- Every progression-free subset of `{1, …, N}` has at most `r k N` elements. -/
theorem le_r {S : Finset ℕ} {k N : ℕ} (hS : S ⊆ Finset.Icc 1 N)
    (hfree : IsAPOfLengthFree (S : Set ℕ) k) : S.card ≤ r k N := by
  refine le_csSup ⟨N, ?_⟩ ⟨S, hS, hfree, rfl⟩
  rintro m ⟨T, hT, -, rfl⟩
  simpa using (Finset.card_le_card hT).trans_eq (by simp)

/-- The trivial upper bound `r k N ≤ N`. -/
theorem r_le (k N : ℕ) : r k N ≤ N := by
  refine csSup_le ⟨0, ∅, by simp, by simpa using isAPOfLengthFree_empty (α := ℕ) k, rfl⟩ ?_
  rintro m ⟨T, hT, -, rfl⟩
  simpa using (Finset.card_le_card hT).trans_eq (by simp)

end Erdos142


