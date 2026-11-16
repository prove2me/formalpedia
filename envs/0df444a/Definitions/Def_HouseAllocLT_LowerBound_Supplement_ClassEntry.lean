-- Prove2me | Definitions.Def_HouseAllocLT_LowerBound_Supplement_ClassEntry
-- name    : HouseAllocLT_LowerBound_Supplement_ClassEntry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T14:14:13.221649+00:00
-- url     : https://prove2.me/theorems/00641300-56fd-4c82-97a8-ddd1e9fb8f89
-- title:
--   The abstract class-entry problem of §4.2
-- statement:
--   Fix agents $\iota$ and objects $\alpha$. A **class-entry problem** gives each agent any allowed classes (possibly none), as a repetition-free list of entries $(i,C)$ in an arbitrary chosen order, where different classes of the same agent are disjoint. A matching may use only the **allowed edges** $(i,a)$ with $a$ in one of $i$'s classes. Its **class vector** lists, entry by entry in the chosen order, $1$ if the matching gives the entry's agent an object of the entry's class and $0$ otherwise.
--
--   An **optimum** is a matching with the lexicographically largest class vector, and an object is **essential** if every optimum uses it. A new problem **adds agent $i$** to an old one if the old problem has no entry of $i$, every new entry not in the old problem belongs to $i$, and the old entries appear in the new list in the same relative order.
--
--   These notions are the setting of Lemma 4.2; applied to an initial segment of the class-vector order they describe a prefix of an RPG run.
-- source:
--   Jinshan Zhang, Nan Zhao, Hao Xu, Meng Xi, Lin Zhao, STOC 2027 submission #174 (October 2026), §4.2, paragraph before Lemma 4.2, PDF p. 11 (printed p. 9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/174.pdf

import Definitions.Def_HouseAllocLT_LowerBound_Preference
import Definitions.Def_TwoStageMatch_Bipartite

open scoped BigOperators
open Classical

namespace HouseAllocLT.LowerBound.Supplement
open HouseAllocLT.LowerBound

/-! # The abstract class-entry problem of §4.2

Zhang, Zhao, Xu, Xi, Zhao, STOC 2027 submission #174 (October 2026), §4.2, PDF p. 11
(printed p. 9), paragraph before Lemma 4.2: "Give each agent any allowed classes and fix any
order of their entries. Classes of the same agent must be disjoint. A matching can use only the
allowed edges. … an optimum means a matching with the lexicographically largest class vector in
this order. … Call an object essential if every optimum uses it." -/

/-- A class-entry problem on agents `ι` and objects `α`: a list of entries `(agent, class)` in
the chosen order, without repetitions, where two different entries of the same agent have
disjoint classes. An agent may have any number of entries, including none. -/
structure ClassEntryProblem (ι α : Type) where
  entries : List (ι × Finset α)
  nodup : entries.Nodup
  disjoint : ∀ e ∈ entries, ∀ e' ∈ entries, e ≠ e' → e.1 = e'.1 → Disjoint e.2 e'.2

namespace ClassEntryProblem

noncomputable section

variable {ι α : Type} [Fintype ι] [Fintype α]

/-- The allowed edges: `(i, a)` with `a` in one of `i`'s classes. -/
def Allowed (I : ClassEntryProblem ι α) (i : ι) (a : α) : Prop :=
  ∃ e ∈ I.entries, e.1 = i ∧ a ∈ e.2

/-- A matching of the problem: a matching that uses only allowed edges. -/
def IsMatching (I : ClassEntryProblem ι α) (M : Finset (ι × α)) : Prop :=
  TwoStageMatch.IsMatching I.Allowed Finset.univ Finset.univ M

/-- The zero-one value of the entry `e = (i, C)` at `M`: `1` iff `M` gives `i` an object of `C`. -/
def entryVal (M : Finset (ι × α)) (e : ι × Finset α) : ℕ :=
  if ∃ a ∈ e.2, (e.1, a) ∈ M then 1 else 0

/-- The class vector of `M`: the entry values in the order of `entries`. -/
def vec (I : ClassEntryProblem ι α) (M : Finset (ι × α)) (k : ℕ) : ℕ :=
  if h : k < I.entries.length then entryVal M (I.entries.get ⟨k, h⟩) else 0

/-- An optimum: a matching of the problem whose class vector is lexicographically largest among
all matchings of the problem. -/
def IsOptimum (I : ClassEntryProblem ι α) (M : Finset (ι × α)) : Prop :=
  I.IsMatching M ∧ ∀ ν, I.IsMatching ν → LexGE I.entries.length (I.vec M) (I.vec ν)

/-- An object is essential if every optimum uses it. -/
def IsEssential (I : ClassEntryProblem ι α) (a : α) : Prop :=
  ∀ M, I.IsOptimum M → ∃ i, (i, a) ∈ M

/-- `new` arises from `old` by adding agent `i` with any allowed classes, its entries inserted
anywhere while all old entries keep their relative order: `old` has no entry of `i`, the old
entry list is a sublist of the new one, and every new entry not in `old` belongs to `i`. -/
def AddsAgent (old new : ClassEntryProblem ι α) (i : ι) : Prop :=
  old.entries.Sublist new.entries ∧ (∀ e ∈ old.entries, e.1 ≠ i) ∧
    ∀ e ∈ new.entries, e ∉ old.entries → e.1 = i

end

end ClassEntryProblem

end HouseAllocLT.LowerBound.Supplement


