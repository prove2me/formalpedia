-- Prove2me | Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Matroid__InfiniteMatroidCorollaries
-- name    : OAI_Combinatorics_InfiniteMatroid_Matroid__InfiniteMatroidCorollaries
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T05:18:53.554989+00:00
-- url     : https://prove2.me/theorems/7666a210-dde4-4b5d-9e73-c25ba746a755
-- title:
--   Matroids from complement-closed basis systems with an interval alternative
-- statement:
--   Let $\alpha$ be an arbitrary, possibly infinite, set. This file isolates purely set-theoretic conditions on a family $\mathcal B$ of subsets of $\alpha$ under which $\mathcal B$ is exactly the family of bases of a matroid on $\alpha$ (a possibly infinite matroid, given by the base axioms together with the maximality axiom).
--
--   1. **Interval alternative.** A family $\mathcal B$ of subsets of $\alpha$ satisfies the *interval alternative* if for all $I\subseteq Y\subseteq\alpha$ with $Y\setminus I$ infinite there is $B\in\mathcal B$ such that
--   $$B\subseteq I\qquad\text{or}\qquad I\subseteq B\subseteq Y\qquad\text{or}\qquad Y\subseteq B .$$
--   2. **Basis system.** A *basis system* on $\alpha$ is a family $\mathcal B$ of subsets of $\alpha$ such that
--      - $\mathcal B$ is nonempty;
--      - $\mathcal B$ is an antichain: if $B,C\in\mathcal B$ and $B\subseteq C$, then $B=C$;
--      - $\mathcal B$ is closed under complementation: $B\in\mathcal B$ implies $\alpha\setminus B\in\mathcal B$;
--      - $\mathcal B$ is closed under every single exchange: if $B\in\mathcal B$, $e\in B$ and $f\in\alpha\setminus B$, then $(B\setminus\{e\})\cup\{f\}\in\mathcal B$;
--      - $\mathcal B$ satisfies the interval alternative.
--   3. **Independent sets.** For a basis system $\mathcal B$, a set $I\subseteq\alpha$ is *independent* if $I\subseteq B$ for some $B\in\mathcal B$.
--   4. **The associated matroid.** $M(\mathcal B)$ is the matroid whose ground set is all of $\alpha$ and whose bases are exactly the members of $\mathcal B$. Its independent sets are then exactly the independent sets of item 3.
--
--   To justify item 4 the file verifies the base axioms. Base exchange follows from the antichain and single-exchange conditions alone. For the maximality axiom (every independent $I$ contained in a set $Y$ extends to a maximal independent subset of $Y$), a member of $\mathcal B$ contained in $Y$ is automatically maximal in $Y$; if $Y\setminus I$ is finite, a maximal element of the finite family of independent sets between $I$ and $Y$ works, and if $Y\setminus I$ is infinite, the interval alternative yields a member of $\mathcal B$ lying between $I$ and $Y$ or shows that $Y$ itself is independent.
--
--   This interface reduces the construction of the self-dual matroid $Q$ on $E_0=D\times\{0,1\}$ used in the counterexamples to producing a family of sets with the combinatorial properties above. Closure under complementation is what makes $M(\mathcal B)$ equal to its own dual, since the bases of the dual matroid are the complements of the bases; the unrestricted single-exchange condition is what makes $M(\mathcal B)$ uniform, in the sense that every subset of $\alpha$ is independent or spanning.
--
--   **Formalization Note** `BasisSystem α` is a structure with fields `bases`, `nonempty`, `antichain`, `compl_closed`, `swap` and `intervals`, the last being the predicate `IntervalAlternative bases`; item 3 is `BasisSystem.Independent`. `BasisSystem.matroid` is built with Mathlib's `Matroid.ofBase` on the ground set `univ`, using the lemmas `exchange`, `maximal_of_base`, `exists_maximal_finite_gap` and `exists_maximal`; the simp lemmas `ground`, `isBase_iff` and `indep_iff` identify its ground set, bases and independent sets.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/InfiniteMatroid/Matroid.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/InfiniteMatroid/Matroid.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the InfiniteMatroidCorollaries mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_InfiniteMatroidCorollaries

namespace OAI

section

open Set Matroid

namespace InfiniteMatroidCounterexample

def IntervalAlternative {α : Type*} (Bases : Set (Set α)) : Prop :=
  ∀ I Y, I ⊆ Y → (Y \ I).Infinite →
    ∃ B ∈ Bases, B ⊆ I ∨ (I ⊆ B ∧ B ⊆ Y) ∨ Y ⊆ B

/-- The purely set-theoretic assumptions supplied by the prototype assembly. -/
structure BasisSystem (α : Type*) where
  bases : Set (Set α)
  nonempty : bases.Nonempty
  antichain : ∀ ⦃B C⦄, B ∈ bases → C ∈ bases → B ⊆ C → B = C
  compl_closed : ∀ ⦃B⦄, B ∈ bases → Bᶜ ∈ bases
  swap : ∀ ⦃B⦄, B ∈ bases → ∀ e ∈ B, ∀ f ∉ B, insert f (B \ {e}) ∈ bases
  intervals : IntervalAlternative bases

namespace BasisSystem

variable {α : Type*} (S : BasisSystem α)

def Independent (I : Set α) : Prop := ∃ B ∈ S.bases, I ⊆ B

lemma maximal_of_base {B : Set α} (hB : B ∈ S.bases) {Y : Set α} (hBY : B ⊆ Y) :
    Maximal (fun K ↦ S.Independent K ∧ K ⊆ Y) B := by
  refine ⟨⟨⟨B, hB, Subset.rfl⟩, hBY⟩, ?_⟩
  intro C hC hBC
  obtain ⟨B', hB', hCB'⟩ := hC.1
  have heq := S.antichain hB hB' (hBC.trans hCB')
  exact heq ▸ hCB'

lemma exists_maximal_finite_gap {I Y : Set α} (hI : S.Independent I) (hIY : I ⊆ Y)
    (hgap : (Y \ I).Finite) :
    ∃ J, I ⊆ J ∧ Maximal (fun K ↦ S.Independent K ∧ K ⊆ Y) J := by
  let F : Set (Set α) := {J | I ⊆ J ∧ S.Independent J ∧ J ⊆ Y}
  have hF : F.Finite := by
    apply ((hgap.finite_subsets).image (fun H ↦ I ∪ H)).subset
    intro J hJ
    refine ⟨J \ I, (fun x hx ↦ ⟨hJ.2.2 hx.1, hx.2⟩), ?_⟩
    ext x
    simp only [Set.mem_union, Set.mem_sdiff]
    have := @hJ.1 x
    tauto
  obtain ⟨J, hJ, hmax⟩ := hF.exists_maximal ⟨I, Subset.rfl, hI, hIY⟩
  refine ⟨J, hJ.1, ⟨hJ.2, ?_⟩⟩
  intro K hK hJK
  exact hmax ⟨hJ.1.trans hJK, hK⟩ hJK

lemma exists_maximal {I Y : Set α} (hI : S.Independent I) (hIY : I ⊆ Y) :
    ∃ J, I ⊆ J ∧ Maximal (fun K ↦ S.Independent K ∧ K ⊆ Y) J := by
  by_cases hgap : (Y \ I).Finite
  · exact S.exists_maximal_finite_gap hI hIY hgap
  obtain ⟨B, hB, hBI | ⟨hIB, hBY⟩ | hYB⟩ := S.intervals I Y hIY hgap
  · obtain ⟨B', hB', hIB'⟩ := hI
    have heq := S.antichain hB hB' (hBI.trans hIB')
    have hIB : I ⊆ B := heq ▸ hIB'
    exact ⟨B, hIB, S.maximal_of_base hB (hBI.trans hIY)⟩
  · exact ⟨B, hIB, S.maximal_of_base hB hBY⟩
  · refine ⟨Y, hIY, ⟨⟨⟨B, hB, hYB⟩, Subset.rfl⟩, ?_⟩⟩
    exact fun _ h _ ↦ h.2

lemma exchange : Matroid.ExchangeProperty (· ∈ S.bases) := by
  intro B C hB hC e he
  have hn : ¬ C ⊆ B := by
    intro hCB
    have heq := S.antichain hC hB hCB
    exact he.2 (heq ▸ he.1)
  obtain ⟨f, hfC, hfB⟩ := Set.not_subset.mp hn
  exact ⟨f, ⟨hfC, hfB⟩, S.swap hB e he.1 f hfB⟩

noncomputable def matroid : Matroid α :=
  Matroid.ofBase univ (· ∈ S.bases) S.nonempty S.exchange
    (fun _ _ _ hI hIY ↦ S.exists_maximal hI hIY)
    (fun _ _ ↦ subset_univ _)

@[simp] lemma ground : S.matroid.E = univ := rfl
@[simp] lemma isBase_iff (B : Set α) : S.matroid.IsBase B ↔ B ∈ S.bases := Iff.rfl
@[simp] lemma indep_iff (I : Set α) : S.matroid.Indep I ↔ S.Independent I := Iff.rfl

end BasisSystem
end InfiniteMatroidCounterexample
end

end OAI


