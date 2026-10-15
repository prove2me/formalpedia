-- Prove2me | Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Matroid
-- name    : OAI_Combinatorics_InfiniteMatroid_Matroid
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T02:44:29.717326+00:00
-- url     : https://prove2.me/theorems/8a6cb2d9-f598-42ae-ac5c-40102a20a473
-- title:
--   Matroids from complement-closed basis systems with an interval alternative
-- statement:
--   Let $\alpha$ be any type (set). This file isolates purely set-theoretic conditions on a family $\mathcal B$ of subsets of $\alpha$ under which $\mathcal B$ is the set of bases of a (possibly infinite) matroid on $\alpha$.
--
--   1. **Interval alternative.** A family $\mathcal B$ of subsets of $\alpha$ satisfies the interval alternative if for all $I\subseteq Y\subseteq\alpha$ with $Y\setminus I$ infinite there is $B\in\mathcal B$ with
--   $$B\subseteq I\quad\text{or}\quad I\subseteq B\subseteq Y\quad\text{or}\quad Y\subseteq B .$$
--   2. **Basis system.** A basis system on $\alpha$ is a family $\mathcal B$ of subsets of $\alpha$ such that
--      - $\mathcal B$ is nonempty;
--      - $\mathcal B$ is an antichain: $B,C\in\mathcal B$ and $B\subseteq C$ imply $B=C$;
--      - $\mathcal B$ is closed under complements: $B\in\mathcal B$ implies $\alpha\setminus B\in\mathcal B$;
--      - $\mathcal B$ is closed under single exchanges: if $B\in\mathcal B$, $e\in B$ and $f\notin B$, then $(B\setminus\{e\})\cup\{f\}\in\mathcal B$;
--      - $\mathcal B$ satisfies the interval alternative.
--   3. **Independent sets.** For a basis system $\mathcal B$, a set $I\subseteq\alpha$ is independent if it is contained in some member of $\mathcal B$:
--   $$\mathcal I(\mathcal B)=\{I\subseteq\alpha:\ \exists B\in\mathcal B,\ I\subseteq B\}.$$
--   4. **The matroid.** $M(\mathcal B)$ is the matroid with ground set all of $\alpha$ whose bases are exactly the members of $\mathcal B$; its independent sets are then exactly $\mathcal I(\mathcal B)$.
--
--   To justify item 4 the file verifies the matroid base axioms. Base exchange follows from the antichain and single-exchange conditions: if $B,C\in\mathcal B$ and $e\in B\setminus C$, then $C\not\subseteq B$, so some $f\in C\setminus B$ gives $(B\setminus\{e\})\cup\{f\}\in\mathcal B$. For the maximality axiom (every independent $I\subseteq Y$ extends to a maximal independent subset of $Y$), a member of $\mathcal B$ contained in $Y$ is automatically maximal there; when $Y\setminus I$ is finite one takes a maximal element of a finite family, and when $Y\setminus I$ is infinite the interval alternative supplies a suitable basis (or shows that $Y$ itself is independent).
--
--   The point of this interface is that the hard construction only has to produce a family of sets with these combinatorial properties. Closure under complements is the property that later makes $M(\mathcal B)$ equal to its own dual.
--
--   **Formalization Note** `BasisSystem α` is a structure with fields `bases`, `nonempty`, `antichain`, `compl_closed`, `swap` and `intervals` (the predicate `IntervalAlternative`). `BasisSystem.matroid` is built with Mathlib's `Matroid.ofBase` on ground set `univ`, using the lemmas `exchange`, `maximal_of_base`, `exists_maximal_finite_gap` and `exists_maximal`; the simp lemmas `ground`, `isBase_iff` and `indep_iff` identify its ground set, bases and independent sets.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/InfiniteMatroid/Matroid.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/InfiniteMatroid/Matroid.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the InfiniteMatroid mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_InfiniteMatroid
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Cardinality
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Ideals
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_OrdinalRank
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_FiniteCounting
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Basic
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_BlockDensity
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Columns
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Cesaro
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_ProbeLimits
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_SparsePerturbation
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Interpolation
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_LocalBases
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_DensityIdeal
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Reservations
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_BasisExtension
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Zones
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Separation
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Prototype
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_PrototypeExtension

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


