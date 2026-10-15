-- Prove2me | Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Ideals__InfiniteMatroidCorollaries
-- name    : OAI_Combinatorics_InfiniteMatroid_Ideals__InfiniteMatroidCorollaries
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T05:22:17.449814+00:00
-- url     : https://prove2.me/theorems/787337ce-64dd-45c0-a369-e11beeda13a6
-- title:
--   Proper ideals of sets, inclusion modulo an ideal, signed column patterns and forbidden sets
-- statement:
--   Let $\alpha$ be a set.
--
--   1. **Subset ideal.** A *subset ideal* $\mathcal K$ on $\alpha$ is a family of subsets of $\alpha$, whose members are called *$\mathcal K$-small*, such that $\emptyset$ is small, every subset of a small set is small, the union of two small sets is small, and $\alpha$ itself is not small. Equivalently, $\mathcal K$ is a proper ideal of the Boolean algebra of subsets of $\alpha$.
--   2. **Inclusion modulo the ideal.** For $X,Y\subseteq\alpha$,
--   $$X\subseteq_{\mathcal K}Y\quad:\Longleftrightarrow\quad X\setminus Y\ \text{is }\mathcal K\text{-small}.$$
--   This relation is reflexive, and $X\subseteq Y$ implies $X\subseteq_{\mathcal K}Y$.
--   3. **Signed column pattern.** For a family $(G_t)_{t\in\iota}$ of subsets of $\alpha$ (the *columns*) and finite sets $F,H\subseteq\iota$,
--   $$\mathrm{Pat}_G(F,H)=\{x\in\alpha:\ x\in G_t\ \text{for all } t\in F\ \text{ and }\ x\notin G_t\ \text{for all } t\in H\}.$$
--   4. **Forbidden set.** A set $Z\subseteq\alpha$ is *forbidden* for $\mathcal K$ and $G$ if $Z$ is almost contained in infinitely many columns:
--   $$\{t\in\iota:\ Z\subseteq_{\mathcal K}G_t\}\ \text{is infinite}.$$
--
--   These notions are the input of the ultrafilter construction in the counterexamples: one wants an ultrafilter on $\alpha$ that contains no $\mathcal K$-small set, contains every column $G_t$, and has no forbidden member, so that each of its members is almost contained in only finitely many columns. The hypothesis that makes this possible is that no signed pattern $\mathrm{Pat}_G(F,H)$ with $F\cap H=\emptyset$ is $\mathcal K$-small. In the application $\alpha=D$ is the countable set of Boolean functions together with their arities, $\mathcal K$ is a density ideal, and the columns are indexed by the continuum.
--
--   **Formalization Note** `SubsetIdeal α` is a structure with the predicate `small` and the axioms `empty`, `mono`, `union` and `proper`; inclusion modulo the ideal is `K.ModSubset X Y`, with the lemmas `modSubset_refl` and `modSubset_of_subset`. `columnPattern G F H` takes two `Finset`s and does not itself require them to be disjoint; `Forbidden K G Z` is `{t | K.ModSubset Z (G t)}.Infinite`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/InfiniteMatroid/Ideals.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/InfiniteMatroid/Ideals.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the InfiniteMatroidCorollaries mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Matroid__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_DoubleRay__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Waves
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Cardinality__InfiniteMatroidCorollaries

namespace OAI

section

open Set Filter
open scoped symmDiff

namespace InfiniteMatroidCounterexample

structure SubsetIdeal (α : Type*) where
  small : Set α → Prop
  empty : small ∅
  mono : ∀ ⦃X Y⦄, small Y → X ⊆ Y → small X
  union : ∀ ⦃X Y⦄, small X → small Y → small (X ∪ Y)
  proper : ¬ small univ

namespace SubsetIdeal
variable {α : Type*} (K : SubsetIdeal α)

def ModSubset (X Y : Set α) : Prop := K.small (X \ Y)

lemma modSubset_refl (X : Set α) : K.ModSubset X X := by
  simpa [ModSubset] using K.empty

lemma modSubset_of_subset {X Y : Set α} (h : X ⊆ Y) : K.ModSubset X Y := by
  simpa [ModSubset, sdiff_eq_empty.mpr h] using K.empty

end SubsetIdeal

/-- A finite signed column pattern. -/
def columnPattern {α ι : Type*} (G : ι → Set α) (F H : Finset ι) : Set α :=
  {x | (∀ t ∈ F, x ∈ G t) ∧ ∀ t ∈ H, x ∉ G t}

def Forbidden {α ι : Type*} (K : SubsetIdeal α) (G : ι → Set α) (Z : Set α) : Prop :=
  {t | K.ModSubset Z (G t)}.Infinite

end InfiniteMatroidCounterexample
end

end OAI


