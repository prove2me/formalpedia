-- Prove2me | Definitions.Def_OAI_Combinatorics_InfiniteMatroid_OrdinalRank
-- name    : OAI_Combinatorics_InfiniteMatroid_OrdinalRank
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:44:14.030717+00:00
-- url     : https://prove2.me/theorems/092fed42-4118-4c47-a5b2-106582b9b5dd
-- title:
--   Rank models: an ultrafilter avoiding an ideal with an antitone continuum-valued rank, and the least-index rank
-- statement:
--   Let $\alpha$ be a set, let $\mathcal K$ be a subset ideal on $\alpha$ (a proper ideal of *small* sets), and write $X\subseteq_{\mathcal K}Y$ when $X\setminus Y$ is small. Let $\mathcal C$ be the continuum index set, i.e. the ordinals below the initial ordinal of $\mathfrak c=2^{\aleph_0}$, a well-order of cardinality $\mathfrak c$. An ultrafilter $\mathcal U$ on $\alpha$ *avoids* $\mathcal K$ if it contains no small set. Two preliminary facts are recorded for such $\mathcal U$: if $X\in\mathcal U$ and $X\subseteq_{\mathcal K}Y$, then $Y\in\mathcal U$; consequently, if $X\triangle Y$ is small, then $X\in\mathcal U\iff Y\in\mathcal U$.
--
--   1. **Rank model.** A rank model on $\alpha$ is a triple $R=(\mathcal K,\mathcal U,\rho)$ consisting of a subset ideal $\mathcal K$, an ultrafilter $\mathcal U$ avoiding $\mathcal K$, and a map $\rho$ from subsets of $\alpha$ to $\mathcal C$, such that
--      - (*antitone*) if $X,Y\in\mathcal U$ and $X\subseteq_{\mathcal K}Y$, then $\rho(Y)\le\rho(X)$;
--      - (*thinning*) if $s\subseteq X\subseteq\alpha$, $s\notin\mathcal U$, $X\in\mathcal U$ and $\gamma\in\mathcal C$, then there is a set $u$ with
--   $$s\subseteq u\subseteq X,\qquad u\in\mathcal U,\qquad \gamma<\rho(u).$$
--      It follows that if $X\triangle Y$ is small, then $X\in\mathcal U\iff Y\in\mathcal U$, and $\rho(X)=\rho(Y)$ whenever $X\in\mathcal U$.
--   2. **Least-index rank.** Let $(F_i)_{i\in\mathcal C}$ be a family of subsets of $\alpha$ in which every member of $\mathcal U$ occurs, i.e. each $X\in\mathcal U$ equals $F_i$ for some $i$. Then for $X\in\mathcal U$ the set $\{i:\ F_i\subseteq_{\mathcal K}X\}$ is nonempty, and
--   $$\rho_F(X)=\begin{cases}\min\{i\in\mathcal C:\ F_i\subseteq_{\mathcal K}X\}, & X\in\mathcal U,\\ i_0, & X\notin\mathcal U,\end{cases}$$
--   where the minimum exists because $\mathcal C$ is well-ordered and $i_0$ is a fixed default index (the one coded by the all-zero binary sequence).
--
--   The least-index rank records how early in the continuum enumeration a set almost contained in $X$ appears, so enlarging $X$ modulo $\mathcal K$ can only lower the rank. In the counterexample a rank model on $D$ is built from $\rho_F$, with $\mathcal U$ an ultrafilter containing a continuum of column sets: thinning is what allows admissible sets of arbitrarily large rank to be chosen, while the antitone property together with the well-foundedness of $\mathcal C$ rules out infinite strictly descending chains of ranks along a ray.
--
--   **Formalization Note** `RankModel α` is a structure with fields `ideal`, `ultra`, `avoids`, `rank`, `antitone` and `thinning`. The preliminary facts are `SubsetIdeal.large_of_modSubset` and `SubsetIdeal.large_iff_symmDiff`, and the consequence stated in item 1 is `RankModel.invariant`. `ordinalRank K U F hFs` takes the covering hypothesis `hFs : ∀ X, X ∈ U → ∃ i, F i = X` (used through `rank_candidates_nonempty`); the minimum is `wellFounded_lt.min`, and the default value `cindexBinaryEquiv.symm (fun _ ↦ false)` for sets outside $\mathcal U$ plays no role.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/InfiniteMatroid/OrdinalRank.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/InfiniteMatroid/OrdinalRank.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the InfiniteMatroid mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_InfiniteMatroid
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Cardinality
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Ideals

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

section

open Set Filter
open scoped symmDiff

namespace InfiniteMatroidCounterexample

namespace SubsetIdeal
variable {α : Type} (K : SubsetIdeal α) (U : Ultrafilter α)
  (hUK : ∀ N, K.small N → N ∉ U)

include hUK in
lemma large_of_modSubset {X Y : Set α} (hX : X ∈ U) (hXY : K.ModSubset X Y) : Y ∈ U := by
  have hc : (X \ Y)ᶜ ∈ U := Ultrafilter.compl_mem_iff_notMem.mpr (hUK _ hXY)
  exact Filter.mem_of_superset (inter_mem hX hc) (by intro x hx; by_contra hy; exact hx.2 ⟨hx.1, hy⟩)

include hUK in
lemma large_iff_symmDiff {X Y : Set α} (h : K.small (X ∆ Y)) : X ∈ U ↔ Y ∈ U := by
  exact ⟨fun hX ↦ K.large_of_modSubset U hUK hX (K.mono h (by simp [symmDiff_def])),
    fun hY ↦ K.large_of_modSubset U hUK hY (K.mono h (by simp [symmDiff_def]))⟩

end SubsetIdeal

/-- The properties of the ordinal rank which are used by the global assembly. -/
structure RankModel (α : Type) where
  ideal : SubsetIdeal α
  ultra : Ultrafilter α
  avoids : ∀ N, ideal.small N → N ∉ ultra
  rank : Set α → CIndex
  antitone : ∀ ⦃X Y⦄, X ∈ ultra → Y ∈ ultra → ideal.ModSubset X Y → rank Y ≤ rank X
  thinning : ∀ s X, s ⊆ X → s ∉ ultra → X ∈ ultra → ∀ γ : CIndex,
    ∃ u, s ⊆ u ∧ u ⊆ X ∧ u ∈ ultra ∧ γ < rank u

namespace RankModel
variable {α : Type} (R : RankModel α)
lemma invariant {X Y : Set α} (h : R.ideal.small (X ∆ Y)) :
    (X ∈ R.ultra ↔ Y ∈ R.ultra) ∧ (X ∈ R.ultra → R.rank X = R.rank Y) := by
  have he := R.ideal.large_iff_symmDiff R.ultra R.avoids h
  refine ⟨he, fun hX ↦ le_antisymm ?_ ?_⟩
  · exact R.antitone (he.mp hX) hX (R.ideal.mono h (by simp [symmDiff_def]))
  · exact R.antitone hX (he.mp hX) (R.ideal.mono h (by simp [symmDiff_def]))
end RankModel

section Construction
variable {α : Type}
variable (K : SubsetIdeal α) (G : CIndex → Set α) (U : Ultrafilter α)
  (hUK : ∀ N, K.small N → N ∉ U) (hG : ∀ t, G t ∈ U)
  (hfinite : ∀ X, X ∈ U → {t | K.ModSubset X (G t)}.Finite)

variable (F : CIndex → Set α) (hF : ∀ i, F i ∈ U)
  (hFs : ∀ X, X ∈ U → ∃ i, F i = X)

include hFs in
lemma rank_candidates_nonempty {X : Set α} (hX : X ∈ U) :
    {i | K.ModSubset (F i) X}.Nonempty := by
  obtain ⟨i, rfl⟩ := hFs X hX
  exact ⟨i, K.modSubset_refl _⟩

noncomputable def ordinalRank (X : Set α) : CIndex := by
  classical
  exact if hX : X ∈ U then wellFounded_lt.min {i | K.ModSubset (F i) X}
    (rank_candidates_nonempty K U F hFs hX)
  else cindexBinaryEquiv.symm (fun _ ↦ false)

end Construction
end InfiniteMatroidCounterexample
end

end OAI


