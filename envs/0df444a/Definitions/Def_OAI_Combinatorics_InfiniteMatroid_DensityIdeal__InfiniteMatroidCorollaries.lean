-- Prove2me | Definitions.Def_OAI_Combinatorics_InfiniteMatroid_DensityIdeal__InfiniteMatroidCorollaries
-- name    : OAI_Combinatorics_InfiniteMatroid_DensityIdeal__InfiniteMatroidCorollaries
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T05:40:12.621569+00:00
-- url     : https://prove2.me/theorems/756a162c-bcc6-4645-bf07-8d7a8be6cdc7
-- title:
--   The column ideal on $D$: density zero after cutting down to finitely many $A$-columns
-- statement:
--   Notation follows the column definitions. $D$ is the set of pairs $(m,g)$ with $m\in\mathbb N$ and $g:\{0,1\}^m\to\{0,1\}$ a Boolean function of $m$ variables; its $m$-th block $D_m=\{(m,g)\}$ has $2^{2^m}$ elements, and $X\subseteq D$ has *density zero* if $|X\cap D_m|/|D_m|\to0$ as $m\to\infty$. Let $\mathfrak c$ be the initial ordinal of the continuum, used as an index set of cardinality $2^{\aleph_0}$, and let $\beta$ be a fixed bijection from $\mathfrak c$ onto the set of infinite binary sequences. A *column tag* is a pair $\tau=(t,i)$ with $t\in\mathfrak c$ and $i\in\{0,1,2\}$. It is coded by the binary sequence $\sigma_\tau=\bigl([i=0],[i=1],\beta(t)_0,\beta(t)_1,\dots\bigr)$, and its *column* is
--
--   $$
--   \mathrm{Col}(\tau)=\bigl\{(m,g)\in D:\ g\bigl(\sigma_\tau(0),\dots,\sigma_\tau(m-1)\bigr)=1\bigr\},
--   $$
--
--   the set of Boolean functions taking the value $1$ on the length-$m$ prefix of $\sigma_\tau$. For finite sets $F,H$ of tags, the signed pattern $\mathrm{Pat}(F,H)$ is the set of $x\in D$ that lie in $\mathrm{Col}(\tau)$ for every $\tau\in F$ and in no $\mathrm{Col}(\tau)$ with $\tau\in H$.
--
--   1. **Three column families.** For $t\in\mathfrak c$ the tags $a_t=(t,0)$, $b_t=(t,1)$ and $g_t=(t,2)$ are distinguished; $A_t=\mathrm{Col}(a_t)$ are the $A$-columns and $G_t=\mathrm{Col}(g_t)$ the $G$-columns (the tags $b_t$ are used later for the reservation cells).
--   2. **Finite meets of $A$-columns.** For a finite set $F\subseteq\mathfrak c$, $A_F=\bigcap_{t\in F}A_t$, with $A_\emptyset=D$; one has $A_{F\cup H}=A_F\cap A_H$.
--   3. **The column ideal.** A set $X\subseteq D$ is $\mathcal K$-small if
--   $$\exists\,F\subseteq\mathfrak c\ \text{finite}:\qquad \lim_{m\to\infty}\frac{|X\cap A_F\cap D_m|}{|D_m|}=0 ,$$
--   that is, $X$ has density zero once it is cut down to finitely many $A$-columns.
--   4. **$\mathcal K$ as an ideal.** The $\mathcal K$-small sets contain $\emptyset$, are closed under subsets and under finite unions, and $D$ itself is not $\mathcal K$-small. This packages $\mathcal K$ as a proper ideal of subsets of $D$.
--
--   The file also proves that for disjoint finite sets $F,H$ of tags the signed pattern $\mathrm{Pat}(F,H)$ does not have density zero; that no $A_F$ has density zero; that every set of density zero is $\mathcal K$-small; and that the complement $D\setminus A_t$ of every $A$-column is $\mathcal K$-small.
--
--   $\mathcal K$ is the ideal underlying the rank model on $D$; the construction of the rank ultrafilter later needs that the signed patterns of the $G$-columns are not $\mathcal K$-small. In the other direction, $D\setminus A_t=\mathrm{Pat}(\emptyset,\{a_t\})$ is $\mathcal K$-small although it does not have density zero, so the reservation cells placed outside $A_t$ are negligible for the rank model while remaining visible to block densities.
--
--   **Formalization Note** Column tags are `ColumnTag = CIndex × Fin 3` with `CIndex = Cardinal.continuum.ord.ToType`. The definitions are `tagA`, `tagB`, `tagG`, `AColumn`, `GColumn`, `Ameet F` (for `F : Finset CIndex`), `KSmall` and `KIdeal : SubsetIdeal D` (fields `small`, `empty`, `mono`, `union`, `proper`). Density zero is `DSmall`, defined through `dDensity X m = finiteDensity (dBlock m) X`, and the signed pattern is `columnPattern column P N`. The lemmas are `signed_columns_positive`, `Ameet_union`, `dSmall_kSmall`, `kSmall_mono`, `kSmall_union`, `Ameet_positive`, `kSmall_proper` and `AColumn_compl_kSmall`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/InfiniteMatroid/DensityIdeal.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/InfiniteMatroid/DensityIdeal.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the InfiniteMatroidCorollaries mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Matroid__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_DoubleRay__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Waves
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Cardinality__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Ideals__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_OrdinalRank__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_FiniteCounting__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_BlockDensity__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Columns__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Cesaro__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_ProbeLimits__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_SparsePerturbation__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Interpolation__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_LocalBases__InfiniteMatroidCorollaries

namespace OAI

section
open Set Filter Finset
open scoped Topology symmDiff
namespace InfiniteMatroidCounterexample

lemma signed_columns_positive (P N : Finset ColumnTag) (hPN : Disjoint P N) :
    ¬ DSmall (columnPattern column P N) := by
  classical
  let F := P ∪ N
  let v (t : F) : Bool := decide (t.val ∈ P)
  apply mt (fun h ↦ dSmall_mono h ?_) (pattern_positive F v)
  intro x hx
  constructor
  · intro t ht
    have he := hx ⟨t, Finset.mem_union_left _ ht⟩
    simpa [v, ht, column] using he
  · intro t ht hc
    have hn : t ∉ P := fun hp ↦ Finset.disjoint_left.mp hPN hp ht
    have he := hx ⟨t, Finset.mem_union_right _ ht⟩
    have hf : x.2 (prefixString (columnString t) x.1) = false := by simpa [v, hn] using he
    exact Bool.false_ne_true (hf.symm.trans hc)

def tagA (t : CIndex) : ColumnTag := (t,0)
def tagB (t : CIndex) : ColumnTag := (t,1)
def tagG (t : CIndex) : ColumnTag := (t,2)
def AColumn (t : CIndex) : Set D := column (tagA t)
def GColumn (t : CIndex) : Set D := column (tagG t)

def Ameet (F : Finset CIndex) : Set D := {x | ∀ t ∈ F, x ∈ AColumn t}
def KSmall (X : Set D) : Prop := ∃ F : Finset CIndex, DSmall (X ∩ Ameet F)

lemma Ameet_union (F H : Finset CIndex) : Ameet (F ∪ H) = Ameet F ∩ Ameet H := by
  ext x
  simp only [Ameet, Set.mem_ofPred_eq, Set.mem_inter_iff, Finset.mem_union]
  constructor
  · exact fun h ↦ ⟨fun t ht ↦ h t (Or.inl ht), fun t ht ↦ h t (Or.inr ht)⟩
  · rintro ⟨hF,hH⟩ t (ht|ht)
    · exact hF t ht
    · exact hH t ht

lemma dSmall_kSmall {X : Set D} (h : DSmall X) : KSmall X := by
  refine ⟨∅, ?_⟩
  simpa [Ameet] using h

lemma kSmall_mono {X Y : Set D} (hY : KSmall Y) (hXY : X ⊆ Y) : KSmall X := by
  obtain ⟨F,hF⟩ := hY
  exact ⟨F,dSmall_mono hF (inter_subset_inter_left _ hXY)⟩

lemma kSmall_union {X Y : Set D} (hX : KSmall X) (hY : KSmall Y) : KSmall (X ∪ Y) := by
  classical
  obtain ⟨F,hF⟩ := hX
  obtain ⟨H,hH⟩ := hY
  refine ⟨F ∪ H, dSmall_mono (dSmall_union hF hH) ?_⟩
  rw [Ameet_union]
  intro x hx
  rcases hx.1 with hxX|hxY
  · exact Or.inl ⟨hxX,hx.2.1⟩
  · exact Or.inr ⟨hxY,hx.2.2⟩

lemma Ameet_positive (F : Finset CIndex) : ¬ DSmall (Ameet F) := by
  classical
  apply mt (fun h ↦ dSmall_mono h ?_) (signed_columns_positive (F.image tagA) ∅ (by simp))
  intro x hx t ht
  exact hx.1 _ (mem_image.mpr ⟨t,ht,rfl⟩)

lemma kSmall_proper : ¬ KSmall univ := by
  rintro ⟨F,hF⟩
  exact Ameet_positive F (by simpa using hF)

noncomputable def KIdeal : SubsetIdeal D :=
  ⟨KSmall,dSmall_kSmall dSmall_empty, fun _ _ h hs ↦ kSmall_mono h hs,
    fun _ _ hX hY ↦ kSmall_union hX hY, kSmall_proper⟩

lemma AColumn_compl_kSmall (t : CIndex) : KSmall (AColumn t)ᶜ := by
  classical
  refine ⟨{t}, ?_⟩
  have he : (AColumn t)ᶜ ∩ Ameet {t} = ∅ := by ext x; simp [Ameet]
  rw [he]
  exact dSmall_empty

end InfiniteMatroidCounterexample
end

end OAI


