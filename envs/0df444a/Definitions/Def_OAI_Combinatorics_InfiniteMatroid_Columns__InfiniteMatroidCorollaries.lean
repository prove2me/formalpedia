-- Prove2me | Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Columns__InfiniteMatroidCorollaries
-- name    : OAI_Combinatorics_InfiniteMatroid_Columns__InfiniteMatroidCorollaries
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T05:26:15.194741+00:00
-- url     : https://prove2.me/theorems/b2960802-b51a-4cbd-87f5-acccab458237
-- title:
--   Continuum many independent column sets of Boolean functions
-- statement:
--   Let $D=\{(m,g):\ m\in\mathbb N,\ g:\{0,1\}^m\to\{0,1\}\}$ and let $D_m\subseteq D$ be its $m$-th block, consisting of the $2^{2^m}$ Boolean functions of arity $m$. Let $\mathcal C$ be the continuum index set (a well-ordered set of cardinality $\mathfrak c=2^{\aleph_0}$) and $\mathrm{bin}:\mathcal C\to\{0,1\}^{\mathbb N}$ the fixed bijection onto the infinite binary sequences. For $h\in\{0,1\}^{\mathbb N}$ and $m\in\mathbb N$ write $h|_m=(h_0,\dots,h_{m-1})\in\{0,1\}^m$ for its prefix of length $m$.
--
--   1. **Column tags and strings.** A *tag* is a pair $\tau=(t,k)$ with $t\in\mathcal C$ and $k\in\{0,1,2\}$. Its string $\sigma_\tau\in\{0,1\}^{\mathbb N}$ is
--   $$\sigma_{(t,k)}(n)=\begin{cases}1, & n<2\ \text{and}\ n=k,\\ 0, & n<2\ \text{and}\ n\ne k,\\ \mathrm{bin}(t)(n-2), & n\ge2.\end{cases}$$
--   The map $\tau\mapsto\sigma_\tau$ is injective. More generally, if $A$ is finite and $h:A\to\{0,1\}^{\mathbb N}$ is injective, then the prefixes $h(a)|_m$, $a\in A$, are pairwise distinct for all sufficiently large $m$.
--   2. **Columns.** The column of a tag $\tau$ is the set of Boolean functions that output $1$ on the prefix of $\sigma_\tau$ whose length is their arity:
--   $$\mathrm{Col}_\tau=\{(m,g)\in D:\ g(\sigma_\tau|_m)=1\}.$$
--   3. **Density on $D$.** For $X\subseteq D$ let $\delta^D_m(X)=|X\cap D_m|/|D_m|=\#\{g:\ (m,g)\in X\}/2^{2^m}$, and call $X$ *$D$-small* if $\delta^D_m(X)\to0$ as $m\to\infty$. The $D$-small sets contain $\emptyset$ and are closed under subsets and finite unions, and a set whose density is eventually equal to a constant $c>0$ is not $D$-small.
--
--   The main facts proved here say that the columns behave like independent fair coins. If $A$ is a finite set, $e$ is an injective map from $A$ to tags and $P$ is any property of maps $A\to\{0,1\}$, then for all sufficiently large $m$
--   $$\delta^D_m\Bigl(\bigl\{(m',g)\in D:\ P\bigl(a\mapsto g(\sigma_{e(a)}|_{m'})\bigr)\bigr\}\Bigr)=\frac{\#\{v\in\{0,1\}^A:\ P(v)\}}{2^{|A|}} .$$
--   In particular, for a finite set $F$ of tags and prescribed values $v:F\to\{0,1\}$, the set $\{(m,g)\in D:\ g(\sigma_\tau|_m)=v(\tau)\ \text{for all }\tau\in F\}$ has density eventually equal to $2^{-|F|}$, so it is not $D$-small.
--
--   This produces continuum many subsets of the countable set $D$, in three families $\mathrm{Col}_{(t,0)}$, $\mathrm{Col}_{(t,1)}$, $\mathrm{Col}_{(t,2)}$ with $t\in\mathcal C$, such that every finite signed pattern of distinct columns (prescribing membership or non-membership in each of finitely many distinct columns) has asymptotic density exactly $2^{-|F|}$, where $|F|$ is the number of columns involved, and in particular is not $D$-small. Later parts of the construction use these families to define the concrete ideal on $D$ and the columns that the rank ultrafilter must contain.
--
--   **Formalization Note** `ColumnTag` is `CIndex × Fin 3`; the definitions are `columnString`, `prefixString h m : Fin m → Bool`, `column`, `dDensity` and `DSmall`. The facts quoted above are `columnString_injective`, `eventually_prefix_injective`, `dBlock_trace_card`, `dDensity_formula`, `columns_uniform`, `columns_pattern`, `dSmall_empty`, `dSmall_mono`, `dSmall_union`, `dSmall_false_of_eventual` and `pattern_positive`; the counting step uses the restriction identity for Boolean functions from the finite-counting definitions. In `columns_pattern` and `pattern_positive` the finite set $F$ is a `Finset ColumnTag` and $v$ is a function on its elements, so the tags are automatically distinct.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/InfiniteMatroid/Columns.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/InfiniteMatroid/Columns.lean by skeleton subtraction
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

namespace OAI

section
open Set Filter Finset
open scoped Topology
namespace InfiniteMatroidCounterexample

abbrev ColumnTag := CIndex × Fin 3

noncomputable def columnString (t : ColumnTag) (n : ℕ) : Bool :=
  if n < 2 then decide (t.2.val = n) else cindexBinaryEquiv t.1 (n-2)

lemma columnString_injective : Function.Injective columnString := by
  intro t s h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have hk : t.2 = s.2 := by
    rcases t with ⟨t,k⟩
    rcases s with ⟨s,l⟩
    fin_cases k <;> fin_cases l <;> simp_all [columnString]
  have ht : t.1 = s.1 := by
    apply cindexBinaryEquiv.injective
    funext n
    have hn := congrFun h (n+2)
    simpa [columnString] using hn
  exact Prod.ext ht hk

def prefixString (h : ℕ → Bool) (m : ℕ) : Fin m → Bool := fun i ↦ h i

lemma eventually_prefix_injective {A : Type} [Finite A] (h : A → (ℕ → Bool))
    (hh : Function.Injective h) :
    ∀ᶠ m : ℕ in atTop, Function.Injective (fun a ↦ prefixString (h a) m) := by
  have he : ∀ a b : A, ∀ᶠ m : ℕ in atTop,
      prefixString (h a) m = prefixString (h b) m → a = b := by
    intro a b
    by_cases hab : a = b
    · exact Eventually.of_forall (fun _ _ ↦ hab)
    have hn : h a ≠ h b := fun he ↦ hab (hh he)
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hn
    filter_upwards [eventually_ge_atTop (k+1)] with m hm heq
    exact (hk (congrFun heq ⟨k, by omega⟩)).elim
  exact eventually_all.mpr (fun a ↦ eventually_all.mpr (fun b ↦ he a b))

def column (t : ColumnTag) : Set D := {x | x.2 (prefixString (columnString t) x.1) = true}

noncomputable def dDensity (X : Set D) (m : ℕ) : ℝ := finiteDensity (dBlock m) X

def DSmall (X : Set D) : Prop := Tendsto (dDensity X) atTop (𝓝 0)

lemma dBlock_trace_card (X : Set D) (m : ℕ) :
    (traceFinset (dBlock m) X).card =
      @Fintype.card {f : (Fin m → Bool) → Bool // (⟨m,f⟩ : D) ∈ X}
        (by classical exact inferInstance) := by
  classical
  let e : ((Fin m → Bool) → Bool) ↪ D := ⟨fun f ↦ ⟨m,f⟩, fun _ _ h ↦ by simpa using h⟩
  have he : traceFinset (dBlock m) X = (univ.filter (fun f ↦ (⟨m,f⟩ : D) ∈ X)).map e := by
    ext x
    rcases x with ⟨k,f⟩
    simp only [mem_traceFinset, mem_dBlock, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨rfl,hf⟩
      exact ⟨f,hf,rfl⟩
    · rintro ⟨g,hg,heq⟩
      change (⟨m,g⟩ : D) = ⟨k,f⟩ at heq
      cases heq
      exact ⟨rfl,hg⟩
  rw [he, card_map]
  exact (Fintype.card_subtype _).symm

lemma dDensity_formula (X : Set D) (m : ℕ) :
    dDensity X m =
      (@Fintype.card {f : (Fin m → Bool) → Bool // (⟨m,f⟩ : D) ∈ X}
        (by classical exact inferInstance) : ℝ) / Fintype.card ((Fin m → Bool) → Bool) := by
  simp only [dDensity, finiteDensity, dBlock_trace_card, card_dBlock, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]

/-- All finite marginals are uniform once the chosen prefixes separate. -/
lemma columns_uniform {A : Type} [Fintype A] [DecidableEq A] (e : A ↪ ColumnTag)
    (P : (A → Bool) → Prop) :
    ∀ᶠ m in atTop,
      dDensity {x : D | P (fun a ↦ x.2 (prefixString (columnString (e a)) x.1))} m =
        (Nat.card {v : A → Bool // P v} : ℝ) /
          Fintype.card (A → Bool) := by
  classical
  filter_upwards [eventually_prefix_injective (fun a ↦ columnString (e a))
    (columnString_injective.comp e.injective)] with m hm
  rw [dDensity_formula]
  rw [Nat.card_eq_fintype_card]
  exact function_density_restriction ⟨fun a ↦ prefixString (columnString (e a)) m, hm⟩ P

lemma columns_pattern (F : Finset ColumnTag) (v : F → Bool) :
    ∀ᶠ m in atTop,
      dDensity {x : D | ∀ t : F, x.2 (prefixString (columnString t) x.1) = v t} m =
        1 / (2 : ℝ)^F.card := by
  classical
  have h := columns_uniform (A := F) ⟨Subtype.val, Subtype.val_injective⟩ (fun w ↦ w = v)
  have hc : Nat.card {w : F → Bool // w = v} = 1 := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_eq_one_iff.mpr ⟨⟨v,rfl⟩, fun w ↦ Subtype.ext w.property⟩
  rw [hc] at h
  simpa [funext_iff] using h

lemma dSmall_empty : DSmall ∅ := by
  have he : dDensity ∅ = fun _ ↦ 0 := by ext m; simp [dDensity, finiteDensity]
  rw [DSmall, he]
  exact tendsto_const_nhds

lemma dSmall_mono {X Y : Set D} (hY : DSmall Y) (hXY : X ⊆ Y) : DSmall X :=
  squeeze_zero (fun _ ↦ finiteDensity_nonneg _ _) (fun _ ↦ finiteDensity_mono _ hXY) hY

lemma dSmall_union {X Y : Set D} (hX : DSmall X) (hY : DSmall Y) : DSmall (X ∪ Y) := by
  have ht : Tendsto (fun m ↦ dDensity X m + dDensity Y m) atTop (𝓝 0) := by simpa using hX.add hY
  exact squeeze_zero (fun m ↦ finiteDensity_nonneg _ _) (fun m ↦ finiteDensity_union_le _ _ _) ht

lemma dSmall_false_of_eventual {X : Set D} {c : ℝ} (hc : 0 < c)
    (h : dDensity X =ᶠ[atTop] fun _ ↦ c) : ¬ DSmall X := by
  intro hX
  have he := tendsto_nhds_unique ((tendsto_congr' h).mp hX) tendsto_const_nhds
  exact hc.ne he

lemma pattern_positive (F : Finset ColumnTag) (v : F → Bool) :
    ¬ DSmall {x : D | ∀ t : F, x.2 (prefixString (columnString t) x.1) = v t} :=
  dSmall_false_of_eventual (by positivity) (columns_pattern F v)

end InfiniteMatroidCounterexample
end

end OAI


