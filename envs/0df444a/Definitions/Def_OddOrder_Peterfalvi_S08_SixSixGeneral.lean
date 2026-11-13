-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_SixSixGeneral
-- name    : OddOrder_Peterfalvi_S08_SixSixGeneral
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:34:42.685022+00:00
-- url     : https://prove2.me/theorems/67afab08-fd12-41b5-a891-982408adfd5c
-- title:
--   Peterfalvi (6.6) for a general kernel: the $X$-set and its degree data
-- statement:
--   Peterfalvi, *Character Theory for the Odd Order Theorem*, §6, (6.6): suppose Hypothesis (6.4) holds with $M=1$, let $Z\trianglelefteq L$ with $1\ne Z\subseteq Z(K)$ and $\mathcal{X}=\mathcal{S}-\mathcal{S}(Z)$ with $\mathcal{X}\subseteq\mathrm{Irr}\,L$. Then $\mathcal{X}=\{\chi\in\mathrm{Irr}\,L\mid Z\not\subseteq\mathrm{Ker}\chi\}$ and $\mathcal{X}$ is coherent. This file develops the $X$-set for a general kernel.
--
--   The main definition is `xSet`, Peterfalvi's $\mathcal{X}=\mathcal{S}-\mathcal{S}(Z)$. The supporting lemmas establish that it is finite, closed under conjugation, has no real members, is pairwise orthogonal, and that each member has a degree of prime-power index shape (`exists_index_primePow_degree_of_mem_inducedKernelFamily`).
--
--   The bundle also proves 1 supporting lemma used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_SixSixGeneral.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_SixSixGeneral.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S08_SixFiveGeneral
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SchurCenterBound
import Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceCorePart1_CoherentAdjoin
import Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceCorePart2

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]

variable {K : Subgroup ↥L} [K.Normal] [Invertible (Nat.card ↥K : ℂ)]

/-- **Peterfalvi (6.6)'s `𝒳 = 𝒮 − 𝒮(Z)` for a general kernel `K`**: the members of the (6.1)
family `𝒮 = 𝒮(⊥)` whose source is *not* trivial on `Z`.  The Sibley `K = H` instance is
`SibleyDadeHypothesis.Xset` (`Xset_eq_inducedKernelFamily_sdiff`). -/
def xSet (K : Subgroup ↥L) [Invertible (Nat.card ↥K : ℂ)] (Z : Subgroup ↥L) :
    Set (ClassFunction ↥L ℂ) :=
  inducedKernelFamily K ⊥ \ inducedKernelFamily K Z

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] [K.Normal] in
theorem xSet_subset (Z : Subgroup ↥L) : xSet K Z ⊆ inducedKernelFamily K ⊥ :=
  fun _ h => h.1

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] [K.Normal] in
theorem xSet_finite (Z : Subgroup ↥L) : (xSet K Z).Finite :=
  (inducedKernelFamily_finite (K := K) ⊥).subset (xSet_subset Z)

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] [K.Normal] in
/-- `𝒳` is closed under complex conjugation (inherited from both `𝒮` and `𝒮(Z)`). -/
theorem xSet_closedUnderConjugate (Z : Subgroup ↥L) :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate (xSet K Z) := by
  intro φ hφ
  refine ⟨inducedKernelFamily_closedUnderConjugate (K := K) ⊥ hφ.1, fun hcon => hφ.2 ?_⟩
  have := inducedKernelFamily_closedUnderConjugate (K := K) Z hcon
  rwa [ClassFunction.conj_conj] at this

omit [Fintype G] [Invertible (Nat.card G : ℂ)] in
/-- `𝒳` has no real members (Peterfalvi (1.1), `|L|` odd). -/
theorem xSet_hasNoRealCharacters (hodd : Odd (Nat.card ↥L)) (Z : Subgroup ↥L) :
    OddOrder.Peterfalvi.S03.HasNoRealCharacters (xSet K Z) :=
  (inducedKernelFamily_hasNoRealCharacters (K := K) hodd ⊥).mono (xSet_subset Z)

omit [Fintype G] [Invertible (Nat.card G : ℂ)] in
/-- Two distinct members of `𝒳` are orthogonal (Hypothesis (5.2.c)). -/
theorem xSet_pairwise_orthogonal (Z : Subgroup ↥L) :
    OddOrder.Peterfalvi.S03.PairwiseOrthogonal (xSet K Z) :=
  fun _ _ hφ hφ' hne => inducedKernelFamily_pairwise_orthogonal hφ.1 hφ'.1 hne

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] [K.Normal] in
/-- **(6.6) per-member degree shape, general kernel.**  Every member `χ = Ind_K^L θ` of `𝒮(X)` has
degree `|L:K|·θ(1)`; when `K` is a `p`-group, `θ(1) = p^k`, so `χ(1) = |L:K|·p^k`.

The Sibley instance is `exists_index_primePow_degree_of_mem_S`; its proof uses the
`SibleyDadeHypothesis` only through `S_eq`, i.e. the family shape, so nothing is lost here. -/
theorem exists_index_primePow_degree_of_mem_inducedKernelFamily
    {p : ℕ} (hp : p.Prime) (hKp : IsPGroup p ↥K) {X : Subgroup ↥L}
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ inducedKernelFamily K X) :
    ∃ k : ℕ, χ 1 = ((K.index * p ^ k : ℕ) : ℂ) := by
  have : Fintype ↥K := Fintype.ofFinite _
  obtain ⟨θ, -, -, rfl⟩ := hχ
  obtain ⟨k, hk⟩ := exists_primePow_natDegree_of_isPGroup hp hKp θ
  exact ⟨k, by rw [ClassFunction.induce_apply_one, hk]; push_cast; ring⟩

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] [K.Normal] in
/-- **(6.6) central degree bound, general kernel.**  For `χ = Ind_K^L θ ∈ 𝒳(Z)` with `K` a
`p`-group and `Z` **central in `K`** (`Z.subgroupOf K ≤ Z(K)`, the book's `Z ⊆ Z(K)`), the source
`θ` satisfies `θ(1) = p^k` and, by [Is] Corollary 2.30 (`exists_degree_sq_le_index`, which is
exactly where centrality is needed), `(p^k)² ≤ |K:Z|`.

This is the `θχ`/`hθsq_le_qtot` datum of every X-chain step.  Centrality is essential: the bound
fails at `Z = [K,K]`. -/
theorem exists_source_primePow_centralBound_of_mem_xSet
    {p : ℕ} (hp : p.Prime) (hKp : IsPGroup p ↥K)
    {Z : Subgroup ↥L} (hZcentral : Z.subgroupOf K ≤ Subgroup.center ↥K)
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ xSet K Z) :
    ∃ k : ℕ, χ 1 = ((K.index * p ^ k : ℕ) : ℂ)
      ∧ (p ^ k) ^ 2 ≤ Nat.card (↥K ⧸ Z.subgroupOf K) := by
  have : Fintype ↥K := Fintype.ofFinite _
  obtain ⟨θ, -, -, rfl⟩ := hχ.1
  obtain ⟨k, hk⟩ := exists_primePow_natDegree_of_isPGroup hp hKp θ
  refine ⟨k, by rw [ClassFunction.induce_apply_one, hk]; push_cast; ring, ?_⟩
  obtain ⟨d, hd, hdsq⟩ := θ.isIrreducible.exists_degree_sq_le_index (Z.subgroupOf K) hZcentral
  have hdpk : d = p ^ k := by
    have hcast : (d : ℂ) = ((p ^ k : ℕ) : ℂ) := by rw [← hd, hk]
    exact_mod_cast hcast
  rw [← hdpk, ← Subgroup.index_eq_card]
  exact hdsq

/-- **Hypothesis (5.2) for the `(6.6)` set `𝒳 = 𝒮 − 𝒮(Z)`.**  `𝒳` is a conjugation-closed,
real-free, pairwise-orthogonal subset of `𝒮`, so every clause restricts from
`InducedFamilyTauData.hypothesis` at `X = ⊥` — with the same (5.3.a) two-element `R(χ)` for the
(irreducible) members and the same derived (5.2.e). -/
noncomputable def InducedFamilyTauData.xSetHypothesis {A₀ : Set ↥L}
    (RD : InducedFamilyTauData (G := G) A₀ K) (hodd : Odd (Nat.card ↥L))
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 → x ∈ A₀)
    {Z : Subgroup ↥L} (hirr : ∀ φ ∈ xSet K Z, IsIrreducibleCharacter φ) :
    OddOrder.Peterfalvi.S07.Hypothesis (L := ↥L) (G := G) (xSet K Z) A₀ :=
  RD.hypothesisOfSubfamily hodd hKsupp (xSet_subset Z) (xSet_closedUnderConjugate Z) hirr

@[simp] theorem InducedFamilyTauData.xSetHypothesis_tau {A₀ : Set ↥L}
    (RD : InducedFamilyTauData (G := G) A₀ K) (hodd : Odd (Nat.card ↥L))
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 → x ∈ A₀)
    {Z : Subgroup ↥L} (hirr : ∀ φ ∈ xSet K Z, IsIrreducibleCharacter φ) :
    (RD.xSetHypothesis hodd hKsupp hirr).tau = RD.tau := rfl

open scoped Classical in
/-- The `Finset` enumerating `𝒳 = 𝒮 − 𝒮(Z)` — the difference of the two kernel-filter images that
`sum_re_div_normSq_inducedKernelFamily_eq` sums over. -/
noncomputable def xSetFinset (K : Subgroup ↥L) [Invertible (Nat.card ↥K : ℂ)]
    (Z : Subgroup ↥L) : Finset (ClassFunction ↥L ℂ) :=
  (Finset.univ.filter (fun θ : IrreducibleCharacter ↥K =>
        (↑((⊥ : Subgroup ↥L).subgroupOf K) : Set ↥K) ⊆ OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥K ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥K)).image
      (fun θ => ClassFunction.induce K θ.toClassFunction) \
    (Finset.univ.filter (fun θ : IrreducibleCharacter ↥K =>
        (↑(Z.subgroupOf K) : Set ↥K) ⊆ OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥K ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥K)).image
      (fun θ => ClassFunction.induce K θ.toClassFunction)

omit [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] [K.Normal] in
open scoped Classical in
theorem coe_xSetFinset (Z : Subgroup ↥L) : ↑(xSetFinset K Z) = xSet K Z := by
  rw [xSetFinset, Finset.coe_sdiff, coe_kernelFilter_image_eq_inducedKernelFamily,
    coe_kernelFilter_image_eq_inducedKernelFamily]
  rfl

omit [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] [K.Normal] in
open scoped Classical in
theorem mem_xSetFinset {Z : Subgroup ↥L} {φ : ClassFunction ↥L ℂ} :
    φ ∈ xSetFinset K Z ↔ φ ∈ xSet K Z := by
  rw [← Finset.mem_coe, coe_xSetFinset]

omit [Invertible (Nat.card G : ℂ)] in
open scoped Classical in
/-- **Peterfalvi (6.6) degree-square sum, general kernel**:
`∑_{χ ∈ 𝒳} χ(1)² = |L:K| · (|K| − |K:Z|)`.

Since `𝒮(Z) ⊆ 𝒮` and `𝒳 = 𝒮 − 𝒮(Z)`, this is the difference of two instances of the general
`S(X)` weighted identity `sum_re_div_normSq_inducedKernelFamily_eq` (at `X = ⊥`, using
`|K ⧸ ⊥| = |K|`, and at `X = Z`), extracted by `Finset.sum_sdiff`.  The weights `‖χ‖²` cancel on
the `𝒳` side because its members are irreducible (`hX` — the book's `𝒳 ⊆ Irr L`), which is exactly
the case-B situation of the Sibley `sum_re_sq_Xset_eq_of_irreducible_X`: reducible members of `𝒮`
are allowed, as long as they lie in `𝒮(Z)`.

This is the `total` of the `X`-chain step data; the book's divisibility argument (p. 32) shows the
source degree `θ(1)²` divides it. -/
theorem sum_re_sq_xSet_eq (Z : Subgroup ↥L) [Z.Normal]
    (hX : ∀ χ ∈ xSet K Z, IsIrreducibleCharacter χ) :
    ∑ χ ∈ xSetFinset K Z, ((χ 1).re) ^ 2
      = (K.index : ℝ) * ((Nat.card ↥K : ℝ) - (Nat.card (↥K ⧸ Z.subgroupOf K) : ℝ)) := by
  set f : ClassFunction ↥L ℂ → ℝ :=
    fun χ => ((χ 1).re) ^ 2 / (ClassFunction.inner χ χ).re with hf
  set A := (Finset.univ.filter (fun θ : IrreducibleCharacter ↥K =>
        (↑((⊥ : Subgroup ↥L).subgroupOf K) : Set ↥K) ⊆ OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥K ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥K)).image
      (fun θ => ClassFunction.induce K θ.toClassFunction) with hA
  set B := (Finset.univ.filter (fun θ : IrreducibleCharacter ↥K =>
        (↑(Z.subgroupOf K) : Set ↥K) ⊆ OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥K ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥K)).image
      (fun θ => ClassFunction.induce K θ.toClassFunction) with hB
  -- `𝒮(Z) ⊆ 𝒮` at the `Finset` level: `⊥ ≤ ker θ` always.
  have hsub : B ⊆ A := by
    refine Finset.image_subset_image ?_
    intro θ hθ
    rw [Finset.mem_filter] at hθ ⊢
    refine ⟨hθ.1, ?_, hθ.2.2⟩
    intro x hx
    rw [Subgroup.bot_subgroupOf, Subgroup.coe_bot, Set.mem_singleton_iff] at hx
    subst hx
    exact OddOrder.Peterfalvi.S03.one_mem_characterKernel _
  have hsd := Finset.sum_sdiff (f := f) hsub
  have h0 := sum_re_div_normSq_inducedKernelFamily_eq (K := K) (⊥ : Subgroup ↥L)
  have hZ := sum_re_div_normSq_inducedKernelFamily_eq (K := K) Z
  have hbotcard : Nat.card (↥K ⧸ (⊥ : Subgroup ↥L).subgroupOf K) = Nat.card ↥K := by
    rw [Subgroup.bot_subgroupOf]
    exact Nat.card_congr (QuotientGroup.quotientBot (G := ↥K)).toEquiv
  rw [hbotcard] at h0
  -- on `𝒳` the weight is `1`, so `f` is the plain degree square there
  have hconv : ∀ χ ∈ A \ B, f χ = ((χ 1).re) ^ 2 := by
    intro χ hχ
    have hirr : IsIrreducibleCharacter χ := hX χ (mem_xSetFinset.mp hχ)
    simp only [hf, hirr.inner_self_eq_one, Complex.one_re, div_one]
  rw [xSetFinset, ← hA, ← hB, ← Finset.sum_congr rfl hconv, eq_sub_of_add_eq hsd, h0, hZ]
  ring

/-- **The base block `𝒮₀`**: the minimal-degree members of `𝒳`.  This is the equal-minimal-degree
prefix `{χ₁,…,χₖ}` of Peterfalvi (6.6) (p. 32), on which (1.1)+(1.4) supplies the base coherence
before the (5.6) adjoining of the strictly-higher-degree conjugate pairs.

`𝒮₀` must contain **all** minimal-degree members, not just one pair: the first (5.6) adjoining of
a pair of degree ratio `a` needs `2a < ∑_{𝒮₀} aⱼ²`, which fails at equal degree.

The Sibley `K = H` instance is `SibleyDadeHypothesis.xBaseBlock`. -/
def xBaseBlock (K : Subgroup ↥L) [Invertible (Nat.card ↥K : ℂ)] (Z : Subgroup ↥L) :
    Set (ClassFunction ↥L ℂ) :=
  {χ ∈ xSet K Z | ∀ ψ ∈ xSet K Z,
    (OddOrder.Peterfalvi.S03.characterDegree χ).re ≤
      (OddOrder.Peterfalvi.S03.characterDegree ψ).re}

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] [K.Normal] in
theorem xBaseBlock_subset (Z : Subgroup ↥L) : xBaseBlock K Z ⊆ xSet K Z :=
  fun _ hχ => hχ.1

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] [K.Normal] in
theorem xBaseBlock_finite (Z : Subgroup ↥L) : (xBaseBlock K Z).Finite :=
  (xSet_finite (K := K) Z).subset (xBaseBlock_subset Z)

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] [K.Normal] in
/-- The minimal-degree base block is closed under conjugation: `𝒳` is, and conjugation preserves
the (real) degree. -/
theorem xBaseBlock_closedUnderConjugate (Z : Subgroup ↥L) :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate (xBaseBlock K Z) := by
  intro χ hχ
  refine ⟨xSet_closedUnderConjugate (K := K) Z hχ.1, fun ψ hψ => ?_⟩
  have hre : (OddOrder.Peterfalvi.S03.characterDegree χ.conj).re =
      (OddOrder.Peterfalvi.S03.characterDegree χ).re := by simp
  rw [hre]
  exact hχ.2 ψ hψ

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] [K.Normal] in
/-- Any two base-block members have the same degree — the *equal*-degree family shape that the
§7 base engine `coherentEqualDegree` consumes. -/
theorem xBaseBlock_degree_re_eq {Z : Subgroup ↥L} {χ χ' : ClassFunction ↥L ℂ}
    (hχ : χ ∈ xBaseBlock K Z) (hχ' : χ' ∈ xBaseBlock K Z) :
    (OddOrder.Peterfalvi.S03.characterDegree χ).re =
      (OddOrder.Peterfalvi.S03.characterDegree χ').re :=
  le_antisymm (hχ.2 χ' hχ'.1) (hχ'.2 χ hχ.1)

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] [K.Normal] in
/-- A base-block anchor has natural degree no larger than any `𝒳`-member's. -/
theorem natDegree_le_of_xBaseBlock_anchor {Z : Subgroup ↥L}
    {χ₁ χ : ClassFunction ↥L ℂ} {d₁ d : ℕ}
    (hχ₁base : χ₁ ∈ xBaseBlock K Z) (hχX : χ ∈ xSet K Z)
    (hχ₁one : χ₁ 1 = (d₁ : ℂ)) (hχone : χ 1 = (d : ℂ)) :
    d₁ ≤ d := by
  have hre := hχ₁base.2 χ hχX
  rw [OddOrder.Peterfalvi.S03.characterDegree_def,
    OddOrder.Peterfalvi.S03.characterDegree_def, hχ₁one, hχone] at hre
  simpa using hre

omit [Fintype G] [Invertible (Nat.card G : ℂ)] in
/-- **`2 ≤ |𝒮₀|`.**  A minimal-degree member `χ` of the nonempty finite `𝒳` lies in `𝒮₀`, and so
does `χ̄ ≠ χ` (conjugation closure plus Peterfalvi (1.1): `|L|` odd forbids real members). -/
theorem two_le_xBaseBlock_ncard (hodd : Odd (Nat.card ↥L)) {Z : Subgroup ↥L}
    (hXne : (xSet K Z).Nonempty) :
    2 ≤ (xBaseBlock K Z).ncard := by
  obtain ⟨χ, hχX, hχmin⟩ := Set.exists_min_image (xSet K Z)
    (fun ψ => (OddOrder.Peterfalvi.S03.characterDegree ψ).re) (xSet_finite (K := K) Z) hXne
  have hχS₀ : χ ∈ xBaseBlock K Z := ⟨hχX, hχmin⟩
  have h1 : 1 < (xBaseBlock K Z).ncard :=
    (Set.one_lt_ncard (xBaseBlock_finite (K := K) Z)).mpr
      ⟨χ.conj, xBaseBlock_closedUnderConjugate (K := K) Z hχS₀, χ, hχS₀,
        xSet_hasNoRealCharacters (K := K) hodd Z hχX⟩
  omega

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] [K.Normal] in
/-- **Base-anchor index existence** (the X-chain step-data `i₁`/`hanchor`).  If `χmem` enumerates
the running prefix `pairUnion 𝒮₀ pair i` and `𝒮₀` is nonempty, some index `i₁` lands in `𝒮₀`
(the base block is contained in every prefix). -/
theorem exists_xBaseBlock_anchor_index {Z : Subgroup ↥L}
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {i k : ℕ}
    {χmem : Fin k → IrreducibleCharacter ↥L}
    (hrange : Set.range (fun j : Fin k => (χmem j : ClassFunction ↥L ℂ)) =
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (xBaseBlock K Z) pair i)
    (hne : (xBaseBlock K Z).Nonempty) :
    ∃ i₁ : Fin k, (χmem i₁ : ClassFunction ↥L ℂ) ∈ xBaseBlock K Z := by
  obtain ⟨φ, hφ⟩ := hne
  have hφpair : φ ∈ Set.range (fun j : Fin k => (χmem j : ClassFunction ↥L ℂ)) := by
    rw [hrange]
    exact OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inl hφ)
  obtain ⟨i₁, hi₁⟩ := hφpair
  exact ⟨i₁, by rw [show (χmem i₁ : ClassFunction ↥L ℂ) = φ from hi₁]; exact hφ⟩

omit [Fintype G] [Invertible (Nat.card G : ℂ)] in
/-- **Routine `𝒳`-member facts.**  For `χ ∈ 𝒳` — irreducible by the standing `hirr` (the book's
`𝒳 ⊆ Irr L`) and non-real because `|L|` is odd (Peterfalvi (1.1)) — the conjugate pair `{χ, χ̄}`
is orthonormal.

These are the per-member `hrealχ`/`hχχ`/`hχbarχbar`/`hχbarχ`/`hχχbar` inputs of the (5.6) engine
`S07.xAdjoinStepW_general`, for both the adjoined break and the accumulator members.  The Sibley
instance is `xMember_characterFacts_of_irreducible_X`. -/
theorem xMember_characterFacts (hodd : Odd (Nat.card ↥L)) {Z : Subgroup ↥L}
    (hirr : ∀ φ ∈ xSet K Z, IsIrreducibleCharacter φ)
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ xSet K Z) :
    ¬ ClassFunction.IsReal χ ∧
      ClassFunction.inner χ χ = 1 ∧
      ClassFunction.inner χ.conj χ.conj = 1 ∧
      ClassFunction.inner χ.conj χ = 0 ∧
      ClassFunction.inner χ χ.conj = 0 := by
  have hχirr : IsIrreducibleCharacter χ := hirr χ hχ
  have hconjirr : IsIrreducibleCharacter χ.conj := hχirr.conj
  have hreal : ¬ ClassFunction.IsReal χ := xSet_hasNoRealCharacters (K := K) hodd Z hχ
  have hne : (⟨χ.conj, hconjirr⟩ : IrreducibleCharacter ↥L) ≠ ⟨χ, hχirr⟩ :=
    fun h => hreal (congrArg Subtype.val h)
  refine ⟨hreal, hχirr.inner_self_eq_one, hconjirr.inner_self_eq_one, ?_, ?_⟩
  · simpa using
      (irreducibleCharacter_inner_eq_ite (⟨χ.conj, hconjirr⟩ : IrreducibleCharacter ↥L)
        ⟨χ, hχirr⟩).trans (if_neg hne)
  · simpa using
      (irreducibleCharacter_inner_eq_ite (⟨χ, hχirr⟩ : IrreducibleCharacter ↥L)
        ⟨χ.conj, hconjirr⟩).trans (if_neg (Ne.symm hne))

omit [Fintype G] [Invertible (Nat.card G : ℂ)] in
/-- **A break `χ ∈ 𝒳` outside an accumulator `S₁ ⊆ 𝒳` is orthogonal to it, as is `χ̄`** — the
`hχ_S1`/`hχbar_S1` inputs of the (5.6) engine.  Pure (5.2.c) pairwise orthogonality: distinct
members of `𝒳` are orthogonal. -/
theorem xMember_inner_eq_zero_of_notMem {Z : Subgroup ↥L}
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁X : S₁ ⊆ xSet K Z)
    {χ : ClassFunction ↥L ℂ} (hχX : χ ∈ xSet K Z) (hχS₁ : χ ∉ S₁) (hχbarS₁ : χ.conj ∉ S₁) :
    (∀ x ∈ S₁, ClassFunction.inner χ x = 0) ∧
      (∀ x ∈ S₁, ClassFunction.inner χ.conj x = 0) := by
  refine ⟨fun x hx => xSet_pairwise_orthogonal (K := K) Z hχX (hS₁X hx) ?_,
    fun x hx => xSet_pairwise_orthogonal (K := K) Z
      (xSet_closedUnderConjugate (K := K) Z hχX) (hS₁X hx) ?_⟩
  · rintro rfl; exact hχS₁ hx
  · rintro rfl; exact hχbarS₁ hx

/-- **Base coherence: `𝒮₀` is coherent** (Peterfalvi (6.6), p. 32: *"By (1.1) and (1.4),
`{χ₁, …, χₖ}` is coherent"*).

For a general kernel this is just the constant-degree theorem (5.7)
(`S07.coherent_of_constant_degree`) applied to the subfamily `𝒮₀ ⊆ 𝒮`: `𝒮₀` carries Hypothesis
(5.2) by `hypothesisOfSubfamily`, has `≥ 2` members (`two_le_xBaseBlock_ncard`), and is by
construction an *equal*-degree family (`xBaseBlock_degree_re_eq`, upgraded from real parts to
complex values because irreducible degrees are positive naturals).  Equal degree also makes every
member difference `K^#`-supported, hence in `ℤ[𝒮, A₀]` where `τ` is an isometry into `ℤ[Irr G]`.

The Sibley `K = H` instance is `xBaseBlock_isCoherent_of_irreducible_X`, which instead builds the
orthonormal target family from the Dade map (`coherentEqualDegree_fromDade`); routing through
(5.7) keeps this `τ`-general. -/
noncomputable def xBaseBlock_isCoherent {A₀ : Set ↥L}
    (RD : InducedFamilyTauData (G := G) A₀ K) (hodd : Odd (Nat.card ↥L))
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 → x ∈ A₀) (h1A : (1 : ↥L) ∉ A₀)
    {Z : Subgroup ↥L} (hirr : ∀ φ ∈ xSet K Z, IsIrreducibleCharacter φ)
    (hXne : (xSet K Z).Nonempty) :
    OddOrder.Peterfalvi.S07.IsCoherent RD.tau (xBaseBlock K Z) A₀ := by
  classical
  have hsub : xBaseBlock K Z ⊆ inducedKernelFamily K ⊥ :=
    (xBaseBlock_subset (K := K) Z).trans (xSet_subset (K := K) Z)
  have hirr₀ : ∀ φ ∈ xBaseBlock K Z, IsIrreducibleCharacter φ :=
    fun φ hφ => hirr φ (xBaseBlock_subset (K := K) Z hφ)
  -- equal degree, as complex values (irreducible degrees are positive naturals)
  have hconst : ∀ a ∈ xBaseBlock K Z, ∀ b ∈ xBaseBlock K Z, a 1 = b 1 := by
    intro a ha b hb
    obtain ⟨da, -, hda⟩ :=
      irreducibleCharacter_apply_one_eq_pos_natCast (⟨a, hirr₀ a ha⟩ : IrreducibleCharacter ↥L)
    obtain ⟨db, -, hdb⟩ :=
      irreducibleCharacter_apply_one_eq_pos_natCast (⟨b, hirr₀ b hb⟩ : IrreducibleCharacter ↥L)
    simp only [IrreducibleCharacter.coe_mk] at hda hdb
    have hre := xBaseBlock_degree_re_eq (K := K) ha hb
    rw [OddOrder.Peterfalvi.S03.characterDegree_def,
      OddOrder.Peterfalvi.S03.characterDegree_def, hda, hdb] at hre
    rw [hda, hdb]
    exact_mod_cast congrArg (Nat.cast : ℕ → ℂ) (by exact_mod_cast hre : da = db)
  -- equal degree ⟹ the member differences are `A₀`-supported
  have hsuppdiff : ∀ a ∈ xBaseBlock K Z, ∀ b ∈ xBaseBlock K Z,
      ((a - b : ClassFunction ↥L ℂ)).support ⊆ A₀ := by
    intro a ha b hb
    have h1 : (a - b : ClassFunction ↥L ℂ) = a - (1 : ℕ) • b := by simp
    rw [h1]
    exact inducedKernelFamily_scaledDiff_support hKsupp (hsub ha) (hsub hb)
      (by rw [hconst a ha b hb]; simp)
  have hmemspan : ∀ a ∈ xBaseBlock K Z, ∀ b ∈ xBaseBlock K Z,
      (a - b : ClassFunction ↥L ℂ) ∈
        OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (inducedKernelFamily K ⊥) A₀ :=
    fun a ha b hb => ⟨Submodule.sub_mem _ (Submodule.subset_span (hsub ha))
      (Submodule.subset_span (hsub hb)), hsuppdiff a ha b hb⟩
  have hdeg0 : ∀ a ∈ xBaseBlock K Z, a 1 ≠ 0 := by
    intro a ha
    obtain ⟨da, hpos, hda⟩ :=
      irreducibleCharacter_apply_one_eq_pos_natCast (⟨a, hirr₀ a ha⟩ : IrreducibleCharacter ↥L)
    simp only [IrreducibleCharacter.coe_mk] at hda
    rw [hda]
    exact_mod_cast hpos.ne'
  exact Classical.choice (OddOrder.Peterfalvi.S07.coherent_of_constant_degree
    (RD.hypothesisOfSubfamily hodd hKsupp hsub
      (xBaseBlock_closedUnderConjugate (K := K) Z) hirr₀)
    (xBaseBlock_finite (K := K) Z)
    (two_le_xBaseBlock_ncard (K := K) hodd hXne)
    (fun ζ hζ => (hirr₀ ζ hζ).inner_self_eq_one)
    (fun a ha b hb => RD.tau_mem_ZIrr (hmemspan a ha b hb))
    hconst hdeg0 h1A hsuppdiff)

open scoped Classical in
/-- **The Peterfalvi (6.6) X-chain fold for a general kernel, with an arbitrary `τ`.**

The book's proof of the coherence half (p. 32) sorts `𝒳` by degree, starts from the
equal-minimal-degree block `𝒮₀` and adjoins conjugate pairs of strictly larger degree one at a
time.  This packages that fold: given base coherence `h0` and a per-step adjoining `hstep`, `𝒳` is
coherent.

**Every ingredient is already `τ`-generic**, which is why no Dade datum appears:

* the conjugate-pair cover `exists_conjugatePairCover` is a statement about the *sets* `𝒳`, `𝒮₀`
  in an abstract group — no isometry at all;
* the accumulator fold `S07.coherentOfPairChainCover` takes `IsCoherent τ` for the ambient `τ`;
* the `𝒳`/`𝒮₀` side conditions (finite, conjugation-closed, real-free) are the general-kernel
  lemmas above.

The Sibley `K = H` instance is `Xset_isCoherent_from_adjoinSteps_withCover_of_irreducible_X`,
whose `τ` is pinned to `dadeIntegralCharacterMap`.  Per-step, the caller supplies the adjoining —
in the intended application through the `τ`-general (5.6) engine `S07.xAdjoinStepW_general`
(issue 0154), so the whole chain stays Dade-free (issue 0155). -/
noncomputable def xSet_isCoherent_of_adjoinSteps
    {A₀ : Set ↥L} {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G}
    (hodd : Odd (Nat.card ↥L)) {Z : Subgroup ↥L}
    (hirr : ∀ φ ∈ xSet K Z, IsIrreducibleCharacter φ) (hXne : (xSet K Z).Nonempty)
    (h0 : OddOrder.Peterfalvi.S07.IsCoherent τ (xBaseBlock K Z) A₀)
    (hstep : ∀ (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
      (χs : ℕ → IrreducibleCharacter ↥L),
      (∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ)) →
      (∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj) →
      (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆ xSet K Z) →
      (∀ j, j < N → Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (xBaseBlock K Z) pair j)) →
      (∀ j, j + 1 < N →
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
          (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re) →
      (∀ φ ∈ xSet K Z, φ ∈ xBaseBlock K Z ∨
        ∃ j, j < N ∧ φ ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j) →
      ∀ i, i < N → OddOrder.Peterfalvi.S07.IsCoherent τ
          (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (xBaseBlock K Z) pair i) A₀ →
        OddOrder.Peterfalvi.S07.IsCoherent τ
          (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (xBaseBlock K Z) pair i ∪
            {(χs i : ClassFunction ↥L ℂ), (χs i : ClassFunction ↥L ℂ).conj}) A₀) :
    OddOrder.Peterfalvi.S07.IsCoherent τ (xSet K Z) A₀ := by
  classical
  choose e pair N hpairχ hsurj hpairs hcoverIdx hpair0Raw hpair1Raw hdisj hmono using
    exists_conjugatePairCover (X := xSet K Z) (S₀ := xBaseBlock K Z)
      (xSet_finite (K := K) Z) (xSet_closedUnderConjugate (K := K) Z)
      (xSet_hasNoRealCharacters (K := K) hodd Z) hirr
      (xBaseBlock_closedUnderConjugate (K := K) Z)
  let χ0 : IrreducibleCharacter ↥L := ⟨Classical.choose hXne, hirr _ (Classical.choose_spec hXne)⟩
  let χs : ℕ → IrreducibleCharacter ↥L := fun i => if hi : i < N then hpairχ i hi else χ0
  have hpair0 : ∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ) := by
    intro i hi; rw [hpair0Raw i hi]; simp [χs, hi]
  have hpair1 : ∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj := by
    intro i hi; rw [hpair1Raw i hi]; simp [χs, hi]
  have hcover : ∀ φ ∈ xSet K Z, φ ∈ xBaseBlock K Z ∨
      ∃ j, j < N ∧ φ ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j := by
    intro φ hφ
    obtain ⟨i, hi⟩ := hsurj φ hφ
    have hci := hcoverIdx i
    rw [hi] at hci
    exact hci
  refine OddOrder.Peterfalvi.S07.coherentOfPairChainCover pair N
    (xBaseBlock_subset (K := K) Z) hpairs hcover h0 (fun i hi hcoh => ?_)
  rw [OddOrder.Peterfalvi.S07.pairUnion_succ_eq_union_pair (hpair0 i hi) (hpair1 i hi)]
  exact hstep pair N χs hpair0 hpair1 hpairs hdisj hmono hcover i hi hcoh

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] [K.Normal] in
/-- The running accumulator of the X-chain lies inside `𝒳`: it is the base block together with
the already-adjoined pairs, all of which are `𝒳`-subsets. -/
theorem pairUnion_subset_xSet {Z : Subgroup ↥L}
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {N i : ℕ} (hi : i ≤ N)
    (hpairs : ∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆ xSet K Z) :
    OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (xBaseBlock K Z) pair i ⊆ xSet K Z := by
  intro φ hφ
  rcases OddOrder.Peterfalvi.S07.mem_pairUnion.mp hφ with hbase | ⟨j, hji, hjpair⟩
  · exact xBaseBlock_subset (K := K) Z hbase
  · exact hpairs j (lt_of_lt_of_le hji hi) hjpair

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] [K.Normal] in
/-- The running accumulator is finite (a subset of the finite `𝒳`). -/
theorem pairUnion_finite {Z : Subgroup ↥L}
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {N i : ℕ} (hi : i ≤ N)
    (hpairs : ∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆ xSet K Z) :
    (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (xBaseBlock K Z) pair i).Finite :=
  (xSet_finite (K := K) Z).subset (pairUnion_subset_xSet hi hpairs)

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] [K.Normal] in
/-- **Tail-degree lower bound.**  An `𝒳`-member `φ` outside the running prefix has degree at least
that of the current pair head `(pair i).1`.

By the cover, `φ` lies in the base block or in some pair `j < N`; it is not in the base block
(which is contained in every prefix), so `φ ∈ pairSet pair j`, and `φ ∉ prefix` forces `j ≥ i`
(pairs below `i` lie in the prefix).  Degree-monotonicity of the enumeration then gives
`(pair i).1(1) ≤ (pair j).1(1) = φ(1)`.

This is the `htail_le` input of the book's degree bookkeeping — the step where cover completeness
is genuinely used.  The Sibley instance is `characterDegree_re_le_of_not_mem_pairUnion`; the proof
is pure combinatorics on the pair structure, so nothing is lost in the port. -/
theorem characterDegree_re_le_of_notMem_pairUnion {Z : Subgroup ↥L}
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {N : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L}
    (hpair0 : ∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ))
    (hpair1 : ∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj)
    (hmono : ∀ j, j + 1 < N →
      (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
        (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re)
    (hcover : ∀ φ ∈ xSet K Z, φ ∈ xBaseBlock K Z ∨
      ∃ j, j < N ∧ φ ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
    {i : ℕ} {φ : ClassFunction ↥L ℂ} (hφX : φ ∈ xSet K Z)
    (hφnot : φ ∉ OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (xBaseBlock K Z) pair i) :
    (OddOrder.Peterfalvi.S03.characterDegree (pair i).1).re ≤
      (OddOrder.Peterfalvi.S03.characterDegree φ).re := by
  have hchain : ∀ d a : ℕ, a + d < N →
      (OddOrder.Peterfalvi.S03.characterDegree (pair a).1).re ≤
        (OddOrder.Peterfalvi.S03.characterDegree (pair (a + d)).1).re := by
    intro d
    induction d with
    | zero => intro a _; simp
    | succ d ih =>
      intro a haN
      have h1 := ih a (by omega)
      have h2 := hmono (a + d) (by omega)
      have heq : a + (d + 1) = (a + d) + 1 := by omega
      rw [heq]
      exact le_trans h1 h2
  rcases hcover φ hφX with hbase | ⟨j, hjN, hjpair⟩
  · exact absurd (OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inl hbase)) hφnot
  · have hij : i ≤ j := by
      by_contra hlt
      push Not at hlt
      exact hφnot (OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inr ⟨j, hlt, hjpair⟩))
    have hdeg_ij : (OddOrder.Peterfalvi.S03.characterDegree (pair i).1).re ≤
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re := by
      have h := hchain (j - i) i (by omega)
      rwa [Nat.add_sub_cancel' hij] at h
    have hφdeg : (OddOrder.Peterfalvi.S03.characterDegree φ).re =
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re := by
      simp only [OddOrder.Peterfalvi.S07.pairSet, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hjpair
      rcases hjpair with h | h
      · rw [h]
      · rw [h, hpair1 j hjN, hpair0 j hjN]; simp
    rw [hφdeg]; exact hdeg_ij

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] in
/-- **The anchor-generation condition `hSgen`.**  If every member of `S₁` has degree a natural
multiple of the anchor's, then `ℤ[S₁] ≤ ℤ⟨ℤ[S₁, A₀] ∪ {χ₁}⟩`: write `φ = (φ − d·χ₁) + d·χ₁`,
where the bracket is `K^#`-supported by `inducedKernelFamily_scaledDiff_support` (matching degrees)
and hence lies in `ℤ[S₁, A₀]`.

This is the `hSgen` input of `xAdjoinStep_of_degreeRatios`; in the (6.6) application the degree
multiples are the `p`-powers of `exists_primePow_degree_ratio_of_xBaseBlock_anchor`. -/
theorem span_le_span_zSupportedSpan_union_anchor {A₀ : Set ↥L}
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 → x ∈ A₀)
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ inducedKernelFamily K ⊥)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ S₁)
    (hratio : ∀ φ ∈ S₁, ∃ d : ℕ, φ 1 = (d : ℂ) * χ₁ 1) :
    Submodule.span ℤ S₁ ≤ Submodule.span ℤ
      (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁ A₀ ∪ {χ₁}) := by
  rw [Submodule.span_le]
  intro φ hφ
  obtain ⟨d, hd⟩ := hratio φ hφ
  have hdiff : (φ - d • χ₁ : ClassFunction ↥L ℂ) ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁ A₀ :=
    ⟨Submodule.sub_mem _ (Submodule.subset_span hφ)
      (nsmul_mem (Submodule.subset_span hχ₁) _),
     inducedKernelFamily_scaledDiff_support hKsupp (hS₁sub hφ) (hS₁sub hχ₁) hd⟩
  have hsplit : φ = (φ - d • χ₁ : ClassFunction ↥L ℂ) + d • χ₁ := by abel
  rw [hsplit]
  refine Submodule.add_mem _
    (Submodule.subset_span (Set.mem_union_left _ hdiff))
    (nsmul_mem (Submodule.subset_span (Set.mem_union_right _ ?_)) _)
  exact Set.mem_singleton _

open scoped Classical in
/-- **Peterfalvi (6.6) per-step adjoining for a general kernel, with an arbitrary `τ`.**

Adjoin the conjugate pair `{χ, χ̄}` of an `𝒳`-member to a coherent accumulator `S₁ ⊆ 𝒳`, given the
book's degree bookkeeping (p. 32): an anchor `χmem i₁ ∈ S₁` of degree `1` relative to the family,
member degree ratios `χmem j (1) = deg j · χmem i₁ (1)`, the break ratio `χ(1) = a · χmem i₁ (1)`,
and the (5.6) inequality `2a < ∑ deg j²`.

This is the general-kernel, `τ`-general analogue of the Sibley
`xAdjoinStepInput_of_memberFamily_degreeRatios` chain; it feeds
`S07.xAdjoinStepW_general` (issue 0154) directly, so no `XAdjoinStepInput`/`xAdjoinStep` layer is
needed.  Everything it supplies to that engine comes from general-kernel facts:

* member/break orthonormality — `xMember_characterFacts`, `xMember_inner_eq_zero_of_notMem`;
* supported differences — `inducedKernelFamily_scaledDiff_support` (degree ratios make
  `χmem j − deg j · χmem i₁` and `χ − a · χmem i₁` vanish off `K^#`);
* the (5.2.d) image families `R(·)` and their (5.2.e) orthogonality — `InducedFamilyImageData`;
* the per-member decomposition `Dmem` — `S07.memberExtensionDecomposition_general`, whose
  `imageFamily` is definitionally `R(χmem j)` and whose `tau1` is the accumulator extension. -/
noncomputable def xAdjoinStep_of_degreeRatios {A₀ : Set ↥L}
    (RD : InducedFamilyTauData (G := G) A₀ K) (hodd : Odd (Nat.card ↥L))
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 → x ∈ A₀) (h1A : (1 : ↥L) ∉ A₀)
    {Z : Subgroup ↥L} (hirr : ∀ φ ∈ xSet K Z, IsIrreducibleCharacter φ)
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁X : S₁ ⊆ xSet K Z)
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁)
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent RD.tau S₁ A₀)
    {χ : ClassFunction ↥L ℂ} (hχX : χ ∈ xSet K Z) (hχS₁ : χ ∉ S₁) (hχbarS₁ : χ.conj ∉ S₁)
    {ι : Type*} (s : Finset ι) (χmem : ι → ClassFunction ↥L ℂ) (deg : ι → ℕ) (i₁ : ι)
    (hi₁ : i₁ ∈ s) (hmemS1 : ∀ j ∈ s, χmem j ∈ S₁)
    (hmeminj : ∀ j ∈ s, ∀ l ∈ s, χmem j = χmem l → j = l)
    {a : ℕ} (ha1 : deg i₁ = 1)
    (hratio : ∀ j ∈ s, χmem j 1 = (deg j : ℂ) * χmem i₁ 1)
    (hχratio : χ 1 = (a : ℂ) * χmem i₁ 1)
    (hDeg : 2 * (a : ℝ) < ∑ j ∈ s, ((deg j : ℝ)) ^ 2)
    (hSgen : Submodule.span ℤ S₁ ≤ Submodule.span ℤ
      (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁ A₀ ∪ {χmem i₁})) :
    OddOrder.Peterfalvi.S07.IsCoherent RD.tau (S₁ ∪ {χ, χ.conj}) A₀ := by
  classical
  have hXsub : xSet K Z ⊆ inducedKernelFamily K ⊥ := xSet_subset (K := K) Z
  have hS₁sub : S₁ ⊆ inducedKernelFamily K ⊥ := hS₁X.trans hXsub
  have hχfam : χ ∈ inducedKernelFamily K ⊥ := hXsub hχX
  obtain ⟨hχreal, hχχ, hχbarχbar, hχbarχ, hχχbar⟩ :=
    xMember_characterFacts (K := K) hodd hirr hχX
  obtain ⟨hχ_S1, hχbar_S1⟩ :=
    xMember_inner_eq_zero_of_notMem (K := K) hS₁X hχX hχS₁ hχbarS₁
  -- members: orthonormality
  have hmemX : ∀ j ∈ s, χmem j ∈ xSet K Z := fun j hj => hS₁X (hmemS1 j hj)
  have hmemortho : ∀ j ∈ s, ∀ l ∈ s,
      ClassFunction.inner (χmem j) (χmem l) = if j = l then ((1 : ℝ) : ℂ) else 0 := by
    intro j hj l hl
    by_cases hjl : j = l
    · subst hjl
      simpa using (hirr _ (hmemX j hj)).inner_self_eq_one
    · rw [if_neg hjl]
      exact xSet_pairwise_orthogonal (K := K) Z (hmemX j hj) (hmemX l hl)
        (fun h => hjl (hmeminj j hj l hl h))
  -- supported differences from the degree ratios
  have hmemdegdiffmem : ∀ j ∈ s, χmem j - deg j • χmem i₁ ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁ A₀ := by
    intro j hj
    refine ⟨Submodule.sub_mem _ (Submodule.subset_span (hmemS1 j hj))
      (nsmul_mem (Submodule.subset_span (hmemS1 i₁ hi₁)) _), ?_⟩
    exact inducedKernelFamily_scaledDiff_support hKsupp (hS₁sub (hmemS1 j hj))
      (hS₁sub (hmemS1 i₁ hi₁)) (hratio j hj)
  have hadiffmem : χ - a • χmem i₁ ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (inducedKernelFamily K ⊥) A₀ := by
    refine ⟨Submodule.sub_mem _ (Submodule.subset_span hχfam)
      (nsmul_mem (Submodule.subset_span (hS₁sub (hmemS1 i₁ hi₁))) _), ?_⟩
    exact inducedKernelFamily_scaledDiff_support hKsupp hχfam
      (hS₁sub (hmemS1 i₁ hi₁)) hχratio
  have hdiffmem : χ - χ.conj ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (inducedKernelFamily K ⊥) A₀ :=
    conjDiff_mem_zSupportedSpan hKsupp hχfam
  -- per-member (5.2.d) decompositions and their (5.2.e) orthogonality to `R(χ)`
  -- (5.2.d)/(5.2.e) for the members of `𝒳`: **derived** from the (5.2.b) isometry, since every
  -- `𝒳`-member is irreducible and non-real (issue 0156).  `hyp.difference_image` is the (5.3.a)
  -- signed pair `τ(φ − φ̄) = ε·(μ − ν)`; `toOrthonormalImage` puts it in the `{ε·μ, −ε·ν}` shape
  -- the (5.6) engine consumes.
  let hyp := RD.xSetHypothesis hodd hKsupp hirr
  have hmemconjsupp : ∀ j ∈ s, ((χmem j).conj - χmem j).support ⊆ A₀ := by
    intro j hj
    have h := (conjDiff_mem_zSupportedSpan hKsupp (hS₁sub (hmemS1 j hj))).2
    have hneg : (χmem j).conj - χmem j = -(χmem j - (χmem j).conj) := by abel
    rw [hneg, ClassFunction.support_neg]
    exact h
  refine OddOrder.Peterfalvi.S07.xAdjoinStepW_general (Samb := inducedKernelFamily K ⊥)
    hS₁ hS₁sub RD.adjoinHisom χ (hyp.difference_image hχX).toOrthonormalImage
    hχχ hχbarχbar hχχbar hχbarχ hχ_S1 hχbar_S1
    s χmem deg i₁ hi₁ hmemdegdiffmem hmemS1 (fun _ => (1 : ℝ)) (fun _ _ => one_pos)
    hmemortho (a := a)
    (fun j hj => OddOrder.Peterfalvi.S07.memberExtensionDecomposition_general hS₁
      (hyp.difference_image (hmemX j hj)).toOrthonormalImage (hmemconjsupp j hj)
      (hmemS1 j hj) (hS₁conj (hmemS1 j hj))
      (hS₁.extension_mem_ZIrr _ (Submodule.subset_span (hmemS1 j hj)))
      ((xMember_characterFacts (K := K) hodd hirr (hmemX j hj)).2.2.2.2))
    ?_ (fun _ _ => rfl) hdiffmem hadiffmem
    (RD.tau_mem_ZIrr hadiffmem) ha1 (by simpa using hDeg) hSgen ?_
  · -- (5.2.e): `χmem j ⊥ {χ, χ̄}` since `χ, χ̄ ∉ S₁` and `𝒳` is pairwise orthogonal
    intro j hj
    exact OddOrder.Peterfalvi.S07.CharacterDifferenceImage.toOrthonormalImage_orthogonal _ _
      (hyp.difference_images_orthogonal (hmemX j hj) hχX
        (xSet_pairwise_orthogonal (K := K) Z (hmemX j hj) hχX
          (fun h => hχS₁ (h ▸ hmemS1 j hj)))
        (xSet_pairwise_orthogonal (K := K) Z (hmemX j hj)
          (xSet_closedUnderConjugate (K := K) Z hχX)
          (fun h => hχbarS₁ (h ▸ hmemS1 j hj))))
  · -- the adjoined pair's supported lattice is generated by the two anchored differences
    have hchi1_ne : (χmem i₁) 1 ≠ 0 := by
      obtain ⟨d, hd, hd1⟩ := irreducibleCharacter_apply_one_eq_pos_natCast
        (⟨χmem i₁, hirr _ (hmemX i₁ hi₁)⟩ : IrreducibleCharacter ↥L)
      simp only [IrreducibleCharacter.coe_mk] at hd1
      rw [hd1]; exact_mod_cast hd.ne'
    exact OddOrder.Peterfalvi.S07.zSupportedSpan_adjoinPair_subset_span_of_anchorGeneration
      (L := ↥L) (S₁ := S₁) (A := A₀) (χ := χ) (chibar := χ.conj) (chi1 := χmem i₁) (a := a)
      hSgen hχratio
      (OddOrder.Peterfalvi.S07.irreducibleCharacter_conj_apply_one
        (⟨χ, hirr χ hχX⟩ : IrreducibleCharacter ↥L))
      hchi1_ne h1A

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] [K.Normal] in
/-- The running accumulator is closed under conjugation: the base block is
(`xBaseBlock_closedUnderConjugate`), and every adjoined `pairSet pair j = {χⱼ, χ̄ⱼ}` is by
construction a conjugate pair.  This is the `hS₁conj` input of `xAdjoinStep_of_degreeRatios`. -/
theorem pairUnion_closedUnderConjugate {Z : Subgroup ↥L}
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {N i : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L} (hi : i ≤ N)
    (hpair0 : ∀ j, j < N → (pair j).1 = (χs j : ClassFunction ↥L ℂ))
    (hpair1 : ∀ j, j < N → (pair j).2 = (χs j : ClassFunction ↥L ℂ).conj) :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (xBaseBlock K Z) pair i) := by
  intro φ hφ
  rcases OddOrder.Peterfalvi.S07.mem_pairUnion.mp hφ with hbase | ⟨j, hji, hjpair⟩
  · exact OddOrder.Peterfalvi.S07.mem_pairUnion.mpr
      (Or.inl (xBaseBlock_closedUnderConjugate (K := K) Z hbase))
  · have hjN : j < N := lt_of_lt_of_le hji hi
    refine OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inr ⟨j, hji, ?_⟩)
    simp only [OddOrder.Peterfalvi.S07.pairSet, Set.mem_insert_iff, Set.mem_singleton_iff]
      at hjpair ⊢
    rcases hjpair with h | h
    · exact Or.inr (by rw [h, hpair0 j hjN, hpair1 j hjN])
    · exact Or.inl (by rw [h, hpair1 j hjN, hpair0 j hjN]; simp)

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] [K.Normal] in
/-- The minimal-degree base block of a nonempty `𝒳` is nonempty. -/
theorem xBaseBlock_nonempty {Z : Subgroup ↥L} (hXne : (xSet K Z).Nonempty) :
    (xBaseBlock K Z).Nonempty := by
  obtain ⟨χ, hχX, hχmin⟩ := Set.exists_min_image (xSet K Z)
    (fun ψ => (OddOrder.Peterfalvi.S03.characterDegree ψ).re) (xSet_finite (K := K) Z) hXne
  exact ⟨χ, hχX, hχmin⟩

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] [K.Normal] in
/-- An `𝒳`-member *outside* the minimal-degree base block has degree **strictly** larger than a
base-block anchor's: it is `≥` by minimality, and equality would put it in the base block.  This is
the `hlt` input of the (5.6) degree bookkeeping. -/
theorem natDegree_lt_of_xBaseBlock_anchor_of_notMem {Z : Subgroup ↥L}
    {χ₁ χ : ClassFunction ↥L ℂ} {d₁ d : ℕ}
    (hχ₁base : χ₁ ∈ xBaseBlock K Z) (hχX : χ ∈ xSet K Z) (hχnotbase : χ ∉ xBaseBlock K Z)
    (hχ₁one : χ₁ 1 = (d₁ : ℂ)) (hχone : χ 1 = (d : ℂ)) :
    d₁ < d := by
  have hle : d₁ ≤ d := natDegree_le_of_xBaseBlock_anchor (K := K) hχ₁base hχX hχ₁one hχone
  have hne : d₁ ≠ d := by
    intro hEq
    refine hχnotbase ⟨hχX, fun ψ hψ => ?_⟩
    have h1 : (OddOrder.Peterfalvi.S03.characterDegree χ).re = (d : ℝ) := by
      rw [OddOrder.Peterfalvi.S03.characterDegree_def, hχone]; simp
    have h2 : (OddOrder.Peterfalvi.S03.characterDegree χ₁).re = (d₁ : ℝ) := by
      rw [OddOrder.Peterfalvi.S03.characterDegree_def, hχ₁one]; simp
    have hmin := hχ₁base.2 ψ hψ
    rw [h2, hEq, ← h1] at hmin
    exact hmin
  omega

open scoped Classical in
/-- **Peterfalvi (6.6), coherence half, for a general kernel `K`** (pp. 31–32):

> Let `Z` be a normal subgroup of `L` with `1 ≠ Z ⊆ Z(K)` and `𝒳 = 𝒮 − 𝒮(Z) ⊆ Irr L`.
> Then `𝒳` is coherent.

This is the general-kernel, `τ`-general form of the Sibley `K = H` instance
`S08_CoherenceBasic.Xset_isCoherent_of_irreducible_X`, whose `τ` is pinned to the Dade map.  The
proof is the book's:

* the base block `𝒮₀` of minimal-degree members is coherent by (5.7) (`xBaseBlock_isCoherent`);
* conjugate pairs of strictly larger degree are adjoined one at a time along the degree-sorted
  cover (`xSet_isCoherent_of_adjoinSteps`), each step by (5.6)
  (`xAdjoinStep_of_degreeRatios`);
* the (5.6) hypothesis `2a < ∑ deg²` at each step comes from the p. 32 divisibility argument:
  every member has degree `|L:K|·p^k`, so all degree ratios over the anchor are `p`-powers; the
  degree-square sum over `𝒳` is `|L:K|·(|K| − |K:Z|)` (`sum_re_sq_xSet_eq`), the tail members have
  degree at least the adjoined one (`characterDegree_re_le_of_notMem_pairUnion`), and [Is] Cor 2.30
  against the **central** `Z` bounds the source degree by `θ(1)² ≤ |K:Z|`
  (`exists_source_primePow_centralBound_of_mem_xSet`) — whence `χ(1)² ∣ D` and the gap.

The hypotheses beyond `𝒳 ⊆ Irr L` are exactly the (6.4)/(6.5) context: `K` is a `p`-group for an
odd prime `p` coprime to `|L:K|` (which `L = K ⋊ W₁` supplies), and `Z ⊆ Z(K)`.  Centrality is
essential — the [Is] Cor 2.30 bound, hence the whole divisibility argument, fails at `Z = [K,K]`. -/
noncomputable def xSet_isCoherent_of_irreducible_X {A₀ : Set ↥L}
    (RD : InducedFamilyTauData (G := G) A₀ K) (hodd : Odd (Nat.card ↥L))
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 → x ∈ A₀) (h1A : (1 : ↥L) ∉ A₀)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hKp : IsPGroup p ↥K)
    (hidx_p : Nat.Coprime K.index p)
    {Z : Subgroup ↥L} [Z.Normal] (hZcentral : Z.subgroupOf K ≤ Subgroup.center ↥K)
    (hirr : ∀ φ ∈ xSet K Z, IsIrreducibleCharacter φ) (hXne : (xSet K Z).Nonempty) :
    OddOrder.Peterfalvi.S07.IsCoherent RD.tau (xSet K Z) A₀ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype ↥K := Fintype.ofFinite _
  have hidxpos : 0 < K.index := Nat.pos_of_ne_zero K.index_ne_zero_of_finite
  have hp1 : 1 < p := hp.one_lt
  -- (1) the `p`-power exponent of every `𝒳`-degree
  have hdegtot : ∀ φ : ClassFunction ↥L ℂ, ∃ k : ℕ,
      φ ∈ xSet K Z → φ 1 = ((K.index * p ^ k : ℕ) : ℂ) := by
    intro φ
    by_cases hφ : φ ∈ xSet K Z
    · obtain ⟨k, hk⟩ := exists_index_primePow_degree_of_mem_inducedKernelFamily (K := K) hp hKp
        (xSet_subset (K := K) Z hφ)
      exact ⟨k, fun _ => hk⟩
    · exact ⟨0, fun h => absurd h hφ⟩
  choose e he using hdegtot
  -- (2) a base-block anchor minimises the exponent, so all degree ratios over it are `p`-powers
  have hexp_anchor : ∀ χ₁ ∈ xBaseBlock K Z, ∀ φ ∈ xSet K Z, e χ₁ ≤ e φ := by
    intro χ₁ h1 φ hφ
    have hle := natDegree_le_of_xBaseBlock_anchor (K := K) h1 hφ
      (he χ₁ (xBaseBlock_subset (K := K) Z h1)) (he φ hφ)
    exact (Nat.pow_le_pow_iff_right hp1).mp (Nat.le_of_mul_le_mul_left hle hidxpos)
  have hratio_gen : ∀ χ₁ ∈ xBaseBlock K Z, ∀ φ ∈ xSet K Z,
      φ 1 = ((p ^ (e φ - e χ₁) : ℕ) : ℂ) * χ₁ 1 := by
    intro χ₁ h1 φ hφ
    have hle := hexp_anchor χ₁ h1 φ hφ
    rw [he φ hφ, he χ₁ (xBaseBlock_subset (K := K) Z h1), ← Nat.cast_mul]
    congr 1
    rw [← mul_assoc, mul_comm (p ^ (e φ - e χ₁)) K.index, mul_assoc, ← pow_add]
    congr 2
    omega
  -- (3) the degree-square sum `total = |L:K|·(|K| − |K:Z|)` and its `p`-power divisor `|K:Z|`
  have hqdvdK : Nat.card (↥K ⧸ Z.subgroupOf K) ∣ Nat.card ↥K := by
    rw [← (Z.subgroupOf K).index_eq_card]
    exact (Z.subgroupOf K).index_dvd_card
  choose nK hcardK using hKp.exists_card_eq
  choose mq hmqle hqpow using (Nat.dvd_prime_pow hp).mp (hcardK ▸ hqdvdK)
  have hqle : Nat.card (↥K ⧸ Z.subgroupOf K) ≤ Nat.card ↥K := Nat.le_of_dvd Nat.card_pos hqdvdK
  have hqdvdtot : Nat.card (↥K ⧸ Z.subgroupOf K) ∣
      K.index * (Nat.card ↥K - Nat.card (↥K ⧸ Z.subgroupOf K)) :=
    (Nat.dvd_sub hqdvdK dvd_rfl).mul_left K.index
  have hcq : K.index * (Nat.card ↥K - Nat.card (↥K ⧸ Z.subgroupOf K)) =
      Nat.card (↥K ⧸ Z.subgroupOf K) *
        (K.index * (Nat.card ↥K - Nat.card (↥K ⧸ Z.subgroupOf K)) /
          Nat.card (↥K ⧸ Z.subgroupOf K)) :=
    (Nat.mul_div_cancel' hqdvdtot).symm
  have hXsumReal : ∑ φ ∈ xSetFinset K Z, ((K.index * p ^ e φ : ℕ) : ℝ) ^ 2 =
      ((K.index * (Nat.card ↥K - Nat.card (↥K ⧸ Z.subgroupOf K)) : ℕ) : ℝ) := by
    have hcast : ((K.index * (Nat.card ↥K - Nat.card (↥K ⧸ Z.subgroupOf K)) : ℕ) : ℝ) =
        (K.index : ℝ) * ((Nat.card ↥K : ℝ) - (Nat.card (↥K ⧸ Z.subgroupOf K) : ℝ)) := by
      push_cast [Nat.cast_sub hqle]; ring
    rw [hcast, ← sum_re_sq_xSet_eq (K := K) Z hirr]
    refine Finset.sum_congr rfl fun φ hφ => ?_
    rw [he φ (mem_xSetFinset.mp hφ), Complex.natCast_re]
  -- (4) fold the X-chain: base coherence plus one (5.6) adjoining per step
  refine xSet_isCoherent_of_adjoinSteps (K := K) hodd hirr hXne
    (xBaseBlock_isCoherent RD hodd hKsupp h1A hirr hXne) ?_
  intro pair N χs hpair0 hpair1 hpairs hdisj hmono hcover i hi hcoh
  have hS₁X : OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (xBaseBlock K Z) pair i ⊆ xSet K Z :=
    pairUnion_subset_xSet (K := K) hi.le hpairs
  have hS₁sub : OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (xBaseBlock K Z) pair i ⊆
      inducedKernelFamily K ⊥ := hS₁X.trans (xSet_subset (K := K) Z)
  -- the adjoined pair `{χ, χ̄}`
  have hχpair : (χs i : ClassFunction ↥L ℂ) ∈
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair i := by
    simp [OddOrder.Peterfalvi.S07.pairSet, hpair0 i hi]
  have hχbarpair : (χs i : ClassFunction ↥L ℂ).conj ∈
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair i := by
    simp [OddOrder.Peterfalvi.S07.pairSet, hpair1 i hi]
  have hχX : (χs i : ClassFunction ↥L ℂ) ∈ xSet K Z := hpairs i hi hχpair
  have hχS₁ : (χs i : ClassFunction ↥L ℂ) ∉
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (xBaseBlock K Z) pair i :=
    fun h => (Set.disjoint_left.mp (hdisj i hi)) hχpair h
  have hχbarS₁ : (χs i : ClassFunction ↥L ℂ).conj ∉
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (xBaseBlock K Z) pair i :=
    fun h => (Set.disjoint_left.mp (hdisj i hi)) hχbarpair h
  have hχnotbase : (χs i : ClassFunction ↥L ℂ) ∉ xBaseBlock K Z :=
    fun hb => hχS₁ (OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inl hb))
  -- (5) enumerate the accumulator and pick a base-block anchor inside it
  choose k χmem hχinj hrange using exists_finEnum_irreducible
    (pairUnion_finite (K := K) hi.le hpairs) (fun φ hφ => hirr φ (hS₁X hφ))
  have hmemS1 : ∀ j : Fin k, (χmem j : ClassFunction ↥L ℂ) ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (xBaseBlock K Z) pair i := by
    intro j; rw [← hrange]; exact Set.mem_range_self j
  have hmemX : ∀ j : Fin k, (χmem j : ClassFunction ↥L ℂ) ∈ xSet K Z :=
    fun j => hS₁X (hmemS1 j)
  choose i₁ hi₁base using
    exists_xBaseBlock_anchor_index (K := K) hrange (xBaseBlock_nonempty (K := K) hXne)
  have hanchorX : (χmem i₁ : ClassFunction ↥L ℂ) ∈ xSet K Z :=
    xBaseBlock_subset (K := K) Z hi₁base
  -- (6) degree data over the anchor
  have hχone : (χs i : ClassFunction ↥L ℂ) 1 =
      ((K.index * p ^ e (χs i : ClassFunction ↥L ℂ) : ℕ) : ℂ) := he _ hχX
  have hχ₁one : (χmem i₁ : ClassFunction ↥L ℂ) 1 =
      ((K.index * p ^ e (χmem i₁ : ClassFunction ↥L ℂ) : ℕ) : ℂ) := he _ hanchorX
  have hmemone : ∀ j ∈ (Finset.univ : Finset (Fin k)), (χmem j : ClassFunction ↥L ℂ) 1 =
      ((K.index * p ^ e (χmem j : ClassFunction ↥L ℂ) : ℕ) : ℂ) := fun j _ => he _ (hmemX j)
  have hratio : ∀ j ∈ (Finset.univ : Finset (Fin k)), (χmem j : ClassFunction ↥L ℂ) 1 =
      ((p ^ (e (χmem j : ClassFunction ↥L ℂ) - e (χmem i₁ : ClassFunction ↥L ℂ)) : ℕ) : ℂ) *
        (χmem i₁ : ClassFunction ↥L ℂ) 1 := fun j _ => hratio_gen _ hi₁base _ (hmemX j)
  have hχratio : (χs i : ClassFunction ↥L ℂ) 1 =
      ((p ^ (e (χs i : ClassFunction ↥L ℂ) - e (χmem i₁ : ClassFunction ↥L ℂ)) : ℕ) : ℂ) *
        (χmem i₁ : ClassFunction ↥L ℂ) 1 := hratio_gen _ hi₁base _ hχX
  -- (7) the tail of `𝒳` beyond the accumulator, and the head/tail split of the degree-square sum
  have hcoeinj : Function.Injective fun j : Fin k => (χmem j : ClassFunction ↥L ℂ) :=
    Subtype.val_injective.comp hχinj
  have hsum := natSum_partition_of_realSum (xSetFinset K Z) (fun φ => K.index * p ^ e φ)
    (K.index * (Nat.card ↥K - Nat.card (↥K ⧸ Z.subgroupOf K))) hXsumReal hcoeinj
    (fun j => mem_xSetFinset.mpr (hmemX j))
  have htail_le : ∀ φ ∈ xSetFinset K Z \
      Finset.univ.image fun j : Fin k => (χmem j : ClassFunction ↥L ℂ),
      K.index * p ^ e (χs i : ClassFunction ↥L ℂ) ≤ K.index * p ^ e φ := by
    intro φ hφ
    rw [Finset.mem_sdiff] at hφ
    have hφX : φ ∈ xSet K Z := mem_xSetFinset.mp hφ.1
    have hφnot : φ ∉ OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (xBaseBlock K Z) pair i := by
      rw [← hrange]
      rintro ⟨j, rfl⟩
      exact hφ.2 (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
    have hdeg := characterDegree_re_le_of_notMem_pairUnion (K := K) hpair0 hpair1 hmono
      hcover hφX hφnot
    rw [hpair0 i hi, OddOrder.Peterfalvi.S03.characterDegree_def,
      OddOrder.Peterfalvi.S03.characterDegree_def, hχone, he φ hφX,
      Complex.natCast_re, Complex.natCast_re] at hdeg
    exact_mod_cast hdeg
  -- (8) the p. 32 divisibility: `χ(1)² ∣ D`, hence the (5.6) gap `2a < ∑ deg²`
  choose kχ hkχ hkχsq using
    exists_source_primePow_centralBound_of_mem_xSet (K := K) hp hKp hZcentral hχX
  have hkχe : kχ = e (χs i : ClassFunction ↥L ℂ) := by
    have hnat : K.index * p ^ kχ = K.index * p ^ e (χs i : ClassFunction ↥L ℂ) := by
      exact_mod_cast hkχ.symm.trans hχone
    exact Nat.pow_right_injective hp.two_le (Nat.eq_of_mul_eq_mul_left hidxpos hnat)
  rw [hkχe] at hkχsq
  have hidx_head : K.index * K.index ∣
      ∑ j : Fin k, (K.index * p ^ e (χmem j : ClassFunction ↥L ℂ)) *
        (K.index * p ^ e (χmem j : ClassFunction ↥L ℂ)) :=
    sq_dvd_natDegreeSquareSum_of_commonIndex rfl fun _ _ => rfl
  have hdvd := OddOrder.Peterfalvi.S07.sq_dvd_head_of_commonIndex_primePower_sums
    (xSetFinset K Z \ Finset.univ.image fun j : Fin k => (χmem j : ClassFunction ↥L ℂ))
    (show 2 ≤ p by omega) hidxpos (θ := p ^ e (χs i : ClassFunction ↥L ℂ)) rfl
    (θdeg := fun φ => p ^ e φ) (fun _ _ => rfl) htail_le hsum hqpow
    (by simpa [pow_two] using hkχsq) hcq hidx_head rfl
    (coprime_commonIndex_primePower hidx_p rfl)
  have hDpos := natDegreeSquareSum_pos_of_memberFamily (χmem := χmem) (i₁ := i₁)
    (Finset.mem_univ i₁) hmemone rfl
  have hlt := natDegree_lt_of_xBaseBlock_anchor_of_notMem (K := K) hi₁base hχX hχnotbase
    hχ₁one hχone
  have hDeg := normalizedDegreeGap_of_natDegreeSumCommonIndexPrimePowerGap
    (χ := χs i) (χ₁ := χmem i₁) (χmem := χmem) hχratio hratio hχone hχ₁one hmemone rfl
    hp3 hlt rfl rfl rfl rfl hdvd hDpos
  -- (9) one (5.6) adjoining step
  exact xAdjoinStep_of_degreeRatios RD hodd hKsupp h1A hirr hS₁X
    (pairUnion_closedUnderConjugate (K := K) hi.le hpair0 hpair1) hcoh hχX hχS₁ hχbarS₁
    Finset.univ (fun j => (χmem j : ClassFunction ↥L ℂ))
    (fun j => p ^ (e (χmem j : ClassFunction ↥L ℂ) - e (χmem i₁ : ClassFunction ↥L ℂ))) i₁
    (Finset.mem_univ i₁) (fun j _ => hmemS1 j)
    (fun j _ l _ h => hcoeinj h) (by simp) hratio hχratio hDeg
    (span_le_span_zSupportedSpan_union_anchor (K := K) hKsupp hS₁sub (hmemS1 i₁)
      fun φ hφ => ⟨p ^ (e φ - e (χmem i₁ : ClassFunction ↥L ℂ)),
        hratio_gen _ hi₁base φ (hS₁X hφ)⟩)

end OddOrder.Peterfalvi.S08


