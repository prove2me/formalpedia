-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_FamilyBundleDade
-- name    : OddOrder_Peterfalvi_S07_Coherence_FamilyBundleDade
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:02:35.428197+00:00
-- url     : https://prove2.me/theorems/0412298b-eca0-4d64-b6d2-4bd87d4ceba2
-- title:
--   Peterfalvi (5.6.1) family bundle and the (5.1) Dade isometry base map
-- statement:
--   Part of the coherence development of Peterfalvi §7: the family bundle of (5.6.1) and the base map from the §4 Dade isometry for (5.1).
--
--   Main definitions: `dadeIntegralCharacterMap` (the §4 Dade isometry lifted to a total $\mathbb{Z}$-linear integral character map), `dadeCharacterDifferenceImageOfDiff` (the Dade difference image $\{\mu,\nu,\varepsilon\}$ of $\chi$, with only the difference supported), `dadeOrthonormalCharacterImageFamilyOfDiff` ($R(\chi)$ from the Dade isometry), `decompositionDaFromDadeOfDiff` (the supported per-step decomposition of $\chi-a\chi_1$), `coherentEqualDegree_fromDade` (Peterfalvi (1.1)+(1.4): an equal-degree set is coherent at the real Dade map) and a support lemma for the integral span of supported class functions.
--
--   The bundle also proves 5 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S07_Coherence/FamilyBundleDade.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S07_Coherence/FamilyBundleDade.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_CoherenceUnion

namespace OddOrder.Peterfalvi.S07

open OddOrder.RepresentationTheory

variable {L G : Type*} [Group L] [Group G]

section DadeBaseMap

open OddOrder.Peterfalvi.S04

variable {G : Type*} [Group G] {A : Set G} {L : Subgroup G} [Fintype G] [Fintype ↥L]

variable [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card L : ℂ)]

/-- The §4 Dade isometry `dade`, lifted to a *total* `ℤ`-linear `IntegralCharacterMap ↥L G`.

Built by extending the `ℂ`-linear Dade map `hyp.dadeLinearMap` (the bare §4 map repackaged as a
`ℂ`-linear map on the supported subspace `CF(L,A)`) to all of `CF(L)` via `LinearMap.exists_extend`,
then restricting scalars to `ℤ`.  Its values on the supported subspace are the Dade map's
(`dadeIntegralCharacterMap_apply_of_support`); off it they are an arbitrary linear extension, which
the coherence machinery never inspects. -/
noncomputable def dadeIntegralCharacterMap (hyp : S04.Hypothesis G A L)
    (_dade : S04.FullDadeIsometryData (G := G) hyp) :
    IntegralCharacterMap (↥L) G :=
  (Classical.choose (LinearMap.exists_extend (hyp.dadeLinearMap (k := ℂ)))).restrictScalars ℤ

/-- The defining property of `dadeIntegralCharacterMap`: on the supported subspace `CF(L,A)` it
agrees with the §4 Dade map.

For a supported class function `φ` (`φ.support ⊆ supportInSubgroup A L`, i.e. `φ ∈ CF(L,A)`), the
lift evaluates to the Dade-map image `hyp.dadeMap ⟨φ, hφ⟩` — the (5.6.3) `τ` on `Z[S,L^#]`. -/
theorem dadeIntegralCharacterMap_apply_of_support (hyp : S04.Hypothesis G A L)
    (dade : S04.FullDadeIsometryData (G := G) hyp)
    {φ : ClassFunction (↥L) ℂ} (hφ : φ.support ⊆ supportInSubgroup A L) :
    dadeIntegralCharacterMap hyp dade φ =
      hyp.dadeMap (k := ℂ)
        (⟨φ, (ClassFunction.mem_supportedSubmodule).mpr hφ⟩ :
          SupportedClassFunctions (G := G) ℂ A L) := by
  have hext := Classical.choose_spec (LinearMap.exists_extend (hyp.dadeLinearMap (k := ℂ)))
  have key := LinearMap.congr_fun hext
    (⟨φ, (ClassFunction.mem_supportedSubmodule).mpr hφ⟩ :
      SupportedClassFunctions (G := G) ℂ A L)
  simpa [dadeIntegralCharacterMap, LinearMap.restrictScalars_apply,
    Hypothesis.dadeLinearMap_apply] using key

omit [Fintype G] in
omit [Fintype ↥L] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] in
/-- Every element of the integral span `ℤ[S]` of a set `S` of **supported** class functions is
itself supported.

`supportedSubmodule (supportInSubgroup A L)` is a `ℂ`-submodule of `CF(L)`; its
`restrictScalars ℤ` is a `ℤ`-submodule containing every generator `s ∈ S` (by hypothesis), hence
contains the whole `ℤ`-span `Submodule.span ℤ S = zSpan S` (`Submodule.span_le`).  This is the
lattice closure fact behind the supply-ability of the (5.4) auxiliary isometry: the difference
generators `χ − χ̄`, `χ − a·χ₁` live in `Z[S, L^#] ⊆ CF(L,A)`, so the whole sponsoring lattice
`ℤ[χ, χ̄, ψ]` is supported and the Dade isometry's `CF(L,A)` inner-preservation applies.

(The ambient `Fintype`/`Invertible` section instances are unused here — this is a pure
`ℤ`-submodule closure fact — but kept in scope for the supply-ability lemma that consumes it.) -/
theorem support_subset_of_mem_zSpan_of_supported
    {S : Set (ClassFunction (↥L) ℂ)}
    (hS : ∀ s ∈ S, s.support ⊆ supportInSubgroup A L)
    {φ : ClassFunction (↥L) ℂ} (hφ : φ ∈ zSpan (L := ↥L) S) :
    φ.support ⊆ supportInSubgroup A L := by
  have hle : zSpan (L := ↥L) S ≤
      (ClassFunction.supportedSubmodule (G := ↥L) (k := ℂ)
        (supportInSubgroup A L)).restrictScalars ℤ :=
    Submodule.span_le.mpr (fun s hs => by
      simpa only [SetLike.mem_coe, Submodule.restrictScalars_mem,
        ClassFunction.mem_supportedSubmodule] using hS s hs)
  exact (ClassFunction.mem_supportedSubmodule).mp (hle hφ)

/-- **Peterfalvi (5.1)/(5.4): the Dade base map supplies the lattice-relative isometry.**

The (5.1) coherence base map `τ = dadeIntegralCharacterMap` preserves the inner product on the
integral span `ℤ[S]` of any set `S` of **supported** class functions — exactly the
**lattice-relative** `htau1_inner_eq` shape consumed by `CharacterPsiDecomposition.ofProjection`
and `decompositionPair`.  This is the supply-ability witness for the Round-13 weakening: a *global*
`IsIntegralIsometry` on all of `CF(L)` does **not** exist in Feit–Thompson (`dim CF(L) > dim
CF(G)`), but the Dade isometry's `CF(L,A)` inner-preservation (`IsDadeIsometry.inner_eq`, the
(2.6.a) isometry property of the explicit (2.5) Dade map) *does* hand back inner-preservation on
every supported sublattice.

Proof: every `φ, ζ ∈ zSpan S` is supported (`support_subset_of_mem_zSpan_of_supported`), so
`dadeIntegralCharacterMap φ = hyp.dadeMap ⟨φ,_⟩` (`dadeIntegralCharacterMap_apply_of_support`); the
isometry property of `hyp.dadeMap` (via `hyp.dadeIsometryData`, whose `toDadeMap` *is*
`hyp.dadeMap`) closes `⟨τ φ, τ ζ⟩ = ⟨φ, ζ⟩`.

So for the running (5.4) `τ₁` *equal to* `τ` on the supported sublattice (the (5.1) base case, where
`τ₁ = τ`), `decompositionPair`'s `htau1_inner_eq` is discharged by this lemma — the per-step
`(D₀, Da)` are constructible from the Dade isometry.  (The general (5.4) `τ₁ ⊋ τ` extends this off
the support; the supported-lattice inner-preservation used by the `(5.4.b)/(5.5)/(5.6.2)` proofs is
exactly what this supplies.) -/
theorem dadeIntegralCharacterMap_inner_eq_on_supported_span
    (hyp : S04.Hypothesis G A L)
    {S : Set (ClassFunction (↥L) ℂ)}
    (hS : ∀ s ∈ S, s.support ⊆ supportInSubgroup A L)
    {φ ζ : ClassFunction (↥L) ℂ}
    (hφ : φ ∈ zSpan (L := ↥L) S) (hζ : ζ ∈ zSpan (L := ↥L) S) :
    ClassFunction.inner
        (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData) φ)
        (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData) ζ) =
      ClassFunction.inner φ ζ := by
  have hφsupp : φ.support ⊆ supportInSubgroup A L :=
    support_subset_of_mem_zSpan_of_supported hS hφ
  have hζsupp : ζ.support ⊆ supportInSubgroup A L :=
    support_subset_of_mem_zSpan_of_supported hS hζ
  rw [dadeIntegralCharacterMap_apply_of_support hyp _ hφsupp,
    dadeIntegralCharacterMap_apply_of_support hyp _ hζsupp]
  -- The (2.6.a) isometry property of the explicit (2.5) Dade map, on the supported pair.
  have hiso := (hyp.dadeIsometryData).isDadeIsometry.inner_eq
    (⟨φ, (ClassFunction.mem_supportedSubmodule).mpr hφsupp⟩ :
      S04.SupportedClassFunctions (G := G) ℂ A L)
    (⟨ζ, (ClassFunction.mem_supportedSubmodule).mpr hζsupp⟩ :
      S04.SupportedClassFunctions (G := G) ℂ A L)
  rwa [hyp.dadeIsometryData_toDadeMap] at hiso

/-- **Pair form of `dadeIntegralCharacterMap_inner_eq_on_supported_span`** (issue 0099): the Dade
base map preserves the inner product of any two **`A`-supported** class functions — no ambient
family or span membership needed (apply the span lemma to the pair `{φ, ζ}` itself).  This is the
unconditional supply for the `S07.Hypothesis.tau_isometry_diff` field in its (0099)
`zSupportedSpan` form: an instantiation site passes the supportedness halves `hφ.2`/`hζ.2` of
`ℤ[S, A]`-membership, and the `ℤ[S]` halves are not needed at all — so this works for **any**
family, mixed degrees included. -/
theorem dadeIntegralCharacterMap_inner_eq_of_supported
    (hyp : S04.Hypothesis G A L)
    {φ ζ : ClassFunction (↥L) ℂ}
    (hφ : φ.support ⊆ supportInSubgroup A L) (hζ : ζ.support ⊆ supportInSubgroup A L) :
    ClassFunction.inner
        (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData) φ)
        (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData) ζ) =
      ClassFunction.inner φ ζ := by
  refine dadeIntegralCharacterMap_inner_eq_on_supported_span hyp
    (S := {φ, ζ}) ?_ (Submodule.subset_span (Set.mem_insert _ _))
    (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  intro s hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl
  · exact hφ
  · exact hζ

/-- **The Dade base map sends supported virtual characters to virtual characters of `G`.**

For a supported class function `φ` (`φ.support ⊆ supportInSubgroup A L`, i.e. `φ ∈ CF(L,A)`) that is
also a virtual character of `L` (`φ ∈ ℤ[Irr L]`), the lift `dadeIntegralCharacterMap hyp dade φ`
lies in `ℤ[Irr G]`.  On the supported subspace the lift agrees with the explicit Dade map
(`dadeIntegralCharacterMap_apply_of_support`), and the §4 `FullDadeIsometryData` records the
(2.6.b) virtual-character preservation `PreservesVirtualCharacters` (`maps_virtualCharacter`).
This is the Round-B supply of the `ZIrr`-membership facts feeding `decompositionPairFromDade`. -/
theorem dadeIntegralCharacterMap_mem_ZIrr_of_supported
    (hyp : S04.Hypothesis G A L)
    {φ : ClassFunction (↥L) ℂ} (hφsupp : φ.support ⊆ supportInSubgroup A L)
    (hφZ : φ ∈ ZIrr (↥L)) :
    dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData) φ ∈ ZIrr G := by
  rw [dadeIntegralCharacterMap_apply_of_support hyp _ hφsupp]
  -- `hyp.dadeMap` is the underlying `toDadeMap` of `fullDadeIsometryData`; apply (2.6.b).
  have hpv := (hyp.fullDadeIsometryData).maps_virtualCharacter
    (⟨φ, (ClassFunction.mem_supportedSubmodule).mpr hφsupp⟩ :
      S04.SupportedClassFunctions (G := G) ℂ A L) hφZ
  rwa [show (hyp.fullDadeIsometryData).toDadeMap = hyp.dadeMap (k := ℂ) from
    hyp.dadeIsometryData_toDadeMap] at hpv

/-- **The Dade base map sends supported class functions to functions vanishing at `1`.**

For a supported class function `φ` (`φ ∈ CF(L,A)`), the lift `dadeIntegralCharacterMap hyp dade φ`
vanishes at the identity of `G`.  On the supported subspace the lift agrees with the explicit Dade
map `hyp.dadeMap ⟨φ,_⟩` (`dadeIntegralCharacterMap_apply_of_support`), which vanishes off
`dadeSupport` (`IsDadeMap.map_eq_zero_of_not_mem_dadeSupport`); since `1 ∉ dadeSupport`
(`one_notMem_dadeSupport`), the value at `1` is `0`.  This discharges the (1.4)
`IsometryDifferenceImagesVanishAtOne` hypothesis for the Dade map. -/
theorem dadeIntegralCharacterMap_apply_one_eq_zero
    (hyp : S04.Hypothesis G A L)
    {φ : ClassFunction (↥L) ℂ} (hφsupp : φ.support ⊆ supportInSubgroup A L) :
    (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData) φ) (1 : G) = 0 := by
  rw [dadeIntegralCharacterMap_apply_of_support hyp _ hφsupp]
  exact (hyp.isDadeMap_dadeMap (k := ℂ)).map_eq_zero_of_not_mem_dadeSupport
    (⟨φ, (ClassFunction.mem_supportedSubmodule).mpr hφsupp⟩ :
      S04.SupportedClassFunctions (G := G) ℂ A L)
    (1 : G) hyp.one_notMem_dadeSupport

/-- **The Dade `CharacterDifferenceImage` `{μ, ν, ε}` of `χ`, with only the DIFFERENCE `χ̄ − χ`
supported (X-family).**  (`.toOrthonormalImage` lifts it to the orthonormal `R(χ)`; see
`dadeOrthonormalCharacterImageFamilyOfDiff` below.)

The orthonormal image family `R(χ)` with `(χ − χ̄)^τ = ∑_{α ∈ R(χ)} α`, built from the Dade base
map — but requiring only that the *difference* `χ̄ − χ` is supported in `CF(L,A)`, **not** the
individual supports `hχsupp`/`hχbarsupp` of `dadeOrthonormalCharacterImageFamily`.  This is what the
(6.8) `X`-family needs: an induced `χ = Ind_H^L θ` has `χ(1) = |W₁|θ(1) ≠ 0`, so `χ` itself is NOT
supported (`1 ∉ A = H^#`), yet the conjugate difference `χ̄ − χ` vanishes at `1` and is supported on
`H^#`.

The Dade `CF(L,A)`-isometry is applied on the **difference set** `D = {0, χ̄ − χ}` (both supported:
`0` trivially, `χ̄ − χ` by hypothesis), into which both keystone differences
`irreducibleCharacterDifference fam i` (`= 0` for `i = 0`, `= χ̄ − χ` for `i = 1`) land — exactly
the
generators the (1.4)/(2.6.a) keystone uses.  No `χ`/`χ̄` individual support is touched.
`dadeOrthonormalCharacterImageFamily` (individual supports) is recovered as the special case where
`hdiffsupp` is derived from `hχsupp`, `hχbarsupp`. -/
noncomputable def dadeCharacterDifferenceImageOfDiff
    (hyp : S04.Hypothesis G A L)
    (χ : IrreducibleCharacter (↥L))
    (hreal : ¬ ClassFunction.IsReal (χ : ClassFunction (↥L) ℂ))
    (hdiffsupp : ((χ : ClassFunction (↥L) ℂ).conj - (χ : ClassFunction (↥L) ℂ)).support ⊆
      supportInSubgroup A L) :
    CharacterDifferenceImage (L := ↥L) (G := G)
      (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (χ : ClassFunction (↥L) ℂ) := by
  classical
  set τ := dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData) with hτ_def
  set fam : Fin 2 → IrreducibleCharacter (↥L) := conjPairFamily (L := ↥L) χ with hfam
  have hfam0 : (fam 0 : ClassFunction (↥L) ℂ) = (χ : ClassFunction (↥L) ℂ) := by
    simp [hfam, conjPairFamily]
  have hfam1 : (fam 1 : ClassFunction (↥L) ℂ) = (χ : ClassFunction (↥L) ℂ).conj := by
    simp [hfam, conjPairFamily]
  -- `irreducibleCharacterDifference fam i = fam i − fam 0`: `0` for `i = 0`, `χ̄ − χ` for `i = 1`.
  have hdiff0 : irreducibleCharacterDifference fam 0 = 0 := by
    simp [irreducibleCharacterDifference]
  have hdiff1 : irreducibleCharacterDifference fam 1 =
      (χ : ClassFunction (↥L) ℂ).conj - (χ : ClassFunction (↥L) ℂ) := by
    simp only [irreducibleCharacterDifference, hfam1, hfam0]
  -- Each keystone difference is supported in `CF(L,A)`.
  have hdiff_supp : ∀ i,
      (irreducibleCharacterDifference fam i).support ⊆ supportInSubgroup A L := by
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · rw [hdiff0]; simp
    · rw [hdiff1]; exact hdiffsupp
  -- The supported difference set `D = {0, χ̄ − χ}`, and the keystone differences land in `ℤ[D]`.
  set D : Set (ClassFunction (↥L) ℂ) :=
    {(0 : ClassFunction (↥L) ℂ), (χ : ClassFunction (↥L) ℂ).conj - (χ : ClassFunction (↥L) ℂ)}
    with hD
  have hDsupp : ∀ s ∈ D, s.support ⊆ supportInSubgroup A L := by
    intro s hs
    simp only [hD, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · simp
    · exact hdiffsupp
  have hdiff_in_D : ∀ i, irreducibleCharacterDifference fam i ∈ zSpan (L := ↥L) D := by
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · rw [hdiff0]; exact Submodule.subset_span (by simp [hD])
    · rw [hdiff1]; exact Submodule.subset_span (by simp [hD])
  -- (1.4) hypotheses, all from the difference support.
  have hvirtual : IsometryDifferenceImagesAreVirtual (G := G) (H := ↥L) τ fam := by
    intro i
    refine dadeIntegralCharacterMap_mem_ZIrr_of_supported hyp (hdiff_supp i) ?_
    refine Submodule.sub_mem _ ?_ (fam 0).mem_ZIrr
    exact (fam i).mem_ZIrr
  have hzero : IsometryDifferenceImagesVanishAtOne (G := G) (H := ↥L) τ fam := by
    intro i
    exact dadeIntegralCharacterMap_apply_one_eq_zero hyp (hdiff_supp i)
  have hisom : ∀ i j,
      ClassFunction.inner (isometryDifferenceImage τ fam i) (isometryDifferenceImage τ fam j) =
        ClassFunction.inner (irreducibleCharacterDifference fam i)
          (irreducibleCharacterDifference fam j) := by
    intro i j
    exact dadeIntegralCharacterMap_inner_eq_on_supported_span hyp hDsupp
      (hdiff_in_D i) (hdiff_in_D j)
  exact characterDifferenceImageOfIsometry τ χ hreal hvirtual hzero hisom

/-- **R(χ) from the Dade isometry, difference-support form**: `dadeCharacterDifferenceImageOfDiff`
lifted to the orthonormal family `R(χ) = {ε·μ, −ε·ν}` via `toOrthonormalImage`.  Requires only the
*difference* `χ̄ − χ` supported in `CF(L,A)` (the `(6.8)`/`(12.2)` X-family situation, where `χ`
itself is unsupported since `χ(1) ≠ 0`).  The underlying `{μ, ν, ε}` data is
`dadeCharacterDifferenceImageOfDiff` (consumed by the cross-`L` (4.1) orthogonality of (12.3)). -/
noncomputable def dadeOrthonormalCharacterImageFamilyOfDiff
    (hyp : S04.Hypothesis G A L)
    (χ : IrreducibleCharacter (↥L))
    (hreal : ¬ ClassFunction.IsReal (χ : ClassFunction (↥L) ℂ))
    (hdiffsupp : ((χ : ClassFunction (↥L) ℂ).conj - (χ : ClassFunction (↥L) ℂ)).support ⊆
      supportInSubgroup A L) :
    OrthonormalCharacterImageFamily (L := ↥L) (G := G)
      (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (χ : ClassFunction (↥L) ℂ) :=
  (dadeCharacterDifferenceImageOfDiff hyp χ hreal hdiffsupp).toOrthonormalImage

/-- **The supported per-step decomposition `Da` of `χ − a·χ₁`, for an UNSUPPORTED `χ` (X-family).**

Builds `Da : CharacterPsiDecomposition τ χ (a·χ₁)` directly via `ofProjection` — **not**
`decompositionPair`, which also builds the `ψ=0` `D₀` requiring the unprovable `τχ ∈ ZIrr`.  This is
now constructible for an unsupported induced X-member `χ = Ind θ` thanks to the
difference-sublattice
weakening of `tau1_inner_eq_on_support`: the auxiliary isometry `τ₁ = τ` only needs
inner-preservation
on `ℤ[χ−χ̄, χ−a·χ₁]` (both supported differences — supplied by
`dadeIntegralCharacterMap_inner_eq_on_supported_span` on the difference set `{χ−χ̄, χ−a·χ₁}`), and
the
`ZIrr`-membership only on `χ − a·χ₁` (`htau1_mema`, the degree-matched difference vanishing at `1`).
`R(χ)` is the difference-support family `dadeOrthonormalCharacterImageFamilyOfDiff`. -/
noncomputable def decompositionDaFromDadeOfDiff
    (hyp : S04.Hypothesis G A L)
    (χ : IrreducibleCharacter (↥L))
    (hreal : ¬ ClassFunction.IsReal (χ : ClassFunction (↥L) ℂ))
    {chi1 : ClassFunction (↥L) ℂ} {a : ℕ}
    (hdiffsupp : ((χ : ClassFunction (↥L) ℂ).conj - (χ : ClassFunction (↥L) ℂ)).support ⊆
      supportInSubgroup A L)
    (hdiffasupp : ((χ : ClassFunction (↥L) ℂ) - a • chi1).support ⊆ supportInSubgroup A L)
    (htau1_mema : dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)
      ((χ : ClassFunction (↥L) ℂ) - a • chi1) ∈ ZIrr G)
    (hχaχ1 : ClassFunction.inner (χ : ClassFunction (↥L) ℂ) (a • chi1 : ClassFunction (↥L) ℂ) = 0)
    (hχbaraχ1 : ClassFunction.inner (χ : ClassFunction (↥L) ℂ).conj
      (a • chi1 : ClassFunction (↥L) ℂ) = 0)
    (hχχbar' : ClassFunction.inner (χ : ClassFunction (↥L) ℂ) (χ : ClassFunction (↥L) ℂ).conj = 0) :
    CharacterPsiDecomposition (L := ↥L) (G := G)
      (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (χ : ClassFunction (↥L) ℂ) (a • chi1) := by
  classical
  set τ := dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData) with hτ
  -- The difference set `{χ−χ̄, χ−a·χ₁}` is supported (`χ−χ̄` via `hdiffsupp` up to sign).
  have hSdiff : ∀ s ∈ ({(χ : ClassFunction (↥L) ℂ) - (χ : ClassFunction (↥L) ℂ).conj,
      (χ : ClassFunction (↥L) ℂ) - a • chi1} : Set (ClassFunction (↥L) ℂ)),
      s.support ⊆ supportInSubgroup A L := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · rw [show (χ : ClassFunction (↥L) ℂ) - (χ : ClassFunction (↥L) ℂ).conj =
          -((χ : ClassFunction (↥L) ℂ).conj - (χ : ClassFunction (↥L) ℂ)) by abel,
        ClassFunction.support_neg]
      exact hdiffsupp
    · exact hdiffasupp
  exact CharacterPsiDecomposition.ofProjection
    (dadeOrthonormalCharacterImageFamilyOfDiff hyp χ hreal hdiffsupp) τ
    (fun φ ζ hφ hζ =>
      dadeIntegralCharacterMap_inner_eq_on_supported_span hyp hSdiff hφ hζ)
    rfl htau1_mema hχaχ1 hχbaraχ1 hχχbar'

open IntegralCharacterMap in
/-- **Peterfalvi (1.1)+(1.4): an equal-degree set is coherent — at the real Dade base map.**

The Dade specialization of `coherentEqualDegree`: an injective, equal-degree family
`χ : Fin n → Irr(L)` (`n ≥ 2`) of irreducible characters supported in `CF(L,A)` is coherent for the
(5.1) base map `τ = dadeIntegralCharacterMap`.  The (1.4) signed-difference family `{μⱼ, ε}` is
**constructed** by applying `isometry_difference_pair_structure` to `τ`, with its three hypotheses
discharged from the Dade isometry exactly as in `dadeOrthonormalCharacterImageFamily`:

* virtual-character images (`dadeIntegralCharacterMap_mem_ZIrr_of_supported`, (2.6.b));
* vanish at `1` (`dadeIntegralCharacterMap_apply_one_eq_zero`, `1 ∉ dadeSupport`);
* inner-product preservation on the supported lattice
  (`dadeIntegralCharacterMap_inner_eq_on_supported_span`, (2.6.a)).

The target family is `Xⱼ = ε • μⱼ` (orthonormal: `{μⱼ}` is, by `classFunction_inner_eq_if`, and
`ε² = 1`), giving the image equation `τ(χⱼ − χ₀) = Xⱼ − X₀` (= `ε•(μⱼ − μ₀)`, the signed
difference); `coherentEqualDegree` then assembles the coherence.  This is the **`h0` base of the
(6.6) equal-minimal-degree prefix and the (6.8) `Y = S(H')`**, both produced directly from the real
Dade τ with no opaque hypotheses (the equal degree and supports are the genuine (6.8) data). -/
noncomputable def coherentEqualDegree_fromDade
    (hyp : S04.Hypothesis G A L)
    {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (χ : Fin n → IrreducibleCharacter (↥L))
    (hχinj : Function.Injective χ)
    (hdeg : ∀ j, ((χ j : ClassFunction (↥L) ℂ) : ↥L → ℂ) 1
      = ((χ 0 : ClassFunction (↥L) ℂ) : ↥L → ℂ) 1)
    (hsuppdiff : ∀ j, (irreducibleCharacterDifference χ j).support ⊆ supportInSubgroup A L)
    (h1notA : (1 : G) ∉ A) :
    IsCoherent (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (Set.range (fun j => (χ j : ClassFunction (↥L) ℂ))) (supportInSubgroup A L) := by
  classical
  set τ := dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData) with hτ
  -- Source orthonormality from the distinct irreducible characters.
  have horthχ : ∀ i j, ClassFunction.inner ((χ i : ClassFunction (↥L) ℂ))
      ((χ j : ClassFunction (↥L) ℂ)) = if i = j then (1 : ℂ) else 0 := by
    intro i j
    rw [irreducibleCharacter_inner_eq_ite]
    by_cases h : i = j
    · rw [if_pos h, if_pos (congrArg χ h)]
    · rw [if_neg h, if_neg (fun he => h (hχinj he))]
  -- The supported difference generators `χⱼ − χ₀` of `ℤ[range χ]` (this is the support
  -- hypothesis directly, so the individual `χⱼ` need not be supported on `A`).
  have hdiff_supp : ∀ i, (irreducibleCharacterDifference χ i).support ⊆ supportInSubgroup A L :=
    hsuppdiff
  have hdiffSset : ∀ s ∈ Set.range (fun j => irreducibleCharacterDifference χ j),
      s.support ⊆ supportInSubgroup A L := by
    rintro s ⟨j, rfl⟩; exact hdiff_supp j
  have hdiff_zspan : ∀ i, irreducibleCharacterDifference χ i ∈
      zSpan (L := ↥L) (Set.range (fun j => irreducibleCharacterDifference χ j)) :=
    fun i => Submodule.subset_span (Set.mem_range_self i)
  -- Discharge the three (1.4) hypotheses for the Dade base map.
  have hvirtual : IsometryDifferenceImagesAreVirtual (G := G) (H := ↥L) τ χ := fun i =>
    dadeIntegralCharacterMap_mem_ZIrr_of_supported hyp (hdiff_supp i)
      (Submodule.sub_mem _ (χ i).mem_ZIrr (χ 0).mem_ZIrr)
  have hzero : IsometryDifferenceImagesVanishAtOne (G := G) (H := ↥L) τ χ := fun i =>
    dadeIntegralCharacterMap_apply_one_eq_zero hyp (hdiff_supp i)
  have hisom : ∀ i j, ClassFunction.inner (isometryDifferenceImage τ χ i)
      (isometryDifferenceImage τ χ j) =
      ClassFunction.inner (irreducibleCharacterDifference χ i)
        (irreducibleCharacterDifference χ j) := fun i j =>
    dadeIntegralCharacterMap_inner_eq_on_supported_span hyp hdiffSset
      (hdiff_zspan i) (hdiff_zspan j)
  -- (1.4): the signed irreducible-difference family `{μⱼ, ε}` (extracted via `Exists.choose`,
  -- as the conclusion is data in `Type`, not a `Prop`).
  have hex := isometry_difference_pair_structure (G := G) (H := ↥L) hn χ hχinj hdeg
    τ hvirtual hzero hisom
  set data := hex.choose with hdata_def
  have hdata : ∀ i, isometryDifferenceImage τ χ i = data.signedDifference i := hex.choose_spec
  -- Target family `Xⱼ = ε • μⱼ`.
  set X : Fin n → ClassFunction G ℂ := fun j => data.sign • data.classFunction j with hX
  have horthX : ∀ i j, ClassFunction.inner (X i) (X j) = if i = j then (1 : ℂ) else 0 := by
    intro i j
    have hmul : (data.sign : ℂ) * (data.sign : ℂ) = 1 := by exact_mod_cast data.sign_mul_self
    simp only [hX]
    rw [← Int.cast_smul_eq_zsmul ℂ data.sign (data.classFunction i),
      ← Int.cast_smul_eq_zsmul ℂ data.sign (data.classFunction j),
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      star_intCast, ← mul_assoc, hmul, one_mul, data.classFunction_inner_eq_if i j]
  -- Image equation `τ(χⱼ − χ₀) = Xⱼ − X₀ = ε•(μⱼ − μ₀)`.
  have himg : ∀ j, τ ((fun k => (χ k : ClassFunction (↥L) ℂ)) j
      - (fun k => (χ k : ClassFunction (↥L) ℂ)) 0) = X j - X 0 := by
    intro j
    have hXd : X j - X 0 = data.signedDifference j := by
      change data.sign • data.classFunction j - data.sign • data.classFunction 0
        = data.sign • (data.classFunction j - data.classFunction 0)
      rw [smul_sub]
    rw [hXd]; exact hdata j
  -- The non-vanishing degree at `1` (irreducible characters have positive degree).
  have hdeg0 : ((χ 0 : ClassFunction (↥L) ℂ) : ↥L → ℂ) 1 ≠ 0 := by
    obtain ⟨d, hd, hd1⟩ := irreducibleCharacter_apply_one_eq_pos_natCast (χ 0)
    rw [hd1]; exact_mod_cast hd.ne'
  -- `1 ∉ supportInSubgroup A L`.
  have h1A : (1 : ↥L) ∉ supportInSubgroup A L := fun h => h1notA (by simpa using h)
  -- `Xⱼ = ε • μⱼ ∈ ℤ[Irr G]` since each `μⱼ` is irreducible and `ε = ±1`.
  have hXZ : ∀ j, X j ∈ ZIrr G := fun j => by
    simp only [hX]
    exact Submodule.smul_mem _ data.sign (data.classFunction_irreducible j).mem_ZIrr
  exact coherentEqualDegree hn horthχ horthX himg hXZ hdeg hdeg0 h1A (fun j => hdiff_supp j)

end DadeBaseMap

end OddOrder.Peterfalvi.S07


