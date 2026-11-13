-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceBasic
-- name    : OddOrder_Peterfalvi_S08_CoherenceBasic
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:36:55.097871+00:00
-- url     : https://prove2.me/theorems/9695c753-5e4f-4365-b531-a0dc7b7abfeb
-- title:
--   Peterfalvi §8: $X$-set coherence for Sibley–Dade data (core, basic part)
-- statement:
--   Part of the Peterfalvi §8 coherence core, concerned with the (6.6)/(6.8) $X=S-S(Z)$ coherence for Sibley–Dade data.
--
--   Main results: `mem_xSetFinset_iff_mem_Xset` (the induced-character `Finset` form of the $X$-set equals the `Set` form), `toInducedFamilyTauData` (the $\tau$-half of Hypothesis (5.2) carried by a Sibley–Dade datum), `Xset_isCoherent_of_irreducible_X` (the (6.6)(b) coherence, $Z$-generic form) and `Xset_centralCommutator_isCoherent_of_frobenius` (coherence at the central commutator).
--
--   The bundle also proves 1 supporting lemma used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_CoherenceBasic.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_CoherenceBasic.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceCorePart2
import Definitions.Def_OddOrder_Peterfalvi_S08_SixSixGeneral

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

open scoped commutatorElement

variable {L G : Type*} [Group L] [Group G]

namespace SibleyDadeHypothesis

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)]

variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

open scoped Classical in
/-- **`X = S − S(Z)` membership bridge: the induced-character `Finset` form equals the `Set` form.**
For any `Z`, a class function `φ` lies in the explicit `Finset`
`(filter bot-kernel).image (Ind ·) \ (filter Z-kernel).image (Ind ·)` (the degree-square-sum domain
of `sum_re_sq_Xset_eq_of_irreducible_X` / `Xset_nonempty_of_subgroupOf_ne_bot_of_irreducible_X`) iff
`φ ∈ Xset Z = S − S(Z)`.  Extracted from the L2 monolith's inline `hmemXF` so that a `Set`-form
irreducibility hypothesis (the `c2`/case-A `isIrreducibleCharacter_of_mem_Xset_c2_caseA`) can feed
the
`Finset`-form nonemptiness lemma. -/
theorem mem_xSetFinset_iff_mem_Xset (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} [Z.Normal] (φ : ClassFunction ↥L ℂ) :
    φ ∈ ((Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) \
        (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction)) ↔
      φ ∈ hyp.Xset Z := by
  let : H.Normal := hyp.H_normal
  have : Fintype ↥H := Fintype.ofFinite _
  rw [Finset.mem_sdiff]
  constructor
  · rintro ⟨hbot, hnotZ⟩
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hbot
    obtain ⟨-, -, hθne⟩ := Finset.mem_filter.mp hθ
    refine hyp.mem_Xset.mpr ⟨by rw [hyp.S_eq]; exact ⟨θ, hθne, rfl⟩, ?_⟩
    intro hmem
    rw [hyp.mem_SsubFiltration] at hmem
    obtain ⟨θ', hne', hker', heq'⟩ := hmem
    exact hnotZ (Finset.mem_image.mpr
      ⟨θ', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hker', hne'⟩, heq'.symm⟩)
  · intro hφ
    obtain ⟨hφS, hφnotZ⟩ := hyp.mem_Xset.mp hφ
    rw [hyp.S_eq, Set.mem_ofPred_eq] at hφS
    obtain ⟨θ, hθne, rfl⟩ := hφS
    refine ⟨Finset.mem_image.mpr ⟨θ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hθne⟩, rfl⟩, ?_⟩
    · intro x hx
      rw [Subgroup.bot_subgroupOf, Subgroup.coe_bot, Set.mem_singleton_iff] at hx
      subst hx; exact OddOrder.Peterfalvi.S03.one_mem_characterKernel _
    · intro hmem
      obtain ⟨θ', hθ', hθ'eq⟩ := Finset.mem_image.mp hmem
      obtain ⟨-, hker', hne'⟩ := Finset.mem_filter.mp hθ'
      exact hφnotZ (hyp.mem_SsubFiltration.mpr ⟨θ', hne', hker', hθ'eq.symm⟩)

/-- **The `τ`-half of Hypothesis (5.2) carried by a Sibley–Dade datum.**

A `SibleyDadeHypothesis` supplies its `τ` as the Dade integral character map on `A₀ = H^#`
(`SibleyDadeHypothesis.tau`), and the three (5.2.b) clauses that the general-kernel engine
consumes — isometry on `ℤ[𝒮, A₀]`, `ℤ[Irr G]` codomain, and vanishing at `1` — are exactly the
§7 Dade-map facts.  This is the bridge that makes the Sibley `K = H` (6.6) instance a
*specialization* of the general-kernel `S08.xSet_isCoherent_of_irreducible_X` (issue 0156). -/
noncomputable def toInducedFamilyTauData (hyp : SibleyDadeHypothesis G L H) :
    InducedFamilyTauData (G := G)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) H where
  tau := hyp.tau
  tau_isometry := fun _φ _ζ hφ hζ =>
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span hyp.dade
      (S := OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (inducedKernelFamily H ⊥)
        (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
      (fun _s hs => hs.2) (Submodule.subset_span hφ) (Submodule.subset_span hζ)
  tau_mem_ZIrr := fun _φ hφ =>
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported hyp.dade hφ.2
      (Submodule.span_le.mpr (fun _x hx => inducedKernelFamily_mem_ZIrr hx) hφ.1)
  tau_apply_one := fun _φ hφ =>
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_one_eq_zero hyp.dade hφ.2

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Fintype ↥L]
  [Invertible (Nat.card ↥L : ℂ)] [Invertible (Nat.card ↥H : ℂ)] in
/-- **`H^#`, read inside `L`, contains every nonidentity element of `H`.**  The `hKsupp` input of
the general (6.6) engine for the Sibley support `A₀ = H^#`. -/
theorem mem_supportInSubgroup_sharpImage {x : ↥L} (hxH : x ∈ H) (hx1 : x ≠ 1) :
    x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
  ⟨⟨x, hxH, rfl⟩, fun h => hx1 (Subtype.ext h)⟩

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Fintype ↥L]
  [Invertible (Nat.card ↥L : ℂ)] [Invertible (Nat.card ↥H : ℂ)] in
/-- **`1 ∉ H^#`.**  The `h1A` input of the general (6.6) engine. -/
theorem one_notMem_supportInSubgroup_sharpImage :
    (1 : ↥L) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
  fun h => h.2 rfl

open scoped Classical in
/-- **Peterfalvi (6.6)(b): `X = S − S(Z)` is coherent — the Z-generic form.**

The Sibley `K = H` instance of the general-kernel, `τ`-general
`S08.xSet_isCoherent_of_irreducible_X` (issue 0156): `hyp.Xset Z` *is* the general `xSet H Z`
(`Xset_eq_inducedKernelFamily_sdiff`) and `hyp.tau` carries the (5.2.b) data
(`toInducedFamilyTauData`), so the entire proof is the general one — in particular the
`XAdjoinStepInput` degree bookkeeping of `S08_CoherenceCorePart2/SibleyBounds` is no longer on
the (6.6) route.

For any normal subgroup `Z` of `L` with `Z ≤ H` central in `H` (`Z.subgroupOf H ≤ Z(H)`, the
book's `Z ⊆ Z(K)`), the set `X(Z) = S − S(Z)` is coherent, given that every `X`-member is
irreducible (`hX` — the book's hypothesis `𝒳 ⊆ Irr L`), that `X` is nonempty (`hXne` — in the
book from `Z ≠ 1` via (1.1)), that `H` is a `p`-group for a prime `p ≥ 3` (the book reduces to
this case by (6.5), and `p` is odd since `|L|` is), and that `|L:H|` is coprime to `p` (`hidxp`,
from (6.4.c)/(6.5.c)).  The central-commutator (`Zc = Z(H) ∩ H′`) instantiations
(`…_of_frobenius`, `…_of_c2_caseA`) are thin specializations differing only in how
`hX`/`hXne`/`hidxp` are produced (`isIrreducibleCharacter_of_mem_Xset_of_frobenius` +
`hF.coprime_card_kernel_complement` vs `isIrreducibleCharacter_of_mem_Xset_c2_caseA` +
`cert.card_coprime`). -/
noncomputable def Xset_isCoherent_of_irreducible_X
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} [Z.Normal] (_hZle : Z ≤ H)
    (hZcent : Z.subgroupOf H ≤ Subgroup.center ↥H)
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    (hXne : (hyp.Xset Z).Nonempty)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    (hidxp : Nat.Coprime H.index p) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset Z)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  letI : H.Normal := hyp.H_normal
  rw [hyp.Xset_eq_inducedKernelFamily_sdiff Z] at hX hXne ⊢
  exact xSet_isCoherent_of_irreducible_X (K := H) hyp.toInducedFamilyTauData hyp.card_L_odd
    (fun _x hxH hx1 => mem_supportInSubgroup_sharpImage hxH hx1)
    one_notMem_supportInSubgroup_sharpImage hp hp3 hHp hidxp hZcent hX hXne

open scoped Classical in
/-- **(6.6)/(6.8) X = S − S(Zc) coherence at the central commutator — the L2 producer.**
The redesign's L2 deliverable: `X(Zc)` is coherent, with `Zc = Z(H) ∩ H′` central.  Builds the
per-step `AnchoredPairUnionStepData` (the first-ever such term) for every
chain step and feeds it to the `…withCover…` Zc shell.  Per step: the current head `χs i` and every
`X`-member `Ind θ` have degree `|L:H|·p^k` (`exists_index_primePow_degree_of_mem_S`), the central
degree bound `θχ² ≤ |H:Zc|` holds ([Is] Cor 2.30 via
`exists_source_primePow_centralBound_of_mem_Xset`),
the `htail_le` field is `characterDegree_re_le_of_not_mem_pairUnion` (uses `hcover`), and the `hsum`
partition is `natSum_partition_of_realSum` pinned by `sum_re_sq_Xset_eq`.  `H` is supplied as a
`p`-group (the capstone's ¬-coherent branch gives this via `isPGroup_of_not_coherent`). -/
noncomputable def Xset_centralCommutator_isCoherent_of_frobenius
    (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  haveI : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hyp.H_ne_bot
  haveI : Fact p.Prime := ⟨hp⟩
  -- `|L:H|` coprime to `p`
  have hpdvd : p ∣ Nat.card ↥H := by
    obtain ⟨n, hn⟩ := hHp.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      exact (Finite.one_lt_card_iff_nontrivial.mpr inferInstance).ne' hn
    rw [hn]; exact dvd_pow_self p hn0
  have hidxp : Nat.Coprime H.index p := by
    rw [hyp.index_H_eq_card_W1]
    exact (Nat.Coprime.coprime_dvd_left hpdvd hF.coprime_card_kernel_complement).symm
  haveI := hyp.centralCommutator_normal
  exact hyp.Xset_isCoherent_of_irreducible_X hyp.centralCommutator_le
    hyp.centralCommutator_subgroupOf_le_center
    (fun _ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)
    (hyp.Xset_centralCommutator_nonempty hF hHnonab) hp hp3 hHp hidxp

open scoped Classical in
/-- **(6.6)/(6.8) X(Zc) coherence, certain-type case (B), math-(A) sub-case `Z(H) ∩ W₂ = ⊥` (CB3).**
The CertainType/(c2) analogue of `Xset_centralCommutator_isCoherent_of_frobenius` under the math-(A)
hypothesis `Z(H) ⊓ W₂ = 1` (`hA`): `W₁` still acts fixed-point-freely on `Zc = Z(H) ∩ H′`
(`centralizer_inf_centralCommutator_eq_bot_of_c2_caseA`), so the same central-`Zc` coherence
machinery
of `Xset_isCoherent_of_irreducible_X` applies. The three
irreducibility/coprimality
inputs are produced from the certain-type data: `hX` from
`isIrreducibleCharacter_of_mem_Xset_c2_caseA`,
`hXne` from `Xset_nonempty_of_subgroupOf_ne_bot_of_irreducible_X` (the `Set`→`Finset` form converted
by
`mem_xSetFinset_iff_mem_Xset`), and `hidxp` from `cert.card_coprime` + `index_H_eq_card_W1`. -/
noncomputable def Xset_centralCommutator_isCoherent_of_c2_caseA
    (hyp : SibleyDadeHypothesis G L H)
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  letI : H.Normal := hyp.H_normal
  haveI := hyp.centralCommutator_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  haveI : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hyp.H_ne_bot
  haveI : Fact p.Prime := ⟨hp⟩
  -- every `X`-member is irreducible (`W₁` FPF on `Zc` from math-(A))
  have hX : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hφ
  -- `Zc.subgroupOf H ≠ ⊥` (since `H` is non-abelian)
  have hZbot : hyp.centralCommutator.subgroupOf H ≠ ⊥ := by
    intro hbot
    apply hyp.centralCommutator_ne_bot hHnonab
    rw [eq_bot_iff]
    intro z hz
    have hzH : z ∈ H := hyp.centralCommutator_le hz
    have hmem : (⟨z, hzH⟩ : ↥H) ∈ hyp.centralCommutator.subgroupOf H :=
      (Subgroup.mem_subgroupOf).mpr hz
    rw [hbot, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hmem
  -- `X` is nonempty
  have hXne : (hyp.Xset hyp.centralCommutator).Nonempty :=
    hyp.Xset_nonempty_of_subgroupOf_ne_bot_of_irreducible_X hZbot
      (fun χ hχ => hX χ ((hyp.mem_xSetFinset_iff_mem_Xset (Z := hyp.centralCommutator) χ).mp hχ))
  -- `|L:H| = |W₁|` coprime to `p`
  have hpdvd : p ∣ Nat.card ↥H := by
    obtain ⟨n, hn⟩ := hHp.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      exact (Finite.one_lt_card_iff_nontrivial.mpr inferInstance).ne' hn
    rw [hn]; exact dvd_pow_self p hn0
  have hidxp : Nat.Coprime H.index p := by
    rw [hyp.index_H_eq_card_W1, ← hW1]
    have hcop := cert.card_coprime
    rw [hK] at hcop
    exact (Nat.Coprime.coprime_dvd_left hpdvd hcop).symm
  exact hyp.Xset_isCoherent_of_irreducible_X hyp.centralCommutator_le
    hyp.centralCommutator_subgroupOf_le_center hX hXne hp hp3 hHp hidxp

/-- **(6.8.1)/(6.8), L3 outer shell — diagonal-aware form.**  Same as
`coherentXunionYset_centralCommutator_of_glued_of_frobenius`, but routing through the corrected
`coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal`: the plain shell's generation
hypothesis `hgen` (without the cross-diagonals `D`) is **false** in the (6.8.1) situation — the
supported cross-diagonal `χ₁ − a·η₁ ∈ ℤ[X(Zc) ∪ Y]` is not a sum of a supported `X`-combination and
a supported `Y`-combination (see `notes/peterfalvi/s08_6_8_blocker_central_Z.md`, framing correction
#2, and the `coherentUnion_of_glued_withDiagonal` docstring).  Here `D` carries those
cross-diagonals
with `hDτ : ∀ d ∈ D, ν d = τ d` (the (6.8.1) `b ≡ 0` conclusion
`(χ₁ − a·η₁)^τ = χ₁^{τ₂} − a·η₁^{τ₁}`), and `hgen` is the satisfiable generation including `D`. -/
noncomputable def coherentXunionYset_centralCommutator_of_glued_withDiagonal_general
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ x ∈ hyp.Xset hyp.centralCommutator, ν x = cX.extension x)
    (hagreeY : ∀ y ∈ hyp.Yset, ν y = cY.extension y)
    (hmixed : ∀ x ∈ hyp.Xset hyp.centralCommutator, ∀ y ∈ hyp.Yset,
      ClassFunction.inner (ν x) (ν y) = ClassFunction.inner x y)
    (D : Set (ClassFunction ↥L ℂ))
    (hDτ : ∀ d ∈ D, ν d = hyp.tau d)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
        Submodule.span ℤ
          (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset hyp.centralCommutator)
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪ D)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  exact OddOrder.Peterfalvi.S07.coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal
    cX cY ν hagreeX hagreeY
    (inner_eq_zero_of_mem_span_of_disjoint_irreducible
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Yset hφ) hdisj)
    hmixed D hDτ hgen

/-- **(6.8) L3 outer shell — diagonal-aware form, case (c2) case (A).**  The certain-type case-(A)
analogue of `coherentXunionYset_centralCommutator_of_glued_withDiagonal_general`: glues the
case-(A) `X(⁅H,H⁆)`-coherence `cX` (from `Xset_centralCommutator_isCoherent_of_c2_caseA`) and the
`Y`-coherence `cY` into `X(⁅H,H⁆) ∪ Y`-coherence.  Identical to the Frobenius version except the
(5.2.e) `X ⊥ Y` orthogonality uses the case-(A) irreducibility
`isIrreducibleCharacter_of_mem_Xset_c2_caseA` (`W₁` FPF on `Z(H) ∩ ⁅H,H⁆` from math-(A), via the
case-(A) datum `hA : Z(H) ⊓ W₂ = ⊥`) in place of the Frobenius
`isIrreducibleCharacter_of_mem_Xset_of_frobenius`. -/
noncomputable def coherentXunionYset_centralCommutator_of_glued_withDiagonal_of_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ x ∈ hyp.Xset hyp.centralCommutator, ν x = cX.extension x)
    (hagreeY : ∀ y ∈ hyp.Yset, ν y = cY.extension y)
    (hmixed : ∀ x ∈ hyp.Xset hyp.centralCommutator, ∀ y ∈ hyp.Yset,
      ClassFunction.inner (ν x) (ν y) = ClassFunction.inner x y)
    (D : Set (ClassFunction ↥L ℂ))
    (hDτ : ∀ d ∈ D, ν d = hyp.tau d)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
        Submodule.span ℤ
          (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset hyp.centralCommutator)
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪ D)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  exact OddOrder.Peterfalvi.S07.coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal
    cX cY ν hagreeX hagreeY
    (inner_eq_zero_of_mem_span_of_disjoint_irreducible
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hφ)
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Yset hφ) hdisj)
    hmixed D hDτ hgen

/-- **`X(Zc)` nonemptiness, case (A) / c2 form.**  As `Xset_centralCommutator_nonempty`, but the
strictly-positive degree-square sum is supplied via
`Xset_nonempty_of_subgroupOf_ne_bot_of_irreducible_X` (which needs only `X`-irreducibility), with
the
`X = S − S(Zc) ⊆ Irr L` fact coming from the certain-type input
`isIrreducibleCharacter_of_mem_Xset_c2_caseA` (cert data `hK`/`hW1`/`hA`) instead of the Frobenius
hypothesis.  The `Zc.subgroupOf H ≠ ⊥` step is the same non-abelian-`H` argument. -/
theorem Xset_centralCommutator_nonempty_c2_caseA (hyp : SibleyDadeHypothesis G L H)
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥) :
    (hyp.Xset hyp.centralCommutator).Nonempty := by
  have := hyp.H_normal
  have := hyp.centralCommutator_normal
  have hX : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hφ
  have hZbot : hyp.centralCommutator.subgroupOf H ≠ ⊥ := by
    intro hbot
    apply hyp.centralCommutator_ne_bot hHnonab
    rw [eq_bot_iff]
    intro z hz
    have hzH : z ∈ H := hyp.centralCommutator_le hz
    have hmem : (⟨z, hzH⟩ : ↥H) ∈ hyp.centralCommutator.subgroupOf H :=
      (Subgroup.mem_subgroupOf).mpr hz
    rw [hbot, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hmem
  exact hyp.Xset_nonempty_of_subgroupOf_ne_bot_of_irreducible_X hZbot
    (fun χ hχ => hX χ ((hyp.mem_xSetFinset_iff_mem_Xset (Z := hyp.centralCommutator) χ).mp hχ))

end SibleyDadeHypothesis

end OddOrder.Peterfalvi.S08


