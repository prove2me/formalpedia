-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_SixTwoThreeFromImageFamilies
-- name    : OddOrder_Peterfalvi_S08_SixTwoThreeFromImageFamilies
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:26:12.921115+00:00
-- url     : https://prove2.me/theorems/8d0cd165-4729-4563-9f0f-33eff9df99d5
-- title:
--   Peterfalvi (6.2)/(6.3) from the Hypothesis (5.2) image families: the oracle-free book form
-- statement:
--   Peterfalvi, *Character Theory for the Odd Order Theorem*, §5 (5.2)/(5.3) and §6 (6.1)-(6.3). The standalone (6.2)/(6.3) statement takes an explicit break-member oracle as hypothesis; this file removes it by deriving the needed data from the Hypothesis (5.2) image families.
--
--   Main definitions: `InducedFamilyTauData` and `InducedFamilyImageData` (Hypothesis (5.2) data for $\mathcal{S}=S(\bot)$, the induced kernel family), `InducedFamilyImageData.breakDa` (the break decomposition from (5.2.d), allowing a reducible break) and `OrthonormalCharacterImageFamily.congrChi` (transport of an image family along an equality of characters).
--
--   The bundle also proves 8 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_SixTwoThreeFromImageFamilies.lean

/-
Copyright (c) 2026 The Odd Order Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_SixTwoThreeFromImageFamilies.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S08_SixTwoGeneral
import Definitions.Def_OddOrder_Peterfalvi_S08_GeneralAdjoin

namespace OddOrder.Peterfalvi.S07

open OddOrder.RepresentationTheory

/-- **Transport an image family along an equality of characters.**  Only `image_eq` mentions `χ`,
so `imageSet`/`mem_ZIrr`/`orthonormal` carry over verbatim and `(R.congrChi h).imageSet` is
*definitionally* `R.imageSet` — which is what lets orthogonality proved for the source family apply
to the transported one.

The use is the (5.2.d) dispatch on a general induced family: a **reducible** member is a
certain-type column `μ_j`, so its `R(·)` is produced for the *column* `∑ᵢ μ_{ij}`, while the family
datum is indexed by the member `χ` itself; the two are equal but not syntactically so.  (Companion
of `congrTau`, which transports along an equality of integral character maps.) -/
def OrthonormalCharacterImageFamily.congrChi {L G : Type*} [Group L] [Group G]
    [Fintype G] [Invertible (Nat.card G : ℂ)] {τ : IntegralCharacterMap L G}
    {χ χ' : ClassFunction L ℂ} (h : χ = χ')
    (R : OrthonormalCharacterImageFamily (L := L) (G := G) τ χ') :
    OrthonormalCharacterImageFamily (L := L) (G := G) τ χ where
  imageSet := R.imageSet
  mem_ZIrr := R.mem_ZIrr
  orthonormal := R.orthonormal
  image_eq := by rw [h]; exact R.image_eq

@[simp] theorem OrthonormalCharacterImageFamily.congrChi_imageSet {L G : Type*} [Group L] [Group G]
    [Fintype G] [Invertible (Nat.card G : ℂ)] {τ : IntegralCharacterMap L G}
    {χ χ' : ClassFunction L ℂ} (h : χ = χ')
    (R : OrthonormalCharacterImageFamily (L := L) (G := G) τ χ') :
    (R.congrChi h).imageSet = R.imageSet := rfl

end OddOrder.Peterfalvi.S07

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]

/-- **Peterfalvi Hypothesis (5.2) data for `𝒮 = S(⊥) = inducedKernelFamily K ⊥`.**

The pieces of Hypothesis (5.2) that are genuinely *data* rather than consequences of the family's
shape:

* **(5.2.b)** the linear isometry `τ : ℤ[𝒮, L^#] → ℤ[Irr G, G^#]` — carried here as the map `tau`
  together with its two clauses `tau_isometry` (inner-product preservation on the `A₀`-supported
  sublattice of `ℤ[𝒮]`) and `tau_mem_ZIrr` (the codomain `ℤ[Irr G]`);
* **(5.2.d)** a difference-image family `R(χ)` per member;
* **(5.2.e)** the disjoint-pair orthogonality.

Everything else in (5.2) is *proved* for this family in `S08_SixTwoGeneral`: (5.2.a) conjugation
closure and non-reality (`inducedKernelFamily_closedUnderConjugate`,
`inducedKernelFamily_hasNoRealCharacters` for `L` of odd order), (5.2.c) pairwise orthogonality
(`inducedKernelFamily_pairwise_orthogonal`).

⚠ `τ` is **arbitrary** here — the Feit–Thompson Dade map is only one witness (issue 0154; the
instance is `S12.Hypothesis.inducedFamilyImageData`).  For an **irreducible** member `R(χ)` is
then the two-element Dade family (`dadeOrthonormalCharacterImageFamilyOfDiff`); for a reducible
one it is the certain-type `R(μ_j) = {δ_j ω_{ij}^σ, −δ_j ω_{ik}^σ}` of Peterfalvi (5.3.b)/(4.9)
(`S06.certainTypeR`). -/
structure InducedFamilyTauData (A₀ : Set ↥L)
    (K : Subgroup ↥L) [Invertible (Nat.card ↥K : ℂ)] where
  /-- **(5.2.b)**: the linear map `τ`. -/
  tau : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G
  /-- **(5.2.b)**: `τ` is an isometry on the `A₀`-supported sublattice `ℤ[𝒮, A₀]`. -/
  tau_isometry : ∀ ⦃φ ζ : ClassFunction ↥L ℂ⦄,
    φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (inducedKernelFamily K ⊥) A₀ →
    ζ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (inducedKernelFamily K ⊥) A₀ →
    ClassFunction.inner (tau φ) (tau ζ) = ClassFunction.inner φ ζ
  /-- **(5.2.b)**: `τ` maps `ℤ[𝒮, A₀]` into `ℤ[Irr G]`. -/
  tau_mem_ZIrr : ∀ ⦃φ : ClassFunction ↥L ℂ⦄,
    φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (inducedKernelFamily K ⊥) A₀ →
    tau φ ∈ ZIrr G
  /-- **(5.2.b), codomain sharpness**: the book's target lattice is `ℤ[Irr G, G^#]`, i.e. virtual
  characters *supported off `1`* — so `τ φ` vanishes at `1`.  Together with `tau_mem_ZIrr` this is
  the literal "linear isometry from `ℤ[𝒮, L^#]` to `ℤ[Irr G, G^#]`" of Hypothesis (5.2.b)
  (p. 25).  The Dade witness supplies it by
  `S07.dadeIntegralCharacterMap_apply_one_eq_zero` (the Dade image vanishes off the support set,
  and `1 ∉ A₀`).  It is what forces the two constituents of `τ(χ − χ̄)` to carry *opposite* signs
  for an irreducible member `χ` — i.e. the (5.3.a) two-element `R(χ) = {μ, −ν}` shape
  (`characterDifferenceImage_of_irreducible`, `S08_SixFiveGeneral`) that Hypothesis (5.2) takes in
  this repository. -/
  tau_apply_one : ∀ ⦃φ : ClassFunction ↥L ℂ⦄,
    φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (inducedKernelFamily K ⊥) A₀ →
    tau φ (1 : G) = 0

/-- **Peterfalvi Hypothesis (5.2) data for `𝒮 = S(⊥) = inducedKernelFamily K ⊥`** — the (5.2.b)
isometry together with the (5.2.d)/(5.2.e) image families for **every** member of `𝒮`.

This is exactly what the book's Hypothesis (6.1) assumes ("Assume that Hypothesis (5.2) holds").
It is genuinely stronger than the `InducedFamilyTauData` half: for a **reducible** member the
two-element (5.3.a) shape does not apply, so `R(χ)` must be supplied — in the Feit-Thompson
consumer by the certain-type column family of (5.3.b)/(4.9)
(`S12.Hypothesis.inducedFamilyImageData`).  Arguments that only ever touch *irreducible* members
(e.g. the (6.6) coherence half, whose `𝒳 ⊆ Irr L`) should take `InducedFamilyTauData` instead and
build `R(χ)` through `characterDifferenceImage_of_irreducible` +
`CharacterDifferenceImage.toOrthonormalImage` (`S07_Coherence/DifferenceImage`). -/
structure InducedFamilyImageData (A₀ : Set ↥L)
    (K : Subgroup ↥L) [Invertible (Nat.card ↥K : ℂ)]
    extends InducedFamilyTauData (G := G) A₀ K where
  /-- **(5.2.d)**: the orthonormal difference-image family `R(χ)` of each member `χ ∈ 𝒮`. -/
  R : ∀ χ ∈ inducedKernelFamily K ⊥,
    OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily (L := ↥L) (G := G)
      toInducedFamilyTauData.tau χ
  /-- **(5.2.e)**: `φ ⊥ {χ, χ̄}` forces `R(φ) ⊥ R(χ)`. -/
  orthogonal : ∀ (χ : ClassFunction ↥L ℂ) (hχ : χ ∈ inducedKernelFamily K ⊥)
      (φ : ClassFunction ↥L ℂ) (hφ : φ ∈ inducedKernelFamily K ⊥),
    ClassFunction.inner φ χ = 0 → ClassFunction.inner φ χ.conj = 0 →
      (R φ hφ).Orthogonal (R χ hχ)

/-- **The (5.2.b) isometry in the `T`-indexed shape the general adjoin engines consume**
(`S07.decompositionDaFromDiff_general`, `S07.xAdjoinStepW_k_general`).  Pure repackaging of
`tau_isometry` through `S07.zSpan_subset_zSupportedSpan`: a set `T` whose members are `A₀`-supported
elements of `ℤ[𝒮]` has its whole `ℤ`-span inside `ℤ[𝒮, A₀]`, where the field applies. -/
theorem InducedFamilyTauData.adjoinHisom {A₀ : Set ↥L} {K : Subgroup ↥L}
    [Invertible (Nat.card ↥K : ℂ)] (RD : InducedFamilyTauData (G := G) A₀ K) :
    ∀ (T : Set (ClassFunction ↥L ℂ)),
      (∀ s ∈ T, s ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
        (inducedKernelFamily K ⊥) A₀) →
      ∀ φ ζ : ClassFunction ↥L ℂ, φ ∈ Submodule.span ℤ T → ζ ∈ Submodule.span ℤ T →
        ClassFunction.inner (RD.tau φ) (RD.tau ζ) = ClassFunction.inner φ ζ :=
  fun _T hT _φ _ζ hφ hζ =>
    RD.tau_isometry (OddOrder.Peterfalvi.S07.zSpan_subset_zSupportedSpan hT hφ)
      (OddOrder.Peterfalvi.S07.zSpan_subset_zSupportedSpan hT hζ)

section Datum

variable {A₀ : Set ↥L} {K : Subgroup ↥L} [K.Normal] [Invertible (Nat.card ↥K : ℂ)]

/-- **The break decomposition `Da` from (5.2.d)** — general in the break's norm, so a
**reducible** break `ψ` is allowed (Peterfalvi (5.6) puts no irreducibility on the adjoined
`χ ∈ 𝒮`).  Feeds `S07.decompositionDaFromDiff_general` the family `R(ψ)` supplied by (5.2.d);
the auxiliary isometry is `τ` itself, so `Da.tau1 = τ` holds definitionally. -/
noncomputable def InducedFamilyImageData.breakDa
    (RD : InducedFamilyImageData A₀ K)
    (hodd : Odd (Nat.card ↥L))
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 → x ∈ A₀)
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ inducedKernelFamily K ⊥)
    {B : Subgroup ↥L} {ψ : ClassFunction ↥L ℂ} (hψB : ψ ∈ inducedKernelFamily K B)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁S₁ : χ₁ ∈ S₁)
    {a : ℕ} (hψdeg : ψ 1 = (a : ℂ) * χ₁ 1) :
    OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G)
      RD.tau
      ψ (a • χ₁) := by
  have hψfam : ψ ∈ inducedKernelFamily K ⊥ := inducedKernelFamily_subset_bot B hψB
  have hψcfam : ψ.conj ∈ inducedKernelFamily K ⊥ :=
    inducedKernelFamily_closedUnderConjugate ⊥ hψfam
  have hχ₁fam : χ₁ ∈ inducedKernelFamily K ⊥ := hS₁sub hχ₁S₁
  have hreal : ¬ ClassFunction.IsReal ψ :=
    inducedKernelFamily_hasNoRealCharacters hodd ⊥ hψfam
  -- the two supported differences `ψ − ψ̄` and `ψ − a·χ₁`
  have hdiffsupp : (ψ.conj - ψ).support ⊆
      A₀ :=
    inducedKernelFamily_conjDiff_support hKsupp hψfam
  have hdiffasupp : (ψ - a • χ₁).support ⊆
      A₀ :=
    inducedKernelFamily_scaledDiff_support hKsupp hψB hχ₁fam (d := a) hψdeg
  have hdiffmem : ψ - ψ.conj ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (inducedKernelFamily K ⊥) A₀ :=
    OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mpr
      ⟨Submodule.sub_mem _ (Submodule.subset_span hψfam) (Submodule.subset_span hψcfam), by
        rw [show ψ - ψ.conj = -(ψ.conj - ψ) from by abel, ClassFunction.support_neg]
        exact hdiffsupp⟩
  have hadiffmem : ψ - a • χ₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (inducedKernelFamily K ⊥) A₀ :=
    OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mpr
      ⟨Submodule.sub_mem _ (Submodule.subset_span hψfam)
        (nsmul_mem (Submodule.subset_span hχ₁fam) a), hdiffasupp⟩
  -- (5.2.b) codomain clause
  have htau1_mema : RD.tau (ψ - a • χ₁) ∈ ZIrr G := RD.tau_mem_ZIrr hadiffmem
  -- the (5.4) orthogonality scalars `ψ, ψ̄ ⊥ a·χ₁` and `ψ ⊥ ψ̄`
  have hψχ₁ : ClassFunction.inner ψ χ₁ = 0 :=
    inducedKernelFamily_pairwise_orthogonal hψfam hχ₁fam (fun h => hψnotS1 (h ▸ hχ₁S₁))
  have hψbarχ₁ : ClassFunction.inner ψ.conj χ₁ = 0 :=
    inducedKernelFamily_pairwise_orthogonal hψcfam hχ₁fam (fun h => hψcnotS1 (h ▸ hχ₁S₁))
  have hψaχ₁ : ClassFunction.inner ψ (a • χ₁ : ClassFunction ↥L ℂ) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ a χ₁, OddOrder.RepresentationTheory.inner_smul_right,
      hψχ₁, mul_zero]
  have hψbaraχ₁ : ClassFunction.inner ψ.conj (a • χ₁ : ClassFunction ↥L ℂ) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ a χ₁, OddOrder.RepresentationTheory.inner_smul_right,
      hψbarχ₁, mul_zero]
  have hψψbar : ClassFunction.inner ψ ψ.conj = 0 :=
    inducedKernelFamily_pairwise_orthogonal hψfam hψcfam (fun h => hreal h.symm)
  exact OddOrder.Peterfalvi.S07.decompositionDaFromDiff_general
    (Samb := inducedKernelFamily K ⊥) (RD.R ψ hψfam)
    RD.adjoinHisom
    hdiffmem hadiffmem htau1_mema hψaχ₁ hψbaraχ₁ hψψbar

@[simp] theorem InducedFamilyImageData.breakDa_tau1
    (RD : InducedFamilyImageData A₀ K) (hodd : Odd (Nat.card ↥L))
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 → x ∈ A₀)
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ inducedKernelFamily K ⊥)
    {B : Subgroup ↥L} {ψ : ClassFunction ↥L ℂ} (hψB : ψ ∈ inducedKernelFamily K B)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁S₁ : χ₁ ∈ S₁)
    {a : ℕ} (hψdeg : ψ 1 = (a : ℂ) * χ₁ 1) :
    (RD.breakDa hodd hKsupp hS₁sub hψB hψnotS1 hψcnotS1 hχ₁S₁ hψdeg).tau1
      = RD.tau :=
  rfl

@[simp] theorem InducedFamilyImageData.breakDa_imageFamily
    (RD : InducedFamilyImageData A₀ K) (hodd : Odd (Nat.card ↥L))
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 → x ∈ A₀)
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ inducedKernelFamily K ⊥)
    {B : Subgroup ↥L} {ψ : ClassFunction ↥L ℂ} (hψB : ψ ∈ inducedKernelFamily K B)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁S₁ : χ₁ ∈ S₁)
    {a : ℕ} (hψdeg : ψ 1 = (a : ℂ) * χ₁ 1) :
    (RD.breakDa hodd hKsupp hS₁sub hψB hψnotS1 hψcnotS1 hχ₁S₁ hψdeg).imageFamily
      = RD.R ψ (inducedKernelFamily_subset_bot B hψB) :=
  rfl

/-- **(5.2.d)/(5.2.e) ⟹ the `hdatum` clause of the h56 producer.**

The decomposition data `exists_source_index_le_two_psi_of_break` asks for, built from the image
families alone:

* the break side is `InducedFamilyImageData.breakDa` (auxiliary isometry `τ`, `R(ψ)` from
  (5.2.d)), with `Da.tau1 = τ` by `rfl`;
* the member side is `S07.memberExtensionDecomposition_general` at `R(χ)` (auxiliary isometry the
  **running extension** `ν = hS₁coh.extension`, which is integral on `S₁` where `τχ` need not be),
  so `D.tau1 χ = ν χ` by `rfl`;
* their cross-orthogonality `R(χ) ⊥ R(ψ)` is exactly (5.2.e), applicable because `χ ∈ S₁` while
  `ψ, ψ̄ ∉ S₁`, so `χ ⊥ {ψ, ψ̄}` by the family's pairwise orthogonality (5.2.c).

Note that the break `ψ` and the members `χ` may both be **reducible**: nothing here consumes
`‖·‖² = 1`. -/
theorem InducedFamilyImageData.datum
    (RD : InducedFamilyImageData A₀ K)
    (hodd : Odd (Nat.card ↥L))
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 → x ∈ A₀)
    (A' B : Subgroup ↥L) :
    ∀ (S₁ : Set (ClassFunction ↥L ℂ)),
      OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁ →
      S₁ ⊆ inducedKernelFamily K A' ∪ inducedKernelFamily K B →
      ∀ (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent
        RD.tau
        S₁ A₀),
      ∀ (ψ : ClassFunction ↥L ℂ), ψ ∈ inducedKernelFamily K B → ψ ∉ S₁ → ψ.conj ∉ S₁ →
      ∀ (χ₁ : ClassFunction ↥L ℂ), χ₁ ∈ S₁ →
      ∀ (a : ℕ), ψ 1 = (a : ℂ) * χ₁ 1 →
      ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
        RD.tau
        (S₁ ∪ {ψ, ψ.conj}) A₀) →
      ∃ Da : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G)
          (RD.tau) ψ (a • χ₁),
        Da.tau1 = RD.tau ∧
        ∀ χ ∈ S₁, ∃ D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G)
            (RD.tau) χ 0,
          D.imageFamily.Orthogonal Da.imageFamily ∧
          D.tau1 χ = hS₁coh.extension χ := by
  intro S₁ hS₁conj hS₁un hS₁coh ψ hψB hψnotS₁ hψcnotS₁ χ₁ hχ₁S₁ a hψdeg _hnc
  have hS₁sub : S₁ ⊆ inducedKernelFamily K ⊥ := fun χ hχ => by
    rcases hS₁un hχ with h | h
    · exact inducedKernelFamily_subset_bot A' h
    · exact inducedKernelFamily_subset_bot B h
  have hψfam : ψ ∈ inducedKernelFamily K ⊥ := inducedKernelFamily_subset_bot B hψB
  have hψcfam : ψ.conj ∈ inducedKernelFamily K ⊥ :=
    inducedKernelFamily_closedUnderConjugate ⊥ hψfam
  refine ⟨RD.breakDa hodd hKsupp hS₁sub hψB hψnotS₁ hψcnotS₁ hχ₁S₁ hψdeg, rfl, ?_⟩
  intro χ hχS₁
  have hχfam : χ ∈ inducedKernelFamily K ⊥ := hS₁sub hχS₁
  have hχcfam : χ.conj ∈ inducedKernelFamily K ⊥ :=
    inducedKernelFamily_closedUnderConjugate ⊥ hχfam
  have hχreal : ¬ ClassFunction.IsReal χ :=
    inducedKernelFamily_hasNoRealCharacters hodd ⊥ hχfam
  have hχχbar : ClassFunction.inner χ χ.conj = 0 :=
    inducedKernelFamily_pairwise_orthogonal hχfam hχcfam (fun h => hχreal h.symm)
  have hνZ : hS₁coh.extension χ ∈ ZIrr G :=
    hS₁coh.extension_mem_ZIrr χ (Submodule.subset_span hχS₁)
  refine ⟨OddOrder.Peterfalvi.S07.memberExtensionDecomposition_general hS₁coh (RD.R χ hχfam)
    (inducedKernelFamily_conjDiff_support hKsupp hχfam) hχS₁ (hS₁conj hχS₁) hνZ hχχbar, ?_, rfl⟩
  -- (5.2.e): `χ ∈ S₁` is orthogonal to `ψ, ψ̄ ∉ S₁`, so `R(χ) ⊥ R(ψ)`.
  exact RD.orthogonal ψ hψfam χ hχfam
    (inducedKernelFamily_pairwise_orthogonal hχfam hψfam (fun h => hψnotS₁ (h ▸ hχS₁)))
    (inducedKernelFamily_pairwise_orthogonal hχfam hψcfam (fun h => hψcnotS₁ (h ▸ hχS₁)))

end Datum

section BookForm

variable {A₀ : Set ↥L} {K : Subgroup ↥L} [K.Normal] [Invertible (Nat.card ↥K : ℂ)]

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
  [K.Normal] [Invertible (Nat.card ↥K : ℂ)] in
/-- **`K/X` has proper commutator subgroup** whenever `X < K` and `K` is solvable — the input of
both the (6.2) degree-`|L:K|` anchor (`exists_inducedKernelFamily_member_degree_index`) and the
`S(X) ≠ ∅` witness (`inducedKernelFamily_nonempty_of_commutator_ne_top`).  Peterfalvi's
"Since `K` is solvable, `K/A` has a non-trivial irreducible character of degree 1" (p. 30). -/
theorem commutator_quotient_ne_top_of_lt [Group.IsSolvable ↥K] {X : Subgroup ↥L} [X.Normal]
    (hXK : X < K) :
    _root_.commutator (↥K ⧸ X.subgroupOf K) ≠ ⊤ := by
  have : (X.subgroupOf K).Normal := (‹X.Normal›).subgroupOf K
  have : Nontrivial (↥K ⧸ X.subgroupOf K) := by
    rw [QuotientGroup.nontrivial_iff]
    intro htop
    exact hXK.ne' (le_antisymm (Subgroup.subgroupOf_eq_top.mp htop) hXK.le)
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (↥K ⧸ X.subgroupOf K)).ne

/-- **The (6.2) break-member bound `|K:A'| − 1 ≤ 2ψ(1)` from Hypothesis (5.2) data alone** — the
`h56` of `six_two_general`/`six_three_of_six_two_oracle`, now a *theorem*.

Peterfalvi's (6.2) proof opening, verbatim: from the coherence dichotomy `S(A')` coherent /
`S(B)` not, the first-obstruction chain (`exists_coherentBreakPair_union`) produces a break pair
`{ψ, ψ̄} ⊆ S(B)` over a maximal coherent conjugation-closed `S₁ ⊆ S(A') ∪ S(B)`; the (5.6)
norm-weighted contrapositive then bounds the `S(A')` degree-square sum, and the (B2) identity
`∑_{χ ∈ S(A')} χ(1)²/‖χ‖² = |L:K|(|K:A'| − 1)` converts it into the index bound.  The anchor
`χ₁ ∈ S(A')` of degree `|L:K|` and the nonemptiness of `S(B)` both come from solvability of `K`
via `commutator_quotient_ne_top_of_lt`. -/
theorem exists_source_index_le_two_psi_of_imageData
    [Group.IsSolvable ↥K] (RD : InducedFamilyImageData A₀ K)
    (hodd : Odd (Nat.card ↥L))
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 → x ∈ A₀)
    (h1A : (1 : ↥L) ∉ A₀)
    {A' B : Subgroup ↥L} [A'.Normal] [B.Normal] (hA'K : A' < K) (hBK : B < K)
    (hAcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent RD.tau
      (inducedKernelFamily K A') A₀))
    (hBncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent RD.tau
      (inducedKernelFamily K B) A₀)) :
    ∃ θ : IrreducibleCharacter ↥K,
      (↑(B.subgroupOf K) : Set ↥K) ⊆ OddOrder.Peterfalvi.S03.characterKernel
          (θ : ClassFunction ↥K ℂ) ∧
      (Nat.card (↥K ⧸ A'.subgroupOf K) : ℝ) - 1 ≤
        2 * (ClassFunction.induce K (θ : ClassFunction ↥K ℂ) 1).re := by
  have : (A'.subgroupOf K).Normal := (‹A'.Normal›).subgroupOf K
  have : (B.subgroupOf K).Normal := (‹B.Normal›).subgroupOf K
  exact exists_source_index_le_two_psi_of_break_general RD.tau RD.tau_isometry RD.tau_mem_ZIrr
    hodd hKsupp h1A
    (exists_inducedKernelFamily_member_degree_index (commutator_quotient_ne_top_of_lt hA'K))
    (inducedKernelFamily_nonempty_of_commutator_ne_top
      (commutator_quotient_ne_top_of_lt hBK))
    (RD.datum hodd hKsupp A' B) hAcoh hBncoh

/-- **Peterfalvi (6.2)** — no oracle.

*Assume Hypothesis (6.1).  Let `A, B, C, D` be normal subgroups of `L` such that*
*(a) `A ⊊ K`, `B ⊆ D ⊆ C ⊆ K` and `D/B ⊆ Z(C/B)`, (b) `S(A)` is coherent but `S(B)` is not.*
*Then `2|L:C|√|C:D| ≥ |K:A| − 1`.*  (p. 30; here `A' = A` to avoid clashing with the Dade
support set `A`.)

Hypothesis (6.1) is realized by: `RD` (the whole Hypothesis (5.2) bundle — the (5.2.b) isometry
`τ` with its `ℤ[Irr G]` codomain, and the (5.2.d)/(5.2.e) image families), `hodd` (so `𝒮` has no
real members, (5.2.a)),
`hKsupp`/`h1A` (the family's differences are `A₀`-supported), `K` solvable normal, and
`𝒮(X) = inducedKernelFamily K X`.

⚠ **`hBK : B < K` repairs the book's statement** — it is *not* implied by (6.2.a)-(6.2.b).  At
`B = K` the hypotheses (a) and (b) both hold vacuously: `D = C = K`, `D/B = 1 ⊆ Z(C/B)`, and
`𝒮(K) = ∅` is *not* coherent because Definition (5.1) demands `ℤ[𝒮, A] ≠ 0` (p. 25).  The
conclusion would then read `|K:A| − 1 ≤ 2|L:K|`, which is false as soon as `K` is large relative
to `|L:K|` (e.g. `A = 1` with `𝒮` coherent — exactly what (6.3) produces).  The book's proof needs
`𝒮(B) ≠ ∅` for its breaking pair `𝒮₂ = {ψ, ψ̄} ⊆ 𝒮(B)`, i.e. `K/B ≠ 1`.  (mathcomp's
`coherent_seqIndD_bound` gets away without it because its `coherent` predicate drops the
`ℤ[𝒮, A] ≠ 0` clause, making the empty family coherent and its `\unless` disjunction true.)

Weaker than the book where nothing depends on it: only `A` and `B` are asked to be normal in `L`
(`C`, `D` are not), and `D` enters only through `D ⊓ C` (`D.subgroupOf C`), so `D ⊆ C` may be
dropped. -/
theorem six_two_of_imageData
    [Group.IsSolvable ↥K] (RD : InducedFamilyImageData A₀ K)
    (hodd : Odd (Nat.card ↥L))
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 → x ∈ A₀)
    (h1A : (1 : ↥L) ∉ A₀)
    {A' B C D : Subgroup ↥L} [A'.Normal] [B.Normal]
    (hA'K : A' < K) (hBK : B < K) (hBD : B ≤ D) (hCK : C ≤ K)
    (hcentral : (D.subgroupOf C).map (QuotientGroup.mk' (B.subgroupOf C)) ≤
        Subgroup.center (↥C ⧸ B.subgroupOf C))
    (hAcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent RD.tau
      (inducedKernelFamily K A') A₀))
    (hBncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent RD.tau
      (inducedKernelFamily K B) A₀)) :
    (Nat.card (↥K ⧸ A'.subgroupOf K) : ℝ) - 1 ≤
      2 * (C.index : ℝ) * Real.sqrt (Nat.card (↥C ⧸ D.subgroupOf C) : ℝ) :=
  six_two_general hBD hCK hcentral
    (exists_source_index_le_two_psi_of_imageData RD hodd hKsupp h1A hA'K hBK hAcoh hBncoh)

/-- **Peterfalvi (6.3)** — no oracle.

*Assume Hypothesis (6.1).  Let `M, H, H₁` be normal subgroups of `L` such that*
*`M ⊆ H₁ ⊆ H ⊆ K`.  Assume further that (a) `H/M` is nilpotent, (b) `S(H₁)` is coherent,*
*(c) `|H:H₁| > 4|L:K|² + 1`.  Then `S(M)` is coherent.*  (p. 30.)

The nilpotency binder is the book's (6.3)(a) verbatim — `[Group.IsNilpotent (↥H ⧸ M.subgroupOf H)]`
= `H/M` nilpotent (issue 0173; an earlier wrapper asked for `H` itself nilpotent, which the engine
`six_three_descent` never needed).  `hH₁H : H₁ < H` is strict where the book writes `H₁ ⊆ H`, but
(c) `4|L:K|² + 1 < |H:H₁|` forces `|H:H₁| ≥ 5`, so nothing is lost.

Everything is discharged: the minimal-`A` descent and maximal-`B` step (`six_three_descent`), the
`√`-arithmetic (`six_three_index_bound_general`), and the (6.2) break bound
(`exists_source_index_le_two_psi_of_imageData`).  The per-section `A' < K`, `B < K` needed by the
anchor come from `A' ≤ H₁ < H ≤ K`. -/
theorem six_three_of_imageData
    [Group.IsSolvable ↥K] (RD : InducedFamilyImageData A₀ K)
    (hodd : Odd (Nat.card ↥L))
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 → x ∈ A₀)
    (h1A : (1 : ↥L) ∉ A₀)
    {H M H₁ : Subgroup ↥L} [M.Normal] [H₁.Normal] [Group.IsNilpotent (↥H ⧸ M.subgroupOf H)]
    (hHnorm : H.Normal) (hMH₁ : M ≤ H₁) (hH₁H : H₁ < H) (hHK : H ≤ K)
    (hcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent RD.tau
      (inducedKernelFamily K H₁) A₀))
    (hbound : 4 * K.index ^ 2 + 1 < Nat.card (↥H ⧸ H₁.subgroupOf H)) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent RD.tau
      (inducedKernelFamily K M) A₀) := by
  refine six_three_of_six_two_oracle hHnorm hMH₁ hH₁H hHK _ _ (inducedKernelFamily K)
    ?_ hcoh hbound
  intro A' B _ _ hBA' hA'H₁ _hcentral hA'coh hBncoh
  have hA'K : A' < K := lt_of_le_of_lt hA'H₁ (lt_of_lt_of_le hH₁H hHK)
  exact exists_source_index_le_two_psi_of_imageData RD hodd hKsupp h1A hA'K
    (lt_of_le_of_lt hBA' hA'K) hA'coh hBncoh

end BookForm

end OddOrder.Peterfalvi.S08


