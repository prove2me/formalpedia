-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_CaseBCoherence2
-- name    : OddOrder_Peterfalvi_S08_CaseBCoherence2
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:09:34.919012+00:00
-- url     : https://prove2.me/theorems/539b6be0-c161-4385-9f43-766abf8e3d4e
-- title:
--   Peterfalvi §8 case (B): coherence assembly
-- statement:
--   The downstream coherence and Dade-isometry assembly for Peterfalvi (6.8), case (B). Constituent aggregation and pinning are factored into a separate file.
--
--   Main definitions: `IsCoherent.congrMap` (transport of coherence across maps agreeing on the supported lattice), `coherentXunionYset_caseB_of_glued` (the (6.8.2) case-(B) $X\cup Y$ coherence, glued form), `columnRFamilyTau` (the reducible $R(\mu_j)$ image family retargeted to `hyp.tau`) and the decompositions `columnDecompositionTau` and `irreducibleDecompositionTau`.
--
--   The bundle also proves 6 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_CaseBCoherence2.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_CaseBCoherence2.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S08_CaseBCoherence2_ConstituentPinning

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]

variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

/-- **Transport of coherence across maps agreeing on the supported lattice.**  A coherent isometry
`IsCoherent τ₁ S A` stays coherent for any `τ₂` that agrees with `τ₁` on the supported lattice
`ℤ[S, A]`: the coherent extension is unchanged, and only `extends_on_supported` (the single field
referring to the ambient map) is re-routed through the agreement.

This is the (6.8) case-(B) bridge mechanism: the certain-type coherence `certainType_isCoherent`
(Peterfalvi (4.9)) is stated for `dadeIntegralCharacterMap h.dade0 h.tau`, while the §8 assembly
needs a coherence for the Sibley–Dade `hyp.tau`; both Dade maps coincide with `Ind_L^G` on the
`H^#`-supported lattice (`dadeIntegralCharacterMap_apply_of_support` + `dade_H_eq_bot`), so the
agreement hypothesis is supplied at capstone wiring. -/
def _root_.OddOrder.Peterfalvi.S07.IsCoherent.congrMap
    {M N : Type*} [Group M] [Group N] [Fintype M] [Fintype N]
    [Invertible (Nat.card M : ℂ)] [Invertible (Nat.card N : ℂ)]
    {τ₁ τ₂ : OddOrder.Peterfalvi.S07.IntegralCharacterMap M N}
    {S : Set (ClassFunction M ℂ)} {A : Set M}
    (c : OddOrder.Peterfalvi.S07.IsCoherent τ₁ S A)
    (h : ∀ φ : ClassFunction M ℂ,
      φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := M) S A → τ₁ φ = τ₂ φ) :
    OddOrder.Peterfalvi.S07.IsCoherent τ₂ S A where
  nonzero := c.nonzero
  extension := c.extension
  extension_inner_eq := c.extension_inner_eq
  extends_on_supported := fun φ hφ => (c.extends_on_supported φ hφ).trans (h φ hφ)
  extension_mem_ZIrr := c.extension_mem_ZIrr

/-- **Span orthogonality from pairwise-orthogonal generators.**  If every `χ ∈ X` is orthogonal to
every `η ∈ Y`, then every element of `ℤ[X]` is orthogonal to every element of `ℤ[Y]` — a pure
`ℤ`-bilinearity fact (`Submodule.span_induction`).

This generalizes `inner_eq_zero_of_mem_span_of_disjoint_irreducible` (which derives the pairwise
orthogonality from distinct-irreducible) so it applies in case (B), where `X = S − S(W₂)` contains
the
**reducible** column characters `μ_j = ∑ᵢ μ_{ij}`: `⟨μ_j, η⟩ = ∑ᵢ ⟨μ_{ij}, η⟩ = 0` (each grid
character `μ_{ij} ∈ X` is a distinct irreducible from `η ∈ Y = S(H')`), supplied as the `hpair`
hypothesis at the case-(B) `X ∪ Y` glue. -/
theorem inner_eq_zero_of_mem_span_of_pairwise_orthogonal
    {Γ : Type*} [Group Γ] [Fintype Γ] [Invertible (Nat.card Γ : ℂ)]
    {X Y : Set (ClassFunction Γ ℂ)}
    (hpair : ∀ χ ∈ X, ∀ η ∈ Y, ClassFunction.inner χ η = 0) :
    ∀ u ∈ Submodule.span ℤ X, ∀ v ∈ Submodule.span ℤ Y,
      ClassFunction.inner u v = 0 := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem χ hχ =>
      intro v hv
      exact OddOrder.Peterfalvi.S07.IntegralCharacterMap.inner_eq_zero_of_mem_zSpan
        (fun η hη => hpair χ hχ η hη) hv
  | zero => intro v _hv; exact ClassFunction.inner_zero_left v
  | add x y _hx _hy ihx ihy =>
      intro v hv; rw [ClassFunction.inner_add_left, ihx v hv, ihy v hv, zero_add]
  | smul a x _hx ih =>
      intro v hv
      rw [← Int.cast_smul_eq_zsmul ℂ a x, ClassFunction.inner_smul_left, ih v hv, mul_zero]

/-- **Restrict-invariance of the Dade integral character map on the smaller supported lattice.**
If `A₁ ⊆ A` (with `A₁` `L`-invariant), then on `CF(L, A₁)` the integral character map of the
restricted Dade datum `(hyp.restrict, dade.restrict)` agrees with that of `(hyp, dade)`: both reduce
(via `dadeIntegralCharacterMap_apply_of_support`) to `hyp.dadeMap`, related by Peterfalvi (2.11)
(`Hypothesis.dadeMap_restrict_apply`).

This is the (6.8) case-(B) `map-agreement` core: Peterfalvi (4.9)'s certain-type coherence
`certainType_isCoherent` uses the *enlarged* datum `dade0` on `A₀ = A ∪ V^L`, while `hyp.tau` is the
base datum on `A = H^#`; the `μ_j`-differences are `A`-supported, so once the wiring identifies
`dade0.restrict A` with the base datum, this lemma + `IsCoherent.congrMap` transport the
certain-type
coherence onto `hyp.tau`. -/
theorem dadeIntegralCharacterMap_restrict_eq_of_support
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
    {A A₁ : Set G} (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L)
    (dade : OddOrder.Peterfalvi.S04.FullDadeIsometryData (G := G) hyp)
    (hA₁A : A₁ ⊆ A)
    (hA₁norm : ∀ (l : ↥L) ⦃a : G⦄, a ∈ A₁ → (l : G) * a * (l : G)⁻¹ ∈ A₁)
    {φ : ClassFunction ↥L ℂ}
    (hφ : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A₁ L) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.restrict hA₁A hA₁norm)
        (dade.restrict hA₁A hA₁norm) φ
      = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp dade φ := by
  have hφA : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L :=
    hφ.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono hA₁A)
  rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support
        (hyp.restrict hA₁A hA₁norm) (dade.restrict hA₁A hA₁norm) hφ,
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support hyp dade hφA,
      OddOrder.Peterfalvi.S04.Hypothesis.dadeMap_restrict_apply hyp hA₁A hA₁norm]
  rfl

/-- **(6.8.2) case-(B) `X ∪ Y` coherence, glued form.**  The case-(B) counterpart of
`coherentXunionYset_centralCommutator_of_glued_of_frobenius`: glue the case-(B) `X`-coherence `cX`
(on `X = S − S(W₂)`, which now contains the reducible column characters `μ_j`) with the
`Y`-coherence
`coherentYset` via the §7 diagonal-aware engine
`coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal`.

The only case-(B) difference from the Frobenius assembly is the **source orthogonality** `X ⊥ Y`:
since `X` is no longer all-irreducible, it is supplied by
`inner_eq_zero_of_mem_span_of_pairwise_orthogonal`
from the pairwise `⟨x, y⟩ = 0` (`x ∈ X`, `y ∈ Y`) — for `x = μ_j = ∑ᵢ μ_{ij}` this is
`∑ᵢ ⟨μ_{ij}, η⟩ = 0`.  The combined extension `ν` (the (6.8.2) `τ₂`), its agreements, the mixed
inner
products `hmixed` (the (6.8.2.3) content), and the cross-diagonal set `D`/`hDτ` (with the
satisfiable
generation `hgen`) are supplied at capstone wiring. -/
noncomputable def SibleyDadeHypothesis.coherentXunionYset_caseB_of_glued
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {W2 : Subgroup ↥L}
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset W2)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ x ∈ hyp.Xset W2, ν x = cX.extension x)
    (hagreeY : ∀ y ∈ hyp.Yset, ν y = cY.extension y)
    (hpair : ∀ x ∈ hyp.Xset W2, ∀ y ∈ hyp.Yset, ClassFunction.inner x y = 0)
    (hmixed : ∀ x ∈ hyp.Xset W2, ∀ y ∈ hyp.Yset,
      ClassFunction.inner (ν x) (ν y) = ClassFunction.inner x y)
    (D : Set (ClassFunction ↥L ℂ)) (hDτ : ∀ d ∈ D, ν d = hyp.tau d)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset W2 ∪ hyp.Yset)
        (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
      Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset W2)
          (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
        OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
          (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪ D)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset W2 ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) :=
  OddOrder.Peterfalvi.S07.coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal
    cX cY ν hagreeX hagreeY
    (inner_eq_zero_of_mem_span_of_pairwise_orthogonal hpair) hmixed D hDτ hgen

/-- **(6.8.2) case-(B), `μ_j ∈ S`** (cont.²¹ item 2a): the certain-type column character
`μ_j = columnSum h46 χ₂` (for a nontrivial column `χ₂ ≠ 1`) lies in the Sibley set
`S = {Ind_H^L θ | θ ∈ Irr H, θ ≠ 1}`.

With `h46.K = H` (case (c2)): `μ_j = Ind_K^L χ_j` ((4.5.a) `induce_restrict_certainType_eq`,
`χ_j = Res_K μ_{0j}`), and transporting the source along `h46.K = H` (`induce_congr_of_subgroup_eq`)
gives `μ_j = Ind_H^L (Res_H μ_{0j})` with `Res_H μ_{0j}` a *nontrivial irreducible* of `H`
(`certainTypeRestrict_isIrreducible` and `chiRestrict_ne_trivialIrreducibleCharacter`, both
transported by `rw [hHK]`). -/
theorem SibleyDadeHypothesis.columnSum_mem_S
    (hyp : SibleyDadeHypothesis G L H)
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1) :
    OddOrder.Peterfalvi.S06.columnSum h46 χ₂ ∈ hyp.S := by
  -- the source `θ = Res_H μ_{0j} : Irr ↥H`, with irreducibility transported from `↥h46.K`
  have hirr : IsIrreducibleCharacter
      (ClassFunction.restrict H ((h46.columnFamily χ₂).mu 0 : ClassFunction ↥L ℂ)) := by
    have h := h46.certainTypeRestrict_isIrreducible χ₂
    rwa [hHK] at h
  rw [hyp.S_eq]
  refine ⟨⟨ClassFunction.restrict H ((h46.columnFamily χ₂).mu 0 : ClassFunction ↥L ℂ), hirr⟩,
    ?_, ?_⟩
  · -- `θ ≠ 1_H`: transport `chiRestrict_ne_trivial` back along `h46.K = H`
    intro hθtriv
    refine OddOrder.Peterfalvi.S06.chiRestrict_ne_trivialIrreducibleCharacter h46 hχ₂
      (Subtype.ext ?_)
    change ClassFunction.restrict h46.K ((h46.columnFamily χ₂).mu 0 : ClassFunction ↥L ℂ)
        = trivialClassFunction ↥h46.K
    have h1 : ClassFunction.restrict H ((h46.columnFamily χ₂).mu 0 : ClassFunction ↥L ℂ)
        = trivialClassFunction ↥H := Subtype.ext_iff.mp hθtriv
    refine ClassFunction.ext (fun g => ?_)
    have hg : (g : ↥L) ∈ H := hHK.le g.2
    have hval := congrArg (fun f : ClassFunction ↥H ℂ => f ⟨(g : ↥L), hg⟩) h1
    simpa using hval
  · -- `μ_j = Ind_H^L θ`: `(4.5.a)` then transport the induction source along `h46.K = H`
    rw [OddOrder.Peterfalvi.S06.columnSum_def,
      ← h46.induce_restrict_certainType_eq χ₂]
    exact OddOrder.Peterfalvi.S04.Hypothesis.induce_congr_of_subgroup_eq hHK
      (fun x hx₁ hx₂ => by simp [ClassFunction.restrict_apply])

/-- **(6.8.2) case-(B), `μ_j = Ind_H^L (Res_H μ_{0j})`.**  The transported form of (4.5.a)
`induce_restrict_certainType_eq`: with `h46.K = H`, the column character `μ_j = columnSum h46 χ₂`
is induced from `H` of the source `Res_H μ_{0j}` (the H-presentation of `χ_j`).  Reuses the
`induce_congr_of_subgroup_eq` transport of `columnSum_mem_S`. -/
theorem columnSum_eq_induce_H
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) :
    OddOrder.Peterfalvi.S06.columnSum h46 χ₂
      = ClassFunction.induce H
        (ClassFunction.restrict H ((h46.columnFamily χ₂).mu 0 : ClassFunction ↥L ℂ)) := by
  rw [OddOrder.Peterfalvi.S06.columnSum_def, ← h46.induce_restrict_certainType_eq χ₂]
  exact OddOrder.Peterfalvi.S04.Hypothesis.induce_congr_of_subgroup_eq hHK
    (fun x hx₁ hx₂ => by simp [ClassFunction.restrict_apply])

omit [Invertible (Nat.card ↥H : ℂ)] in
/-- **(6.8.2) case-(B), `Res_H μ_{ij} = Res_H μ_{0j}`.**  The H-presentation of (4.8) step 1
`restrict_certainType_eq` (`Res_K μ_{ij} = Res_K μ_{0j} = χ_j`), transported pointwise along
`h46.K = H`. -/
theorem restrict_H_certainType_eq
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Finite ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) (i : Fin (Nat.card h46.W1)) :
    ClassFunction.restrict H ((h46.columnFamily χ₂).mu i : ClassFunction ↥L ℂ)
      = ClassFunction.restrict H ((h46.columnFamily χ₂).mu 0 : ClassFunction ↥L ℂ) := by
  have : Fintype ↥(h46.W1 ⊔ h46.W2) := Fintype.ofFinite _
  refine ClassFunction.ext (fun g => ?_)
  have hgK : (g : ↥L) ∈ h46.K := hHK.ge g.2
  have hval := congrArg (fun f : ClassFunction ↥h46.K ℂ => f ⟨(g : ↥L), hgK⟩)
    (h46.restrict_certainType_eq χ₂ i)
  simpa using hval

/-- **(6.8.2.3) reducible `R(μ_j)` image family, retargeted to `hyp.tau`.**  The certain-type column
image family `certainTypeR` is built against the *enlarged* certain-type map
`τ_enl = dadeIntegralCharacterMap h46.dade0 h46.tau` (the only map whose isometry data supports the
`σ`-image construction).  Its `imageSet`/`mem_ZIrr`/`orthonormal` are pure facts about the σ-image
*set* (`R(μ_j) ⊆ ℤ[Irr G]`, orthonormal), independent of the Dade map; only the image equation
`(μ_j − μ̄_j)^τ = ∑ R(μ_j)` mentions `τ`.

This rebuilds the family against the Sibley–Dade map `hyp.tau`, reusing the three map-independent
fields and transferring the image equation along the `H^#`-agreement `hmapagree`
(`(μ_j − μ̄_j)^{hyp.tau} = (μ_j − μ̄_j)^{τ_enl}`, valid since `μ_j − μ̄_j` is `H^#`-supported in
case c2
`K = H` and both maps coincide there).  This puts the column `R(μ_j)` and the irreducible Dade
families `dadeOrthonormalCharacterImageFamilyOfDiff hyp.dade` in the *same* map `hyp.tau`,
the single `τ` of the per-`φ` family.  `hmapagree` is supplied at capstone wiring (as for
`certainTypeSet_isCoherent_tau`). -/
noncomputable def columnRFamilyTau
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1)
    (hdeg : (∑ i, ((h46.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1)
      = (∑ i, ((h46.columnFamily χ₂⁻¹).mu i : ClassFunction ↥L ℂ) 1))
    (hmapagree : hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂
        - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj)
      = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau
        (OddOrder.Peterfalvi.S06.columnSum h46 χ₂
          - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj)) :
    OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily hyp.tau
      (OddOrder.Peterfalvi.S06.columnSum h46 χ₂) where
  imageSet := (OddOrder.Peterfalvi.S06.certainTypeR h46 hχ₂ hdeg).imageSet
  mem_ZIrr := (OddOrder.Peterfalvi.S06.certainTypeR h46 hχ₂ hdeg).mem_ZIrr
  orthonormal := (OddOrder.Peterfalvi.S06.certainTypeR h46 hχ₂ hdeg).orthonormal
  image_eq := by
    rw [hmapagree]; exact (OddOrder.Peterfalvi.S06.certainTypeR h46 hχ₂ hdeg).image_eq

/-- **(6.8.2.3) column constituent decomposition for `hyp.tau`.**  The (5.4) decomposition data for
a
reducible column `μ_j = columnSum χ₂` against the Sibley–Dade map `hyp.tau`, built by `ofProjection`
from the retargeted family `columnRFamilyTau` and `hyp.tau`'s `H^#`-inner-preservation
(`dadeIntegralCharacterMap_inner_eq_on_supported_span hyp.dade`). This is the column
branch
of the per-`φ` family living in the *same* `τ = hyp.tau` as the irreducible constituents
(`decompositionDaFromDadeOfDiff hyp.dade`).  The column differences `μ_j − μ̄_j`,
`μ_j − a·η₁` are `H^#`-supported (`hSdiff`, case c2 `K = H`); `hmapagree` transfers the family's
image
equation; both are discharged at capstone wiring. -/
noncomputable def columnDecompositionTau
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1)
    (hdeg : (∑ i, ((h46.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1)
      = (∑ i, ((h46.columnFamily χ₂⁻¹).mu i : ClassFunction ↥L ℂ) 1))
    {η₁ : ClassFunction ↥L ℂ} {a : ℕ}
    (hmapagree : hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂
        - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj)
      = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau
        (OddOrder.Peterfalvi.S06.columnSum h46 χ₂
          - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj))
    (hSdiff : ∀ s ∈ ({OddOrder.Peterfalvi.S06.columnSum h46 χ₂
        - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj,
        OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a • η₁} : Set (ClassFunction ↥L ℂ)),
      s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (htau1_mema : hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a • η₁) ∈ ZIrr G)
    (hχψ : ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)
      (a • η₁ : ClassFunction ↥L ℂ) = 0)
    (hχbarψ : ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj
      (a • η₁ : ClassFunction ↥L ℂ) = 0) :
    OddOrder.Peterfalvi.S07.CharacterPsiDecomposition hyp.tau
      (OddOrder.Peterfalvi.S06.columnSum h46 χ₂) (a • η₁) := by
  have hχχbar : ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)
      (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj = 0 := by
    rw [OddOrder.Peterfalvi.S06.columnSum_conj_eq, OddOrder.Peterfalvi.S06.columnSum_def,
      OddOrder.Peterfalvi.S06.columnSum_def, OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner,
      if_neg (OddOrder.Peterfalvi.S06.column_inv_ne_self h46 hχ₂).symm]
  exact OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.ofProjection
    (columnRFamilyTau hyp h46 hχ₂ hdeg hmapagree) hyp.tau
    (fun _φ _ζ hφ hζ =>
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
        hyp.dade hSdiff hφ hζ)
    rfl htau1_mema hχψ hχbarψ hχχbar

/-- **(6.8.2.3) irreducible constituent decomposition for `hyp.tau`.**  The (5.4) decomposition data
for an irreducible induced constituent `Ind^L_H θ` (non-column `θ`), via
`decompositionDaFromDadeOfDiff`
for the Sibley–Dade datum `hyp.dade` (which carries `hyp.hconj : HConjInvariant`).  Since
`hyp.tau = dadeIntegralCharacterMap hyp.dade (hyp.dade.fullDadeIsometryData)`, this lands
directly in `hyp.tau` — the *same* map as the column decompositions (`columnDecompositionTau`), so
both branches feed one per-`φ` family.  The per-`θ` orthonormality/support/`ZIrr` hypotheses are
discharged at the family (from the §5 X-member machinery, as in the case-A chain). -/
noncomputable def irreducibleDecompositionTau
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (θ : IrreducibleCharacter ↥H)
    (hirr : IsIrreducibleCharacter (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)))
    {η₁ : ClassFunction ↥L ℂ} {a : ℕ}
    (hreal : ¬ ClassFunction.IsReal (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)))
    (hdiffsupp : ((ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj
        - ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (hdiffasupp : (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) - a • η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (htau1_mema : hyp.tau (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) - a • η₁) ∈ ZIrr G)
    (hχaχ1 : ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ))
      (a • η₁ : ClassFunction ↥L ℂ) = 0)
    (hχbaraχ1 : ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj
      (a • η₁ : ClassFunction ↥L ℂ) = 0)
    (hχχbar' : ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ))
      (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj = 0) :
    OddOrder.Peterfalvi.S07.CharacterPsiDecomposition hyp.tau
      (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) (a • η₁) :=
  OddOrder.Peterfalvi.S07.decompositionDaFromDadeOfDiff hyp.dade
    ⟨ClassFunction.induce H (θ : ClassFunction ↥H ℂ), hirr⟩ hreal hdiffsupp hdiffasupp htau1_mema
    hχaχ1 hχbaraχ1 hχχbar'

/-- **(6.8.2.3) per-constituent anchored image, mixed family (assembly skeleton).**  Given the
per-`φ`
decomposition family `D` (one (5.4) decomposition `CharacterPsiDecomposition hyp.tau (χ i) (aᵢ·η₁)`
per constituent — built by dispatching `columnDecompositionTau` / `irreducibleDecompositionTau`),
with
`(D i).tau1 = hyp.tau` (`htau1`, immediate for both branches), the (6.8.2.2) aggregate
(`hagg`/`hsq`/`hXaggorth`), and the per-step `R(χᵢ) ⊥ Y₀` / coefficient data (`hXorth`/`hbi`), the
pinning `per_constituent_Y_eq_smul` forces `(D i).Y = aᵢ·Y₀`, and the decomposition image equation
`(D i).tau1_image` then gives the **(6.8.2.3) anchored image**
`(χᵢ − aᵢ·η₁)^{hyp.tau} = (D i).X − aᵢ·Y₀` (`Y₀ = cY.extension η₁`).

The `Y`-coherence `cY` is arbitrary (not fixed to `hyp.coherentYset`): the case-(B) aggregate
`exists_decomposition_caseB` threads the witness `cY` of `exists_Ycoherence_hgood_caseB`, which is
`hyp.coherentYset` in the main branch but a *swapped* witness in the `|Y| = 2` edge.  All facts used
(`extension_inner_eq`, the norm-`1` anchor) hold for any coherence on `hyp.Yset`.

This is the route-independent (6.8.2.3) core, parametric in the family `D`; only the family
construction (the constituent dispatch + per-`θ` hypothesis discharge) remains for the capstone. -/
theorem per_phi_anchored_image
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {ι : Type*} (s : Finset ι) {χ : ι → ClassFunction ↥L ℂ} {a : ι → ℕ}
    (D : (i : ι) → OddOrder.Peterfalvi.S07.CharacterPsiDecomposition hyp.tau (χ i) (a i • η₁))
    (htau1 : ∀ i, (D i).tau1 = hyp.tau)
    {Xagg : ClassFunction G ℂ} {b : ι → ℤ} {n : ℤ}
    (hXaggorth : ClassFunction.inner Xagg (cY.extension η₁) = 0)
    (hagg : Xagg - (n : ℂ) • cY.extension η₁
      = ∑ i ∈ s, ((a i : ℤ) : ℂ) • ((D i).X - (D i).Y))
    (hsq : ∑ i ∈ s, ((a i : ℤ)) ^ 2 = n)
    (hXorth : ∀ i ∈ s, ClassFunction.inner (D i).X (cY.extension η₁) = 0)
    (hbi : ∀ i ∈ s,
      ClassFunction.inner (D i).Y (cY.extension η₁) = (b i : ℂ))
    (i : ι) (hi : i ∈ s) (hpos : 0 < a i) :
    hyp.tau (χ i - a i • η₁)
      = (D i).X - (a i : ℂ) • cY.extension η₁ := by
  have hηirr := hyp.isIrreducibleCharacter_of_mem_Yset hη₁
  have hηnorm : ClassFunction.inner η₁ η₁ = 1 := by
    have h := irreducibleCharacter_inner_eq_ite
      (⟨η₁, hηirr⟩ : IrreducibleCharacter ↥L) (⟨η₁, hηirr⟩ : IrreducibleCharacter ↥L)
    rwa [if_pos rfl] at h
  have hYY : ClassFunction.inner (cY.extension η₁)
      (cY.extension η₁) = 1 := by
    rw [cY.extension_inner_eq η₁ η₁
      (Submodule.subset_span hη₁) (Submodule.subset_span hη₁)]
    exact hηnorm
  have hY := per_constituent_Y_eq_smul s D hηnorm hYY hXaggorth hagg hsq hXorth hbi i hi hpos
  have h1 : hyp.tau (χ i - a i • η₁) = (D i).X - (D i).Y := by
    have h := (D i).tau1_image
    rw [htau1 i] at h
    exact h
  rw [h1, hY]

/-- **(6.8.2) case-(B), `μ_j ∉ S(W₂)`** (cont.²² item 2b): the certain-type column character
`μ_j = columnSum h46 χ₂` (for `χ₂ ≠ 1`) does **not** lie in the filtration `S(W₂)` — no nontrivial
irreducible `θ` of `H` with `W₂ ⊆ Ker θ` induces to `μ_j`.

**Clifford-uniqueness.**  Any `θ` with `Ind_H^L θ = μ_j` is forced to be `Res_H μ_{0j}`: writing
`ψ = Res_H μ_{0j}` (irreducible, `μ_j = Ind_H^L ψ`), Frobenius reciprocity term-by-term over
`μ_j = ∑_i μ_{ij}` (with `Res_H μ_{ij} = ψ`) gives `∑_i ⟨θ, ψ⟩ = ⟨μ_j, μ_j⟩ = ∑_i ⟨ψ, ψ⟩`, so
`w₁·⟨θ, ψ⟩ = w₁·1` and `⟨θ, ψ⟩ = 1 ≠ 0`, whence `θ = ψ` (both irreducible).  But then `W₂ ⊆ Ker ψ`,
contradicting (4.7) `not_subset_characterKernel_chiRestrict_of_ne_one`. -/
theorem SibleyDadeHypothesis.columnSum_notMem_SsubFiltration
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1) :
    OddOrder.Peterfalvi.S06.columnSum h46 χ₂ ∉ hyp.SsubFiltration h46.W2 := by
  classical
  have : Fintype ↥H := Fintype.ofFinite _
  set ψ : ClassFunction ↥H ℂ :=
    ClassFunction.restrict H ((h46.columnFamily χ₂).mu 0 : ClassFunction ↥L ℂ) with hψdef
  have hψirr : IsIrreducibleCharacter ψ := by
    have h := h46.certainTypeRestrict_isIrreducible χ₂
    rwa [hHK] at h
  set ψirr : IrreducibleCharacter ↥H := ⟨ψ, hψirr⟩ with hψirrdef
  intro hmem
  rw [hyp.mem_SsubFiltration] at hmem
  obtain ⟨θ, hθne, hθker, hθind⟩ := hmem
  -- `μ_j = Ind_H^L ψ` in `ψ`-form.
  have hcind : ClassFunction.induce H ψ = OddOrder.Peterfalvi.S06.columnSum h46 χ₂ := by
    rw [hψdef]; exact (columnSum_eq_induce_H h46 hHK χ₂).symm
  -- Per-term Frobenius: for any source `φ`, `⟨Ind_H φ, μ_j⟩ = ∑_i ⟨φ, ψ⟩`.
  have key : ∀ φ : ClassFunction ↥H ℂ,
      ClassFunction.inner (ClassFunction.induce H φ) (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)
        = ∑ _i : Fin (Nat.card h46.W1), ClassFunction.inner φ ψ := by
    intro φ
    rw [OddOrder.Peterfalvi.S06.columnSum_def, inner_sum_right]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [ClassFunction.inner_induce_eq_inner_restrict, restrict_H_certainType_eq h46 hHK χ₂ i,
      ← hψdef]
  -- `⟨μ_j, μ_j⟩` computed two ways, via `θ` and via `ψ`.
  have hθeq : ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)
      (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)
        = ∑ _i : Fin (Nat.card h46.W1), ClassFunction.inner (θ : ClassFunction ↥H ℂ) ψ := by
    have hk := key (θ : ClassFunction ↥H ℂ); rwa [← hθind] at hk
  have hψeq : ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)
      (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)
        = ∑ _i : Fin (Nat.card h46.W1), ClassFunction.inner ψ ψ := by
    have hk := key ψ; rwa [hcind] at hk
  -- `w₁·⟨θ, ψ⟩ = w₁·⟨ψ, ψ⟩`, cancel `w₁ ≠ 0`, then `⟨θ, ψ⟩ = ⟨ψ, ψ⟩ = 1 ≠ 0`.
  have hsum : (Nat.card h46.W1 : ℂ) * ClassFunction.inner (θ : ClassFunction ↥H ℂ) ψ
      = (Nat.card h46.W1 : ℂ) * ClassFunction.inner ψ ψ := by
    have h := hθeq.symm.trans hψeq
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h
  have hw1 : (Nat.card h46.W1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  have hinner : ClassFunction.inner (θ : ClassFunction ↥H ℂ) ψ = ClassFunction.inner ψ ψ :=
    mul_left_cancel₀ hw1 hsum
  -- `⟨θ, ψirr⟩ = ⟨ψ, ψ⟩ = ⟨ψirr, ψirr⟩ = 1 ≠ 0`, so `θ = ψirr`.
  have hθeqψ : θ = ψirr := by
    by_contra hc
    have e0 : ClassFunction.inner (θ : ClassFunction ↥H ℂ) (ψirr : ClassFunction ↥H ℂ) = 0 := by
      rw [irreducibleCharacter_inner_eq_ite, if_neg hc]
    have e1 : ClassFunction.inner (ψirr : ClassFunction ↥H ℂ) (ψirr : ClassFunction ↥H ℂ) = 1 := by
      rw [irreducibleCharacter_inner_eq_ite, if_pos rfl]
    rw [show (ψirr : ClassFunction ↥H ℂ) = ψ from rfl] at e0 e1
    rw [hinner] at e0
    exact zero_ne_one (e0.symm.trans e1)
  -- contradiction: `W₂ ⊆ Ker ψ = Ker(Res_K μ_{0j}) = Ker χ_j`
  rw [hθeqψ] at hθker
  refine OddOrder.Peterfalvi.S06.Hypothesis.not_subset_characterKernel_chiRestrict_of_ne_one
    h46.toCertainTypeHypothesis.toHypothesis hχ₂ (fun x hx => ?_)
  have hxW2 : (x : ↥L) ∈ h46.W2 := Subgroup.mem_subgroupOf.mp hx
  have hxH : (x : ↥L) ∈ H := hHK.le x.2
  have hxker : (⟨(x : ↥L), hxH⟩ : ↥H)
      ∈ OddOrder.Peterfalvi.S03.characterKernel (ψirr : ClassFunction ↥H ℂ) :=
    hθker (Subgroup.mem_subgroupOf.mpr hxW2)
  rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
    OddOrder.Peterfalvi.S03.characterDegree_def] at hxker
  rw [OddOrder.Peterfalvi.S03.mem_characterKernel, OddOrder.Peterfalvi.S03.characterDegree_def]
  simp only [show (ψirr : ClassFunction ↥H ℂ) = ψ from rfl, hψdef,
    OddOrder.Peterfalvi.S06.Hypothesis.coe_chiRestrict, ClassFunction.restrict_apply,
    OneMemClass.coe_one] at hxker ⊢
  exact hxker

end OddOrder.Peterfalvi.S08


