-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_CaseBHortho
-- name    : OddOrder_Peterfalvi_S08_CaseBHortho
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:14:51.510211+00:00
-- url     : https://prove2.me/theorems/b52f54c2-eadf-4a22-b0df-48d853ede5a4
-- title:
--   Peterfalvi §8 case (B): certain-type column vs break-pair cross-orthogonality
-- statement:
--   Peterfalvi, *Character Theory for the Odd Order Theorem*, §8, the (6.8.2) branch, feeding the norm-weighted (5.6) $X$-adjoin engine. The file supplies the (5.2.e) cross-family orthogonality $R(\mu_j)\perp R(\chi)$ between the reducible certain-type column image family and a break-pair family.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 2 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_CaseBHortho.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_CaseBHortho.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S08_CrossOrthogonality

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]

variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

/-- **(5.2.e) certain-type column vs break-pair cross-orthogonality** (Peterfalvi §8, case (B)). -/
theorem certainTypeR_imageSet_orthogonal_dadeOfDiff
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1)
    (hdeg : (∑ i, ((h46.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1)
      = (∑ i, ((h46.columnFamily χ₂⁻¹).mu i : ClassFunction ↥L ℂ) 1))
    (χ : IrreducibleCharacter ↥L)
    (hrealχ : ¬ ClassFunction.IsReal (χ : ClassFunction ↥L ℂ))
    (hdiffsuppχ : ((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) :
    ∀ α ∈ (OddOrder.Peterfalvi.S06.certainTypeR h46 hχ₂ hdeg).imageSet,
    ∀ β ∈ (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff hyp.dade χ
        hrealχ hdiffsuppχ).imageSet,
      ClassFunction.inner α β = 0 := by
  -- The whole argument is now the general (5.2.e) mixed-stratum theorem
  -- (`S08_CrossOrthogonality`); the only Sibley-specific input is the anchor: `(χ − χ̄)^τ`
  -- vanishes on the `ticVdiff`-exceptional set `V`, because `χ − χ̄` is `H^#`-supported.
  have hsuppsub : ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
    rw [show (χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj =
        -((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)) by abel,
      ClassFunction.support_neg]
    exact hdiffsuppχ
  exact certainTypeR_imageSet_orthogonal_dadeOfDiff_of_vanishOnV h46 hχ₂ hdeg hyp.dade
    χ hrealχ hdiffsuppχ
    (fun v hv => tau_apply_eq_zero_of_mem_ticVdiffV hyp h46 hHK hsuppsub hv)

/-- **(5.2.e) irreducible break-pair vs certain-type column cross-orthogonality** `R(χ) ⊥ R(μ_j)`.
The `R(μ_j) ⊥ R(χ)` lemma `certainTypeR_imageSet_orthogonal_dadeOfDiff` with the two families
swapped, by conjugate symmetry of the inner product.  This is the member-side ingredient when the
**break** is a reducible certain-type column (the family roles are reversed from the
irreducible-break
`caseB_member_orthoDatum`): an irreducible member `x = Ind θ` has image family `R(x) =
dadeOrthonormalCharacterImageFamilyOfDiff`, which must be orthogonal to the column break's
`R(μ_j) = certainTypeR`. -/
theorem dadeOfDiff_imageSet_orthogonal_certainTypeR
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1)
    (hdeg : (∑ i, ((h46.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1)
      = (∑ i, ((h46.columnFamily χ₂⁻¹).mu i : ClassFunction ↥L ℂ) 1))
    (χ : IrreducibleCharacter ↥L)
    (hrealχ : ¬ ClassFunction.IsReal (χ : ClassFunction ↥L ℂ))
    (hdiffsuppχ : ((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) :
    ∀ α ∈ (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff hyp.dade χ
        hrealχ hdiffsuppχ).imageSet,
    ∀ β ∈ (OddOrder.Peterfalvi.S06.certainTypeR h46 hχ₂ hdeg).imageSet,
      ClassFunction.inner α β = 0 := by
  intro α hα β hβ
  rw [OddOrder.RepresentationTheory.inner_conj_symm,
    certainTypeR_imageSet_orthogonal_dadeOfDiff hyp h46 hHK hχ₂ hdeg χ hrealχ hdiffsuppχ β hβ α hα,
    star_zero]

end OddOrder.Peterfalvi.S08


