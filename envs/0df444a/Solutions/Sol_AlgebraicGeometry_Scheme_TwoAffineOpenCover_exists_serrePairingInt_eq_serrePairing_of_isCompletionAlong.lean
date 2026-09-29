-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_serrePairingInt_eq_serrePairing_of_isCompletionAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/60e9a990-628e-56db-8bfd-e5c258c28183

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSerrePairingInt
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverSectional
import Definitions.Def_AlgebraicCurve_KaehlerToFunctionField
import Definitions.Def_AlgebraicCurve_SerrePairing
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2
import Definitions.Def_AlgebraicCurve_PlacesOf
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_ringHom_functionField_laurentSeries_of_isCompletionAlong
import Theorems.Thm_TwoChartCech_Cover_LaurentChart_residue_eq_kaehlerResidueTerm
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_kaehlerToFunctionField_mem_regularDifferentials
import Theorems.Thm_AlgebraicCurve_exists_linearEquiv_cechH1_swap
import Theorems.Thm_AlgebraicCurve_placesOf_union_eq_univ_of_sup_eq_top
import Theorems.Thm_AlgebraicCurve_germToFunctionField_inf_mem_lSpaceOn_inter_placesOf
import Theorems.Thm_AlgebraicGeometry_not_isAffine_of_isProper_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_exists_linearEquiv_structureSheafH1_cechH1
import Theorems.Thm_TwoChartCech_Cover_serrePairingInt_eq_serrePairing
import Theorems.Thm_AlgebraicCurve_exists_embedding_place_range_eq_compl_placesOf_of_isSectional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_serrePairingInt_eq_serrePairing_of_isCompletionAlong
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option maxHeartbeats 6400000 in
theorem solution
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover)
    (c : X ⟶ Spec (CommRingCat.of k)) [IsIntegral X] [IsProper c] [SmoothOfRelativeDimension 1 c]
    {ι : Type w} [Fintype ι] (σ : ι → (Spec (CommRingCat.of k) ⟶ X)) (hσ : 𝒱.IsSectional c σ)
    (Λ : ι → (𝒱.cover c).LaurentChart) (hv : (𝒱.cover c).ResiduesVanishOnCoboundaries Λ)
    (hΛ : ∀ i, (Λ i).IsCompletionAlong (𝒱.cover c).ρ0
      (Scheme.TwoAffineOpenCover.sectionAlgHom (σ i) (hσ.comp_eq i) (hσ.range_subset i)))
    (hΛt : ∀ i, (Λ i).HasParameter (𝒱.cover c).ρ0) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    ∀ [AlgebraicCurve.IsCurveOver k X.functionField]
      [∀ v : AlgebraicCurve.Place k X.functionField, v.DCoordGenerates]
      [AlgebraicCurve.HasCanonicalDivisor (K := k) (F := X.functionField)]
      (hRT : AlgebraicCurve.ResidueTheorem k X.functionField),
    ∃ (_ : Nonempty (𝒱.U0 ⊓ 𝒱.U1 : X.Opens))
      (hW : AlgebraicCurve.placesOf c 𝒱.U1 ∪ AlgebraicCurve.placesOf c 𝒱.U0 = Set.univ)
      (hgerm : ∀ s : (𝒱.cover c).A01, (X.germToFunctionField (𝒱.U0 ⊓ 𝒱.U1)).hom s ∈
        AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf c 𝒱.U1 ∩ AlgebraicCurve.placesOf c 𝒱.U0)
          (0 : AlgebraicCurve.Divisor k X.functionField))
      (e1 : (𝒱.structureSheafSections c).H1 →ₗ[k]
        AlgebraicCurve.cechH1 (AlgebraicCurve.placesOf c 𝒱.U1) (AlgebraicCurve.placesOf c 𝒱.U0)
          (0 : AlgebraicCurve.Divisor k X.functionField))
      (_ : ∀ s : (𝒱.cover c).A01, e1 (Submodule.Quotient.mk s) =
        Submodule.Quotient.mk ⟨(X.germToFunctionField (𝒱.U0 ⊓ 𝒱.U1)).hom s, hgerm s⟩)
      (eΩ : (𝒱.kaehlerSections c).H0 →ₗ[k] ↥(AlgebraicCurve.regularDifferentials k X.functionField))
      (_ : Nonempty (𝒱.U0 : X.Opens))
      (_ : ∀ ω : (𝒱.kaehlerSections c).H0,
        ((eΩ ω : ↥(AlgebraicCurve.regularDifferentials k X.functionField)) : Ω[X.functionField⁄k]) =
          AlgebraicCurve.kaehlerToFunctionField c 𝒱.U0 ω.val.1),
      ∀ (ω : (𝒱.kaehlerSections c).H0) (x : (𝒱.structureSheafSections c).H1),
        (𝒱.cover c).serrePairingInt Λ hv ω x = AlgebraicCurve.serrePairing hRT hW (eΩ ω) (e1 x) := by
  intro instCO instDC instCD hRT
  letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝒱.U0
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝒱.U1
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c (𝒱.U0 ⊓ 𝒱.U1)

  have hnaff := AlgebraicGeometry.not_isAffine_of_isProper_of_smoothOfRelativeDimension_one c
  have hne_top : ∀ U : X.Opens, IsAffineOpen U → U ≠ ⊤ := by
    rintro U hU rfl
    haveI : IsAffine (⊤ : X.Opens) := hU
    exact hnaff (IsAffine.of_isIso (Scheme.topIso X).inv)
  have hU0 : 𝒱.U0 ≠ ⊤ := hne_top _ 𝒱.isAffineOpen_U0
  have hU1 : 𝒱.U1 ≠ ⊤ := hne_top _ 𝒱.isAffineOpen_U1
  have hne_bot : ∀ U V : X.Opens, U ⊔ V = ⊤ → V ≠ ⊤ → Nonempty (U : X.Opens) := by
    intro U V hUV hV
    by_contra h
    rw [not_nonempty_iff] at h
    have hU : U = ⊥ := by
      ext x; simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hx => h.elim ⟨x, hx⟩
    rw [hU, bot_sup_eq] at hUV
    exact hV hUV
  haveI hne0 : Nonempty (𝒱.U0 : X.Opens) := hne_bot _ _ 𝒱.sup_eq_top hU1
  haveI hne1 : Nonempty (𝒱.U1 : X.Opens) := hne_bot _ _ (by rw [sup_comm]; exact 𝒱.sup_eq_top) hU0
  haveI hne01 : Nonempty (𝒱.U0 ⊓ 𝒱.U1 : X.Opens) := by
    obtain ⟨⟨x, hx⟩⟩ := hne0; obtain ⟨⟨y, hy⟩⟩ := hne1
    obtain ⟨z, hz0, hz1⟩ := nonempty_preirreducible_inter (𝒱.U0).isOpen (𝒱.U1).isOpen ⟨x, hx⟩ ⟨y, hy⟩
    exact ⟨⟨z, ⟨hz0, hz1⟩⟩⟩

  obtain ⟨hW0, -, -⟩ := AlgebraicCurve.placesOf_union_eq_univ_of_sup_eq_top c 𝒱.U0 𝒱.U1 𝒱.sup_eq_top hU0 hU1
  have hW : AlgebraicCurve.placesOf c 𝒱.U1 ∪ AlgebraicCurve.placesOf c 𝒱.U0 = Set.univ := by
    rw [Set.union_comm]; exact hW0

  obtain ⟨hgerm0, e, he⟩ := AlgebraicCurve.exists_linearEquiv_structureSheafH1_cechH1 𝒱 c hne0 hne1
  have hgerm : ∀ s : (𝒱.cover c).A01, (X.germToFunctionField (𝒱.U0 ⊓ 𝒱.U1)).hom s ∈
      AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf c 𝒱.U1 ∩ AlgebraicCurve.placesOf c 𝒱.U0)
        (0 : AlgebraicCurve.Divisor k X.functionField) := fun s => by
    rw [Set.inter_comm]; exact hgerm0 s
  obtain ⟨sw, hsw⟩ := AlgebraicCurve.exists_linearEquiv_cechH1_swap
    (AlgebraicCurve.placesOf c 𝒱.U0) (AlgebraicCurve.placesOf c 𝒱.U1) (0 : AlgebraicCurve.Divisor k X.functionField)
  let e1 : (𝒱.structureSheafSections c).H1 →ₗ[k]
      AlgebraicCurve.cechH1 (AlgebraicCurve.placesOf c 𝒱.U1) (AlgebraicCurve.placesOf c 𝒱.U0)
        (0 : AlgebraicCurve.Divisor k X.functionField) := sw.toLinearMap ∘ₗ e.toLinearMap
  have he1 : ∀ s : (𝒱.cover c).A01, e1 (Submodule.Quotient.mk s) =
      Submodule.Quotient.mk ⟨(X.germToFunctionField (𝒱.U0 ⊓ 𝒱.U1)).hom s, hgerm s⟩ := by
    intro s
    change sw (e (Submodule.Quotient.mk s)) = _
    rw [he s (hgerm0 s), hsw]

  let eΩ : (𝒱.kaehlerSections c).H0 →ₗ[k] ↥(AlgebraicCurve.regularDifferentials k X.functionField) :=
    { toFun := fun ω => ⟨AlgebraicCurve.kaehlerToFunctionField c 𝒱.U0 ω.val.1,
        AlgebraicGeometry.Scheme.TwoAffineOpenCover.kaehlerToFunctionField_mem_regularDifferentials 𝒱 c ω⟩
      map_add' := fun ω η => Subtype.ext (by
        change AlgebraicCurve.kaehlerToFunctionField c 𝒱.U0 (ω.val.1 + η.val.1) =
          AlgebraicCurve.kaehlerToFunctionField c 𝒱.U0 ω.val.1 + AlgebraicCurve.kaehlerToFunctionField c 𝒱.U0 η.val.1
        exact (AlgebraicCurve.kaehlerToFunctionField c 𝒱.U0).map_add _ _)
      map_smul' := fun r ω => Subtype.ext (by
        change AlgebraicCurve.kaehlerToFunctionField c 𝒱.U0 (r • ω.val.1) =
          r • AlgebraicCurve.kaehlerToFunctionField c 𝒱.U0 ω.val.1
        exact (AlgebraicCurve.kaehlerToFunctionField c 𝒱.U0).map_smul r _) }
  have heΩ : ∀ ω : (𝒱.kaehlerSections c).H0,
      ((eΩ ω : ↥(AlgebraicCurve.regularDifferentials k X.functionField)) : Ω[X.functionField⁄k]) =
        AlgebraicCurve.kaehlerToFunctionField c 𝒱.U0 ω.val.1 := fun ω => rfl

  obtain ⟨p, hp, hpv⟩ := AlgebraicCurve.exists_embedding_place_range_eq_compl_placesOf_of_isSectional 𝒱 c σ hσ

  let ψ : (𝒱.cover c).A01 →ₐ[k] X.functionField :=
    { (X.germToFunctionField (𝒱.U0 ⊓ 𝒱.U1)).hom with
      commutes' := fun r => AlgebraicCurve.germToFunctionField_algebraMap c (𝒱.U0 ⊓ 𝒱.U1) r }
  have hψ : ∀ s : (𝒱.cover c).A01, ψ s = (X.germToFunctionField (𝒱.U0 ⊓ 𝒱.U1)).hom s := fun _ => rfl

  have hres : ∀ (i : ι) (s : (𝒱.cover c).A01) (ω : (𝒱.cover c).kaehler.H0),
      (Λ i).residue (s • (𝒱.cover c).kaehler.r0 ω.val.1) =
        AlgebraicCurve.kaehlerResidueTerm ((eΩ ω : ↥(AlgebraicCurve.regularDifferentials k X.functionField)) :
          Ω[X.functionField⁄k]) (AlgebraicCurve.diagonalHom k X.functionField (ψ s)) (p i) := by
    intro i s ω
    obtain ⟨Λ', hΛ'ψ, hΛ'v⟩ :=
      AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_ringHom_functionField_laurentSeries_of_isCompletionAlong
        𝒱 c (σ i) (hσ.comp_eq i) (hσ.range_subset i) (Λ i) (hΛ i) (p i) (hpv i)
    obtain ⟨b, hb⟩ := hΛt i
    have key := TwoChartCech.Cover.LaurentChart.residue_eq_kaehlerResidueTerm (Λ i) ψ
      (AlgebraicCurve.kaehlerToFunctionField c (𝒱.U0 ⊓ 𝒱.U1))
      (fun s' g => AlgebraicCurve.kaehlerToFunctionField_smul_D c (𝒱.U0 ⊓ 𝒱.U1) s' g)
      Λ' (fun y => hΛ'ψ y) (p i) hΛ'v (t₀ := ψ ((𝒱.cover c).ρ0 b)) (by rw [hψ, hΛ'ψ]; exact hb)
      (s • (𝒱.cover c).kaehler.r0 ω.val.1)
    rw [key]
    have h1 : AlgebraicCurve.kaehlerToFunctionField c (𝒱.U0 ⊓ 𝒱.U1) (s • (𝒱.cover c).kaehler.r0 ω.val.1) =
        ψ s • AlgebraicCurve.kaehlerToFunctionField c 𝒱.U0 ω.val.1 := by
      have h2 := AlgebraicCurve.kaehlerToFunctionField_smul c (𝒱.U0 ⊓ 𝒱.U1) s ((𝒱.kaehlerSections c).r0 ω.val.1)
      rw [Scheme.TwoAffineOpenCover.kaehlerToFunctionField_r0 𝒱 c] at h2
      exact h2
    have h3 : ((eΩ ω : ↥(AlgebraicCurve.regularDifferentials k X.functionField)) : Ω[X.functionField⁄k]) =
        AlgebraicCurve.kaehlerToFunctionField c 𝒱.U0 ω.val.1 := rfl
    refine (congrArg (fun η => AlgebraicCurve.kaehlerResidueTerm η
      (AlgebraicCurve.diagonalHom k X.functionField 1) (p i)) h1).trans ?_
    simp only [h3, AlgebraicCurve.kaehlerResidueTerm, AlgebraicCurve.diagonalHom_apply, one_mul,
      AlgebraicCurve.Place.differentialCoeff_smul]
  refine ⟨hne01, hW, hgerm, e1, he1, eΩ, hne0, heΩ, fun ω x => ?_⟩
  exact TwoChartCech.Cover.serrePairingInt_eq_serrePairing hRT hW (𝒱.cover c) Λ hv ψ hgerm e1 he1 eΩ p hp hres ω x

#print axioms solution

end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_serrePairingInt_eq_serrePairing_of_isCompletionAlong
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_serrePairingInt_eq_serrePairing_of_isCompletionAlong (solution)
