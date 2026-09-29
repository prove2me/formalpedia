-- Prove2me | solution 1 for AlgebraicGeometry.exists_isAffineOpen_of_finite_of_isProper_of_forall_smoothOfRelativeDimension_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/e3dbd719-0e83-5547-9a4e-decfec5a4dd9

import Mathlib
import Theorems.Thm_AlgebraicCurve_exists_isAffineOpen_forall_mem_and_finite_compl
import Theorems.Thm_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_isAffine_of_iUnion_range_eq_univ
import Theorems.Thm_AlgebraicCurve_finite_compl_of_isOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isAffineOpen_of_finite_of_isProper_of_forall_smoothOfRelativeDimension_one
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem solution
    (k : Type) [CommRing k] (hk : IsField k)
    (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k))
    (hsep : IsSeparated f) (hqc : QuasiCompact f) (hft : LocallyOfFiniteType f)
    (hred : IsReduced X)
    (hprop : IsProper f)
    (hcomp : ∀ Y ∈ irreducibleComponents X, ∃ (C : Scheme.{0}) (i : C ⟶ X),
      IsClosedImmersion i ∧ IsIntegral C ∧ Set.range i.base = Y ∧ SmoothOfRelativeDimension 1 (i ≫ f))
    (hdim : ∀ z : X, IsClosed ({z} : Set X) ∨ closure ({z} : Set X) ∈ irreducibleComponents X)
    (hinf : ∀ C ∈ irreducibleComponents X, Set.Infinite C)
    (S : Set X) (hS : S.Finite) :
    ∃ U : X.Opens, IsAffineOpen U ∧ S ⊆ (U : Set X) := by
  classical
  letI : Field k := hk.toField
  haveI := hprop; haveI := hred; haveI := hqc; haveI := hft

  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : CompactSpace ↥X := QuasiCompact.compactSpace_of_compactSpace f
  haveI : IsNoetherian X := {}
  haveI : TopologicalSpace.NoetherianSpace ↥X := inferInstance
  have hfin : (irreducibleComponents ↥X).Finite := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  haveI hιfin : Finite {Y : Set ↥X // Y ∈ irreducibleComponents ↥X} := hfin.to_subtype

  choose C₀ i₀ h₀ using hcomp
  obtain ⟨C, i, hci, hint, hrange, hsm⟩ : ∃ (C : {Y : Set ↥X // Y ∈ irreducibleComponents ↥X} → Scheme.{0})
      (i : ∀ Y, C Y ⟶ X), (∀ Y, IsClosedImmersion (i Y)) ∧ (∀ Y, IsIntegral (C Y)) ∧
      (∀ Y, Set.range (i Y).base = Y.1) ∧ (∀ Y, SmoothOfRelativeDimension 1 (i Y ≫ f)) :=
    ⟨fun Y => C₀ Y.1 Y.2, fun Y => i₀ Y.1 Y.2, fun Y => (h₀ Y.1 Y.2).1, fun Y => (h₀ Y.1 Y.2).2.1,
      fun Y => (h₀ Y.1 Y.2).2.2.1, fun Y => (h₀ Y.1 Y.2).2.2.2⟩

  have hPfin : ∀ Y : {Y : Set ↥X // Y ∈ irreducibleComponents ↥X},
      ((i Y).base ⁻¹' (S ∪ ⋃ Y' : {Y' : {Y : Set ↥X // Y ∈ irreducibleComponents ↥X} // Y' ≠ Y},
        (Y'.1.1 : Set ↥X))).Finite := by
    intro Y
    haveI := hci Y; haveI := hint Y; haveI := hsm Y
    rw [Set.preimage_union, Set.preimage_iUnion]
    refine Set.Finite.union (hS.preimage (i Y).isClosedEmbedding.injective.injOn) (Set.finite_iUnion fun Y' => ?_)
    have hcl : IsClosed ((i Y).base ⁻¹' Y'.1.1) :=
      (isClosed_of_mem_irreducibleComponents _ Y'.1.2).preimage (i Y).continuous
    have hgen : genericPoint (C Y) ∉ (i Y).base ⁻¹' Y'.1.1 := by
      intro hmem
      have h1 : Y.1 ⊆ Y'.1.1 := by
        rw [← hrange Y]
        have : Set.range (i Y).base = (i Y).base '' closure {genericPoint ↥(C Y)} := by
          rw [genericPoint_closure, Set.image_univ]
        rw [this]
        refine (image_closure_subset_closure_image (i Y).continuous).trans ?_
        rw [Set.image_singleton]
        exact closure_minimal (Set.singleton_subset_iff.mpr hmem) (isClosed_of_mem_irreducibleComponents _ Y'.1.2)
      have h2 : Y'.1.1 ⊆ Y.1 := Y.2.2 Y'.1.2.1 h1
      exact Y'.2 (Subtype.ext (Set.Subset.antisymm h2 h1))
    have := AlgebraicCurve.finite_compl_of_isOpen (i Y ≫ f) ⟨((i Y).base ⁻¹' Y'.1.1)ᶜ, hcl.isOpen_compl⟩
      ⟨genericPoint (C Y), hgen⟩
    simpa using this

  have hG2 : ∀ Y : {Y : Set ↥X // Y ∈ irreducibleComponents ↥X}, ∃ U : (C Y).Opens,
      IsAffineOpen U ∧ (∀ x ∈ (hPfin Y).toFinset, x ∈ U) ∧ ((U : Set ↥(C Y))ᶜ).Finite := by
    intro Y
    haveI := hci Y; haveI := hint Y; haveI := hsm Y
    exact AlgebraicCurve.exists_isAffineOpen_forall_mem_and_finite_compl (i Y ≫ f) _
  choose UY hUaff hUF hUfin using hG2

  have hBcl : IsClosed (⋃ Y : {Y : Set ↥X // Y ∈ irreducibleComponents ↥X}, (i Y).base '' ((UY Y : Set ↥(C Y))ᶜ)) :=
    isClosed_iUnion_of_finite fun Y => by
      haveI := hci Y
      exact (i Y).isClosedEmbedding.isClosedMap _ (UY Y).2.isClosed_compl
  obtain ⟨U, hUdef⟩ : ∃ U : X.Opens, (U : Set ↥X) =
      (⋃ Y : {Y : Set ↥X // Y ∈ irreducibleComponents ↥X}, (i Y).base '' ((UY Y : Set ↥(C Y))ᶜ))ᶜ :=
    ⟨⟨_, hBcl.isOpen_compl⟩, rfl⟩
  have hmemU : ∀ x : ↥X, x ∈ U ↔
      x ∉ ⋃ Y : {Y : Set ↥X // Y ∈ irreducibleComponents ↥X}, (i Y).base '' ((UY Y : Set ↥(C Y))ᶜ) := by
    intro x
    rw [← SetLike.mem_coe, hUdef]; rfl

  have hpre : ∀ Y, (i Y) ⁻¹ᵁ U = UY Y := by
    intro Y
    ext t
    show (i Y).base t ∈ U ↔ t ∈ (UY Y : Set _)
    rw [hmemU]
    constructor
    · intro h
      by_contra ht
      exact h (Set.mem_iUnion.mpr ⟨Y, t, ht, rfl⟩)
    · intro ht hB
      obtain ⟨Y', hY'⟩ := Set.mem_iUnion.mp hB
      obtain ⟨t', ht', he⟩ := hY'
      by_cases hYY : Y' = Y
      · subst hYY
        haveI := hci Y'
        exact ht' ((i Y').isClosedEmbedding.injective he ▸ ht)
      · have hmem : t' ∈ (hPfin Y').toFinset := by
          rw [Set.Finite.mem_toFinset]
          refine Or.inr (Set.mem_iUnion.mpr ⟨⟨Y, Ne.symm hYY⟩, ?_⟩)
          show (i Y').base t' ∈ Y.1
          rw [he, ← hrange Y]
          exact ⟨t, rfl⟩
        exact ht' (hUF Y' t' hmem)
  refine ⟨U, ?_, ?_⟩
  swap
  ·
    intro s hs
    rw [SetLike.mem_coe, hmemU]
    intro hB
    obtain ⟨Y, hY⟩ := Set.mem_iUnion.mp hB
    obtain ⟨t, ht, rfl⟩ := hY
    exact ht (hUF Y t (by rw [Set.Finite.mem_toFinset]; exact Or.inl hs))

  let e := Finite.equivFin {Y : Set ↥X // Y ∈ irreducibleComponents ↥X}
  have hcov' : ∀ x : ↥(U : X.Opens), ∃ (Y : {Y : Set ↥X // Y ∈ irreducibleComponents ↥X})
      (z : ↥((i Y) ⁻¹ᵁ U)), ((i Y) ∣_ U).base z = x := by
    intro x
    obtain ⟨Y, hY⟩ : ∃ Y : {Y : Set ↥X // Y ∈ irreducibleComponents ↥X}, x.1 ∈ Set.range (i Y).base :=
      ⟨⟨irreducibleComponent x.1, irreducibleComponent_mem_irreducibleComponents x.1⟩,
        by rw [hrange]; exact mem_irreducibleComponent⟩
    obtain ⟨c, hc⟩ := hY
    refine ⟨Y, ⟨c, show (i Y).base c ∈ U by rw [hc]; exact x.2⟩, Subtype.ext ?_⟩
    rw [morphismRestrict_base_coe]
    exact hc
  refine AlgebraicGeometry.isAffine_of_isClosedImmersion_of_isAffine_of_iUnion_range_eq_univ (↑U)
    (Nat.card {Y : Set ↥X // Y ∈ irreducibleComponents ↥X})
    (fun j => ↑((i (e.symm j)) ⁻¹ᵁ U)) (fun j => (i (e.symm j)) ∣_ U)
    (fun j => by haveI := hci (e.symm j); infer_instance)
    (fun j => by show IsAffine ↑((i (e.symm j)) ⁻¹ᵁ U); rw [hpre]; exact hUaff _) inferInstance ?_
  show ⋃ j, (fun Y => Set.range ((i Y) ∣_ U).base) (e.symm j) = Set.univ
  rw [e.symm.surjective.iUnion_comp (fun Y => Set.range ((i Y) ∣_ U).base)]
  ext x
  simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
  obtain ⟨Y, z, hz⟩ := hcov' x
  exact ⟨Y, z, hz⟩

end S_AlgebraicGeometry_exists_isAffineOpen_of_finite_of_isProper_of_forall_smoothOfRelativeDimension_one
end P2MW
export P2MW.S_AlgebraicGeometry_exists_isAffineOpen_of_finite_of_isProper_of_forall_smoothOfRelativeDimension_one (solution)
