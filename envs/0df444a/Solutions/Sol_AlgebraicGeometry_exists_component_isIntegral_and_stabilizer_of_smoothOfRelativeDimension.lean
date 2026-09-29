-- Prove2me | solution 1 for AlgebraicGeometry.exists_component_isIntegral_and_stabilizer_of_smoothOfRelativeDimension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/28edf863-6d01-50b6-90dd-f71e75fa0ca7

import Mathlib
import Theorems.Thm_Algebra_IsStandardSmoothOfRelativeDimension_exists_etale_aeval
import Theorems.Thm_Algebra_Etale_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime
import Theorems.Thm_AlgebraicGeometry_not_isDomain_stalk_of_mem_irreducibleComponents_of_ne
import Theorems.Thm_AlgebraicGeometry_isReduced_of_smooth_of_field
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_component_isIntegral_and_stabilizer_of_smoothOfRelativeDimension

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

namespace COMPAuxFFX

theorem isDomain_stalk {k : Type u} [Field k] (M : Scheme.{u}) (πM : M ⟶ Spec (CommRingCat.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n πM] (y : M) : IsDomain (M.presheaf.stalk y) := by
  obtain ⟨U, hU, V, hV, hy, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := πM) y

  obtain rfl : U = ⊤ := by
    apply TopologicalSpace.Opens.ext
    apply Set.eq_univ_of_forall
    intro p
    have hp : πM.base y ∈ (U : Set _) := e hy
    have : p = πM.base y := Subsingleton.elim _ _
    rw [this]; exact hp

  let R : Type u := Γ(Spec (CommRingCat.of k), ⊤)
  let S : Type u := Γ(M, V)
  let eR : R ≃+* k := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  haveI : IsDomain R := eR.toMulEquiv.isDomain_iff.mpr inferInstance
  haveI : UniqueFactorizationMonoid R := MulEquiv.uniqueFactorizationMonoid eR.symm.toMulEquiv inferInstance
  letI algRS : Algebra R S := (πM.appLE ⊤ V e).hom.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension n R S := hf
  obtain ⟨xs, hxs⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_aeval (R := R) (S := S) n
  let P : Type u := MvPolynomial (Fin n) R
  letI algPS : Algebra P S := (MvPolynomial.aeval xs : P →ₐ[R] S).toRingHom.toAlgebra
  haveI : Algebra.Etale P S := hxs
  haveI : IsIntegrallyClosed P := inferInstance
  letI algSy : Algebra S (M.presheaf.stalk y) := TopCat.Presheaf.algebra_section_stalk M.presheaf ⟨y, hy⟩
  haveI hloc : IsLocalization.AtPrime (M.presheaf.stalk y) (hV.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hV.isLocalization_stalk ⟨y, hy⟩
  exact (Algebra.Etale.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime P S
    (hV.primeIdealOf ⟨y, hy⟩).asIdeal (M.presheaf.stalk y)).1

theorem eq_of_mem_irreducibleComponents {k : Type u} [Field k] (M : Scheme.{u}) (πM : M ⟶ Spec (CommRingCat.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n πM] (y : M) (Z₁ Z₂ : Set M)
    (h₁ : Z₁ ∈ irreducibleComponents (M : Type u)) (h₂ : Z₂ ∈ irreducibleComponents (M : Type u))
    (hy₁ : y ∈ Z₁) (hy₂ : y ∈ Z₂) : Z₁ = Z₂ := by
  by_contra hne
  exact AlgebraicGeometry.not_isDomain_stalk_of_mem_irreducibleComponents_of_ne M y Z₁ Z₂ h₁ h₂ hne hy₁ hy₂
    (isDomain_stalk M πM n y)

theorem isOpen_of_mem_irreducibleComponents {k : Type u} [Field k] (M : Scheme.{u}) (πM : M ⟶ Spec (CommRingCat.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n πM] (Z : Set M) (hZ : Z ∈ irreducibleComponents (M : Type u)) : IsOpen Z := by
  haveI : Smooth πM := SmoothOfRelativeDimension.smooth (n := n) (f := πM)
  haveI : IsLocallyNoetherian M := LocallyOfFiniteType.isLocallyNoetherian πM
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  obtain ⟨V, hV, hzV, -⟩ := exists_isAffineOpen_mem_and_subset (X := M) (x := z) (U := ⊤) trivial
  haveI : IsNoetherianRing Γ(M, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  haveI : TopologicalSpace.NoetherianSpace V := noetherianSpace_of_isAffineOpen V hV
  have hfin : (irreducibleComponents (V : Type u)).Finite := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents

  let Bad : Set (Set V) := {T | T ∈ irreducibleComponents (V : Type u) ∧ ¬ ((Subtype.val : V → M) '' T ⊆ Z)}
  have hBadfin : Bad.Finite := hfin.subset (fun T hT => hT.1)
  have hBadcl : IsClosed (⋃ T ∈ Bad, T) := hBadfin.isClosed_biUnion (fun T hT => isClosed_of_mem_irreducibleComponents T hT.1)

  have hkey : ∀ T ∈ irreducibleComponents (V : Type u), ∀ w : V, w ∈ T → (w : M) ∈ Z → (Subtype.val : V → M) '' T ⊆ Z := by
    intro T hT w hwT hwZ
    obtain ⟨Z', hZ', hTZ'⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
      (hT.1.image Subtype.val continuous_subtype_val.continuousOn)
    have : Z' = Z := eq_of_mem_irreducibleComponents M πM n (w : M) Z' Z hZ' hZ (hTZ' ⟨w, hwT, rfl⟩) hwZ
    rw [← this]; exact hTZ'
  refine ⟨(Subtype.val : V → M) '' (⋃ T ∈ Bad, T)ᶜ, ?_, ?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    have hwT : w ∈ irreducibleComponent w := mem_irreducibleComponent
    have hT := irreducibleComponent_mem_irreducibleComponents w
    by_contra hwZ
    apply hw
    refine Set.mem_biUnion (x := irreducibleComponent w) ⟨hT, ?_⟩ hwT
    intro hsub
    exact hwZ (hsub ⟨w, hwT, rfl⟩)
  · exact V.2.isOpenEmbedding_subtypeVal.isOpenMap _ hBadcl.isOpen_compl
  · refine ⟨⟨z, hzV⟩, ?_, rfl⟩
    intro hmem
    simp only [Set.mem_iUnion, exists_prop] at hmem
    obtain ⟨T, hTBad, hzT⟩ := hmem
    exact hTBad.2 (hkey T hTBad.1 ⟨z, hzV⟩ hzT hz)

theorem inv_preimage_eq {C : Scheme.{u}} (U : C.Opens) (f : Aut C) (hf : f.hom ⁻¹ᵁ U = U) : f.inv ⁻¹ᵁ U = U := by
  conv_lhs => rw [← hf]
  rw [← Scheme.Hom.comp_preimage, Iso.inv_hom_id, Scheme.Hom.id_preimage]

end COMPAuxFFX

open COMPAuxFFX in

theorem solution
    {k : Type u} [Field k] (M : Scheme.{u}) (πM : M ⟶ Spec (CommRingCat.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n πM]
    (x : M) (G : Type u) [Group G] (ρ : G →* Aut M) :
    ∃ (C₀ : M.Opens) (G₀ : Subgroup G),
      IsClosed (C₀ : Set M) ∧ _root_.IsConnected (C₀ : Set M) ∧ x ∈ C₀ ∧ IsIntegral (C₀ : Scheme.{u}) ∧
      (∀ g : G, g ∈ G₀ ↔ (ρ g).hom ⁻¹ᵁ C₀ = C₀) ∧
      (∀ g : G, (ρ g).hom.base x ∈ C₀ → g ∈ G₀) := by
  let Z : Set M := irreducibleComponent x
  have hZ : Z ∈ irreducibleComponents (M : Type u) := irreducibleComponent_mem_irreducibleComponents x
  have hZopen : IsOpen Z := isOpen_of_mem_irreducibleComponents M πM n Z hZ
  let C₀ : M.Opens := ⟨Z, hZopen⟩
  let G₀ : Subgroup G :=
    { carrier := {g | (ρ g).hom ⁻¹ᵁ C₀ = C₀}
      one_mem' := by
        show (ρ 1).hom ⁻¹ᵁ C₀ = C₀
        rw [map_one]
        exact Scheme.Hom.id_preimage C₀
      mul_mem' := fun {a b} ha hb => by
        show (ρ (a * b)).hom ⁻¹ᵁ C₀ = C₀
        rw [map_mul, Aut.Aut_mul_def, Iso.trans_hom, Scheme.Hom.comp_preimage]
        change (ρ b).hom ⁻¹ᵁ ((ρ a).hom ⁻¹ᵁ C₀) = C₀
        rw [ha, hb]
      inv_mem' := fun {a} ha => by
        show (ρ a⁻¹).hom ⁻¹ᵁ C₀ = C₀
        rw [map_inv, Aut.Aut_inv_def]
        exact inv_preimage_eq C₀ (ρ a) ha }
  refine ⟨C₀, G₀, isClosed_irreducibleComponent, isIrreducible_irreducibleComponent.isConnected,
    mem_irreducibleComponent, ?_, fun g => Iff.rfl, ?_⟩
  ·
    haveI : Smooth πM := SmoothOfRelativeDimension.smooth (n := n) (f := πM)
    haveI : IsReduced M := AlgebraicGeometry.isReduced_of_smooth_of_field πM
    haveI : IsReduced (C₀ : Scheme.{u}) := isReduced_of_isOpenImmersion C₀.ι
    haveI : IrreducibleSpace (C₀ : Scheme.{u}) := Subtype.irreducibleSpace isIrreducible_irreducibleComponent
    exact isIntegral_of_irreducibleSpace_of_isReduced _
  · intro g hg
    show (ρ g).hom ⁻¹ᵁ C₀ = C₀

    let φ := Scheme.homeoOfIso (ρ g)
    have hpre : φ ⁻¹' Z ∈ irreducibleComponents (M : Type u) :=
      preimage_mem_irreducibleComponents hZ φ.isOpenEmbedding
        (by rw [φ.range_coe, Set.inter_univ]; exact hZ.1.nonempty)
    have hxpre : x ∈ φ ⁻¹' Z := hg
    have heq : φ ⁻¹' Z = Z :=
      eq_of_mem_irreducibleComponents M πM n x _ _ hpre hZ hxpre mem_irreducibleComponent
    apply TopologicalSpace.Opens.ext
    exact heq

#print axioms solution

end S_AlgebraicGeometry_exists_component_isIntegral_and_stabilizer_of_smoothOfRelativeDimension
end P2MW
export P2MW.S_AlgebraicGeometry_exists_component_isIntegral_and_stabilizer_of_smoothOfRelativeDimension (solution)
