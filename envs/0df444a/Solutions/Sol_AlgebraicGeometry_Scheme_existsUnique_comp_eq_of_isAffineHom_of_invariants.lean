-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.existsUnique_comp_eq_of_isAffineHom_of_invariants
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/b29fe125-9c8d-5471-b210-523feda18679

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_quotient_of_finite_of_forall_exists_isAffineOpen_invariant
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_existsUnique_comp_eq_of_isAffineHom_of_invariants

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry

namespace OmegaQuotP10

theorem existsUnique_comp_eq_of_invariants
    {M X : Scheme.{u}} (π : M ⟶ X) {H : Type v} [Group H] [Finite H] (ρ : H →* Aut M)
    (hπ : ∀ h : H, (ρ h).hom ≫ π = π) (haff : IsAffineHom π) (hsurj : Function.Surjective π.base)
    (hsec : ∀ V : X.Opens, Function.Injective (π.app V))
    (hinv : ∀ V : X.Opens, Set.range (π.app V) =
      {s | ∀ h : H, (ρ h).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ h]) s = s})
    (hopen : ∀ U : M.Opens, IsAffineOpen U → (∀ h : H, (ρ h).hom ⁻¹ᵁ U = U) → ∃ V : X.Opens, IsAffineOpen V ∧ π ⁻¹ᵁ V = U)
    (T : Scheme.{u}) (f : M ⟶ T) (hf : ∀ h : H, (ρ h).hom ≫ f = f) :
    ∃! f' : X ⟶ T, π ≫ f' = f := by
  classical

  have hadm : ∀ x : M, ∃ U : M.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∀ g : H, (ρ g).hom ⁻¹ᵁ U = U := by
    intro x
    obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := π.base x) (U := ⊤) trivial
    refine ⟨π ⁻¹ᵁ V, hV.preimage π, hxV, fun g => ?_⟩
    have := congrArg (fun φ => φ ⁻¹ᵁ V) (hπ g)
    simpa only [Scheme.Hom.comp_preimage] using this

  obtain ⟨Y, πY, hπY, -, haffY, hsurjY, -, hsecY, hinvY, hopenY, hcatY⟩ :=
    AlgebraicGeometry.Scheme.exists_quotient_of_finite_of_forall_exists_isAffineOpen_invariant ρ hadm

  obtain ⟨e, he, -⟩ := hcatY X π hπ
  subst he

  have hpre : ∀ V : X.Opens, IsAffineOpen V → IsAffineOpen (e ⁻¹ᵁ V) := by
    intro V hV
    obtain ⟨V', hV', hVV'⟩ := hopenY (πY ⁻¹ᵁ (e ⁻¹ᵁ V)) ((hV.preimage (πY ≫ e))) (fun g => by
      have := congrArg (fun φ => φ ⁻¹ᵁ (e ⁻¹ᵁ V)) (hπY g)
      simpa only [Scheme.Hom.comp_preimage] using this)
    have : V' = e ⁻¹ᵁ V := by
      apply TopologicalSpace.Opens.ext
      apply hsurjY.preimage_injective
      exact congrArg (fun W : M.Opens => (W : Set M)) hVV'
    rw [← this]; exact hV'
  haveI : IsAffineHom e := (isAffineHom_iff e).mpr hpre
  have hbij : ∀ V : X.Opens, Function.Bijective (e.app V) := by
    intro V
    constructor
    · intro s t hst
      apply hsec V
      change πY.app _ (e.app V s) = πY.app _ (e.app V t)
      rw [hst]
    · intro t
      have ht : πY.app (e ⁻¹ᵁ V) t ∈ Set.range ((πY ≫ e).app V) := by
        rw [hinv V]
        have := Set.mem_range_self (f := πY.app (e ⁻¹ᵁ V)) t
        rw [hinvY (e ⁻¹ᵁ V)] at this
        exact this
      obtain ⟨s, hs⟩ := ht
      refine ⟨s, hsecY _ ?_⟩
      rw [← hs]
      rfl
  haveI : IsIso e := by
    apply (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
      (fun V : X.affineOpens => (V : X.Opens)) (iSup_affineOpens_eq_top X)).mpr
    intro V
    show IsIso (e ∣_ (V : X.Opens))
    rw [isIso_morphismRestrict_iff_isIso_app e V.2]
    exact (ConcreteCategory.isIso_iff_bijective _).mpr (hbij V)

  obtain ⟨fY, hfY, huY⟩ := hcatY T f hf
  refine ⟨inv e ≫ fY, ?_, ?_⟩
  · show (πY ≫ e) ≫ inv e ≫ fY = f
    rw [Category.assoc, IsIso.hom_inv_id_assoc, hfY]
  · intro f'' hf''
    rw [IsIso.eq_inv_comp]
    exact huY _ (by rw [← hf'', Category.assoc])

end OmegaQuotP10

theorem solution
    {M X : Scheme.{u}} (π : M ⟶ X) {H : Type v} [Group H] [Finite H] (ρ : H →* Aut M)
    (hπ : ∀ h : H, (ρ h).hom ≫ π = π) (haff : IsAffineHom π) (hsurj : Function.Surjective π.base)
    (hsec : ∀ V : X.Opens, Function.Injective (π.app V))
    (hinv : ∀ V : X.Opens, Set.range (π.app V) =
      {s | ∀ h : H, (ρ h).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ h]) s = s})
    (hopen : ∀ U : M.Opens, IsAffineOpen U → (∀ h : H, (ρ h).hom ⁻¹ᵁ U = U) → ∃ V : X.Opens, IsAffineOpen V ∧ π ⁻¹ᵁ V = U) :
    ∀ (T : Scheme.{u}) (f : M ⟶ T), (∀ h : H, (ρ h).hom ≫ f = f) → ∃! f' : X ⟶ T, π ≫ f' = f :=
  fun T f hf => OmegaQuotP10.existsUnique_comp_eq_of_invariants π ρ hπ haff hsurj hsec hinv hopen T f hf

end S_AlgebraicGeometry_Scheme_existsUnique_comp_eq_of_isAffineHom_of_invariants
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_existsUnique_comp_eq_of_isAffineHom_of_invariants (solution)
