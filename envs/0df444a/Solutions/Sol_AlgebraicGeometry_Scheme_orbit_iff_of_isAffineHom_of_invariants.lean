-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.orbit_iff_of_isAffineHom_of_invariants
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/9d2094fa-b55e-537c-ba2e-993cf45889b6

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_orbit_iff_of_isAffineHom_of_invariants

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped Pointwise

namespace GenOrbitGC5

theorem appLE_congr_hom {X Y : Scheme.{0}} {f g : X ⟶ Y} (hfg : f = g) (U : Y.Opens) (V : X.Opens)
    (hf : V ≤ f ⁻¹ᵁ U) : f.appLE U V hf = g.appLE U V (hfg ▸ hf) := by
  subst hfg; rfl

theorem id_appLE {X : Scheme.{0}} (U : X.Opens) (e : U ≤ (𝟙 X) ⁻¹ᵁ U) :
    (𝟙 X : X ⟶ X).appLE U U e = 𝟙 _ := by
  rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
  erw [Category.id_comp]
  exact X.presheaf.map_id _

end GenOrbitGC5

theorem solution
    {M X : Scheme.{0}} (π : M ⟶ X)
    {H : Type} [Group H] [Finite H] (ρ : H →* Aut M)
    (hπ : ∀ h : H, (ρ h).hom ≫ π = π) (haff : IsAffineHom π)
    (hinv : ∀ V : X.Opens, Set.range (π.app V) =
      {s | ∀ h : H, (ρ h).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ h]) s = s}) :
    ∀ x x' : M, π.base x = π.base x' ↔ ∃ h : H, (ρ h).hom.base x = x' := by
  classical
  haveI := haff
  haveI : Fintype H := Fintype.ofFinite H
  intro x x'
  refine ⟨fun hxx => ?_, ?_⟩
  swap
  · rintro ⟨h, rfl⟩
    rw [← Scheme.Hom.comp_apply, hπ h]

  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (π.base x)) isOpen_univ
  have hU : IsAffineOpen (π ⁻¹ᵁ V) := hV.preimage π
  have hx : x ∈ π ⁻¹ᵁ V := hxV
  have hx' : x' ∈ π ⁻¹ᵁ V := show π.base x' ∈ V by rw [← hxx]; exact hxV
  have hst : ∀ h : H, (ρ h).hom ⁻¹ᵁ (π ⁻¹ᵁ V) = π ⁻¹ᵁ V := fun h => by
    rw [← Scheme.Hom.comp_preimage, hπ h]

  let ψ : H → (Γ(M, π ⁻¹ᵁ V) ⟶ Γ(M, π ⁻¹ᵁ V)) := fun h =>
    (ρ h).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (hst h).ge
  have hψ_one : ψ 1 = 𝟙 _ := by
    have h1 : (ρ 1).hom = 𝟙 M := by rw [map_one]; rfl
    change (ρ 1).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (hst 1).ge = 𝟙 _
    rw [GenOrbitGC5.appLE_congr_hom h1]
    exact GenOrbitGC5.id_appLE _ _
  have hψ_mul : ∀ h₁ h₂ : H, ψ (h₁ * h₂) = ψ h₁ ≫ ψ h₂ := by
    intro h₁ h₂
    have hm : (ρ (h₁ * h₂)).hom = (ρ h₂).hom ≫ (ρ h₁).hom := by rw [map_mul]; rfl
    change (ρ (h₁ * h₂)).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (hst (h₁ * h₂)).ge =
      (ρ h₁).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (hst h₁).ge ≫ (ρ h₂).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (hst h₂).ge
    rw [Scheme.Hom.appLE_comp_appLE]
    exact GenOrbitGC5.appLE_congr_hom hm _ _ _
  letI act : MulSemiringAction H Γ(M, π ⁻¹ᵁ V) :=
    { smul := fun h a => (ψ h⁻¹).hom a
      one_smul := fun a => by
        change (ψ 1⁻¹).hom a = a
        rw [inv_one, hψ_one]; rfl
      mul_smul := fun h₁ h₂ a => by
        change (ψ (h₁ * h₂)⁻¹).hom a = (ψ h₁⁻¹).hom ((ψ h₂⁻¹).hom a)
        rw [mul_inv_rev, hψ_mul]; rfl
      smul_zero := fun h => map_zero _
      smul_add := fun h a b => map_add _ a b
      smul_one := fun h => map_one _
      smul_mul := fun h a b => map_mul _ a b }
  have act_def : ∀ (h : H) (a : Γ(M, π ⁻¹ᵁ V)), h • a = (ψ h⁻¹).hom a := fun _ _ => rfl

  let φ : Γ(X, V) ⟶ Γ(M, π ⁻¹ᵁ V) := π.app V
  letI alg : Algebra Γ(X, V) Γ(M, π ⁻¹ᵁ V) := φ.hom.toAlgebra
  have hinvV : ∀ s : Γ(M, π ⁻¹ᵁ V), s ∈ Set.range (π.app V) ↔ ∀ h : H, (ψ h).hom s = s := by
    intro s; rw [hinv V]; rfl
  have hfixφ : ∀ (h : H) (r : Γ(X, V)), (ψ h).hom (algebraMap Γ(X, V) Γ(M, π ⁻¹ᵁ V) r) =
      algebraMap Γ(X, V) Γ(M, π ⁻¹ᵁ V) r :=
    fun h r => (hinvV _).mp ⟨r, rfl⟩ h
  haveI : SMulCommClass H Γ(X, V) Γ(M, π ⁻¹ᵁ V) :=
    ⟨fun h r a => by simp only [Algebra.smul_def, act_def, map_mul, hfixφ]⟩
  haveI : Algebra.IsInvariant Γ(X, V) Γ(M, π ⁻¹ᵁ V) H :=
    ⟨fun a ha => by
      have ha' : a ∈ Set.range (π.app V) := (hinvV a).mpr fun h => by
        have := ha h⁻¹; rwa [act_def, inv_inv] at this
      obtain ⟨r, hr⟩ := ha'
      exact ⟨r, hr⟩⟩

  let Q : PrimeSpectrum Γ(M, π ⁻¹ᵁ V) := hU.primeIdealOf ⟨x, hx⟩
  let Q' : PrimeSpectrum Γ(M, π ⁻¹ᵁ V) := hU.primeIdealOf ⟨x', hx'⟩
  have hcQ : Q.comap φ.hom = hV.primeIdealOf ⟨π.base x, hxV⟩ := by
    have := IsAffineOpen.comap_primeIdealOf_appLE (f := π) V hV (π ⁻¹ᵁ V) hU le_rfl hx
    rwa [Scheme.Hom.appLE_eq_app] at this
  have hcQ' : Q'.comap φ.hom = hV.primeIdealOf ⟨π.base x, hxV⟩ := by
    have := IsAffineOpen.comap_primeIdealOf_appLE (f := π) V hV (π ⁻¹ᵁ V) hU le_rfl hx'
    rw [Scheme.Hom.appLE_eq_app] at this
    rw [this]; congr 1; exact Subtype.ext hxx.symm
  have hunder : Q.asIdeal.under Γ(X, V) = Q'.asIdeal.under Γ(X, V) := by
    have := congrArg PrimeSpectrum.asIdeal (hcQ.trans hcQ'.symm)
    simp only [PrimeSpectrum.comap_asIdeal] at this
    exact this
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq Γ(X, V) Γ(M, π ⁻¹ᵁ V) H
    Q.asIdeal Q'.asIdeal hunder

  have hQ' : Q'.asIdeal = Q.asIdeal.comap (ψ g).hom := by
    rw [hg, Ideal.pointwise_smul_eq_comap]
    ext a
    simp only [Ideal.mem_comap]
    change (ψ (g⁻¹)⁻¹).hom a ∈ Q.asIdeal ↔ _
    rw [inv_inv]
  have hgx : (ρ g).hom.base x ∈ π ⁻¹ᵁ V := by
    have h := hx
    rw [← hst g] at h
    exact h
  have hcg : Q.comap (ψ g).hom = hU.primeIdealOf ⟨(ρ g).hom.base x, hgx⟩ :=
    IsAffineOpen.comap_primeIdealOf_appLE (f := (ρ g).hom) (π ⁻¹ᵁ V) hU (π ⁻¹ᵁ V) hU (hst g).ge hx
  have hQQ : Q' = hU.primeIdealOf ⟨(ρ g).hom.base x, hgx⟩ := by
    rw [← hcg]; exact PrimeSpectrum.ext (by rw [hQ', PrimeSpectrum.comap_asIdeal])
  refine ⟨g, ?_⟩
  have e1 := hU.fromSpec_primeIdealOf ⟨x', hx'⟩
  have e2 := hU.fromSpec_primeIdealOf ⟨(ρ g).hom.base x, hgx⟩
  change hU.fromSpec.base Q' = x' at e1
  rw [hQQ] at e1
  exact e2.symm.trans e1 ▸ rfl

end S_AlgebraicGeometry_Scheme_orbit_iff_of_isAffineHom_of_invariants
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_orbit_iff_of_isAffineHom_of_invariants (solution)
