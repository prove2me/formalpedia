-- Prove2me | solution 1 for AlgebraicGeometry.LocallyOfFinitePresentation.of_comp_of_isFinite_of_flat_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/5f332865-ac57-5ba8-828f-7a7dd8a04225

import Mathlib
import Theorems.Thm_Algebra_FiniteType_of_faithfullyFlat_of_finitePresentation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_LocallyOfFinitePresentation_of_comp_of_isFinite_of_flat_of_surjective

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u v w

namespace C2aAux

theorem exists_surjective_of_projective_of_faithfullyFlat
    (A : Type v) (B : Type w) [CommRing A] [AddCommGroup B] [Module A B]
    [Module.Projective A B] [Module.Finite A B] [Module.FaithfullyFlat A B] :
    ∃ (k : ℕ) (φ : (Fin k → B) →ₗ[A] A), Function.Surjective φ := by
  classical

  obtain ⟨k, π, hπ⟩ := Module.Finite.exists_fin' A B
  obtain ⟨i, hi⟩ := Module.projective_lifting_property π LinearMap.id hπ

  let f : Fin k → (B →ₗ[A] A) := fun j => (LinearMap.proj j) ∘ₗ i

  let τ : Ideal A := ⨆ j, LinearMap.range (f j)
  have hB : (⊤ : Submodule A B) ≤ τ • (⊤ : Submodule A B) := by
    rintro x -
    have hx : x = π (i x) := (LinearMap.congr_fun hi x).symm
    have : i x = ∑ j, (f j x) • (Pi.single j (1 : A) : Fin k → A) := by
      ext j'; simp [f, Pi.single_apply, Finset.sum_apply]
    rw [hx, this, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem_smul (Submodule.mem_iSup_of_mem j ⟨x, rfl⟩) Submodule.mem_top
  have hτ : τ = ⊤ := by
    have h := (Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top A B).1 inferInstance
    exact h.2 τ (le_antisymm le_top hB)

  have h1 : (1 : A) ∈ ⨆ j, LinearMap.range (f j) := by rw [show (⨆ j, LinearMap.range (f j)) = τ from rfl, hτ]; trivial
  obtain ⟨c, hc, hcsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 h1

  choose x hx using fun j => LinearMap.mem_range.1 (hc j)
  refine ⟨k, ∑ j, (f j) ∘ₗ (LinearMap.proj j), ?_⟩
  intro a
  refine ⟨fun j => a • x j, ?_⟩
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.coe_proj, Function.eval, map_smul, hx]
  rw [← Finset.smul_sum]
  have : (∑ j, (c j : A)) = 1 := by
    rw [← hcsum, Finsupp.sum_fintype]
    exact fun _ => rfl
  rw [this, smul_eq_mul, mul_one]

theorem finitePresentation_of_projective_of_faithfullyFlat
    (R : Type u) (A : Type v) (B : Type w) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Module.Projective A B] [Module.Finite A B] [Module.FaithfullyFlat A B] [Algebra.FinitePresentation R B] :
    Algebra.FinitePresentation R A := by
  classical
  haveI : Module.FinitePresentation A B := Module.finitePresentation_of_projective A B
  haveI : Algebra.FinitePresentation A B := inferInstance
  haveI : Algebra.FiniteType R B := inferInstance
  haveI hft : Algebra.FiniteType R A := Algebra.FiniteType.of_faithfullyFlat_of_finitePresentation R A B
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 hft
  let P := MvPolynomial (Fin n) R
  letI algPA : Algebra P A := f.toRingHom.toAlgebra
  haveI : IsScalarTower R P A := IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)
  letI algPB : Algebra P B := ((algebraMap A B).comp f.toRingHom).toAlgebra
  haveI : IsScalarTower P A B := IsScalarTower.of_algebraMap_eq (fun p => rfl)
  haveI : IsScalarTower R P B := IsScalarTower.of_algebraMap_eq (fun r => by
    change algebraMap R B r = algebraMap A B (f (algebraMap R P r))
    rw [f.commutes, ← IsScalarTower.algebraMap_apply])
  haveI : Algebra.FinitePresentation P B :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R P B
  haveI : Module.Finite P A :=
    Module.Finite.of_surjective (Algebra.linearMap P A) (by
      intro a; obtain ⟨p, rfl⟩ := hf a; exact ⟨p, rfl⟩)
  haveI : Module.Finite P B := Module.Finite.trans A B
  haveI : Module.FinitePresentation P B := Module.FinitePresentation.of_finite_of_finitePresentation P B

  obtain ⟨k, φ, hφ⟩ := exists_surjective_of_projective_of_faithfullyFlat A B
  obtain ⟨x0, hx0⟩ := hφ 1
  let σ : A →ₗ[A] (Fin k → B) := LinearMap.toSpanSingleton A (Fin k → B) x0
  have hφσ : ∀ a, φ (σ a) = a := by
    intro a; simp [σ, LinearMap.toSpanSingleton_apply, map_smul, hx0]
  let g : (Fin k → B) →ₗ[A] (Fin k → B) := LinearMap.id - σ ∘ₗ φ
  have hker : LinearMap.ker φ = LinearMap.range g := by
    ext x
    constructor
    · intro hx
      refine ⟨x, ?_⟩
      simp [g, LinearMap.mem_ker.mp hx]
    · rintro ⟨y, rfl⟩
      simp [g, LinearMap.mem_ker, hφσ]
  let φP : (Fin k → B) →ₗ[P] A := φ.restrictScalars P
  have hφP : Function.Surjective φP := hφ
  have hkerP : (LinearMap.ker φP).FG := by
    have h1 : LinearMap.ker φP = LinearMap.range (g.restrictScalars P) := by
      ext x
      change x ∈ LinearMap.ker φ ↔ _
      rw [hker]
      simp [LinearMap.mem_range]
    rw [h1, LinearMap.range_eq_map]
    exact Submodule.FG.map _ Module.Finite.fg_top
  haveI : Module.FinitePresentation P A := Module.finitePresentation_of_surjective φP hφP hkerP
  haveI : Algebra.FinitePresentation P A := inferInstance
  exact Algebra.FinitePresentation.trans (R := R) (A := P) (B := A)

theorem finitePresentation_of_finite_of_faithfullyFlat
    (R : Type u) (A : Type v) (B : Type w) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Module.Finite A B] [Module.FaithfullyFlat A B] [Algebra.FinitePresentation A B]
    [Algebra.FinitePresentation R B] :
    Algebra.FinitePresentation R A := by
  haveI : Module.FinitePresentation A B := Module.FinitePresentation.of_finite_of_finitePresentation A B
  haveI : Module.Projective A B :=
    (Module.freeLocus_eq_univ_iff (R := A) (M := B)).1 (Module.freeLocus_eq_univ (R := A) (M := B))
  exact finitePresentation_of_projective_of_faithfullyFlat R A B

end C2aAux

theorem solution
    {X Y Z : Scheme.{u}} (p : X ⟶ Y) (g : Y ⟶ Z)
    [IsFinite p] [Flat p] [Surjective p] [LocallyOfFinitePresentation p]
    [LocallyOfFinitePresentation (p ≫ g)] :
    LocallyOfFinitePresentation g := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyOfFinitePresentation)]
  intro U V e
  have hV : IsAffineOpen (V : Y.Opens) := V.2
  have hW : IsAffineOpen (p ⁻¹ᵁ (V : Y.Opens)) := hV.preimage p
  let W : X.affineOpens := ⟨p ⁻¹ᵁ (V : Y.Opens), hW⟩
  have eW : (W : X.Opens) ≤ (p ≫ g) ⁻¹ᵁ (U : Z.Opens) := by
    change p ⁻¹ᵁ (V : Y.Opens) ≤ (p ≫ g) ⁻¹ᵁ (U : Z.Opens)
    rw [Scheme.Hom.comp_preimage]
    exact Scheme.Hom.preimage_mono p e

  set φRA : (Γ(Z, U) : Type u) →+* Γ(Y, V) := (g.appLE U V e).hom with hφRA
  set φAB : (Γ(Y, V) : Type u) →+* Γ(X, p ⁻¹ᵁ (V : Y.Opens)) :=
    (p.appLE V (p ⁻¹ᵁ (V : Y.Opens)) le_rfl).hom with hφAB
  have hcomp : φAB.comp φRA = ((p ≫ g).appLE U (p ⁻¹ᵁ (V : Y.Opens)) eW).hom := by
    rw [hφRA, hφAB, ← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]

  have hflat : φAB.Flat := by
    rw [hφAB]; exact HasRingHomProperty.appLE (P := @Flat) (f := p) inferInstance V W le_rfl
  have hfpAB : φAB.FinitePresentation := by
    rw [hφAB]; exact HasRingHomProperty.appLE (P := @LocallyOfFinitePresentation) (f := p) inferInstance V W le_rfl
  have hfpRB : (φAB.comp φRA).FinitePresentation := by
    rw [hcomp]; exact HasRingHomProperty.appLE (P := @LocallyOfFinitePresentation) (f := p ≫ g) inferInstance U W eW
  have hfin : φAB.Finite := by
    have h : IsFinite p := inferInstance
    rw [HasAffineProperty.eq_targetAffineLocally (P := @IsFinite)] at h
    have h2 := ((targetAffineLocally_affineAnd_iff' RingHom.finite_respectsIso p).1 h).2 V hV
    rw [hφAB, ← Scheme.Hom.app_eq_appLE]
    exact h2

  have hsurj : Function.Surjective (PrimeSpectrum.comap φAB) := by
    intro 𝔭
    have hy : hV.fromSpec.base 𝔭 ∈ Set.range hV.fromSpec.base := ⟨𝔭, rfl⟩
    rw [hV.range_fromSpec] at hy
    obtain ⟨x, hx⟩ := p.surjective (hV.fromSpec.base 𝔭)
    have hxW : x ∈ p ⁻¹ᵁ (V : Y.Opens) := by
      change p.base x ∈ (V : Y.Opens); rw [hx]; exact hy
    have hxr : x ∈ Set.range hW.fromSpec.base := by rw [hW.range_fromSpec]; exact hxW
    obtain ⟨𝔮, rfl⟩ := hxr
    refine ⟨𝔮, ?_⟩
    apply hV.fromSpec.isOpenEmbedding.injective
    have hnat := IsAffineOpen.SpecMap_appLE_fromSpec p hV hW le_rfl
    have h1 : hV.fromSpec.base ((Spec.map (p.appLE V (p ⁻¹ᵁ (V : Y.Opens)) le_rfl)).base 𝔮) =
        p.base (hW.fromSpec.base 𝔮) := congrArg (fun h => h.base 𝔮) hnat
    rw [← hx, ← h1, hφAB]
    rfl

  algebraize [φRA, φAB, φAB.comp φRA]
  haveI : Module.FaithfullyFlat (Γ(Y, V) : Type u) (Γ(X, p ⁻¹ᵁ (V : Y.Opens)) : Type u) :=
    Module.FaithfullyFlat.of_comap_surjective hsurj
  exact C2aAux.finitePresentation_of_finite_of_faithfullyFlat (Γ(Z, U) : Type u) (Γ(Y, V) : Type u)
    (Γ(X, p ⁻¹ᵁ (V : Y.Opens)) : Type u)

end S_AlgebraicGeometry_LocallyOfFinitePresentation_of_comp_of_isFinite_of_flat_of_surjective
end P2MW
export P2MW.S_AlgebraicGeometry_LocallyOfFinitePresentation_of_comp_of_isFinite_of_flat_of_surjective (solution)
