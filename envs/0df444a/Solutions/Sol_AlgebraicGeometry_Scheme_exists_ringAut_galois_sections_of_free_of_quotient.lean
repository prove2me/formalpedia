-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_ringAut_galois_sections_of_free_of_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/8e00d5b0-bb03-5fe6-b665-70abb56e5593

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_ringAut_galois_sections_of_free_of_quotient

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

theorem solution
    {X Y : Scheme.{u}} {G : Type v} [Group G] [Finite G] (ρ : G →* Aut X)
    (hadm : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∀ g : G, (ρ g).hom ⁻¹ᵁ U = U)
    (π : X ⟶ Y) (hπ : ∀ g : G, (ρ g).hom ≫ π = π)
    (haff : IsAffineHom π) (hsurj : Function.Surjective π.base)
    (hfib : ∀ x x' : X, π.base x = π.base x' ↔ ∃ g : G, (ρ g).hom.base x = x')
    (hinj : ∀ V : Y.Opens, Function.Injective (π.app V))
    (hrange : ∀ V : Y.Opens, Set.range (π.app V) =
      {s | ∀ g : G, (ρ g).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ g]) s = s})
    (hfree : ∀ (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ X) (g : G), x ≫ (ρ g).hom = x → g = 1)
    (V : Y.Opens) (hV : IsAffineOpen V) :
    IsAffineOpen (π ⁻¹ᵁ V) ∧
    letI : Algebra Γ(Y, V) Γ(X, π ⁻¹ᵁ V) := (π.app V).hom.toAlgebra
    ∃ σ : G →* (Γ(X, π ⁻¹ᵁ V) ≃+* Γ(X, π ⁻¹ᵁ V)),
      (∀ (g : G) (a : Γ(X, π ⁻¹ᵁ V)),
        σ g a = (ρ g⁻¹).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ g⁻¹]) a) ∧
      (∀ (g : G) (r : Γ(Y, V)), σ g (algebraMap Γ(Y, V) Γ(X, π ⁻¹ᵁ V) r) = algebraMap Γ(Y, V) Γ(X, π ⁻¹ᵁ V) r) ∧
      Function.Injective (algebraMap Γ(Y, V) Γ(X, π ⁻¹ᵁ V)) ∧
      (∀ a : Γ(X, π ⁻¹ᵁ V), (∀ g : G, σ g a = a) → a ∈ Set.range (algebraMap Γ(Y, V) Γ(X, π ⁻¹ᵁ V))) ∧
      (∀ P : Ideal Γ(X, π ⁻¹ᵁ V), P.IsPrime → ∀ g : G, g ≠ 1 → ∃ a : Γ(X, π ⁻¹ᵁ V), a - σ g a ∉ P) := by
  classical
  haveI : IsAffineHom π := haff
  have hU : IsAffineOpen (π ⁻¹ᵁ V) := hV.preimage π
  refine ⟨hU, ?_⟩
  have hle : ∀ g : G, π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V) := fun g => by
    rw [← Scheme.Hom.comp_preimage, hπ g]

  have keyX : ∀ {f f' : X ⟶ X} (_ : f = f') (e : π ⁻¹ᵁ V ≤ f ⁻¹ᵁ (π ⁻¹ᵁ V)) (e' : π ⁻¹ᵁ V ≤ f' ⁻¹ᵁ (π ⁻¹ᵁ V)),
      f.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) e = f'.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) e' := by
    intro f f' h e e'; subst h; rfl
  have keyY : ∀ {f f' : X ⟶ Y} (_ : f = f') (e : π ⁻¹ᵁ V ≤ f ⁻¹ᵁ V) (e' : π ⁻¹ᵁ V ≤ f' ⁻¹ᵁ V),
      f.appLE V (π ⁻¹ᵁ V) e = f'.appLE V (π ⁻¹ᵁ V) e' := by
    intro f f' h e e'; subst h; rfl

  let E : G → (Γ(X, π ⁻¹ᵁ V) →+* Γ(X, π ⁻¹ᵁ V)) := fun g =>
    ((ρ g⁻¹).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (hle g⁻¹)).hom
  have hEdef : ∀ (g : G) (a : Γ(X, π ⁻¹ᵁ V)), E g a = (ρ g⁻¹).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (hle g⁻¹) a :=
    fun g a => rfl
  have hEmul : ∀ (g h : G) (a : Γ(X, π ⁻¹ᵁ V)), E (g * h) a = E g (E h a) := by
    intro g h a
    rw [hEdef, hEdef, hEdef, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
    have hmor : (ρ (g * h)⁻¹).hom = (ρ g⁻¹).hom ≫ (ρ h⁻¹).hom := by
      rw [mul_inv_rev, map_mul, Aut.Aut_mul_def, Iso.trans_hom]
    exact congrFun (congrArg (fun φ => (ConcreteCategory.hom φ : _ → _)) (keyX hmor _ _)) a
  have hEone : ∀ a : Γ(X, π ⁻¹ᵁ V), E 1 a = a := by
    intro a
    rw [hEdef]
    have hmor : (ρ (1 : G)⁻¹).hom = 𝟙 X := by rw [inv_one, map_one]; rfl
    have e' : π ⁻¹ᵁ V ≤ (𝟙 X) ⁻¹ᵁ (π ⁻¹ᵁ V) := le_of_eq (by simp)
    rw [keyX hmor (hle (1 : G)⁻¹) e']
    have hid : (homOfLE e').op = 𝟙 _ := Subsingleton.elim _ _
    simp only [Scheme.Hom.appLE, hid]
    erw [CategoryTheory.Functor.map_id]
    simp
    rfl

  let σ : G →* (Γ(X, π ⁻¹ᵁ V) ≃+* Γ(X, π ⁻¹ᵁ V)) :=
    { toFun := fun g => RingEquiv.ofRingHom (E g) (E g⁻¹)
        (by ext a; show E g (E g⁻¹ a) = a; rw [← hEmul, mul_inv_cancel, hEone])
        (by ext a; show E g⁻¹ (E g a) = a; rw [← hEmul, inv_mul_cancel, hEone])
      map_one' := by ext a; exact hEone a
      map_mul' := by intro g h; ext a; exact hEmul g h a }
  have hσE : ∀ (g : G) (a : Γ(X, π ⁻¹ᵁ V)), σ g a = E g a := fun g a => rfl
  refine ⟨σ, fun g a => rfl, ?_, hinj V, ?_, ?_⟩
  ·
    intro g r
    rw [hσE]
    show E g (π.app V r) = π.app V r
    rw [hEdef, Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
    exact congrFun (congrArg (fun φ => (ConcreteCategory.hom φ : _ → _)) (keyY (hπ g⁻¹) _ _)) r
  ·
    intro a ha
    have ha' : ∀ g : G,
        (ρ g).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ g]) a = a := by
      intro g
      have := ha g⁻¹
      rw [hσE, hEdef] at this
      rw [keyX (show (ρ g).hom = (ρ g⁻¹⁻¹).hom by rw [inv_inv]) _ (hle g⁻¹⁻¹)]
      exact this
    have hmem : a ∈ Set.range (π.app V) := by rw [hrange V]; exact ha'
    exact hmem
  ·
    intro P hP g hg
    by_contra H
    push Not at H
    haveI := hP
    let K : Type u := FractionRing (Γ(X, π ⁻¹ᵁ V) ⧸ P)
    let φ₀ : Γ(X, π ⁻¹ᵁ V) →+* K := (algebraMap (Γ(X, π ⁻¹ᵁ V) ⧸ P) K).comp (Ideal.Quotient.mk P)
    have hφ : φ₀.comp (E g) = φ₀ := by
      ext a
      show algebraMap _ K (Ideal.Quotient.mk P (E g a)) = algebraMap _ K (Ideal.Quotient.mk P a)
      congr 1
      rw [eq_comm, Ideal.Quotient.eq]
      have := H a
      rwa [hσE] at this
    let x : Spec (CommRingCat.of K) ⟶ X := Spec.map (CommRingCat.ofHom φ₀) ≫ hU.fromSpec
    have hx : x ≫ (ρ g⁻¹).hom = x := by
      show (Spec.map (CommRingCat.ofHom φ₀) ≫ hU.fromSpec) ≫ (ρ g⁻¹).hom = Spec.map (CommRingCat.ofHom φ₀) ≫ hU.fromSpec
      rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec (ρ g⁻¹).hom hU hU (hle g⁻¹), ← Category.assoc,
        ← Spec.map_comp]
      congr 2
      ext a
      exact congrFun (congrArg (fun ψ : Γ(X, π ⁻¹ᵁ V) →+* K => (ψ : _ → K)) hφ) a
    have := hfree K x g⁻¹ hx
    exact hg (inv_eq_one.mp this)

end S_AlgebraicGeometry_Scheme_exists_ringAut_galois_sections_of_free_of_quotient
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_ringAut_galois_sections_of_free_of_quotient (solution)
