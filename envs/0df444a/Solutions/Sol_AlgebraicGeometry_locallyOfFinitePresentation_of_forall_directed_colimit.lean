-- Prove2me | solution 1 for AlgebraicGeometry.locallyOfFinitePresentation_of_forall_directed_colimit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/888915cb-3bca-5ba0-97f8-d91b558a0715

import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import Theorems.Thm_Algebra_FinitePresentation_of_forall_isDirectLimit_exists_comp_eq
import Theorems.Thm_AlgebraicGeometry_exists_forall_specMap_base_mem_of_isDirectLimit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_locallyOfFinitePresentation_of_forall_directed_colimit

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace LFPCriterion

theorem ringHom_eq_of_spec_eq {R S : Type u} [CommRing R] [CommRing S] (f g : R →+* S)
    (h : Spec.map (CommRingCat.ofHom f) = Spec.map (CommRingCat.ofHom g)) : f = g := by
  have := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom this

end LFPCriterion

open LFPCriterion in
theorem solution
    {𝒪 : Type u} [CommRing 𝒪] {M : Scheme.{u}} (πM : M ⟶ Spec (CommRingCat.of 𝒪))
    (H : ∀ (ι : Type u) [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
      (S : ι → Type u) [∀ i, CommRing (S i)] [∀ i, Algebra 𝒪 (S i)]
      (t : ∀ i j, i ≤ j → (S i →ₐ[𝒪] S j))
      (_ : ∀ i (h : i ≤ i), t i i h = AlgHom.id 𝒪 (S i))
      (_ : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k), (t j k hjk).comp (t i j hij) = t i k (hij.trans hjk))
      (L : Type u) [CommRing L] [Algebra 𝒪 L] (c : ∀ i, S i →ₐ[𝒪] L)
      (_ : ∀ i j (h : i ≤ j), (c j).comp (t i j h) = c i)
      (_ : ∀ x : L, ∃ (i : ι) (y : S i), c i y = x)
      (_ : ∀ (i : ι) (y z : S i), c i y = c i z → ∃ (j : ι) (h : i ≤ j), t i j h y = t i j h z),
      (∀ x : Spec (CommRingCat.of L) ⟶ M, x ≫ πM = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 L)) →
          ∃ (i : ι) (xi : Spec (CommRingCat.of (S i)) ⟶ M), xi ≫ πM = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (S i))) ∧
            x = Spec.map (CommRingCat.ofHom (c i).toRingHom) ≫ xi) ∧
      (∀ (i : ι) (xi yi : Spec (CommRingCat.of (S i)) ⟶ M),
          xi ≫ πM = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (S i))) → yi ≫ πM = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (S i))) →
          Spec.map (CommRingCat.ofHom (c i).toRingHom) ≫ xi = Spec.map (CommRingCat.ofHom (c i).toRingHom) ≫ yi →
          ∃ (j : ι) (h : i ≤ j), Spec.map (CommRingCat.ofHom (t i j h).toRingHom) ≫ xi = Spec.map (CommRingCat.ofHom (t i j h).toRingHom) ≫ yi)) :
    LocallyOfFinitePresentation πM := by
  classical

  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFinitePresentation) M.affineCover]
  intro j

  let A : CommRingCat.{u} := M.affineOpenCover.X j
  let ch : Spec A ⟶ M := M.affineCover.f j
  haveI : IsOpenImmersion ch := M.affineCover.map_prop j
  let φ : CommRingCat.of 𝒪 ⟶ A := Spec.preimage (ch ≫ πM)
  have hφ : Spec.map φ = ch ≫ πM := Spec.map_preimage _
  show LocallyOfFinitePresentation (ch ≫ πM)
  rw [← hφ, HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]

  letI : Algebra 𝒪 A := φ.hom.toAlgebra
  show Algebra.FinitePresentation 𝒪 A
  apply Algebra.FinitePresentation.of_forall_isDirectLimit_exists_comp_eq
  intro ι _ _ _ S _ _ t _ L _ _ c _ ψ

  let x : Spec (CommRingCat.of L) ⟶ M := Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ ch
  have hx : x ≫ πM = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 L)) := by
    show (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ ch) ≫ πM = _
    rw [Category.assoc, ← hφ, ← Spec.map_comp]
    congr 1
    exact congrArg CommRingCat.ofHom (ψ.comp_algebraMap).symm ▸ rfl

  obtain ⟨hA, -⟩ := H ι S t
    (fun i h => AlgHom.ext fun y => DirectedSystem.map_self (f := fun i j h => ⇑(t i j h)) y)
    (fun i j k hij hjk => AlgHom.ext fun y => DirectedSystem.map_map (f := fun i j h => ⇑(t i j h)) hij hjk y)
    L c
    (fun i j h => AlgHom.ext fun y => IsDirectLimit.compatibility (f := fun i j h => ⇑(t i j h)) (g := fun i => ⇑(c i)) i j h y)
    (IsDirectLimit.surj (f := fun i j h => ⇑(t i j h)))
    (fun i y z h => by
      obtain ⟨k, hik, hik', e⟩ := IsDirectLimit.inj (f := fun i j h => ⇑(t i j h)) (g := fun i => ⇑(c i)) i i y z h
      exact ⟨k, hik, e⟩)
  obtain ⟨i, xi, hxi, hxxi⟩ := hA x hx

  have hW : ∀ p : Spec (CommRingCat.of L), (Spec.map (CommRingCat.ofHom (c i).toRingHom)).base p ∈ xi ⁻¹ᵁ ch.opensRange := by
    intro p
    show (Spec.map (CommRingCat.ofHom (c i).toRingHom) ≫ xi).base p ∈ ch.opensRange
    rw [← hxxi]
    exact ⟨(Spec.map (CommRingCat.ofHom ψ.toRingHom)).base p, rfl⟩
  obtain ⟨j', hij', hj'⟩ := AlgebraicGeometry.exists_forall_specMap_base_mem_of_isDirectLimit
    (fun i j h => (t i j h).toRingHom) (g := fun i => (c i).toRingHom) ‹_› i (xi ⁻¹ᵁ ch.opensRange) hW

  let xj : Spec (CommRingCat.of (S j')) ⟶ M := Spec.map (CommRingCat.ofHom (t i j' hij').toRingHom) ≫ xi
  have hrange : Set.range xj.base ⊆ Set.range ch.base := by
    rintro _ ⟨q, rfl⟩
    exact hj' q
  let ℓ : Spec (CommRingCat.of (S j')) ⟶ Spec A := IsOpenImmersion.lift ch xj hrange
  have hℓ : ℓ ≫ ch = xj := IsOpenImmersion.lift_fac ch xj hrange
  let φ' : A ⟶ CommRingCat.of (S j') := Spec.preimage ℓ
  have hφ' : Spec.map φ' = ℓ := Spec.map_preimage _

  have hcomm : φ'.hom.comp (algebraMap 𝒪 A) = algebraMap 𝒪 (S j') := by
    apply ringHom_eq_of_spec_eq
    have e1 : CommRingCat.ofHom (φ'.hom.comp (algebraMap 𝒪 A)) = φ ≫ φ' := rfl
    rw [e1, Spec.map_comp, hφ', hφ]
    show ℓ ≫ ch ≫ πM = _
    rw [← Category.assoc, hℓ]
    show (Spec.map (CommRingCat.ofHom (t i j' hij').toRingHom) ≫ xi) ≫ πM = _
    rw [Category.assoc, hxi, ← Spec.map_comp]
    congr 1
    exact congrArg CommRingCat.ofHom ((t i j' hij').comp_algebraMap).symm ▸ rfl
  let φa : A →ₐ[𝒪] S j' := { toRingHom := φ'.hom, commutes' := fun o => congrArg (fun f : 𝒪 →+* S j' => f o) hcomm }
  refine ⟨j', φa, ?_⟩

  apply AlgHom.ext
  intro a
  have key : Spec.map (CommRingCat.ofHom ((c j').comp φa).toRingHom) = Spec.map (CommRingCat.ofHom ψ.toRingHom) := by
    haveI : Mono ch := inferInstance
    rw [← cancel_mono ch]
    have e2 : CommRingCat.ofHom ((c j').comp φa).toRingHom = φ' ≫ CommRingCat.ofHom (c j').toRingHom := rfl
    rw [e2, Spec.map_comp, Category.assoc, hφ', hℓ]
    show Spec.map (CommRingCat.ofHom (c j').toRingHom) ≫ Spec.map (CommRingCat.ofHom (t i j' hij').toRingHom) ≫ xi = x
    have hcomp : (c j').comp (t i j' hij') = c i :=
      AlgHom.ext fun y => IsDirectLimit.compatibility (f := fun i j h => ⇑(t i j h)) (g := fun i => ⇑(c i)) i j' hij' y
    have e3 : CommRingCat.ofHom (t i j' hij').toRingHom ≫ CommRingCat.ofHom (c j').toRingHom = CommRingCat.ofHom (c i).toRingHom := by
      rw [← hcomp]; rfl
    rw [← Spec.map_comp_assoc, e3, hxxi]
  have := ringHom_eq_of_spec_eq _ _ key
  exact congrArg (fun f : ↑A →+* L => f a) this

end S_AlgebraicGeometry_locallyOfFinitePresentation_of_forall_directed_colimit
end P2MW
export P2MW.S_AlgebraicGeometry_locallyOfFinitePresentation_of_forall_directed_colimit (solution)
