-- Prove2me | solution 1 for AlgebraicGeometry.existsUnique_comp_eq_of_etale_of_isLocalRing_of_surjective_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/d084f8c6-dab2-559d-8904-0eb0fa956bb3

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_existsUnique_comp_eq_of_etale_of_isLocalRing_of_surjective_of_isNilpotent

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace TanLift8

theorem ring_existsUnique {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    (f : R →+* A) (hfs : f.FormallySmooth) (hfu : f.FormallyUnramified)
    (β : R →+* B) (π : B →+* C) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (φ₀ : A →+* C) (hcomp : φ₀.comp f = π.comp β) :
    ∃! φ : A →+* B, φ.comp f = β ∧ π.comp φ = φ₀ := by
  letI algA : Algebra R A := f.toAlgebra
  letI algB : Algebra R B := β.toAlgebra
  letI algC : Algebra R C := (π.comp β).toAlgebra
  haveI : Algebra.FormallySmooth R A := hfs
  haveI : Algebra.FormallyUnramified R A := hfu
  have hc : ∀ r : R, φ₀ (f r) = π (β r) := fun r => congrArg (fun g : R →+* C => g r) hcomp
  let φ₀' : A →ₐ[R] C :=
    { toRingHom := φ₀
      commutes' := fun r => by change φ₀ (f r) = π (β r); exact hc r }
  let π' : B →ₐ[R] C :=
    { toRingHom := π
      commutes' := fun r => rfl }
  have hπ' : Function.Surjective π' := hπ
  have hker' : IsNilpotent (RingHom.ker (π' : B →+* C)) := hker
  let φ := Algebra.FormallySmooth.liftOfSurjective φ₀' π' hπ' hker'
  refine ⟨φ.toRingHom, ⟨?_, ?_⟩, ?_⟩
  · ext r; exact φ.commutes r
  · ext a; exact Algebra.FormallySmooth.liftOfSurjective_apply φ₀' π' hπ' hker' a
  · rintro ψ ⟨hψ1, hψ2⟩
    let ψ' : A →ₐ[R] B :=
      { toRingHom := ψ
        commutes' := fun r => by change ψ (f r) = β r; exact congrArg (fun g : R →+* B => g r) hψ1 }
    have : ψ' = φ := by
      apply Algebra.FormallyUnramified.lift_unique_of_ringHom (π' : B →+* C) hker'
      ext a
      show π (ψ a) = π (φ a)
      have hφa := Algebra.FormallySmooth.liftOfSurjective_apply φ₀' π' hπ' hker' a
      change π (φ a) = φ₀ a at hφa
      rw [hφa]
      exact congrArg (fun g : A →+* C => g a) hψ2
    exact congrArg AlgHom.toRingHom this

variable {B C : Type u} [CommRing B] [IsLocalRing B] [CommRing C] [IsLocalRing C]

theorem stalkClosedPointTo_SpecMap (π : B →+* C) [IsLocalHom π]
    (hb : (Spec.map (CommRingCat.ofHom π)).base (IsLocalRing.closedPoint C) = IsLocalRing.closedPoint B) :
    Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom π)) =
      ((Spec (CommRingCat.of B)).presheaf.stalkCongr (.of_eq hb)).hom ≫
        (stalkClosedPointIso (CommRingCat.of B)).hom ≫ CommRingCat.ofHom π := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hU
  have hU' : IsLocalRing.closedPoint B ∈ U := hb ▸ hU
  obtain rfl : U = ⊤ := (IsLocalRing.closed_point_mem_iff.mp hU')
  rw [Scheme.germ_stalkClosedPointTo_Spec, TopCat.Presheaf.stalkCongr_hom,
    TopCat.Presheaf.germ_stalkSpecializes_assoc, germ_stalkClosedPointIso_hom_assoc]

theorem stalkClosedPointTo_id :
    Scheme.stalkClosedPointTo (𝟙 (Spec (CommRingCat.of B))) = (stalkClosedPointIso (CommRingCat.of B)).hom := by
  rw [Scheme.stalkClosedPointTo, Scheme.Hom.stalkMap_id]
  exact Category.id_comp _

end TanLift8

namespace TanLift8

open IsLocalRing

variable {B C : Type u} [CommRing B] [IsLocalRing B] [CommRing C] [IsLocalRing C]

theorem stalkClosedPointTo_congr {X : Scheme.{u}} {R : CommRingCat.{u}} [IsLocalRing R]
    (f g : Spec R ⟶ X) (hfg : f = g) (h : f.base (closedPoint R) ⤳ g.base (closedPoint R)) :
    Scheme.stalkClosedPointTo g = X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo f := by
  subst hfg
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hU
  rw [TopCat.Presheaf.germ_stalkSpecializes_assoc]

omit [IsLocalRing C] in
theorem specializes_of_eq {X : Scheme.{u}} {x y : ↥X} (h : x = y) : x ⤳ y := h ▸ specializes_rfl

theorem stalkClosedPointTo_SpecMap' (π : B →+* C) [IsLocalHom π]
    (hb : closedPoint B ⤳ (Spec.map (CommRingCat.ofHom π)).base (closedPoint C)) :
    Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom π)) =
      (Spec (CommRingCat.of B)).presheaf.stalkSpecializes hb ≫
        (stalkClosedPointIso (CommRingCat.of B)).hom ≫ CommRingCat.ofHom π := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hU
  have hb' : (Spec.map (CommRingCat.ofHom π)).base (closedPoint C) = closedPoint B :=
    Spec_closedPoint (f := CommRingCat.ofHom π)
  have hU' : closedPoint B ∈ U := hb' ▸ hU
  obtain rfl : U = ⊤ := (closed_point_mem_iff.mp hU')
  rw [Scheme.germ_stalkClosedPointTo_Spec, TopCat.Presheaf.germ_stalkSpecializes_assoc, germ_stalkClosedPointIso_hom_assoc]

theorem existsUnique_section {X : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of B)) [Etale q]
    (π : B →+* C) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (a : Spec (CommRingCat.of C) ⟶ X) (ha : a ≫ q = Spec.map (CommRingCat.ofHom π)) :
    ∃! s : Spec (CommRingCat.of B) ⟶ X, s ≫ q = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom π) ≫ s = a := by
  classical
  haveI hπl : IsLocalHom π := IsLocalHom.of_surjective π hπ
  have hσ : (Spec.map (CommRingCat.ofHom π)).base (closedPoint C) = closedPoint B :=
    Spec_closedPoint (f := CommRingCat.ofHom π)

  have hx : q.base (a.base (closedPoint C)) = closedPoint B := by
    have := congrArg (fun g : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of B) => g.base (closedPoint C)) ha
    dsimp only at this
    rw [Scheme.Hom.comp_apply] at this
    rw [this]; exact hσ
  have sx : closedPoint B ⤳ q.base (a.base (closedPoint C)) := specializes_of_eq (X := Spec (CommRingCat.of B)) hx.symm

  have hcc : Spec.map ((Spec (CommRingCat.of B)).presheaf.stalkSpecializes sx ≫
      (stalkClosedPointIso (CommRingCat.of B)).hom) ≫
        (Spec (CommRingCat.of B)).fromSpecStalk (q.base (a.base (closedPoint C))) = 𝟙 _ := by
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk, ← Spec_stalkClosedPointIso,
      ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]

  have hcompat : q.stalkMap (a.base (closedPoint C)) ≫ Scheme.stalkClosedPointTo a =
      ((Spec (CommRingCat.of B)).presheaf.stalkSpecializes sx ≫ (stalkClosedPointIso (CommRingCat.of B)).hom) ≫
        CommRingCat.ofHom π := by
    have h1 : Scheme.stalkClosedPointTo (a ≫ q) = q.stalkMap (a.base (closedPoint C)) ≫ Scheme.stalkClosedPointTo a :=
      Scheme.stalkClosedPointTo_comp a q
    have h2 := stalkClosedPointTo_congr (Spec.map (CommRingCat.ofHom π)) (a ≫ q) ha.symm
      (specializes_of_eq (X := Spec (CommRingCat.of B)) (by rw [hσ, Scheme.Hom.comp_apply, hx]))
    rw [h1, stalkClosedPointTo_SpecMap' π (specializes_of_eq (X := Spec (CommRingCat.of B)) hσ.symm), ← Category.assoc,
      TopCat.Presheaf.stalkSpecializes_comp] at h2
    rw [Category.assoc]
    exact h2

  have hθu : (q.stalkMap (a.base (closedPoint C))).hom.FormallyUnramified := FormallyUnramified.stalkMap q _
  have hθs : (q.stalkMap (a.base (closedPoint C))).hom.FormallySmooth := by
    have : a.base (closedPoint C) ∈ q.smoothLocus := by rw [Scheme.Hom.smoothLocus_eq_top]; trivial
    exact Scheme.Hom.mem_smoothLocus.mp this

  obtain ⟨φ, ⟨hφ1, hφ2⟩, huniq⟩ := ring_existsUnique (q.stalkMap (a.base (closedPoint C))).hom hθs hθu
    ((Spec (CommRingCat.of B)).presheaf.stalkSpecializes sx ≫ (stalkClosedPointIso (CommRingCat.of B)).hom).hom
    π hπ hker (Scheme.stalkClosedPointTo a).hom (by rw [← CommRingCat.hom_comp, hcompat]; rfl)
  obtain ⟨φc, hφc⟩ : ∃ φc : X.presheaf.stalk (a.base (closedPoint C)) ⟶ CommRingCat.of B, φc.hom = φ :=
    ⟨CommRingCat.ofHom φ, rfl⟩
  have hφ1' : q.stalkMap (a.base (closedPoint C)) ≫ φc =
      (Spec (CommRingCat.of B)).presheaf.stalkSpecializes sx ≫ (stalkClosedPointIso (CommRingCat.of B)).hom := by
    ext1; rw [CommRingCat.hom_comp, hφc]; exact hφ1
  have hφ2' : φc ≫ CommRingCat.ofHom π = Scheme.stalkClosedPointTo a := by
    ext1; rw [CommRingCat.hom_comp, hφc]; exact hφ2
  haveI : IsLocalHom φc.hom := by
    constructor
    intro y hy
    have : IsUnit ((Scheme.stalkClosedPointTo a).hom y) := by rw [← hφ2, ← hφc]; exact hy.map π
    exact (isUnit_map_iff (Scheme.stalkClosedPointTo a).hom y).mp this
  have hs1 : (Spec.map φc ≫ X.fromSpecStalk (a.base (closedPoint C))) ≫ q = 𝟙 _ := by
    rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc, ← Spec.map_comp, hφ1', hcc]
  have hs2 : Spec.map (CommRingCat.ofHom π) ≫ (Spec.map φc ≫ X.fromSpecStalk (a.base (closedPoint C))) = a := by
    rw [← Category.assoc, ← Spec.map_comp, hφ2', Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  refine ⟨Spec.map φc ≫ X.fromSpecStalk (a.base (closedPoint C)), ⟨hs1, hs2⟩, ?_⟩

  rintro s' ⟨hs'1, hs'2⟩
  have hx' : s'.base (closedPoint B) = a.base (closedPoint C) := by
    have := congrArg (fun g : Spec (CommRingCat.of C) ⟶ X => g.base (closedPoint C)) hs'2
    dsimp only at this
    rw [Scheme.Hom.comp_apply, hσ] at this
    exact this
  have sxx' : s'.base (closedPoint B) ⤳ a.base (closedPoint C) := specializes_of_eq hx'

  have hs' : s' = Spec.map (X.presheaf.stalkSpecializes sxx' ≫ Scheme.stalkClosedPointTo s') ≫
      X.fromSpecStalk (a.base (closedPoint C)) := by
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]

  have e2 : (X.presheaf.stalkSpecializes sxx' ≫ Scheme.stalkClosedPointTo s') ≫ CommRingCat.ofHom π =
      Scheme.stalkClosedPointTo a := by
    have h2 := stalkClosedPointTo_congr (Spec.map (CommRingCat.ofHom π) ≫ s') a hs'2
      (specializes_of_eq (by rw [Scheme.Hom.comp_apply, hσ, hx']))
    rw [Scheme.stalkClosedPointTo_comp, stalkClosedPointTo_SpecMap' π (specializes_of_eq (X := Spec (CommRingCat.of B)) hσ.symm)] at h2
    have hP1 : s'.base ((Spec.map (CommRingCat.ofHom π)).base (closedPoint C)) ⤳ a.base (closedPoint C) :=
      specializes_of_eq (by rw [hσ, hx'])
    change Scheme.stalkClosedPointTo a = X.presheaf.stalkSpecializes hP1 ≫
      s'.stalkMap ((Spec.map (CommRingCat.ofHom π)).base (closedPoint C)) ≫
        (Spec (CommRingCat.of B)).presheaf.stalkSpecializes (specializes_of_eq (X := Spec (CommRingCat.of B)) hσ.symm) ≫
          (stalkClosedPointIso (CommRingCat.of B)).hom ≫ CommRingCat.ofHom π at h2
    rw [h2]
    simp only [Scheme.stalkClosedPointTo, Category.assoc]
    rw [← Scheme.Hom.stalkSpecializes_stalkMap_assoc s' (closedPoint B) _
      (specializes_of_eq (X := Spec (CommRingCat.of B)) hσ.symm)]
    rw [TopCat.Presheaf.stalkSpecializes_comp_assoc]
  have e1 : q.stalkMap (a.base (closedPoint C)) ≫ (X.presheaf.stalkSpecializes sxx' ≫ Scheme.stalkClosedPointTo s') =
      (Spec (CommRingCat.of B)).presheaf.stalkSpecializes sx ≫ (stalkClosedPointIso (CommRingCat.of B)).hom := by
    have hq' : q.base (s'.base (closedPoint B)) = closedPoint B := by rw [hx', hx]
    have h2 := stalkClosedPointTo_congr (𝟙 _) (s' ≫ q) hs'1.symm
      (specializes_of_eq (X := Spec (CommRingCat.of B)) (by rw [Scheme.Hom.comp_apply, hq']; rfl))
    rw [Scheme.stalkClosedPointTo_comp, stalkClosedPointTo_id] at h2
    have hP2 : closedPoint B ⤳ q.base (s'.base (closedPoint B)) := specializes_of_eq (X := Spec (CommRingCat.of B)) hq'.symm
    change q.stalkMap (s'.base (closedPoint B)) ≫ Scheme.stalkClosedPointTo s' =
      (Spec (CommRingCat.of B)).presheaf.stalkSpecializes hP2 ≫ (stalkClosedPointIso (CommRingCat.of B)).hom at h2
    have h5 := Scheme.Hom.stalkSpecializes_stalkMap q _ _ sxx'
    rw [← Category.assoc, ← h5, Category.assoc, h2, TopCat.Presheaf.stalkSpecializes_comp_assoc]
  have hφ' : (X.presheaf.stalkSpecializes sxx' ≫ Scheme.stalkClosedPointTo s').hom = φ :=
    huniq _ ⟨by rw [← CommRingCat.hom_comp, e1], by
      have := congrArg CommRingCat.Hom.hom e2
      rw [CommRingCat.hom_comp] at this
      exact this⟩
  have hφeq : X.presheaf.stalkSpecializes sxx' ≫ Scheme.stalkClosedPointTo s' = φc := by
    ext1; rw [hφ', hφc]
  rw [hs', hφeq]

end TanLift8

namespace TanLift10

theorem main_of_section
    (hsec : ∀ {B C : Type u} [CommRing B] [IsLocalRing B] [CommRing C] [IsLocalRing C]
      {X : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of B)) [Etale q]
      (π : B →+* C) (_ : Function.Surjective π) (_ : IsNilpotent (RingHom.ker π))
      (a : Spec (CommRingCat.of C) ⟶ X) (_ : a ≫ q = Spec.map (CommRingCat.ofHom π)),
      ∃! s : Spec (CommRingCat.of B) ⟶ X, s ≫ q = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom π) ≫ s = a)
    {X Y : Scheme.{u}} (p : X ⟶ Y) [Etale p]
    {B C : Type u} [CommRing B] [IsLocalRing B] [CommRing C] [IsLocalRing C]
    (π : B →+* C) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (Q : Spec (CommRingCat.of B) ⟶ Y) (a₀ : Spec (CommRingCat.of C) ⟶ X)
    (h : a₀ ≫ p = Spec.map (CommRingCat.ofHom π) ≫ Q) :
    ∃! Q' : Spec (CommRingCat.of B) ⟶ X, Q' ≫ p = Q ∧ Spec.map (CommRingCat.ofHom π) ≫ Q' = a₀ := by

  let q : pullback p Q ⟶ Spec (CommRingCat.of B) := pullback.snd p Q
  let a : Spec (CommRingCat.of C) ⟶ pullback p Q := pullback.lift a₀ (Spec.map (CommRingCat.ofHom π)) h
  have ha : a ≫ q = Spec.map (CommRingCat.ofHom π) := pullback.lift_snd _ _ _
  obtain ⟨s, ⟨hs1, hs2⟩, huniq⟩ := hsec q π hπ hker a ha
  refine ⟨s ≫ pullback.fst p Q, ⟨?_, ?_⟩, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hs1, Category.id_comp]
  · rw [← Category.assoc, hs2, pullback.lift_fst]
  · rintro Q'' ⟨h1, h2⟩
    let s'' : Spec (CommRingCat.of B) ⟶ pullback p Q := pullback.lift Q'' (𝟙 _) (by rw [h1, Category.id_comp])
    have e : s'' = s := by
      apply huniq
      refine ⟨pullback.lift_snd _ _ _, ?_⟩
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, h2]
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id]
    rw [← e, pullback.lift_fst]

end TanLift10

theorem solution
    {X Y : Scheme.{u}} (p : X ⟶ Y) [Etale p]
    {B C : Type u} [CommRing B] [IsLocalRing B] [CommRing C] [IsLocalRing C]
    (π : B →+* C) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (Q : Spec (CommRingCat.of B) ⟶ Y) (a₀ : Spec (CommRingCat.of C) ⟶ X)
    (h : a₀ ≫ p = Spec.map (CommRingCat.ofHom π) ≫ Q) :
    ∃! Q' : Spec (CommRingCat.of B) ⟶ X, Q' ≫ p = Q ∧ Spec.map (CommRingCat.ofHom π) ≫ Q' = a₀ := by
  exact TanLift10.main_of_section (fun q _ π hπ hker a ha => TanLift8.existsUnique_section q π hπ hker a ha) p π hπ hker Q a₀ h

end S_AlgebraicGeometry_existsUnique_comp_eq_of_etale_of_isLocalRing_of_surjective_of_isNilpotent
end P2MW
export P2MW.S_AlgebraicGeometry_existsUnique_comp_eq_of_etale_of_isLocalRing_of_surjective_of_isNilpotent (solution)
