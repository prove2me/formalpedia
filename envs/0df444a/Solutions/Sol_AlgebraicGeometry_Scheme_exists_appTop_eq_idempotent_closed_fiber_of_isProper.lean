-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_appTop_eq_idempotent_closed_fiber_of_isProper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-21T23:18:56.427003+00:00
-- url     : https://prove2.me/submissions/6a70e907-f19b-4863-90e8-455538333450
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AlgebraicGeometry_Scheme_ProperClosedFiberModels
import Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_closedFiberModels_of_isProper
import Theorems.Thm_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper

noncomputable section

section

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponClosedFiberThickenings (Fiber transition transition_fst transition_snd transition_comp)


namespace PhilipponIdempotentLiftingNoetherian

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

private abbrev q (I : Ideal R) := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
private abbrev swap (I : Ideal R) := pullbackSymmetry (q I) f

private abbrev reverseTransition {I J : Ideal R} (h : I ≤ J) : pullback f (q J) ⟶ pullback f (q I) :=
  pullback.map f (q J) f (q I) (𝟙 X) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)))
    (𝟙 _) (by simp) (by
      rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp_mk])

private theorem swap_transition {I J : Ideal R} (h : I ≤ J) :
    (swap f J).hom ≫ reverseTransition f h = transition f h ≫ (swap f I).hom := by
  apply pullback.hom_ext
  · simp only [Category.assoc, reverseTransition, pullback.map, pullback.lift_fst, Category.comp_id,
      pullbackSymmetry_hom_comp_fst, transition_snd]
  · simp only [Category.assoc, reverseTransition, pullback.map, pullback.lift_snd,
      pullbackSymmetry_hom_comp_snd_assoc, pullbackSymmetry_hom_comp_snd, transition_fst]

/-- A special-fiber idempotent lifts to a global regular function over a Noetherian base. -/
theorem exists_lift [IsNoetherianRing R] [IsProper f] (I : Ideal R)
    (e : Γ(Fiber f I, ⊤)) (he : IsIdempotentElem e) :
    ∃ b : Γ(X, ⊤), (pullback.snd (q I) f).appTop.hom b = e := by
  obtain ⟨c, hc⟩ := AlgebraicGeometry.exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper I f 1
  let n := 1 + c
  let hn : n ≠ 0 := by dsimp [n]; omega
  let H : I ^ n ≤ I ^ 1 := Ideal.pow_le_pow_right (Nat.le_add_right 1 c)
  let j := transition f (Ideal.pow_le_self (I := I) (n := 1) one_ne_zero)
  let k := transition f (Ideal.pow_le_self (I := I) hn)
  let : Surjective k := PhilipponClosedFiberThickenings.surjective_transition_pow f I hn
  obtain ⟨a, ⟨_, ha⟩, _⟩ := PhilipponSchemeIdempotentPullback.existsUnique_idempotent_lift k e he
  let t := (swap f (I ^ n)).inv.appTop.hom a
  obtain ⟨b, hb⟩ := hc t
  change (reverseTransition f H).appTop.hom t = (pullback.fst f (q (I ^ 1))).appTop.hom b at hb
  let s := j ≫ (swap f (I ^ 1)).hom
  have hTop : s ≫ reverseTransition f H = k ≫ (swap f (I ^ n)).hom := by
    dsimp only [s]
    rw [Category.assoc, swap_transition, ← Category.assoc, transition_comp]
  have hBottom : s ≫ pullback.fst f (q (I ^ 1)) = pullback.snd (q I) f := by
    dsimp only [s]
    rw [Category.assoc, pullbackSymmetry_hom_comp_fst, transition_snd]
  have ht : (swap f (I ^ n)).hom.appTop.hom t = a := by
    have h : (swap f (I ^ n)).inv.appTop ≫ (swap f (I ^ n)).hom.appTop = 𝟙 _ := by
      rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
    exact ConcreteCategory.congr_hom h a
  refine ⟨b, ?_⟩
  rw [← hBottom, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ← hb,
    ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hTop, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, ht]
  exact ha

end PhilipponIdempotentLiftingNoetherian

end

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution    {A : Type u} [CommRing A] [IsLocalRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f]
    (e : Γ(pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) f, ⊤))
    (he : IsIdempotentElem e) :
    ∃ a : Γ(X, ⊤),
      (pullback.snd (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) f).appTop.hom a = e := by
  obtain ⟨D⟩ := AlgebraicGeometry.Scheme.nonempty_closedFiberModels_of_isProper f
  refine PhilipponProperClosedFiberApproximation.exists_idempotent_lift
    (pullback.snd (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) f) D ?_ e he
  intro B _ _ _ Y g _ b hb
  exact PhilipponIdempotentLiftingNoetherian.exists_lift g (IsLocalRing.maximalIdeal B) b hb

end

end
