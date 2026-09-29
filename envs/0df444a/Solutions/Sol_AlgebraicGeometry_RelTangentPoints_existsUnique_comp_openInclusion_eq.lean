-- Prove2me | solution 1 for AlgebraicGeometry.RelTangentPoints.existsUnique_comp_openInclusion_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/8e0f5161-4169-558e-b172-10c479568caa

import Mathlib
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelTangentPoints_existsUnique_comp_openInclusion_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FactorAux

theorem subsingleton_spec (k : Type u) [Field k] (V : Type u) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V]
    [IsCentralScalar k V] : Subsingleton (PrimeSpectrum (TrivSqZeroExt k V)) := by
  have key : ∀ P : PrimeSpectrum (TrivSqZeroExt k V), P.asIdeal = IsLocalRing.maximalIdeal _ := by
    intro P
    refine le_antisymm (IsLocalRing.le_maximalIdeal P.isPrime.ne_top) fun m hm => ?_
    have hfst : m.fst = 0 := by
      by_contra h
      exact hm (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (Ne.isUnit h))
    have hsq : m * m = 0 := by
      have : m = TrivSqZeroExt.inr m.snd := by ext <;> simp [hfst]
      rw [this, TrivSqZeroExt.inr_mul_inr]
    have : m * m ∈ P.asIdeal := by rw [hsq]; exact P.asIdeal.zero_mem
    exact (P.isPrime.mem_or_mem this).elim id id
  exact ⟨fun P Q => PrimeSpectrum.ext ((key P).trans (key Q).symm)⟩

end FactorAux

theorem solution
    {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (pt : Spec (CommRingCat.of k) ⟶ X)
    (V : Type u) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]
    {Z₀ Z : Scheme.{u}} (f₀ : Z₀ ⟶ Spec (CommRingCat.of k))
    (q₁ : Z ⟶ Z₀) (q₂ : Z ⟶ SquareZero.spec k V) (hZ : IsPullback q₁ q₂ f₀ (SquareZero.toBase k V))
    (w : RelTangentPoints x pt V f₀ q₁ q₂ hZ)
    (U : X.Opens) (p₁ : Spec (CommRingCat.of k) ⟶ (U : Scheme.{u})) (hp₁ : p₁ ≫ U.ι = pt) :
    ∃! w₁ : Z ⟶ (U : Scheme.{u}), w₁ ≫ U.ι = w.1 := by

  set s := SquareZero.zeroSection V f₀ q₁ q₂ hZ with hs
  have hsq : IsPullback s f₀ q₂ (SquareZero.basePoint k V) := by
    refine IsPullback.of_right ?_ (SquareZero.zeroSection_snd V f₀ q₁ q₂ hZ) hZ
    rw [hs, SquareZero.zeroSection_fst, SquareZero.basePoint_toBase]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  have hbp : Surjective (SquareZero.basePoint k V) := by
    exact ⟨fun d => ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k),
      @Subsingleton.elim _ (FactorAux.subsingleton_spec k V) _ _⟩⟩
  have hsurj : Surjective s := MorphismProperty.of_isPullback (P := @Surjective) hsq.flip hbp
  have hrange : Set.range w.1.base ⊆ Set.range U.ι.base := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨z₀, rfl⟩ := hsurj.surj z
    refine ⟨p₁.base (f₀.base z₀), ?_⟩
    have h1 : w.1.base (s.base z₀) = pt.base (f₀.base z₀) := by
      have := congrArg (fun h : Z₀ ⟶ X => h.base z₀) w.zeroSection_comp
      exact this
    have h2 : U.ι.base (p₁.base (f₀.base z₀)) = pt.base (f₀.base z₀) := by
      have := congrArg (fun h : Spec (CommRingCat.of k) ⟶ X => h.base (f₀.base z₀)) hp₁
      exact this
    exact h2.trans h1.symm
  refine ⟨IsOpenImmersion.lift U.ι w.1 hrange, IsOpenImmersion.lift_fac _ _ _, fun w₁ hw₁ => ?_⟩
  exact (cancel_mono U.ι).mp (hw₁.trans (IsOpenImmersion.lift_fac _ _ _).symm)

end S_AlgebraicGeometry_RelTangentPoints_existsUnique_comp_openInclusion_eq
end P2MW
export P2MW.S_AlgebraicGeometry_RelTangentPoints_existsUnique_comp_openInclusion_eq (solution)
