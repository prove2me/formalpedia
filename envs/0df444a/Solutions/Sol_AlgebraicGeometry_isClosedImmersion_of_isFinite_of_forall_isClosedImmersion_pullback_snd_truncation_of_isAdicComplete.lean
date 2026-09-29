-- Prove2me | solution 1 for AlgebraicGeometry.isClosedImmersion_of_isFinite_of_forall_isClosedImmersion_pullback_snd_truncation_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/6e56579e-e2df-5fd1-ad1e-8e899863682f

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_AlgebraicGeometry_IdealSheafData_eq_bot_of_forall_le_ker_pullback_fst_truncation_of_isProper_of_isAdicComplete
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isClosedImmersion_of_isFinite_of_forall_isClosedImmersion_pullback_snd_truncation_of_isAdicComplete

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {Γ X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] (h : Γ ⟶ X) [IsFinite h]

    (sR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of R))
    (hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1)))))
    (hn : ∀ n : ℕ, IsClosedImmersion (Limits.pullback.snd h (Limits.pullback.fst f (sR n)))) :
    IsClosedImmersion h := by

  let pP : pullback h h ⟶ Spec (CommRingCat.of R) := pullback.fst h h ≫ h ≫ f
  haveI : IsProper pP := inferInstance
  let Δ := pullback.diagonal h
  haveI : IsClosedImmersion Δ := inferInstance

  have hfac : ∀ n : ℕ, Δ.ker ≤ (pullback.fst pP (sR n)).ker := by
    intro n
    haveI := hn n
    let q := pullback.fst pP (sR n)

    have wX : (q ≫ pullback.fst h h ≫ h) ≫ f = pullback.snd pP (sR n) ≫ sR n := by
      simp only [Category.assoc]; exact pullback.condition
    let xP : pullback pP (sR n) ⟶ pullback f (sR n) := pullback.lift (q ≫ pullback.fst h h ≫ h) (pullback.snd pP (sR n)) wX
    have w₁ : (q ≫ pullback.fst h h) ≫ h = xP ≫ pullback.fst f (sR n) := by rw [Category.assoc, pullback.lift_fst]
    have w₂ : (q ≫ pullback.snd h h) ≫ h = xP ≫ pullback.fst f (sR n) := by
      rw [Category.assoc, ← pullback.condition, pullback.lift_fst]
    let a := pullback.lift (q ≫ pullback.fst h h) xP w₁
    let b := pullback.lift (q ≫ pullback.snd h h) xP w₂
    have hab : a = b := by
      rw [← cancel_mono (pullback.snd h (pullback.fst f (sR n)))]
      simp only [a, b, pullback.lift_snd]
    have h12 : q ≫ pullback.fst h h = q ≫ pullback.snd h h := by
      have := congrArg (· ≫ pullback.fst h (pullback.fst f (sR n))) hab
      simpa only [a, b, pullback.lift_fst] using this
    have hq : q = (q ≫ pullback.fst h h) ≫ Δ := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
      · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, h12]
    have hq' : pullback.fst pP (sR n) = (q ≫ pullback.fst h h) ≫ Δ := hq
    rw [hq']
    exact Scheme.Hom.le_ker_comp _ _
  have hker : Δ.ker = ⊥ :=
    AlgebraicGeometry.IdealSheafData.eq_bot_of_forall_le_ker_pullback_fst_truncation_of_isProper_of_isAdicComplete
      R I pP sR hsR Δ.ker hfac
  haveI : IsIso Δ := (IsClosedImmersion.isIso_iff_ker_eq_bot).mpr hker
  haveI : Mono h := (pullback.isIso_diagonal_iff h).mp inferInstance
  exact (IsClosedImmersion.iff_isFinite_and_mono h).mpr ⟨inferInstance, inferInstance⟩

end S_AlgebraicGeometry_isClosedImmersion_of_isFinite_of_forall_isClosedImmersion_pullback_snd_truncation_of_isAdicComplete
end P2MW
export P2MW.S_AlgebraicGeometry_isClosedImmersion_of_isFinite_of_forall_isClosedImmersion_pullback_snd_truncation_of_isAdicComplete (solution)
