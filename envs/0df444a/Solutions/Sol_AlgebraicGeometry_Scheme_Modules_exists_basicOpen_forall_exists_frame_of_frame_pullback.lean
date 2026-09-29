-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_basicOpen_forall_exists_frame_of_frame_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/478b0534-8071-5c05-8001-31f0e3aac43c

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_frame_of_frame_pullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_forall_exists_frame
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_forall_exists_frame_of_frame_pullback

universe u

set_option autoImplicit false
section beta_solution
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [UniversallyClosed f]
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) {ι : Type*} [Finite ι] (m : ι → Γ(M, ⊤))
    (K : Type u) [Field K] [Algebra R K] (𝔭 : PrimeSpectrum R) (h𝔭 : RingHom.ker (algebraMap R K) = 𝔭.asIdeal)
    (hgen : ∀ z : ↑(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
      ∃ (i : ι) (U' : (Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).Opens), z ∈ U' ∧
        ∀ V' : (Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).Opens, V' ≤ U' →
          Function.Bijective fun g : Γ(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K))), V') =>
            g • (((Scheme.Modules.pullback
                    (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj M).presheaf.map
                  (homOfLE (le_top : V' ≤ ⊤)).op
              ((((Scheme.Modules.pullbackPushforwardAdjunction
                  (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))).unit.app M).app ⊤) (m i)) :
              Γ((Scheme.Modules.pullback
                    (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj M, V'))) :
    ∃ g : R, g ∉ 𝔭.asIdeal ∧ ∀ x : X, f x ∈ PrimeSpectrum.basicOpen g →
      ∃ (i : ι) (U : X.Opens), x ∈ U ∧ ∀ V : X.Opens, V ≤ U →
        Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (m i) : Γ(M, V)) := by
  classical
  apply Scheme.Modules.exists_basicOpen_forall_exists_frame f M m 𝔭
  intro x hx
  have hpt : f x = (Spec.map (CommRingCat.ofHom (algebraMap R K))) (⊥ : PrimeSpectrum K) := by
    rw [hx]
    apply PrimeSpectrum.ext
    rw [Spec.map_apply, PrimeSpectrum.comap_asIdeal]
    change 𝔭.asIdeal = Ideal.comap (algebraMap R K) ⊥
    rw [← RingHom.ker_eq_comap_bot, h𝔭]
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := f) (g := Spec.map (CommRingCat.ofHom (algebraMap R K))) x _ hpt
  obtain ⟨i, U', hzU', hU'⟩ := hgen z
  obtain ⟨U, hxU, hU⟩ := Scheme.Modules.exists_frame_of_frame_pullback
    (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) M hM (m i) z ⟨U', hzU', hU'⟩
  exact ⟨i, U, hz ▸ hxU, hU⟩

end beta_solution

end S_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_forall_exists_frame_of_frame_pullback
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_forall_exists_frame_of_frame_pullback (solution)
