-- Prove2me | solution 1 for AlgebraicGeometry.exists_comp_eq_specMap_of_asIdeal_eq_bot_of_locallyOfFiniteType_of_isAlgClosed_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/89102379-4149-5cf0-938b-d1811111bf76

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_comp_eq_of_surjective_of_locallyOfFiniteType_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_comp_eq_specMap_of_asIdeal_eq_bot_of_locallyOfFiniteType_of_isAlgClosed_of_injective

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits Topology

theorem solution
    (R : Type) [CommRing R] [IsDomain R]
    (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
    (x : X) (hx : (f.base x).asIdeal = ⊥)
    (K : Type) [Field K] [IsAlgClosed K] (φ : R →+* K) (hφ : Function.Injective φ) :
    ∃ σ : Spec (CommRingCat.of K) ⟶ X, σ ≫ f = Spec.map (CommRingCat.ofHom φ) := by
  classical
  let g := Spec.map (CommRingCat.ofHom φ)
  obtain ⟨pt⟩ := (inferInstance : Nonempty ↥(Spec (CommRingCat.of K)))
  have hpt : g.base pt = f.base x := by
    show PrimeSpectrum.comap φ pt = f.base x
    apply PrimeSpectrum.ext
    rw [hx]
    show Ideal.comap φ pt.asIdeal = ⊥
    rw [Ideal.eq_bot_of_prime pt.asIdeal, Ideal.comap_bot_of_injective φ hφ]

  obtain ⟨z, hz1, hz2⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) x pt hpt.symm
  haveI : Surjective (pullback.snd f g) := ⟨fun y ↦ by
    obtain rfl : y = pt := Subsingleton.elim y pt
    exact ⟨z, hz2⟩⟩
  obtain ⟨τ, hτ⟩ :=
    AlgebraicGeometry.exists_comp_eq_of_surjective_of_locallyOfFiniteType_of_isAlgClosed
      (pullback.snd f g) (𝟙 _)
  refine ⟨τ ≫ pullback.fst f g, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hτ, Category.id_comp]

end S_AlgebraicGeometry_exists_comp_eq_specMap_of_asIdeal_eq_bot_of_locallyOfFiniteType_of_isAlgClosed_of_injective
end P2MW
export P2MW.S_AlgebraicGeometry_exists_comp_eq_specMap_of_asIdeal_eq_bot_of_locallyOfFiniteType_of_isAlgClosed_of_injective (solution)
