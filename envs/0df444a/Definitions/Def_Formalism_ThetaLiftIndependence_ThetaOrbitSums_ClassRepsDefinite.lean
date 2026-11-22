-- Prove2me | Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_ClassRepsDefinite
-- name    : Formalism_ThetaLiftIndependence_ThetaOrbitSums_ClassRepsDefinite
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:14:23.15919+00:00
-- url     : https://prove2.me/theorems/4dde4fd1-925f-4aba-a3ee-6aa8369acbb4
-- title:
--   Class Reps Definite
-- statement:
--   Definitions and structural lemmas for Class Reps Definite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLiftIndependence/ThetaOrbitSums/ClassRepsDefinite.lean

import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_HermitianLattices_FinalNeighbourConstruct
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_LatLiftIndep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.ThetaLiftIndependence
namespace DefiniteClassRepresentatives
open Formalism.HermitianLatticesTheory LatticeLiftIndependence
variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
def isoSetoid (h : V →ₗ⋆[K] V →ₗ[K] K) :
    Setoid (Submodule (NumberField.RingOfIntegers K) V) where
  r N M := ∃ g ∈ isom h, gmap g N = M
  iseqv := by
    refine ⟨fun N => ⟨1, (isom h).one_mem, gmap_one N⟩, ?_, ?_⟩
    · rintro N M ⟨g, hg, e⟩
      exact ⟨g⁻¹, (isom h).inv_mem hg, by rw [← e, gmap_inv_gmap]⟩
    · rintro N M P ⟨g, hg, e⟩ ⟨g', hg', e'⟩
      exact ⟨g' * g, (isom h).mul_mem hg' hg, by rw [gmap_mul, e, e']⟩
open Classical in

def pick (h : V →ₗ⋆[K] V →ₗ[K] K) (s₀ : Finset (Submodule (NumberField.RingOfIntegers K) V))
    (q : Quotient (isoSetoid h)) : Submodule (NumberField.RingOfIntegers K) V :=
  if hq : ∃ N ∈ s₀, Quotient.mk (isoSetoid h) N = q then Classical.choose hq else ⊥
end DefiniteClassRepresentatives
end Formalism.ThetaLiftIndependence


