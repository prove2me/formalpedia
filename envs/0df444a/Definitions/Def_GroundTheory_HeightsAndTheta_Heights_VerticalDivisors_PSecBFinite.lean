-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBFinite
-- name    : GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBFinite
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:33:04.898341+00:00
-- url     : https://prove2.me/theorems/e127f06c-3407-4109-b228-a8e191c4f328
-- title:
--   PSec BFinite
-- statement:
--   Definitions and structural lemmas for PSec BFinite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBFinite.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
namespace SecBFinite
section Homog
variable {σ R S : Type*} [CommRing R] [CommRing S]
attribute [local instance] MvPolynomial.gradedAlgebra
end Homog
section NumberField
variable {K : Type*} [Field K] [NumberField K]
def parIdx (e n : ℕ) (ij : Fin (e + 1) × Fin n) : Par e n :=
  Fin.cases (motive := fun _ => Par e n) (Sum.inr ij.2) (fun i => Sum.inl (i, ij.2)) ij.1
def specHom (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    MvPolynomial (Fin n ⊕ (Fin (e + 1) × Fin n)) (𝓞 K) →+* MvPolynomial (Fin n) (ParDVR e n v) :=
  eval₂Hom (C.comp (algebraMap (𝓞 K) (ParDVR e n v)))
    (Sum.elim X fun ij => C (parY e n v (parIdx e n ij)))
end NumberField
end SecBFinite
end
end GroundTheory.Heights₂.Heights.Vertical


