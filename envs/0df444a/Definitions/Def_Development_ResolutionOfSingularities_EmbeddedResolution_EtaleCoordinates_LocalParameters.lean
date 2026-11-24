-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_LocalParameters
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_LocalParameters
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:47:53.809902+00:00
-- url     : https://prove2.me/theorems/14fc5a28-0efb-4ab1-9275-da7ce4b80329
-- title:
--   Local Parameters
-- statement:
--   Definitions and structural lemmas for Local Parameters, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/LocalParameters.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
namespace FunctorialResolution.EmbeddedResolution
noncomputable def residueFieldExtension (k A : Type*) [CommRing k] [CommRing A] [Algebra k A]
    [IsLocalRing A] [Algebra k (IsLocalRing.ResidueField A)]
    [IsScalarTower k A (IsLocalRing.ResidueField A)] :
    Algebra.Extension k (IsLocalRing.ResidueField A) :=
  { Ring := A
    σ := Function.surjInv (Ideal.Quotient.mk_surjective :
      Function.Surjective (algebraMap A (IsLocalRing.ResidueField A)))
    algebraMap_σ := Function.surjInv_eq _ }
noncomputable def kerToTensorResidueField (k A : Type*) [CommRing k] [CommRing A] [Algebra k A]
    [IsLocalRing A] :
    ↥(RingHom.ker (algebraMap A (IsLocalRing.ResidueField A))) →ₗ[A]
      IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A :=
  KaehlerDifferential.kerToTensor k A (IsLocalRing.ResidueField A)
section
variable (k A : Type*) [CommRing k] [CommRing A] [Algebra k A] [IsLocalRing A]
  [IsNoetherianRing A] [Algebra.FormallySmooth k A]
  [Module.Free A (KaehlerDifferential k A)] [Module.Finite A (KaehlerDifferential k A)]
  [Algebra k (IsLocalRing.ResidueField A)]
  [IsScalarTower k A (IsLocalRing.ResidueField A)]
  [Algebra.FormallySmooth k (IsLocalRing.ResidueField A)]
end
end FunctorialResolution.EmbeddedResolution


