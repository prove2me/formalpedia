-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_PolynomialCoordinateExtension
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_PolynomialCoordinateExtension
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:58.377311+00:00
-- url     : https://prove2.me/theorems/1c224b5d-c9a7-4376-9a29-7fc2aaae4050
-- title:
--   Polynomial Coordinate Extension
-- statement:
--   Definitions and structural lemmas for Polynomial Coordinate Extension, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/PolynomialCoordinateExtension.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace FunctorialResolution.EmbeddedResolution
namespace EtaleCoordinates
open MvPolynomial
section
variable (k : Type*) [CommRing k] (ι κ : Type*)
noncomputable def sumEvalIter :
    MvPolynomial (ι ⊕ κ) k →ₐ[k] MvPolynomial κ (MvPolynomial ι k) :=
  aeval (Sum.elim (fun i : ι => (C (X i) : MvPolynomial κ (MvPolynomial ι k)))
    (fun j : κ => (X j : MvPolynomial κ (MvPolynomial ι k))))
@[reducible] noncomputable def sumEvalIterAlgebra :
    Algebra (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ (MvPolynomial ι k)) :=
  (sumEvalIter k ι κ).toRingHom.toAlgebra
end
section
variable (k : Type*) [CommRing k] (ι κ : Type*)
noncomputable def iterToSumRingHom :
    MvPolynomial κ (MvPolynomial ι k) →+* MvPolynomial (ι ⊕ κ) k :=
  eval₂Hom (eval₂Hom (C : k →+* MvPolynomial (ι ⊕ κ) k)
      (fun i : ι => (X (Sum.inl i) : MvPolynomial (ι ⊕ κ) k)))
    (fun j : κ => (X (Sum.inr j) : MvPolynomial (ι ⊕ κ) k))
attribute [local instance] sumEvalIterAlgebra
end
section
variable (k : Type*) [CommRing k] (ι κ : Type*) (S : Type*) [CommRing S]
  [Algebra (MvPolynomial ι k) S]
@[reducible] noncomputable def mapCoeffAlgebra :
    Algebra (MvPolynomial κ (MvPolynomial ι k)) (MvPolynomial κ S) :=
  (MvPolynomial.map (algebraMap (MvPolynomial ι k) S)).toAlgebra
attribute [local instance] mapCoeffAlgebra
end
section
universe u v
end
section
variable (k : Type*) [CommRing k] (ι κ : Type*) (S : Type*) [CommRing S]
  [Algebra (MvPolynomial ι k) S] [Algebra k S]
noncomputable def sumEval : MvPolynomial (ι ⊕ κ) k →ₐ[k] MvPolynomial κ S :=
  aeval (Sum.elim (fun i : ι => (C (coord k ι S i) : MvPolynomial κ S))
    (fun j : κ => (X j : MvPolynomial κ S)))
@[reducible] noncomputable def sumEvalAlgebra :
    Algebra (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ S) :=
  (sumEval k ι κ S).toRingHom.toAlgebra
attribute [local instance] sumEvalAlgebra
attribute [local instance] sumEvalIterAlgebra
attribute [local instance] mapCoeffAlgebra
variable (T : Type*) [CommRing T]
end
end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution


