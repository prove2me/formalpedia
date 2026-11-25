-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsVertPointNagata
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsVertPointNagata
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T06:09:40.30718+00:00
-- url     : https://prove2.me/theorems/0db9b744-4027-40d4-9137-6279d0de4f2e
-- title:
--   Statements Vert Point Nagata
-- statement:
--   Definitions and structural lemmas for Statements Vert Point Nagata, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsVertPointNagata.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsVertPointLengthSteps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
noncomputable section
instance isPrime_map_C_maximalIdeal (R : Type*) [CommRing R] [IsLocalRing R] :
    ((IsLocalRing.maximalIdeal R).map (Polynomial.C : R →+* Polynomial R)).IsPrime :=
  (Ideal.isPrime_map_C_iff_isPrime _).2 inferInstance
abbrev nagataRing (R : Type*) [CommRing R] [IsLocalRing R] : Type _ :=
  Localization.AtPrime ((IsLocalRing.maximalIdeal R).map (Polynomial.C : R →+* Polynomial R))
def VertPointNagata.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      ∀ W ∈ divSupp (mCoordIdeal y) s, ∀ t : T, (X ⟨(), t⟩ : MRing (fun _ : Unit => T)) ∉ W →
        ∀ [W.IsPrime] [(curvePtIdeal y W).IsPrime] (a b : T → curveRing y)
          (hb : ∀ u, b u ∉ curvePtIdeal y W), (∀ u, (b u : K') * (y ⟨(), u⟩ / y ⟨(), t⟩) = a u) →
          ∃ Φ : Localization.AtPrime W →+* nagataRing (Localization.AtPrime (curvePtIdeal y W)),
            Function.Surjective Φ ∧
            RingHom.ker Φ = (mCoordIdeal y).map (algebraMap (MRing (fun _ : Unit => T)) _) ∧
            ∀ f : MRing (fun _ : Unit => T), Φ (algebraMap _ _ f) =
              algebraMap (Polynomial (Localization.AtPrime (curvePtIdeal y W))) _
                (aeval (fun p : (Σ _ : Unit, T) => Polynomial.C (IsLocalization.mk'
                  (Localization.AtPrime (curvePtIdeal y W)) (a p.2)
                  (⟨b p.2, hb p.2⟩ : (curvePtIdeal y W).primeCompl)) * Polynomial.X) f)
end
end GroundTheory.Heights₂.Heights


