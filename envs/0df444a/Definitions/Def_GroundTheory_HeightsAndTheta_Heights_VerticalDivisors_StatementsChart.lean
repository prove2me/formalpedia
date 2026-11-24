-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChart
-- name    : GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChart
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:33:17.277774+00:00
-- url     : https://prove2.me/theorems/7f596c32-90ea-4f86-9ac2-1b19ad700203
-- title:
--   Statements Chart
-- statement:
--   Definitions and structural lemmas for Statements Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/StatementsChart.lean

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
def SpecChart.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (v : HeightOneSpectrum (𝓞 K)), IsProjPrime I →
      ∀ (𝔫 : MaximalSpectrum (SecB e I v)) (W : Ideal (MvPolynomial (Fin n) (𝓞 K))) [W.IsPrime],
        W ∈ specComps I v → secIdealOf e I v W = 𝔫.asIdeal →
          ∃ ψ : Localization.AtPrime W ⧸
                (integralModel I).map (algebraMap _ (Localization.AtPrime W)) →+*
              Localization.AtPrime 𝔫.asIdeal,
            (∀ g : MvPolynomial (Fin n) (𝓞 K),
              ψ (Ideal.Quotient.mk _ (algebraMap _ (Localization.AtPrime W) g)) =
                algebraMap (SecB e I v) (Localization.AtPrime 𝔫.asIdeal)
                  (Ideal.Quotient.mk _ (g.map (algebraMap (𝓞 K) (ParDVR e n v))))) ∧
            IsLocalHom (ψ.comp (Ideal.Quotient.mk _)) ∧
            @RingHom.Flat (Localization.AtPrime W ⧸
                (integralModel I).map (algebraMap _ (Localization.AtPrime W)))
              (Localization.AtPrime 𝔫.asIdeal) _ _ ψ ∧
            (IsLocalRing.maximalIdeal (Localization.AtPrime W)).map (ψ.comp (Ideal.Quotient.mk _)) =
              IsLocalRing.maximalIdeal (Localization.AtPrime 𝔫.asIdeal)
end
end GroundTheory.Heights₂.Heights.Vertical


