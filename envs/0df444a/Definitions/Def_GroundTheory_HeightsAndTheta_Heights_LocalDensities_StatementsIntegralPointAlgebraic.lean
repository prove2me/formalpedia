-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsIntegralPointAlgebraic
-- name    : GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsIntegralPointAlgebraic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:29:25.808275+00:00
-- url     : https://prove2.me/theorems/ccde475f-4e53-4f9e-81ed-240fc69c15fa
-- title:
--   Statements Integral Point Algebraic
-- statement:
--   Definitions and structural lemmas for Statements Integral Point Algebraic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/StatementsIntegralPointAlgebraic.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsIntegralPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.FourB
open IsDedekindDomain NumberField
noncomputable section
def IntegralPointOfAlgebraicDomain.Hyp (F : Type) [Field F] [NumberField F] (S : Type) [CommRing S]
    [Algebra (𝓞 F) S] (v : HeightOneSpectrum (𝓞 F)) (M : Ideal S) : Prop :=
  Function.Injective (algebraMap (𝓞 F) S) ∧ Algebra.IsAlgebraic (𝓞 F) S ∧ M.IsMaximal ∧
    M.comap (algebraMap (𝓞 F) S) = v.asIdeal
def IntegralPointOfAlgebraicDomain.Statement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Type) [CommRing S] [IsDomain S] [Algebra (𝓞 F) S]
    [Algebra.FiniteType (𝓞 F) S] (v : HeightOneSpectrum (𝓞 F)) (M : Ideal S),
    IntegralPointOfAlgebraicDomain.Hyp F S v M →
    ∃ (L : Type) (_ : Field L) (_ : Algebra (v.adicCompletion F) L)
      (_ : FiniteDimensional (v.adicCompletion F) L) (y : S →+* L),
      y.comp (algebraMap (𝓞 F) S) =
          (algebraMap (v.adicCompletion F) L).comp
            ((algebraMap F (v.adicCompletion F)).comp (algebraMap (𝓞 F) F)) ∧
        Function.Injective y ∧
        (∀ a : S, (completionIntegersTo F v L).IsIntegralElem (y a)) ∧
        (∀ a ∉ M, ∃ b : L, b * y a = 1 ∧ (completionIntegersTo F v L).IsIntegralElem b) ∧
        ∀ a ∈ M, ∀ b : L, b * y a = 1 → ¬ (completionIntegersTo F v L).IsIntegralElem b
end
end GroundTheory.Heights₂.Heights.FourB


