-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsSecIdealOfPrime
-- name    : GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsSecIdealOfPrime
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:55.970878+00:00
-- url     : https://prove2.me/theorems/655e4809-11f1-4269-9bf8-dbf2d80ae9b5
-- title:
--   Statements Sec Ideal Of Prime
-- statement:
--   Definitions and structural lemmas for Statements Sec Ideal Of Prime, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/StatementsSecIdealOfPrime.lean

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
def toSecB {K : Type*} [Field K] [NumberField K] {n : ℕ} (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (v : HeightOneSpectrum (𝓞 K)) : MvPolynomial (Fin n) (𝓞 K) →+* SecB e I v :=
  (Ideal.Quotient.mk (secIdeal (modelR e I v) (parY e n v))).comp
    (MvPolynomial.map (algebraMap (𝓞 K) (ParDVR e n v)))
def SecIdealOfPrime.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin (e + 1) × Fin n) K) (v : HeightOneSpectrum (𝓞 K)),
    IsProjPrime I → IsChowForm I (e + 1) f → ∀ W ∈ specComps I v,
      (secIdealOf e I v W).IsPrime ∧ (secIdealOf e I v W).comap (toSecB e I v) = W
end
end GroundTheory.Heights₂.Heights.Vertical


