-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_WeightedSumScaling
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_WeightedSumScaling
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:18:23.339744+00:00
-- url     : https://prove2.me/theorems/598f8d78-37bd-4579-bac7-14fcf39826ae
-- title:
--   Weighted Sum Scaling
-- statement:
--   Definitions and structural lemmas for Weighted Sum Scaling, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/WeightedSumScaling.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Lemmata_PeriodicFunctions_PeriodicApplyMulAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
namespace PI.TwistedEisensteinNonvanishing.W
open Loc LocE
section Perm
variable {K : Type} [Field K]
end Perm
variable {E K : Type} [Field E] [NumberField E] [Field K]
def Sg (P : HeightOneSpectrum (𝓞 E)) (A B : ℕ) (φ : E → K) : K :=
  ∑ i ∈ Finset.range (qOf P ^ (A + B)), φ ((i : E) / (qOf P : E) ^ A)
def W1 (P : HeightOneSpectrum (𝓞 E)) (A B : ℕ) (φ : E → K) : K := ((qOf P : K) ^ B)⁻¹ * Sg P A B φ
def Good1 (P : HeightOneSpectrum (𝓞 E)) (a b : ℕ) (φ : E → K) : Prop :=
  (∀ u, φ u ≠ 0 → IntAt P ((qOf P : E) ^ a * u)) ∧
  (∀ u δ, IntAt P (δ / (qOf P : E) ^ b) → φ (u + δ) = φ u)
variable {P : HeightOneSpectrum (𝓞 E)}
section Main
variable (hN : NTAll) (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (hK : ((qOf P : ℕ) : K) ≠ 0)
include hN hp hq
end Main
end PI.TwistedEisensteinNonvanishing.W


