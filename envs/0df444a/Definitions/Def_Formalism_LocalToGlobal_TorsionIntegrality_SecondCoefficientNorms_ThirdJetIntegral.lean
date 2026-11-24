-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_ThirdJetIntegral
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_ThirdJetIntegral
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T21:23:25.767799+00:00
-- url     : https://prove2.me/theorems/3c7708c8-dcc6-4542-bb9d-eb63e643ae9f
-- title:
--   Third Jet Integral
-- statement:
--   Definitions and structural lemmas for Third Jet Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/ThirdJetIntegral.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SigmaConstantAgrees
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.L2.Th1.C
def LogDerivInt : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv : PowerSeries K),
    IsLogPair l linv → FGInt R l linv → IsOneUnit R (PowerSeries.derivative K l)
def ThirdJetIntegral : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K),
    Frame R l linv ph → F1 R l linv ph →
    IntPS R ((Dinv l)^[3] ph) ∧ ∀ i : ℕ, 3 ≤ i → jet l ph i ∈ R
def JetsUnramified : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K) (a b : K),
    Frame R l linv ph → F1 R l linv ph → PhNormAt R l linv ph (-1) (-1) → (2 : K)⁻¹ ∈ R →
    AdjAt R l linv ph a b → (a - b)⁻¹ ∈ R → a ≠ b →
    (∀ i : ℕ, 1 ≤ i → jet l ph i ∈ R) ∧ ∀ i : ℕ, jet l (mvExp (-ph) : PowerSeries K) i ∈ R
def JetsShape : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K),
    Frame R l linv ph → F1 R l linv ph → PhNormAt R l linv ph (-1) (-1) → (2 : K)⁻¹ ∈ R →
    (∃ H : PowerSeries K, (∀ i : ℕ, jet l H i ∈ R) ∧
      (mvExp (-ph) : PowerSeries K) = mvExp (-(PowerSeries.C (jet l ph 2 / 2) * l ^ 2)) * H) ∧
    ∀ a b : K, AdjAt R l linv ph a b → (a - b) * jet l ph 2 ∈ R
def SumTwoUnitsProd : Prop :=
  ∀ (A B : Type) [CommRing A] [CommRing B],
    (∀ a : A, ∃ u v : Aˣ, a = u + v) → (∀ b : B, ∃ u v : Bˣ, b = u + v) →
    ∀ x : A × B, ∃ u v : (A × B)ˣ, x = u + v
end Formalism.L2.Th1.C


