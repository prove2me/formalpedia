-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_JetExpShape
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_JetExpShape
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:04.098457+00:00
-- url     : https://prove2.me/theorems/d01ee33a-70aa-48e8-bd17-1f22986cf972
-- title:
--   Jet Exp Shape
-- statement:
--   Definitions and structural lemmas for Jet Exp Shape, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/JetExpShape.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IsotropicVanish
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
def Dinv {K : Type} [Field K] (l f : PowerSeries K) : PowerSeries K :=
  (PowerSeries.derivative K l)⁻¹ * PowerSeries.derivative K f
def jet {K : Type} [Field K] (l f : PowerSeries K) (i : ℕ) : K :=
  PowerSeries.constantCoeff ((Dinv l)^[i] f)
def JetAdditive : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (l linv f : PowerSeries K), IsLogPair l linv →
    ∀ i : ℕ, jet l f i = (i.factorial : K) * PowerSeries.coeff i (PowerSeries.subst linv f)
def JetLG : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l f : PowerSeries K),
    IsOneUnit R (PowerSeries.derivative K l) → LG R f → ∀ i : ℕ, 1 ≤ i → jet l f i ∈ R
def JetNorm : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K) (a b : K),
    IsLogPair l linv → IsOneUnit R (PowerSeries.derivative K l) →
    PowerSeries.constantCoeff ph = 0 → PhNormAt R l linv ph a b →
    ∀ i : ℕ, 1 ≤ i → (a ^ i - a * b) * jet l ph i ∈ R
def JetOne : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K),
    IsLogPair l linv → IsOneUnit R (PowerSeries.derivative K l) →
    PowerSeries.constantCoeff ph = 0 → PhNormAt R l linv ph (-1) (-1) → (2 : K)⁻¹ ∈ R →
    jet l ph 1 ∈ R
def JetAdj : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K) (a b : K),
    IsLogPair l linv → PowerSeries.constantCoeff ph = 0 → AdjAt R l linv ph a b →
    (a - b) * jet l ph 2 ∈ R
def JetExp : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K),
    IsLogPair l linv → PowerSeries.constantCoeff ph = 0 → (∀ i : ℕ, 1 ≤ i → jet l ph i ∈ R) →
    ∀ i : ℕ, jet l (mvExp (-ph) : PowerSeries K) i ∈ R
def JetExpShape : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K),
    IsLogPair l linv → PowerSeries.constantCoeff ph = 0 →
    (∀ i : ℕ, 1 ≤ i → i ≠ 2 → jet l ph i ∈ R) →
    ∃ H : PowerSeries K, (∀ i : ℕ, jet l H i ∈ R) ∧
      (mvExp (-ph) : PowerSeries K) = mvExp (-(PowerSeries.C (jet l ph 2 / 2) * l ^ 2)) * H
end Formalism.L2.Th1.C


