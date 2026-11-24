-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveEndoAll
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveEndoAll
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T21:13:31.272619+00:00
-- url     : https://prove2.me/theorems/2a6ee762-4d41-47e6-a573-573b4c0c677d
-- title:
--   Curve Endo All
-- statement:
--   Definitions and structural lemmas for Curve Endo All, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/CurveEndoAll.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_JetExpShape
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
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
open Formalism.L2.Th1.A (logSer expSer wpReg xS xPlus)
section Defs8
variable {K : Type} [Field K]
def CoeffIn (R : Subring K) (W : WeierstrassCurve K) : Prop :=
  W.a₁ ∈ R ∧ W.a₂ ∈ R ∧ W.a₃ ∈ R ∧ W.a₄ ∈ R ∧ W.a₆ ∈ R
def wTr (W : WeierstrassCurve K) (xP yP : K) : PowerSeries K :=
  PowerSeries.subst (expSer W) (xPlus W xP yP) + PowerSeries.C (W.b₂ / 12)
def IsEndoCurve (W : WeierstrassCurve K) {ι : Type} [Fintype ι] (neg : ι → ι) (xP yP : ι → K)
    (al : K) : Prop :=
  (∀ P, W.toAffine.Equation (xP P) (yP P)) ∧ (∀ P, neg (neg P) = P) ∧
  (∀ P, xP (neg P) = xP P ∧ yP (neg P) = W.toAffine.negY (xP P) (yP P)) ∧
  PowerSeries.C (al ^ 2) * PowerSeries.rescale al (wpReg W) =
    wpReg W + ∑ P, (wTr W (xP P) (yP P) - PowerSeries.C (xP P + W.b₂ / 12))
end Defs8
def CurveFrame : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (W : WeierstrassCurve K), CoeffIn R W →
    IsLogPair (logSer W) (expSer W) ∧ XIsWp (wpReg W) (logSer W) (xS W) (W.b₂ / 12) ∧
    IsOneUnit R (xS W) ∧ FGInt R (logSer W) (expSer W) ∧
    IsOneUnit R (PowerSeries.derivative K (logSer W))
def CurveSecondLogDerivative : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (W : WeierstrassCurve K) (xP yP : K),
    W.toAffine.Equation xP yP →
    HasSecondLogDeriv (wpShift (wpReg W) (xP + W.b₂ / 12))
      (2 * wpReg W - wTr W xP yP - wTr W xP (W.toAffine.negY xP yP))
def CurveEndoZ : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (W : WeierstrassCurve K) (ι : Type) [Fintype ι]
    (neg : ι → ι) (xP yP : ι → K) (al : K), IsEndoCurve W neg xP yP al →
    IsEndoZ (wpReg W) neg (fun P => xP P + W.b₂ / 12) (fun P => wTr W (xP P) (yP P)) al
def CurveEndoR : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (W : WeierstrassCurve K), CoeffIn R W →
    ∀ (ι : Type) [Fintype ι] (neg : ι → ι) (xP yP : ι → K) (al albar : K),
    IsEndoCurve W neg xP yP al → (∀ P, xP P ∈ R) → (∀ P, yP P ∈ R) →
    al * albar = (Fintype.card ι : K) + 1 → al ∈ R → al⁻¹ ∈ R → (al ^ 2 - 1) * (W.b₂ / 12) ∈ R →
    IsEndoR R (wpReg W) (logSer W) (W.b₂ / 12) neg xP (fun P => wTr W (xP P) (yP P))
      (fun P => xPlus W (xP P) (yP P)) al albar
def CurveEndoAll : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K),
    IsClosed (R : Set K) → (2 : K)⁻¹ ∈ R → ∀ (W : WeierstrassCurve K), CoeffIn R W → ∀ s2 : K,
    F1 R (logSer W) (expSer W) (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) →
    ∀ (O : Type) [CommRing O] [StarRing O] [TopologicalSpace O] (τ : O →+* K),
    Continuous τ → Continuous (star : O → O) →
    (∀ z : O, star z = z → τ z ∈ closure (Set.range (fun n : ℤ => (n : K)))) →
    IsUnit (2 : O) → (∀ α : O, ∃ u v : Oˣ, α = u + v) →
    ∀ Dn : Set O, (∀ α : Oˣ, (α : O) ∈ closure Dn) →
    (∀ α ∈ Dn, ∃ (ι : Type) (_ : Fintype ι) (neg : ι → ι) (xP yP : ι → K),
      IsEndoCurve W neg xP yP (τ α) ∧ (∀ P, xP P ∈ R) ∧ (∀ P, yP P ∈ R) ∧
      τ α * τ (star α) = (Fintype.card ι : K) + 1 ∧ τ α ∈ R ∧ (τ α)⁻¹ ∈ R ∧
      ((τ α) ^ 2 - 1) * (W.b₂ / 12) ∈ R ∧
      τ α * (τ α - τ (star α)) * s2 = ∑ P, (xP P + W.b₂ / 12)) →
    (∀ α : O, EndInt R (logSer W) (expSer W) (τ α) ∧
      PhNormAt R (logSer W) (expSer W) (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) (τ α) (τ (star α)) ∧
      AdjAt R (logSer W) (expSer W) (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) (τ α) (τ (star α)) ∧
      (τ α - τ (star α)) * jet (logSer W) (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) 2 ∈ R) ∧
    jet (logSer W) (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) 1 ∈ R
end Formalism.L2.Th1.C


