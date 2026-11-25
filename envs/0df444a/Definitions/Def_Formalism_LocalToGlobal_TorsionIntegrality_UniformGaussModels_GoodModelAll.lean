-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_UniformGaussModels_GoodModelAll
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_UniformGaussModels_GoodModelAll
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T04:30:05.18501+00:00
-- url     : https://prove2.me/theorems/1f4e2828-2c6c-5358-9c4b-71ac4fe74a57
-- title:
--   Good Model All
-- statement:
--   Definitions and structural lemmas for Good Model All, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/UniformGaussModels/GoodModelAll.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_UniformGaussModels_IsHypPair
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_HomotheticLatticeIntegralS2
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementV
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
namespace Formalism.L2.Th1.Top
open Formalism.L2.Th1.CM (HasCMBy omegaK)
open Formalism.L2.Th1.E (IntCurve curveL)
open Formalism.L2.Th1.A (logSer expSer wpReg)
open Formalism.G (unitBall)
def thetaZ (p : ℕ) [Fact p.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[p]) (ω₀ : ℂ)
    {κ n : Type} [Fintype κ] [Fintype n] (r : κ → ℂ_[p]) (s : κ → n → ℂ) : MvPowerSeries n ℂ_[p] :=
  Formalism.L2.Th1.E.thetaProd r (fun k i => PowerSeries.map (ι : ℂ →+* ℂ_[p])
    (Formalism.L2.Th1.F.taylor0 (Formalism.L2.Th1.F.opU L (s k i) (Formalism.L2.Th1.F.th0 L (ω₀ / 2)))))
def phC (p : ℕ) [Fact p.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[p]) : PowerSeries ℂ_[p] :=
  Formalism.L2.Th1.B.phO (ι (Formalism.L2.Th1.F.s2 L)) (wpReg (curveL p L ι)) (logSer (curveL p L ι))
def GoodModelAll : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), Squarefree dK → dK % 4 = 3 → HasCMBy dK L →
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ ι : ℂ ≃+* ℂ_[p],
    ∃ (c : ℂ) (hc : c ≠ 0), IntCurve (curveL p (Formalism.L2.Th1.F.scalePair L c hc) ι)
def CMDatum : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), dK % 4 = 3 → HasCMBy dK L →
  ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), IntCurve (curveL p L ι) →
  ∀ m n : ℤ, ¬ (p : ℤ) ∣ Formalism.L2.Th1.D.normInt dK m n →
  ∃ (S : Finset ℂ) (neg : S → S) (xP yP : S → ℂ_[p]),
    Formalism.L2.Th1.C.IsEndoCurve (curveL p L ι) neg xP yP (ι ((m : ℂ) + (n : ℂ) * omegaK dK)) ∧
    (∀ P, ‖xP P‖ ≤ 1) ∧ (∀ P, ‖yP P‖ ≤ 1) ∧
    ι ((m : ℂ) + (n : ℂ) * omegaK dK) * ι ((m : ℂ) + (n : ℂ) * (1 - omegaK dK)) =
      (Fintype.card S : ℂ_[p]) + 1 ∧
    ι ((m : ℂ) + (n : ℂ) * omegaK dK) *
        (ι ((m : ℂ) + (n : ℂ) * omegaK dK) - ι ((m : ℂ) + (n : ℂ) * (1 - omegaK dK))) *
        ι (Formalism.L2.Th1.F.s2 L) = ∑ P, (xP P + (curveL p L ι).b₂ / 12)
def ShapeCM : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), dK % 4 = 3 → HasCMBy dK L →
  ∀ (p : ℕ) [Fact p.Prime], p ∣ dK → ∀ ι : ℂ ≃+* ℂ_[p], IntCurve (curveL p L ι) →
    Formalism.L2.Th1.G.ShapeAt (logSer (curveL p L ι)) (expSer (curveL p L ι)) (phC p L ι) dK
def JetsCM : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), dK % 4 = 3 → HasCMBy dK L →
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ¬ p ∣ dK → ∀ ι : ℂ ≃+* ℂ_[p], IntCurve (curveL p L ι) →
    ∀ i : ℕ, 1 ≤ i → ‖Formalism.L2.Th1.C.jet (logSer (curveL p L ι)) (phC p L ι) i‖ ≤ 1
def KernelJoint : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[p]), p ≠ 2 → IntCurve (curveL p L ι) →
  ∀ (n : Type) [Fintype n],
  ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
  ∀ (κ : Type) [Fintype κ] (r : κ → ℂ_[p]) (s : κ → n → ℂ) (N : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < N →
    ¬ p ∣ N → (∀ k i, (N : ℂ) * s k i ∈ L.lattice) →
    ∃ G : MvPowerSeries n ℂ_[p], Formalism.L2.Th1.C.IntMv (unitBall ℂ_[p]) G ∧
      thetaZ p L ι ω₀ r s = Formalism.L2.Th1.G.toZ (expSer (curveL p L ι))
        (Formalism.L2.Th1.C.mvExp (-(Formalism.L2.Th1.G.phSum (fun _ => (1 : ℂ_[p])) (phC p L ι))) * G)
end Formalism.L2.Th1.Top


