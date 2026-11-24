-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementE
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementE
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:47:14.639813+00:00
-- url     : https://prove2.me/theorems/7d4c6450-9be1-464c-8374-c256ed0244c1
-- title:
--   Statement E
-- statement:
--   Definitions and structural lemmas for Statement E, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/StatementE.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementJ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
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
namespace Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp BHyp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq cob UnrOK IsLawOfLog BetaHyp)
section Defs
variable {K : Type} [Field K]
def thetaS (l : ℕ) (g2 g3 ε : K) : PowerSeries K :=
  PowerSeries.subst (PowerSeries.C ε * lgF K l) (Formalism.L2.Th1.CM.uSer g2 g3)
variable [CharZero K]
def phFF (l : ℕ) (g2 g3 s2 ε : K) : PowerSeries K :=
  -PowerSeries.subst (PowerSeries.C ε * lgF K l)
      (Formalism.L2.Th1.B.sigS (Formalism.L2.Th1.A.wpReg (Formalism.L2.Th1.A.shortW g2 g3))) +
    PowerSeries.C (s2 / 2) * (PowerSeries.C ε * lgF K l) ^ 2 -
    Formalism.L2.Th1.B.fLog (Formalism.L2.Th1.B.lU (lgF K l))
def phCurve (g2 g3 s2 : K) : PowerSeries K :=
  Formalism.L2.Th1.B.phO s2 (Formalism.L2.Th1.A.wpReg (Formalism.L2.Th1.A.shortW g2 g3)) (Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW g2 g3))
end Defs
def LtLogIsLgF : Prop :=
  ∀ (K : Type) [Field K] (l : ℕ), 2 ≤ l → Formalism.L2.Th1.CM.ltLog K l = lgF K l
def ThetaHom : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ‖(l : K)‖ = (l : ℝ)⁻¹ → ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F → ∀ g2 g3 ε : K,
    PowerSeries.subst (thetaS l g2 g3 ε) (Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW g2 g3)) =
      PowerSeries.C ε * lgF K l ∧
    IsHom F (Formalism.L2.Th1.A.fgl (Formalism.L2.Th1.A.shortW g2 g3)) (thetaS l g2 g3 ε)
def PhCompare : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ∀ g2 g3 s2 ε : K, ‖ε‖ = 1 → (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
    Simeq (phFF l g2 g3 s2 ε : MvPowerSeries Unit K)
      (PowerSeries.subst (thetaS l g2 g3 ε) (phCurve g2 g3 s2))
def CurveExponentCoboundaryCocycle : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime → 2 < l →
    ‖(l : K)‖ = (l : ℝ)⁻¹ → ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F →
    ∀ g2 g3 s2 ε : K, ‖g2‖ ≤ 1 → ‖g3‖ ≤ 1 → ‖ε‖ = 1 →
      (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
      F1 F (cob F (phFF l g2 g3 s2 ε))
def BHypCurve : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d : ℕ) [NeZero d]
    (σ : K →+* K), UnrOK K l σ → 2 ≤ d → Even d →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F →
    ∀ g2 g3 s2 ε : K, ‖g2‖ ≤ 1 → ‖g3‖ ≤ 1 → ‖ε‖ = 1 →
      (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
    ∀ (ι : Type) [Fintype ι] (om oms : ι → K), OwOK d σ om oms →
    ∀ ζ : K, IsPrimitiveRoot ζ (l ^ d - 1) →
      BHyp l d ⊤ ζ (beMean l σ (cob F (phFF l g2 g3 s2 ε)) om oms ζ)
end Formalism.L2.Th1.D


