-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementJ
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementJ
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T22:16:52.835973+00:00
-- url     : https://prove2.me/theorems/74f51f0c-d635-4e79-aced-a2373993eb65
-- title:
--   Statement J
-- statement:
--   Definitions and structural lemmas for Statement J, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/StatementJ.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementX
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_CMQuasiPeriodConst
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsTorsionFree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Formalism.L2.Th1.B
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq)
open Formalism.L2.Th1.F (MulStable IsKerReps taylor0 pSeries)
open Formalism.L2.Th1.E (Unif ptW inW px py IntCurve OneUnit)
def IsHalfFibre (L : PeriodPair) (α t : ℂ) (Sq : Finset ℂ) : Prop :=
  (∀ Q ∈ Sq, α * Q - t ∈ L.lattice ∧ 2 * Q ∉ L.lattice) ∧
  (∀ Q ∈ Sq, ∀ Q' ∈ Sq, (Q - Q' ∈ L.lattice ∨ Q + Q' ∈ L.lattice) → Q = Q') ∧
  (∀ z, α * z - t ∈ L.lattice → ∃ Q ∈ Sq, z - Q ∈ L.lattice ∨ z + Q ∈ L.lattice)
def HalfFibreExists : Prop :=
  ∀ (L : PeriodPair) (α ω₀ : ℂ), α ≠ 0 → MulStable L α → ω₀ ∈ L.lattice →
    (∀ z, α * z - ω₀ / 2 ∈ L.lattice → 2 * z ∉ L.lattice) →
    ∃ Sq : Finset ℂ, IsHalfFibre L α (ω₀ / 2) Sq
def FibreZInstance : Prop :=
  ∀ (L : PeriodPair) (α ω₀ : ℂ) (S Sq : Finset ℂ), α ≠ 0 → MulStable L α → IsKerReps L α S →
    ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice → IsHalfFibre L α (ω₀ / 2) Sq →
    2 * Sq.card = S.card + 1 ∧
    IsFibreZ (pSeries L) (taylor0 fun z => L.weierstrassP (z + ω₀ / 2))
      (fun Q : Sq => L.weierstrassP (Q : ℂ))
      (fun Q : Sq => taylor0 fun z => L.weierstrassP (z + (Q : ℂ)))
      (fun Q : Sq => taylor0 fun z => L.weierstrassP (z - (Q : ℂ)))
      α (∑ P ∈ S, L.weierstrassP P)
def HalfShiftSeries : Prop :=
  ∀ (L : PeriodPair) (ω₀ : ℂ), ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
    (taylor0 fun z => L.weierstrassP (z + ω₀ / 2)) =
      PowerSeries.C (L.weierstrassP (ω₀ / 2)) +
        PowerSeries.C (3 * L.weierstrassP (ω₀ / 2) ^ 2 - L.g₂ / 4) *
          wOf (L.weierstrassP (ω₀ / 2)) (pSeries L)
def FibreMap : Prop :=
  ∀ (K K' : Type) [Field K] [CharZero K] [Field K'] [CharZero K'] (j : K →+* K')
    (P tr : PowerSeries K) (ι : Type) [Fintype ι] (c : ι → K) (wp wm : ι → PowerSeries K) (al S : K),
    IsFibreZ P tr c wp wm al S →
    IsFibreZ (PowerSeries.map j P) (PowerSeries.map j tr) (fun Q => j (c Q))
      (fun Q => PowerSeries.map j (wp Q)) (fun Q => PowerSeries.map j (wm Q)) (j al) (j S)
def ThetaZeroTwoAnalytic : Prop :=
  ∀ (L : PeriodPair) (ι : ℂ ≃+* ℂ_[2]) (W : WeierstrassCurve ℂ_[2]), Unif 2 L ι W →
    Formalism.L2.Th1.A.IntModel W → ∀ (α ω₀ : ℂ) (b b' : ℤ_[2]), α ≠ 0 → MulStable L α →
    ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
    ι α = ((b : ℚ_[2]) : ℂ_[2]) → ι (conj α) = ((b' : ℚ_[2]) : ℂ_[2]) → ‖b‖ = 1 → ‖b'‖ < 1 →
    (∀ z, α * z - ω₀ / 2 ∈ L.lattice → 2 * z ∉ L.lattice) →
    ‖px W (ptW 2 L ι W (ω₀ / 2))‖ ≤ 1 →
    (∀ z, α * z - ω₀ / 2 ∈ L.lattice → ‖px W (ptW 2 L ι W z)‖ ≤ 1) →
    Simeq (ι := Unit) (evenSigmaLogAtTwoTorsion W (ι (Formalism.L2.Th1.F.s2 L)) (px W (ptW 2 L ι W (ω₀ / 2)))) 0 ∧
      OneUnit (inW 2 ι W (Formalism.L2.Th1.F.th0 L (ω₀ / 2)))
def PointsIntTwo : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (W : WeierstrassCurve ℂ_[l]),
    Unif l L ι W → IntCurve W → ∀ (α α' t0 t' t'' : ℂ),
    (∀ t, Formalism.ELL.InFormalGroupPoints (ptW l L ι W t) → Formalism.ELL.InFormalGroupPoints (ptW l L ι W (α * t))) →
    (∀ t, Formalism.ELL.InFormalGroupPoints (ptW l L ι W t) → Formalism.ELL.InFormalGroupPoints (ptW l L ι W (α' * t))) →
    (∀ t, Formalism.ELL.InFormalGroupPoints (ptW l L ι W t) → α * t ∈ L.lattice → t ∈ L.lattice) →
    t0 = t' + t'' → α' * t' ∈ L.lattice → α' * t'' - t'' ∈ L.lattice → t'' ∉ L.lattice →
    α * t'' ∈ L.lattice →
    ‖px W (ptW l L ι W t0)‖ ≤ 1 ∧ ∀ Q, α * Q - t0 ∈ L.lattice → ‖px W (ptW l L ι W Q)‖ ≤ 1
end Formalism.L2.Th1.B


