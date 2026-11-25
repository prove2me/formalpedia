-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_AlgebraicTheory_StatementA
-- name    : Formalism_LocalToGlobal_AlgebraicTheory_StatementA
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T08:53:24.02487+00:00
-- url     : https://prove2.me/theorems/96a6e5fa-4032-454f-8e87-4999dc710b12
-- title:
--   Statement A
-- statement:
--   Definitions and structural lemmas for Statement A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/AlgebraicTheory/StatementA.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussianEigenFrames_StatementH
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
namespace Formalism.L2.AlgTh
open Formalism.L2.Th1.G (linSub)
open Formalism.DworkPowerSeriesWeights (JetsIntegral mfact)
def scl {K : Type} [Field K] (n : Type) [DecidableEq n] (c : K) : n → n → K := fun i j => if i = j then c else 0
def LogDerJets : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (F a : PowerSeries K) (ρ : ℝ), 1 ≤ ρ →
    PowerSeries.derivative K F = a * F → ‖PowerSeries.constantCoeff F‖ ≤ 1 →
    (∀ i : ℕ, ‖((i.factorial : ℕ) : K) * PowerSeries.coeff i a‖ ≤ ρ) →
    ∀ i : ℕ, ‖((i.factorial : ℕ) : K) * PowerSeries.coeff i F‖ ≤ ρ ^ i
def PowLogDer : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (G V : PowerSeries K) (c : K) (M : ℕ), 0 < M → c ≠ 0 →
    G ^ M = PowerSeries.C (c ^ M) * V →
    PowerSeries.C (M : K) * (PowerSeries.derivative K G * V) = G * PowerSeries.derivative K V
def ScaleJets : Prop :=
  ∀ (K : Type) [NormedField K] (n : Type) [Fintype n] [DecidableEq n] (c : K) (f : MvPowerSeries n K),
    JetsIntegral (linSub (scl n c) f) ↔
      ∀ κ : n →₀ ℕ, ‖((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ f‖ * ‖c‖ ^ κ.degree ≤ 1
def ProdScaleJets : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (κ n : Type) [Fintype κ] [Fintype n] [DecidableEq n] (c : K)
    (r : κ → K) (H : κ → n → PowerSeries K), (∀ k, ‖r k‖ ≤ 1) →
    (∀ k i (j : ℕ), ‖((j.factorial : ℕ) : K) * PowerSeries.coeff j (H k i)‖ * ‖c‖ ^ j ≤ 1) →
    JetsIntegral (linSub (scl n c) (Formalism.L2.Th1.E.thetaProd r H))
def LinScale : Prop :=
  ∀ (K : Type) [Field K] (n m : Type) [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] (c : K) (A : n → m → K)
    (f : MvPowerSeries n K),
    linSub (scl m c) (linSub A f) = linSub (fun i x => c * A i x) f ∧
    linSub A (linSub (scl n c) f) = linSub (fun i x => c * A i x) f
end Formalism.L2.AlgTh


