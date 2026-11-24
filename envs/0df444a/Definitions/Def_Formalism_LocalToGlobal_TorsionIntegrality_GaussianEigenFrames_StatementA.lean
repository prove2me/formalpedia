-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussianEigenFrames_StatementA
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_GaussianEigenFrames_StatementA
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T22:07:46.150571+00:00
-- url     : https://prove2.me/theorems/83246dc7-07e2-496e-ab3d-f5110277db42
-- title:
--   Statement A
-- statement:
--   Definitions and structural lemmas for Statement A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussianEigenFrames/StatementA.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementV
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementN
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
namespace Formalism.L2.Th1.GD
open Formalism.L2.Th1.C
open Formalism.L2.Th1.G (linSub sqSum toZ phSum tens4 betaPair ShapeAt)
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
def ShapeToZ : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l linv ph : PowerSeries K),
    IsLogPair l linv → PowerSeries.constantCoeff ph = 0 →
    ∀ (n : Type) [Fintype n] (T : MvPowerSeries n K) (γ : Matrix (Fin 4 × n) (Fin 4 × n) K),
    Formalism.L2.Th1.E.ThetaFourthTensorPowerProductShape l linv ph (RingHom.id K)
      (MvPowerSeries.subst (fun i => Formalism.InvariantFactorPaths.G7.at1 i l) T) γ →
    ∃ G : MvPowerSeries (Fin 4 × n) K, IntMv (unitBall K) G ∧
      linSub (fun w w' => γ w w') (tens4 T) =
        toZ linv (mvExp (-(phSum (fun _ => (1 : K)) ph)) * G)
def GramSeries : Prop :=
  ∀ (K : Type) [Field K] (n m : Type) [Fintype n] [Fintype m] (c : n → K) (A : n → m → K),
    linSub A (sqSum c) =
      ∑ x, ∑ y, MvPowerSeries.C (∑ i, c i * A i x * A i y) * MvPowerSeries.X x * MvPowerSeries.X y
def ShapeLin : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l linv ph : PowerSeries K) (d : ℕ),
    IsLogPair l linv → IsOneUnit (unitBall K) (PowerSeries.derivative K l) →
    PowerSeries.constantCoeff ph = 0 → ShapeAt l linv ph d → (d : K) ≠ 0 → ‖(2 : K)‖ = 1 →
    ∀ (n : Type) [Fintype n] (T : MvPowerSeries n K) (γ : Fin 4 × n → Fin 4 × n → K)
      (G : MvPowerSeries (Fin 4 × n) K), IntMv (unitBall K) G →
      linSub γ (tens4 T) = toZ linv (mvExp (-(phSum (fun _ => (1 : K)) ph)) * G) →
    ∀ (H : Type) [Fintype H] [DecidableEq H] (N0 N1 : ℕ)
      (M : n → ((Bool × H) × Fin N0 × Fin N1) → K)
      (Cm : Fin 4 × n → Fin 4 × ((Bool × H) × Fin N0 × Fin N1) → K) (u : H → K) (th : K)
      (q : Fin 4 × ((Bool × H) × Fin N0 × Fin N1) → Fin 4 × ((Bool × H) × Fin N0 × Fin N1) → K),
    (∀ w x, ‖Cm w x‖ ≤ 1) →
    (∀ (a : Fin 4) (i : n) (b : Fin 4) (x : (Bool × H) × Fin N0 × Fin N1),
      ∑ w, γ (a, i) w * Cm w (b, x) = if a = b then M i x else 0) →
    ‖th‖ ≤ ‖(d : K)‖ ^ (1 / 2 : ℝ) → (∀ x y, ‖q x y‖ ≤ 1) →
    (∀ x y, ∑ w, Cm w x * Cm w y =
      (if x.1 = y.1 ∧ x.2.1.2 = y.2.1.2 ∧ x.2.2 = y.2.2 ∧ x.2.1.1 ≠ y.2.1.1 then u x.2.1.2 else 0)
        + th * q x y) →
    ∃ sg : MvPowerSeries ((Bool × H) × Fin N0 × Fin N1) K, JetsIntegral sg ∧
      linSub M T = Formalism.DworkPowerSeriesWeights.mvExp ((-(jet l ph 2)) • betaPair H N0 N1 u) * sg
def JetsLin : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l linv ph : PowerSeries K),
    IsLogPair l linv → IsOneUnit (unitBall K) (PowerSeries.derivative K l) →
    PowerSeries.constantCoeff ph = 0 → (∀ i : ℕ, 1 ≤ i → ‖jet l ph i‖ ≤ 1) → ‖(2 : K)‖ = 1 →
    ∀ (n : Type) [Fintype n] (T : MvPowerSeries n K) (γ : Fin 4 × n → Fin 4 × n → K)
      (G : MvPowerSeries (Fin 4 × n) K), IntMv (unitBall K) G →
      linSub γ (tens4 T) = toZ linv (mvExp (-(phSum (fun _ => (1 : K)) ph)) * G) →
    ∀ (ν : Type) [Fintype ν] (M : n → ν → K) (Cm : Fin 4 × n → Fin 4 × ν → K),
    (∀ w x, ‖Cm w x‖ ≤ 1) →
    (∀ (a : Fin 4) (i : n) (b : Fin 4) (x : ν),
      ∑ w, γ (a, i) w * Cm w (b, x) = if a = b then M i x else 0) →
    JetsIntegral (linSub M T)
def FrameCompose : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (m n J X : Type) [Fintype m] [Fintype n] [Fintype J]
    (γ : Fin 4 × n → m → K) (D : m → Fin 4 × J → K) (V : n → J → K) (W : J → J → K) (th0 : K)
    (q0 : Fin 4 × J → Fin 4 × J → K) (A : J → X → K),
    (∀ w x, ‖D w x‖ ≤ 1) → (∀ x y, ‖q0 x y‖ ≤ 1) → (∀ j x, ‖A j x‖ ≤ 1) →
    (∀ (a : Fin 4) (i : n) (b : Fin 4) (j : J),
      ∑ w, γ (a, i) w * D w (b, j) = if a = b then V i j else 0) →
    (∀ x y, ∑ w, D w x * D w y = (if x.1 = y.1 then W x.2 y.2 else 0) + th0 * q0 x y) →
    ∃ (Cm : m → Fin 4 × X → K) (q1 : Fin 4 × X → Fin 4 × X → K),
      (∀ w x, ‖Cm w x‖ ≤ 1) ∧ (∀ x y, ‖q1 x y‖ ≤ 1) ∧
      (∀ (a : Fin 4) (i : n) (b : Fin 4) (x : X),
        ∑ w, γ (a, i) w * Cm w (b, x) = if a = b then ∑ j, V i j * A j x else 0) ∧
      ∀ x y, ∑ w, Cm w x * Cm w y =
        (if x.1 = y.1 then ∑ j, ∑ k, A j x.2 * W j k * A k y.2 else 0) + th0 * q1 x y
end Formalism.L2.Th1.GD


