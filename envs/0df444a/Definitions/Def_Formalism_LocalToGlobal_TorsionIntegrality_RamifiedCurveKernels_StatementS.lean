-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementS
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementS
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T21:45:48.438789+00:00
-- url     : https://prove2.me/theorems/8a4275d3-bef6-4c70-b1ee-846543145784
-- title:
--   Statement S
-- statement:
--   Definitions and structural lemmas for Statement S, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/StatementS.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementR
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_GramFormula
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
namespace Formalism.L2.Th1.G
open Formalism.L2.Th1.C
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
section DefsS
variable {K : Type} [Field K]
def toZ {n : Type} (linv : PowerSeries K) (G : MvPowerSeries n K) : MvPowerSeries n K :=
  MvPowerSeries.subst
    (fun i => (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries n K) linv : MvPowerSeries n K)) G
def phSum {n : Type} [Fintype n] (c : n → K) (ph : PowerSeries K) : MvPowerSeries n K :=
  ∑ i, c i • (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries n K) ph : MvPowerSeries n K)
def sqSum {n : Type} [Fintype n] (c : n → K) : MvPowerSeries n K :=
  ∑ i, MvPowerSeries.C (c i) * MvPowerSeries.X i ^ 2
def linSub {n m : Type} [Fintype m] (A : n → m → K) (f : MvPowerSeries n K) : MvPowerSeries m K :=
  MvPowerSeries.subst
    (fun i => (∑ x, MvPowerSeries.C (A i x) * MvPowerSeries.X x : MvPowerSeries m K)) f
def phIso {O : Type} [CommRing O] (τ : O →+* K) (l linv ph : PowerSeries K) {m ν : Type} [Fintype m]
    [Fintype ν] (δ : m → ν → O) : MvPowerSeries ν K :=
  ∑ i, PowerSeries.subst
    (flin l linv (fun a => τ (δ i a)) (fun a => (MvPowerSeries.X a : MvPowerSeries ν K))) ph
def pairMat {ι : Type} [DecidableEq ι] (I : K) (i y : Bool × ι) : K :=
  if i.2 = y.2 then (if i.1 = false then 1 else if y.1 = false then I else -I) else 0
end DefsS
def ShapeOrth : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l linv ph : PowerSeries K) (d : ℕ),
    IsLogPair l linv → IsOneUnit (unitBall K) (PowerSeries.derivative K l) →
    PowerSeries.constantCoeff ph = 0 → ShapeAt l linv ph d →
    ∀ (n : Type) [Fintype n] (c : n → K), (∀ i, ‖c i‖ ≤ 1) →
    ∀ G : MvPowerSeries n K, IntMv (unitBall K) G →
    ∃ J : MvPowerSeries n K, JetsIntegral J ∧
      toZ linv (mvExp (-(phSum c ph)) * G) =
        mvExp (-(MvPowerSeries.C (jet l ph 2 / 2) * sqSum c)) * J
def IntAtD : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l linv ph : PowerSeries K) (d : ℕ),
    Frame (unitBall K) l linv ph → IsOneUnit (unitBall K) (PowerSeries.derivative K l) →
    F1 (unitBall K) l linv ph → ShapeAt l linv ph d →
    ∀ (O : Type) [CommRing O] [StarRing O] (τ : O →+* K),
    (∀ α, EndInt (unitBall K) l linv (τ α)) →
    (∀ z : O, star z = z → IsBinomScalar (unitBall K) (τ z)) →
    (∀ α : O, PhNormAt (unitBall K) l linv ph (τ α) (τ (star α))) →
    (∀ α : O, AdjAt (unitBall K) l linv ph (τ α) (τ (star α))) →
    ∀ (n m : Type) [Fintype n] [DecidableEq n] [Fintype m] (w : n → O), (∀ j, star (w j) = w j) →
    ∀ δ : m → Fin 4 × n → O,
      (∀ a b, ∑ i, star (δ i a) * δ i b = if a = b then w a.2 else 0) →
    ∀ (Th : MvPowerSeries n K) (G : MvPowerSeries (Fin 4 × n) K), IntMv (unitBall K) G →
      tens4 Th = toZ linv (mvExp (-(phIso τ l linv ph δ)) * G) →
    ∃ J : MvPowerSeries n K, JetsIntegral J ∧
      Th = mvExp (-(MvPowerSeries.C (jet l ph 2 / 2) * sqSum (fun j => τ (w j)))) * J
def EigenSplit : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (ι T X : Type) [DecidableEq T] (ty : ι → T) (pr : T → T)
    (BB : ι → ι → K) (th : K) (chi chi' : X → T → K),
    th ≠ 0 → (∀ i j, ‖BB i j‖ ≤ 1) →
    (∀ x i j, ‖(chi x (ty i) - chi' x (ty j)) * BB i j‖ ≤ ‖th‖) →
    (∀ τ ρ, ρ ≠ pr τ → ∃ x, ‖chi x τ - chi' x ρ‖ = 1) →
    ∃ q : ι → ι → K, (∀ i j, ‖q i j‖ ≤ 1) ∧
      ∀ i j, BB i j = (if ty j = pr (ty i) then BB i j else 0) + th * q i j
def ShapeCong : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (n m : Type) [Fintype n] [Fintype m]
    (S0 th : K) (c : n → K) (A : n → m → K) (be Q2 : MvPowerSeries m K),
    ‖(2 : K)‖ = 1 → ‖S0 * th‖ ≤ 1 → (∀ i x, ‖A i x‖ ≤ 1) →
    MvPowerSeries.constantCoeff be = 0 → MvPowerSeries.constantCoeff Q2 = 0 → JetsIntegral Q2 →
    linSub A (sqSum c) = MvPowerSeries.C 2 * be + MvPowerSeries.C th * Q2 →
    ∀ J : MvPowerSeries n K, JetsIntegral J →
    ∃ sg : MvPowerSeries m K, JetsIntegral sg ∧
      linSub A (mvExp (-(MvPowerSeries.C (S0 / 2) * sqSum c)) * J) = mvExp ((-S0) • be) * sg
def PairedSquares : Prop :=
  ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] (I : K), I ^ 2 = -1 →
    linSub (pairMat (ι := ι) I) (sqSum (fun _ => (1 : K))) =
      MvPowerSeries.C 2 * ∑ x : ι, MvPowerSeries.C 2 * MvPowerSeries.X (false, x) * MvPowerSeries.X (true, x)
end Formalism.L2.Th1.G


