-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_IntDThmB
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_IntDThmB
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T22:08:56.866652+00:00
-- url     : https://prove2.me/theorems/9a88f04d-021e-4252-a999-e7e5a5cf4aaa
-- title:
--   Int DThm B
-- statement:
--   Definitions and structural lemmas for Int DThm B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/IntDThmB.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementK
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
open Formalism.DworkPowerSeriesWeights (JetsIntegral jetPair minorProd)
def IntDThmB : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l linv ph : PowerSeries K) (d : ℕ),
    Frame (unitBall K) l linv ph → IsOneUnit (unitBall K) (PowerSeries.derivative K l) →
    F1 (unitBall K) l linv ph → ShapeAt l linv ph d → 0 < ‖(d : K)‖ → ‖(d : K)‖ < 1 →
    ‖(2 : K)‖ = 1 →
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
    ∀ (H : Type) [Fintype H] [DecidableEq H] (N0 N1 : ℕ)
      (A : n → ((Bool × H) × Fin N0 × Fin N1) → K) (u : H → K) (th : K)
      (Q2 : MvPowerSeries ((Bool × H) × Fin N0 × Fin N1) K),
    (∀ i x, ‖A i x‖ ≤ 1) → ‖th‖ ≤ ‖(d : K)‖ ^ (1 / 2 : ℝ) →
    (∀ t, ‖u t‖ ≤ 1) → MvPowerSeries.constantCoeff Q2 = 0 → JetsIntegral Q2 →
    linSub A (sqSum (fun j => τ (w j))) =
      MvPowerSeries.C 2 * betaPair H N0 N1 u + MvPowerSeries.C th * Q2 →
    ∀ (x : Bool × H → Matrix (Fin N0) (Fin N0) K), (∀ τ i a, ‖x τ i a‖ ≤ 1) →
      (∀ τ, ‖(x τ).det‖ = 1) →
    ∀ (TT : Finset H) (colN : Bool × H → ℕ) (p : ∀ τ, Fin (colN τ) → ℕ)
      (hp : ∀ τ c, p τ c ≤ N0), (∀ τ c, 1 ≤ p τ c) → ∀ (I : ∀ τ c, Fin (p τ c) → Fin N1),
    ∀ (nu1 nu2 size : Bool × H → ℕ), (∀ τ, nu1 τ = colN τ) →
      (∀ τ, nu2 τ = (Finset.univ.filter (fun c => 2 ≤ p τ c)).card) → (∀ τ, size τ = ∑ c, p τ c) →
      ‖jetPair (∏ τ : Bool × H, minorProd
            (fun (i : Fin N0) (b : Fin N1) => (∑ a, MvPolynomial.C (x τ i a) * MvPolynomial.X (τ, a, b) :
              MvPolynomial ((Bool × H) × Fin N0 × Fin N1) K)) (p τ) (hp τ) (I τ))
          (linSub A Th)‖ ≤
        ‖(d : K)‖ ^ (-(1 / 2 : ℝ) * ∑ t : H, ((size (false, t) : ℝ) -
          (if t ∈ TT then (nu1 (false, t) : ℝ) - nu2 (false, t) else 0) +
          (if t ∈ TT then (nu1 (true, t) : ℝ) else 0)))
end Formalism.L2.Th1.G


