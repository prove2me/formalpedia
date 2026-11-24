-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementK
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementK
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T21:57:38.14872+00:00
-- url     : https://prove2.me/theorems/b08c6cd9-9af9-4d00-822e-08f214b5ab5d
-- title:
--   Statement K
-- statement:
--   Definitions and structural lemmas for Statement K, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/StatementK.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementS
import Definitions.Def_Formalism_GaussJetBounds_StatementY
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
open Formalism.L2.Th1.A (logSer expSer wpReg)
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral jetPair jetPairPoly minorProd)
section DefsK
variable {K : Type} [Field K]
def kernelAt [CharZero K] (linv ph : PowerSeries K) {n m : Type} [Fintype n] [Fintype m] (c : n → K)
    (A : n → m → K) (G : MvPowerSeries n K) : MvPowerSeries m K :=
  linSub A (toZ linv (mvExp (-(phSum c ph)) * G))
def betaPair (H : Type) [Fintype H] (N0 N1 : ℕ) (u : H → K) :
    MvPowerSeries ((Bool × H) × Fin N0 × Fin N1) K :=
  ∑ t : H, ∑ ab : Fin N0 × Fin N1, MvPowerSeries.C (u t) *
    MvPowerSeries.X ((false, t), ab.1, ab.2) * MvPowerSeries.X ((true, t), ab.1, ab.2)
def pairMatB {H : Type} [DecidableEq H] {N0 N1 : ℕ} (I : K)
    (i y : (Bool × H) × Fin N0 × Fin N1) : K :=
  if i.1.2 = y.1.2 ∧ i.2 = y.2 then (if i.1.1 = false then 1 else if y.1.1 = false then I else -I)
  else 0
end DefsK
def KernelShape : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l linv ph : PowerSeries K) (d : ℕ),
    IsLogPair l linv → IsOneUnit (unitBall K) (PowerSeries.derivative K l) →
    PowerSeries.constantCoeff ph = 0 → ShapeAt l linv ph d → (d : K) ≠ 0 →
    ∀ (H : Type) [Fintype H] (N0 N1 : ℕ) (n : Type) [Fintype n] (c : n → K)
      (A : n → ((Bool × H) × Fin N0 × Fin N1) → K) (u : H → K) (th : K)
      (Q2 : MvPowerSeries ((Bool × H) × Fin N0 × Fin N1) K),
    ‖(2 : K)‖ = 1 → (∀ i, ‖c i‖ ≤ 1) → (∀ i x, ‖A i x‖ ≤ 1) → ‖th‖ ≤ ‖(d : K)‖ ^ (1 / 2 : ℝ) →
    MvPowerSeries.constantCoeff Q2 = 0 → JetsIntegral Q2 →
    linSub A (sqSum c) = MvPowerSeries.C 2 * betaPair H N0 N1 u + MvPowerSeries.C th * Q2 →
    ∀ G : MvPowerSeries n K, IntMv (unitBall K) G →
    ∃ sg : MvPowerSeries ((Bool × H) × Fin N0 × Fin N1) K, JetsIntegral sg ∧
      kernelAt linv ph c A G = Formalism.DworkPowerSeriesWeights.mvExp ((-(jet l ph 2)) • betaPair H N0 N1 u) * sg
def KernelThmB : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l linv ph : PowerSeries K) (d : ℕ),
    IsLogPair l linv → IsOneUnit (unitBall K) (PowerSeries.derivative K l) →
    PowerSeries.constantCoeff ph = 0 → ShapeAt l linv ph d → 0 < ‖(d : K)‖ → ‖(d : K)‖ < 1 →
    ∀ (H : Type) [Fintype H] [DecidableEq H] (N0 N1 : ℕ) (n : Type) [Fintype n] (c : n → K)
      (A : n → ((Bool × H) × Fin N0 × Fin N1) → K) (u : H → K) (th : K)
      (Q2 : MvPowerSeries ((Bool × H) × Fin N0 × Fin N1) K),
    ‖(2 : K)‖ = 1 → (∀ i, ‖c i‖ ≤ 1) → (∀ i x, ‖A i x‖ ≤ 1) → ‖th‖ ≤ ‖(d : K)‖ ^ (1 / 2 : ℝ) →
    (∀ t, ‖u t‖ ≤ 1) → MvPowerSeries.constantCoeff Q2 = 0 → JetsIntegral Q2 →
    linSub A (sqSum c) = MvPowerSeries.C 2 * betaPair H N0 N1 u + MvPowerSeries.C th * Q2 →
    ∀ G : MvPowerSeries n K, IntMv (unitBall K) G →
    ∀ (x : Bool × H → Matrix (Fin N0) (Fin N0) K), (∀ τ i a, ‖x τ i a‖ ≤ 1) →
      (∀ τ, ‖(x τ).det‖ = 1) →
    ∀ (TT : Finset H) (colN : Bool × H → ℕ) (p : ∀ τ, Fin (colN τ) → ℕ)
      (hp : ∀ τ c, p τ c ≤ N0), (∀ τ c, 1 ≤ p τ c) → ∀ (I : ∀ τ c, Fin (p τ c) → Fin N1),
    ∀ (nu1 nu2 size : Bool × H → ℕ), (∀ τ, nu1 τ = colN τ) →
      (∀ τ, nu2 τ = (Finset.univ.filter (fun c => 2 ≤ p τ c)).card) → (∀ τ, size τ = ∑ c, p τ c) →
      ‖jetPair (∏ τ : Bool × H, minorProd
            (fun (i : Fin N0) (b : Fin N1) => (∑ a, MvPolynomial.C (x τ i a) * MvPolynomial.X (τ, a, b) :
              MvPolynomial ((Bool × H) × Fin N0 × Fin N1) K)) (p τ) (hp τ) (I τ))
          (kernelAt linv ph c A G)‖ ≤
        ‖(d : K)‖ ^ (-(1 / 2 : ℝ) * ∑ t : H, ((size (false, t) : ℝ) -
          (if t ∈ TT then (nu1 (false, t) : ℝ) - nu2 (false, t) else 0) +
          (if t ∈ TT then (nu1 (true, t) : ℝ) else 0)))
def KernelThmBGauss : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l linv ph : PowerSeries ℂ_[p]),
    IsLogPair l linv → IsOneUnit (unitBall ℂ_[p]) (PowerSeries.derivative ℂ_[p] l) →
    PowerSeries.constantCoeff ph = 0 → ShapeAt l linv ph p →
    ∀ (H : Type) [Fintype H] [DecidableEq H] (N0 N1 : ℕ) (n : Type) [Fintype n] (c : n → ℂ_[p])
      (A : n → ((Bool × H) × Fin N0 × Fin N1) → ℂ_[p]) (u : H → ℂ_[p]) (th : ℂ_[p])
      (Q2 : MvPowerSeries ((Bool × H) × Fin N0 × Fin N1) ℂ_[p]),
    ‖(2 : ℂ_[p])‖ = 1 → (∀ i, ‖c i‖ ≤ 1) → (∀ i x, ‖A i x‖ ≤ 1) →
    ‖th‖ ≤ ‖(p : ℂ_[p])‖ ^ (1 / 2 : ℝ) →
    (∀ t, ‖u t‖ ≤ 1) → MvPowerSeries.constantCoeff Q2 = 0 → JetsIntegral Q2 →
    linSub A (sqSum c) = MvPowerSeries.C 2 * betaPair H N0 N1 u + MvPowerSeries.C th * Q2 →
    ∀ G : MvPowerSeries n ℂ_[p], IntMv (unitBall ℂ_[p]) G →
    ∀ (TT : Finset H) (colN : Bool × H → ℕ) (ht : ∀ τ, Fin (colN τ) → ℕ)
      (hht : ∀ τ c, ht τ c ≤ N0), (∀ τ c, 1 ≤ ht τ c) → ∀ (I : ∀ τ c, Fin (ht τ c) → Fin N1),
    ∀ (nu1 nu2 size : Bool × H → ℕ), (∀ τ, nu1 τ = colN τ) →
      (∀ τ, nu2 τ = (Finset.univ.filter (fun c => 2 ≤ ht τ c)).card) →
      (∀ τ, size τ = ∑ c, ht τ c) →
    ∀ nn : ((Bool × H) × Fin N0 × Fin N0) →₀ ℕ,
      ‖MvPolynomial.coeff nn (jetPairPoly (∏ τ : Bool × H, minorProd
            (fun (i : Fin N0) (b : Fin N1) =>
              (∑ a : Fin N0, MvPolynomial.C (MvPolynomial.X (τ, i, a)) * MvPolynomial.X (τ, a, b) :
                MvPolynomial ((Bool × H) × Fin N0 × Fin N1)
                  (MvPolynomial ((Bool × H) × Fin N0 × Fin N0) ℂ_[p])))
            (ht τ) (hht τ) (I τ))
          (kernelAt linv ph c A G))‖ ≤
        ‖(p : ℂ_[p])‖ ^ (-(1 / 2 : ℝ) * ∑ t : H, ((size (false, t) : ℝ) -
          (if t ∈ TT then (nu1 (false, t) : ℝ) - nu2 (false, t) else 0) +
          (if t ∈ TT then (nu1 (true, t) : ℝ) else 0)))
def PairedSquaresB : Prop :=
  ∀ (K : Type) [Field K] (H : Type) [Fintype H] [DecidableEq H] (N0 N1 : ℕ) (I : K), I ^ 2 = -1 →
    linSub (pairMatB (H := H) (N0 := N0) (N1 := N1) I) (sqSum (fun _ => (1 : K))) =
      MvPowerSeries.C 2 * betaPair H N0 N1 (fun _ => 2)
def CurvePairedThmB : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K),
    CoeffIn (unitBall K) W → ‖(2 : K)‖ = 1 →
    ∀ (s2 al albar : K) (d : ℕ) (t : ℤ) (ι : Type) [Fintype ι] (neg : ι → ι) (xP yP : ι → K),
    IsEndoCurve W neg xP yP al → (∀ P, ‖xP P‖ ≤ 1) → (∀ P, ‖yP P‖ ≤ 1) →
    al * albar = (Fintype.card ι : K) + 1 → ‖al‖ = 1 → al + albar = (t : K) →
    (al - albar) ^ 2 = -(d : K) → d ≠ 0 → ‖(al ^ 2 - 1) * (W.b₂ / 12)‖ ≤ 1 →
    al * (al - albar) * s2 = ∑ P, (xP P + W.b₂ / 12) → ‖(d : K)‖ < 1 →
    ∀ (Im : K), Im ^ 2 = -1 →
    ∀ (H : Type) [Fintype H] [DecidableEq H] (N0 N1 : ℕ)
      (G : MvPowerSeries ((Bool × H) × Fin N0 × Fin N1) K), IntMv (unitBall K) G →
    ∀ (x : Bool × H → Matrix (Fin N0) (Fin N0) K), (∀ τ i a, ‖x τ i a‖ ≤ 1) →
      (∀ τ, ‖(x τ).det‖ = 1) →
    ∀ (TT : Finset H) (colN : Bool × H → ℕ) (p : ∀ τ, Fin (colN τ) → ℕ)
      (hp : ∀ τ c, p τ c ≤ N0), (∀ τ c, 1 ≤ p τ c) → ∀ (I : ∀ τ c, Fin (p τ c) → Fin N1),
    ∀ (nu1 nu2 size : Bool × H → ℕ), (∀ τ, nu1 τ = colN τ) →
      (∀ τ, nu2 τ = (Finset.univ.filter (fun c => 2 ≤ p τ c)).card) → (∀ τ, size τ = ∑ c, p τ c) →
      ‖jetPair (∏ τ : Bool × H, minorProd
            (fun (i : Fin N0) (b : Fin N1) => (∑ a, MvPolynomial.C (x τ i a) * MvPolynomial.X (τ, a, b) :
              MvPolynomial ((Bool × H) × Fin N0 × Fin N1) K)) (p τ) (hp τ) (I τ))
          (kernelAt (expSer W) (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) (fun _ => (1 : K))
            (pairMatB Im) G)‖ ≤
        ‖(d : K)‖ ^ (-(1 / 2 : ℝ) * ∑ t : H, ((size (false, t) : ℝ) -
          (if t ∈ TT then (nu1 (false, t) : ℝ) - nu2 (false, t) else 0) +
          (if t ∈ TT then (nu1 (true, t) : ℝ) else 0)))
end Formalism.L2.Th1.G


