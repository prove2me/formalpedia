-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementB
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:03:58.665196+00:00
-- url     : https://prove2.me/theorems/e5793d2f-9abb-40ca-a730-176d173c3eed
-- title:
--   Statement B
-- statement:
--   Definitions and structural lemmas for Statement B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/StatementB.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementA
import Definitions.Def_Formalism_GaussJetBounds_StatementX
import Definitions.Def_Formalism_GaussJetBounds_StatementU
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementGK
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
open Formalism.IncomingBounds
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus BHyp Unram entLog oneLog thetaZ thetaOne frameJet frameJetOne
  nablaO)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 UnrOK IsLawOfLog BetaHyp OmOK)
section Defs
variable {K0 K : Type} [Field K0] [Field K] {ι : Type} {d N0 N1 : ℕ} [NeZero d]
def xOfZ (l : ℕ) (j : K0 →+* K) (σ : K0 →+* K0) (om oms : ι → K0)
    (x : Bool × ι × Fin N0 × Fin N1) : MvPowerSeries (Formalism.DworkPowerSeriesWeights.ZV d N0 N1) K :=
  PowerSeries.subst
    (if x.1 = false then
      ∑ s : ZMod d, if s.val % 2 = 0 then
        MvPowerSeries.C (j (σ^[s.val] (oms x.2.1))) *
          (MvPowerSeries.X (s, x.2.2.1, x.2.2.2) : MvPowerSeries (Formalism.DworkPowerSeriesWeights.ZV d N0 N1) K) else 0
    else
      ∑ s : ZMod d, if s.val % 2 = 0 then 0 else
        MvPowerSeries.C (j (σ^[s.val] (om x.2.1))) *
          (MvPowerSeries.X (s, x.2.2.1, x.2.2.2) : MvPowerSeries (Formalism.DworkPowerSeriesWeights.ZV d N0 N1) K))
    (expF K l)
def thetaInZ (l : ℕ) (j : K0 →+* K) (σ : K0 →+* K0) (om oms : ι → K0)
    (Tht : MvPowerSeries (Bool × ι × Fin N0 × Fin N1) K) :
    MvPowerSeries (Formalism.DworkPowerSeriesWeights.ZV d N0 N1) K :=
  MvPowerSeries.subst (xOfZ l j σ om oms) Tht
def sumE [Fintype ι] (be : MvPowerSeries (Fin 2) K) :
    MvPowerSeries (Bool × ι × Fin N0 × Fin N1) K :=
  ∑ e : ι × Fin N0 × Fin N1, MvPowerSeries.subst
    (fun a : Fin 2 => (MvPowerSeries.X (if a = 0 then (false, e) else (true, e)) :
      MvPowerSeries (Bool × ι × Fin N0 × Fin N1) K)) be
def conjJ {ν : ℕ} (j : K0 →+* K) (σ : K0 →+* K0) (c : Fin ν → K0) : Fin ν → ZMod (2 * ν) → K :=
  fun r s => j (σ^[s.val] (c r))
end Defs
def B0 : Prop :=
  ∀ (K0 K : Type) [NormedField K0] [IsUltrametricDist K0] [CharZero K0] [NormedField K]
    [IsUltrametricDist K] [CharZero K] (l d N0 N1 : ℕ) [NeZero d] (σ : K0 →+* K0) (j : K0 →+* K),
    UnrOK K0 l σ → (∀ a, ‖j a‖ = ‖a‖) → 2 ≤ d → Even d →
    ∀ F : MvPowerSeries (Fin 2) K0, IsLawOfLog l F → ∀ be0 : MvPowerSeries (Fin 2) K0, F1 F be0 →
    F2 l σ be0 →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (om oms : ι → K0), OwOK d σ om oms →
      TrDual d σ om oms → ∀ ζ : K0, IsPrimitiveRoot ζ (l ^ d - 1) →
    ∀ U0 Φ : MvPowerSeries (Bool × ι × Fin N0 × Fin N1) K, Integral U0 →
      MvPowerSeries.constantCoeff Φ = 0 → Simeq Φ (sumE (MvPowerSeries.map j be0)) →
      ∃ U : MvPowerSeries (Formalism.DworkPowerSeriesWeights.ZV d N0 N1) K, Integral U ∧
        ∀ g : Formalism.DworkPowerSeriesWeights.ZV d N0 N1 → MvPowerSeries (Formalism.DworkPowerSeriesWeights.ZV d N0 N1) K,
          (∀ y, MvPowerSeries.constantCoeff (g y) = 0) →
          (∀ y, MvPowerSeries.subst g (entLog (K := K) l y) = MvPowerSeries.X y) →
          thetaInZ l j σ om oms (mvExp (-Φ) * U0) =
            thetaZ g U (-1) (MvPowerSeries.map j (beMean l σ be0 om oms ζ))
def OneLetterHalf : Prop :=
  ∀ (K0 : Type) [NormedField K0] [IsUltrametricDist K0] [CharZero K0] (l : ℕ) (σ : K0 →+* K0),
    UnrOK K0 l σ →
    ∀ F : MvPowerSeries (Fin 2) K0, IsLawOfLog l F → ∀ be0 : MvPowerSeries (Fin 2) K0, F1 F be0 →
    F2 l σ be0 → ∀ ζ : K0, IsPrimitiveRoot ζ (l ^ 2 - 1) →
    ∀ ph : PowerSeries K0,
      Simeq (MvPowerSeries.C (2 : K0) * ph)
        (MvPowerSeries.subst (fun _ : Fin 2 => (PowerSeries.X : PowerSeries K0)) be0) →
      Simeq (ph : MvPowerSeries Unit K0) (MvPowerSeries.C ((2 : K0)⁻¹) *
        MvPowerSeries.subst (fun _ : ZMod 2 => lgF K0 l)
          (beMean (d := 2) l σ be0 (fun _ : Unit => (1 : K0)) (fun _ => 1) ζ))
def SingleLetterThetaFactorization : Prop :=
  ∀ (K0 K : Type) [NormedField K0] [IsUltrametricDist K0] [CharZero K0] [NormedField K]
    [IsUltrametricDist K] [CharZero K] (l N0 N1 : ℕ) (σ : K0 →+* K0) (j : K0 →+* K),
    UnrOK K0 l σ → (∀ a, ‖j a‖ = ‖a‖) →
    ∀ F : MvPowerSeries (Fin 2) K0, IsLawOfLog l F → ∀ be0 : MvPowerSeries (Fin 2) K0, F1 F be0 →
    F2 l σ be0 → ∀ ζ : K0, IsPrimitiveRoot ζ (l ^ 2 - 1) →
    ∀ ph : PowerSeries K0,
      Simeq (MvPowerSeries.C (2 : K0) * ph)
        (MvPowerSeries.subst (fun _ : Fin 2 => (PowerSeries.X : PowerSeries K0)) be0) →
    ∀ U0 Φ : MvPowerSeries (Fin N0 × Fin N1) K, Integral U0 →
      MvPowerSeries.constantCoeff Φ = 0 →
      Simeq Φ (∑ x : Fin N0 × Fin N1, at1 x (PowerSeries.map j ph)) →
      ∃ U : MvPowerSeries (Fin N0 × Fin N1) K, Integral U ∧
        ∀ g : Fin N0 × Fin N1 → MvPowerSeries (Fin N0 × Fin N1) K,
          (∀ y, MvPowerSeries.constantCoeff (g y) = 0) →
          (∀ y, MvPowerSeries.subst g (oneLog (K := K) l y) = MvPowerSeries.X y) →
          MvPowerSeries.subst (fun x => at1 x (expF K l)) (mvExp (-Φ) * U0) =
            thetaOne g U (-1) 1 (MvPowerSeries.map j
              (beMean (d := 2) l σ be0 (fun _ : Unit => (1 : K0)) (fun _ => 1) ζ))
def OmOKOf : Prop :=
  ∀ (K0 K : Type) [NormedField K0] [IsUltrametricDist K0] [CharZero K0] [NormedField K]
    (l ν : ℕ) [NeZero ν] (σ : K0 →+* K0) (j : K0 →+* K), UnrOK K0 l σ → (∀ a, ‖j a‖ = ‖a‖) →
    ∀ om oms : Fin ν → K0, OwOK (2 * ν) σ om oms → TrDual (2 * ν) σ om oms →
      OmOK l ν (conjJ j σ om) (conjJ j σ oms)
def ThetaInZIsSSub : Prop :=
  ∀ (K0 K : Type) [Field K0] [Field K] (l ν r0 r1 : ℕ) [NeZero ν] (σ : K0 →+* K0) (j : K0 →+* K)
    (om oms : Fin ν → K0) (Tht : MvPowerSeries (Bool × Fin ν × Fin r0 × Fin r1) K),
    thetaInZ (d := 2 * ν) l j σ om oms Tht =
      MvPowerSeries.subst (Formalism.InvariantFactorPaths.G7.sSub (conjJ j σ om) (conjJ j σ oms) (expF K l)) Tht
def ThmAEntryOfF : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K0 : Type) [NormedField K0] [IsUltrametricDist K0] [CharZero K0]
    (σ : K0 →+* K0), UnrOK K0 l σ → ∀ (j : K0 →+* ℂ_[l]), (∀ a, ‖j a‖ = ‖a‖) →
    ∀ F : MvPowerSeries (Fin 2) K0, IsLawOfLog l F → ∀ be0 : MvPowerSeries (Fin 2) K0, F1 F be0 →
    F2 l σ be0 →
    ∀ (d N0 N1 : ℕ) [NeZero d], 2 ≤ d → Even d →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (om oms : ι → K0), OwOK d σ om oms →
      TrDual d σ om oms → (∃ ζ : K0, IsPrimitiveRoot ζ (l ^ d - 1)) →
    ∀ U0 Φ : MvPowerSeries (Bool × ι × Fin N0 × Fin N1) ℂ_[l], Integral U0 →
      MvPowerSeries.constantCoeff Φ = 0 → Simeq Φ (sumE (MvPowerSeries.map j be0)) →
    ∀ (TT : Finset (ZMod d)) (colN : ZMod d → ℕ) (p : ∀ s, Fin (colN s) → ℕ)
      (hp : ∀ s c, p s c ≤ N0), (∀ s c, 1 ≤ p s c) → ∀ (I : ∀ s c, Fin (p s c) → Fin N1),
    ∀ (nu1 nu2 size : ZMod d → ℕ), (∀ s, nu1 s = colN s) →
      (∀ s, nu2 s = (Finset.univ.filter (fun c => 2 ≤ p s c)).card) → (∀ s, size s = ∑ c, p s c) →
    ∀ a : ℕ, 1 ≤ a → (∀ s, size s ≤ a) → 2 * Real.logb l a + 2 ≤ (N0 : ℝ) - 1 →
    ∀ δ : MvPolynomial (ZMod d × Fin N0 × Fin N0) ℂ_[l] →ₗ[ℂ_[l]] ℂ_[l],
      (∀ P ∈ nablaO (K := ℂ_[l]) colN p hp, ‖δ P‖ ≤ 1) →
      ‖δ (frameJet colN p hp I (thetaInZ l j σ om oms (mvExp (-Φ) * U0)))‖ ≤
        ‖(l : ℂ_[l])‖ ^ ((∑ s ∈ TT, (topTerm l d TT nu1 nu2 s -
            gam l * (Wcap l d TT nu1 nu2 size s : ℝ))) +
          Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) -
          ((d : ℝ) * N0 * N1) * (Real.logb l (a : ℝ) + 1))
def ThmAGaussOfF : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K0 : Type) [NormedField K0] [IsUltrametricDist K0] [CharZero K0]
    (σ : K0 →+* K0), UnrOK K0 l σ → ∀ (j : K0 →+* ℂ_[l]), (∀ a, ‖j a‖ = ‖a‖) →
    ∀ F : MvPowerSeries (Fin 2) K0, IsLawOfLog l F → ∀ be0 : MvPowerSeries (Fin 2) K0, F1 F be0 →
    F2 l σ be0 →
    ∀ (d N0 N1 : ℕ) [NeZero d], 2 ≤ d → Even d →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (om oms : ι → K0), OwOK d σ om oms →
      TrDual d σ om oms → (∃ ζ : K0, IsPrimitiveRoot ζ (l ^ d - 1)) →
    ∀ U0 Φ : MvPowerSeries (Bool × ι × Fin N0 × Fin N1) ℂ_[l], Integral U0 →
      MvPowerSeries.constantCoeff Φ = 0 → Simeq Φ (sumE (MvPowerSeries.map j be0)) →
    ∀ (TT : Finset (ZMod d)) (colN : ZMod d → ℕ) (p : ∀ s, Fin (colN s) → ℕ)
      (hp : ∀ s c, p s c ≤ N0), (∀ s c, 1 ≤ p s c) → ∀ (I : ∀ s c, Fin (p s c) → Fin N1),
    ∀ (nu1 nu2 size : ZMod d → ℕ), (∀ s, nu1 s = colN s) →
      (∀ s, nu2 s = (Finset.univ.filter (fun c => 2 ≤ p s c)).card) → (∀ s, size s = ∑ c, p s c) →
    ∀ a : ℕ, 1 ≤ a → (∀ s, size s ≤ a) → 2 * Real.logb l a + 2 ≤ (N0 : ℝ) - 1 →
    ∀ n : (ZMod d × Fin N0 × Fin N0) →₀ ℕ,
      ‖MvPolynomial.coeff n (frameJet colN p hp I (thetaInZ l j σ om oms (mvExp (-Φ) * U0)))‖ ≤
        ‖(l : ℂ_[l])‖ ^ ((∑ s ∈ TT, (topTerm l d TT nu1 nu2 s -
            gam l * (Wcap l d TT nu1 nu2 size s : ℝ))) +
          Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) -
          ((d : ℝ) * N0 * N1) * (Real.logb l (a : ℝ) + 1))
def OneLetterGaussOfF : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K0 : Type) [NormedField K0] [IsUltrametricDist K0] [CharZero K0]
    (σ : K0 →+* K0), UnrOK K0 l σ → ∀ (j : K0 →+* ℂ_[l]), (∀ a, ‖j a‖ = ‖a‖) →
    ∀ F : MvPowerSeries (Fin 2) K0, IsLawOfLog l F → ∀ be0 : MvPowerSeries (Fin 2) K0, F1 F be0 →
    F2 l σ be0 →
    (∃ ζ : K0, IsPrimitiveRoot ζ (l ^ 2 - 1)) →
    ∀ ph : PowerSeries K0,
      Simeq (MvPowerSeries.C (2 : K0) * ph)
        (MvPowerSeries.subst (fun _ : Fin 2 => (PowerSeries.X : PowerSeries K0)) be0) →
    ∀ (N0 N1 C : ℕ) (U0 Φ : MvPowerSeries (Fin N0 × Fin N1) ℂ_[l]), Integral U0 →
      MvPowerSeries.constantCoeff Φ = 0 →
      Simeq Φ (∑ x : Fin N0 × Fin N1, at1 x (PowerSeries.map j ph)) →
    ∀ (p : Fin C → ℕ) (hp : ∀ c, p c ≤ N0) (I : ∀ c, Fin (p c) → Fin N1) (a : ℕ), 1 ≤ a →
      (∑ c, p c) ≤ a → ∀ n : (Fin N0 × Fin N0) →₀ ℕ,
      ‖MvPolynomial.coeff n (frameJetOne p hp I
          (MvPowerSeries.subst (fun x => at1 x (expF ℂ_[l] l)) (mvExp (-Φ) * U0)))‖ ≤
        ‖(l : ℂ_[l])‖ ^ (rho l * ((∑ c, p c : ℕ) : ℝ) -
          ((N0 : ℝ) * N1) * (Real.logb l (a : ℝ) + 1))
end Formalism.L2.Th1.D


