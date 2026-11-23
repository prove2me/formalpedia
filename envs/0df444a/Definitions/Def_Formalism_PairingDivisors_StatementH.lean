-- Prove2me | Definitions.Def_Formalism_PairingDivisors_StatementH
-- name    : Formalism_PairingDivisors_StatementH
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:12:15.371432+00:00
-- url     : https://prove2.me/theorems/f2b36862-7f1d-42d9-952d-196b305e7090
-- title:
--   Statement H
-- statement:
--   Definitions and structural lemmas for Statement H, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PairingDivisors/StatementH.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw conjPl)
noncomputable section
namespace Formalism.PairingDivisionLocalBalance
abbrev Pl (K : Type) [Field K] [NumberField K] := HeightOneSpectrum (𝓞 K)
def meanInf (K : Type) [Field K] [NumberField K] (φ : InfinitePlace K → ℝ) : ℝ :=
  (2 / (finrank ℚ K : ℝ)) * ∑ v, φ v
def wt {K : Type} [Field K] [NumberField K] [StarRing K] (S : Finset ℕ) (c : ℕ → ℝ) (w : Pl K) : ℝ :=
  ∑ l ∈ S, c l * (vw w (l : K) : ℝ)
def SumValNat : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (n : ℕ),
    (Function.support fun w : Pl K => lw w * (vw w (n : K) : ℝ)).Finite ∧
    ∑ᶠ w : Pl K, lw w * (vw w (n : K) : ℝ) = Real.log n
def WtSum : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (S : Finset ℕ) (c : ℕ → ℝ),
    (Function.support fun w : Pl K => lw w * wt S c w).Finite ∧
    ∑ᶠ w : Pl K, lw w * wt S c w = ∑ l ∈ S, c l * Real.log l ∧
    ((∀ l ∈ S, 0 ≤ c l) → ∀ w : Pl K, 0 ≤ wt S c w)
def HeightCore : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    (a De : K) (M nff : ℕ) (o vA : Pl K → ℤ) (S : Finset ℕ) (N0 : ℕ → ℝ),
    a ≠ 0 → De ≠ 0 →
    (∀ w, vw w De = -12 * o w) →
    (∀ w, vw w a + M * o w ≤ vA w) →
    (∀ w, vA w ≤ vw w a + M * o w + M * vw w (nff : K)) →
    (∀ l ∈ S, 0 ≤ N0 l) →
    (∀ w, - wt S N0 w ≤ (vA w : ℝ)) →
    (Function.support fun w : Pl K => lw w * |(vA w : ℝ)|).Finite ∧
    ∑ᶠ w : Pl K, lw w * |(vA w : ℝ)| ≤
      (1 / 12) * meanInf K (fun v => Real.log ‖v.embedding (a ^ 12 * (De ^ M)⁻¹)‖)
        + M * Real.log nff + 2 * ∑ l ∈ S, N0 l * Real.log l
def absK {Φ : Type} [Fintype Φ] (κ : Φ → ℕ) : ℕ := ∑ τ, κ τ
def wtM {Φ : Type} [Fintype Φ] (k : ℕ) (κ : Φ → ℕ) : ℕ := k * Fintype.card Φ + 2 * absK κ
def cmConst {Φ : Type} [Fintype Φ] (dF d : ℝ) (k : ℕ) (κ : Φ → ℕ) : ℝ :=
  dF ^ (((k : ℝ) - 1) / 2) * (∏ τ, Real.Gamma ((k : ℝ) + κ τ)) * (2 * Real.pi / Real.sqrt d) ^ absK κ
def CmConstLog : Prop :=
  ∀ (Φ : Type) [Fintype Φ] (dF d : ℝ) (k : ℕ) (κ : Φ → ℕ), 0 < dF → 0 < d → 1 ≤ k →
    0 < cmConst dF d k κ ∧
    Real.log (cmConst dF d k κ) =
      (((k : ℝ) - 1) / 2) * Real.log dF + ∑ τ, Real.log (Real.Gamma ((k : ℝ) + κ τ))
        + (absK κ : ℝ) * Real.log (2 * Real.pi) - ((absK κ : ℝ) / 2) * Real.log d
def LimitArith : Prop :=
  ∀ (Cl : Type) [Fintype Cl] [Nonempty Cl] (d p_power_smul_sub_sum : ℝ) (Y Dc : Cl → ℝ), 0 < d → (∀ c, 0 < Y c) →
    (∑ c, Real.log (Y c)) / (Fintype.card Cl : ℝ) =
      Real.eulerMascheroniConstant - Real.log (2 * Real.sqrt d) - p_power_smul_sub_sum →
    (∀ c, Dc c = (2 * Real.pi) ^ 12 * (2 / Real.sqrt d) ^ 6 * (Y c) ^ 6) →
    (∑ c, Real.log (Dc c)) / (Fintype.card Cl : ℝ) =
      12 * Real.log (2 * Real.pi) - 6 * Real.log d + 6 * Real.eulerMascheroniConstant - 6 * p_power_smul_sub_sum
def BB {Φ : Type} [Fintype Φ] (dF d : ℝ) (k : ℕ) (κ : Φ → ℕ) (p_power_smul_sub_sum LB : ℝ) (nff : ℕ) (SN : ℝ) : ℝ :=
  (((k : ℝ) - 1) / 2) * Real.log dF + ∑ τ, Real.log (Real.Gamma ((k : ℝ) + κ τ))
    + (absK κ : ℝ) * Real.log (2 * Real.pi)
    + (((k : ℝ) * Fintype.card Φ + absK κ) / 2) * Real.log d
    + ((wtM k κ : ℝ) / 2) * |p_power_smul_sub_sum| + LB + (wtM k κ : ℝ) * Real.log nff + 2 * SN
def HeightBoundOfLocalValuations : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    (Φ : Type) [Fintype Φ] (Cl : Type) [Fintype Cl] [Nonempty Cl] [DecidableEq Cl]
    (a De : K) (nff k : ℕ) (κ : Φ → ℕ) (o vA : Pl K → ℤ) (S : Finset ℕ) (N0 : ℕ → ℝ)
    (dF d p_power_smul_sub_sum LB : ℝ) (Lv : InfinitePlace K → ℝ) (cls : InfinitePlace K → Cl) (Dc : Cl → ℝ) (m0 : ℕ),
    a ≠ 0 → De ≠ 0 → 0 < dF → 0 < d → 1 ≤ k →

    (∀ w, vw w De = -12 * o w) →

    (∀ w, vw w a + (wtM k κ : ℤ) * o w ≤ vA w) →
    (∀ w, vA w ≤ vw w a + (wtM k κ : ℤ) * o w + (wtM k κ : ℤ) * vw w (nff : K)) →

    (∀ l ∈ S, 0 ≤ N0 l) →
    (∀ w, - wt S N0 w ≤ (vA w : ℝ)) →

    (∀ v, 0 < Lv v) → (∀ c, 0 < Dc c) →
    (∀ v : InfinitePlace K, ‖v.embedding (a ^ 12 * (De ^ wtM k κ)⁻¹)‖ =
      (cmConst dF d k κ * Lv v) ^ 12 / (Dc (cls v)) ^ wtM k κ) →
    (∀ c, (univ.filter fun v => cls v = c).card = m0) →

    (∑ c, Real.log (Dc c)) / (Fintype.card Cl : ℝ) =
      12 * Real.log (2 * Real.pi) - 6 * Real.log d + 6 * Real.eulerMascheroniConstant - 6 * p_power_smul_sub_sum →

    (∀ v, Real.log (Lv v) ≤ LB) →
    (Function.support fun w : Pl K => lw w * |(vA w : ℝ)|).Finite ∧
    ∑ᶠ w : Pl K, lw w * |(vA w : ℝ)| ≤ BB dF d k κ p_power_smul_sub_sum LB nff (∑ l ∈ S, N0 l * Real.log l)
def PlaceVaryingValuesBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    (T : Finset (Pl K)) (v1 v2 vy : Pl K → ℝ) (ch : Pl K → Bool) (S Se : Finset ℕ) (N0 ep : ℕ → ℝ)
    (B1 B2 : ℝ),
    (Function.support fun w : Pl K => lw w * |v1 w|).Finite →
    (Function.support fun w : Pl K => lw w * |v2 w|).Finite →
    ∑ᶠ w : Pl K, lw w * |v1 w| ≤ B1 → ∑ᶠ w : Pl K, lw w * |v2 w| ≤ B2 →
    (∀ l ∈ S, 0 ≤ N0 l) → (∀ l ∈ Se, 0 ≤ ep l) →
    (∀ w ∈ T, - wt S N0 w ≤ vy w ∧ vy w ≤ (if ch w then v1 w else v2 w) + wt Se ep w) →
    ∑ w ∈ T, lw w * |vy w| ≤
      B1 + B2 + ∑ l ∈ S, N0 l * Real.log l + ∑ l ∈ Se, ep l * Real.log l
def PrimeSum : Prop :=
  ∀ S : Finset ℕ, (∀ l ∈ S, l.Prime) → ∑ l ∈ S, Real.log l / (l : ℝ) ^ 2 ≤ 1
def LogGammaLe : Prop :=
  ∀ n : ℕ, 1 ≤ n → Real.log (Real.Gamma n) ≤ n * Real.log n
def LBval {Φ : Type} [Fintype Φ] (logZ dE Nff : ℝ) (mm : Φ → ℕ) : ℝ :=
  2 * Fintype.card Φ * logZ + (1 / 4) * Real.log (dE * Nff) + (1 / 2) * ∑ τ, Real.log (1 + (mm τ : ℝ))
def BBSize : Prop :=
  ∀ (Φ : Type) [Fintype Φ] (dF dE d Nff logZ p_power_smul_sub_sum SN : ℝ) (k nff : ℕ) (κ mm : Φ → ℕ)
    (x L b Cκ Cn Cf CN : ℝ),
    1 ≤ x → 1 ≤ L → 1 ≤ b → 0 ≤ Cκ → 0 ≤ Cn → 0 ≤ Cf → 0 ≤ CN → 1 ≤ k →
    1 ≤ dF → 1 ≤ dE → 1 ≤ d → 1 ≤ Nff → 1 ≤ nff →

    (k : ℝ) ≤ b → (absK κ : ℝ) ≤ Cκ * Fintype.card Φ * b →

    Real.log dF ≤ Fintype.card Φ * L → Real.log dE ≤ 2 * Fintype.card Φ * L → Real.log d ≤ L →
    |p_power_smul_sub_sum| ≤ L →

    (∀ τ, Real.log ((k : ℝ) + κ τ) ≤ 2 * L) → (∀ τ, Real.log (1 + (mm τ : ℝ)) ≤ 2 * L) →

    Real.log nff ≤ Cn * L → Real.log Nff ≤ Cf * Fintype.card Φ * L → logZ ≤ 1 →

    SN ≤ CN * Fintype.card Φ * b * (L + Real.log x) →
    BB dF d k κ p_power_smul_sub_sum (LBval logZ dE Nff mm) nff SN ≤
      ((Cκ + 1) * (6 + 2 * Cn) + 4 + Cf / 4 + 2 * CN) * Fintype.card Φ * b * (L + Real.log x)
end Formalism.PairingDivisionLocalBalance


