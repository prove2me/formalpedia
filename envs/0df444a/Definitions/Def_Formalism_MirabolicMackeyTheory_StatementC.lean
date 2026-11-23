-- Prove2me | Definitions.Def_Formalism_MirabolicMackeyTheory_StatementC
-- name    : Formalism_MirabolicMackeyTheory_StatementC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:50:30.159612+00:00
-- url     : https://prove2.me/theorems/d4f05e0e-b6ed-472c-9f23-38a4968fc87e
-- title:
--   Statement C
-- statement:
--   Definitions and structural lemmas for Statement C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/StatementC.lean

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
namespace Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
def PrimeSumsC (c Y X2 T Cth Cadd : ℝ) (th add : ℕ → ℝ) : Prop :=
  (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ (p : ℝ) ≤ Y) →
      ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ≤ Real.log Y) ∧
    (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ (p : ℝ) ≤ Y) → ∑ p ∈ Q, Real.log (p : ℝ) ≤ c * Y) ∧
    (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ X2 < (p : ℝ)) →
      ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ 2 * c / X2) ∧
    (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) → ∑ p ∈ Q, th p * Real.log (p : ℝ) ≤ Cth) ∧
    (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) → T * ∑ p ∈ Q, add p * Real.log (p : ℝ) ≤ Cadd)
def ErrSumGoodC : Prop :=
  ∀ (c : ℝ) (PI : Finset ℕ), (∀ p ∈ PI, p.Prime) →
  ∀ (Y X2 A1 A2 kw T Cth Cadd : ℝ) (th add : ℕ → ℝ), 1 < Y → 0 < X2 → 0 ≤ A1 → 0 ≤ A2 → 0 ≤ kw →
    0 ≤ T → (∀ p, 0 ≤ th p) → (∀ p, 0 ≤ add p) → PrimeSumsC c Y X2 T Cth Cadd th add →
      ∑ p ∈ PI, Real.log (p : ℝ) * errGood Y X2 A1 A2 kw T th add p ≤
        2 * (A1 * Real.log Y + kw * Cth + Cadd + 2 * c * A2 / X2 + c * Y)
def OnSumC : Prop :=
  ∀ (c : ℝ) (K : Type) [Field K] [NumberField K] [StarRing K] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (Bad : Finset ℕ) (eb : ℕ → ℝ), (∀ p, 0 ≤ eb p) →
  ∀ (Y X2 A1 A2 kw T Cth Cadd : ℝ) (th add : ℕ → ℝ), 1 < Y → 0 < X2 → 0 ≤ A1 → 0 ≤ A2 → 0 ≤ kw →
    0 ≤ T → (∀ p, 0 ≤ th p) → (∀ p, 0 ≤ add p) → PrimeSumsC c Y X2 T Cth Cadd th add →
  ∀ (errl : HeightOneSpectrum (𝓞 K) → ℝ),
    (∀ w ∈ S, errl w ≤ if plc w ∈ Bad then eb (plc w) else errGood Y X2 A1 A2 kw T th add (plc w)) →
      ∑ w ∈ S, lw w * ((ramw w : ℝ) * errl w) ≤
        2 * (A1 * Real.log Y + kw * Cth + Cadd + 2 * c * A2 / X2 + c * Y) +
          ∑ p ∈ Bad, Real.log (p : ℝ) * eb p
def AbsorbOnC : Prop :=
  ∀ (c C Cb L xe f m b k ws Se Y X2 bad : ℝ), 0 ≤ c → 1 ≤ C → 0 ≤ Cb → 1 ≤ L → L ≤ xe → 1 ≤ f → 1 ≤ m →
    0 < b → 1 ≤ k → Real.log k ≤ L → 0 ≤ ws → ws ≤ 2 * f * b → 0 ≤ Se → k * Se * L ≤ m * b → 1 < Y →
    Real.log Y ≤ 2 * L → Y ≤ m * b → k ≤ X2 → bad ≤ Cb * (f * m * b * L) →
      2 * (C * (Real.log k * m * ws + f * k * Se) * Real.log Y + C * k * ws * (C / k) + C * (m * b) +
          2 * c * (C * k * ws) / X2 + c * Y) + bad + 12 * (f * m * b) ≤
        (4 * C ^ 2 + (14 + 10 * c) * C + Cb + 12) * xe * (f * m * b * L)
def ThetaLog4 : Prop :=
  ∀ (Y : ℝ), 0 ≤ Y → ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ (p : ℝ) ≤ Y) →
    ∑ p ∈ Q, Real.log (p : ℝ) ≤ Real.log 4 * Y
def PrimeSumsLog4 (Y X2 T Cth Cadd : ℝ) (th add : ℕ → ℝ) : Prop :=
  (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ (p : ℝ) ≤ Y) →
      ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ≤ Real.log Y) ∧
    (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ X2 < (p : ℝ)) →
      ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ 2 * Real.log 4 / X2) ∧
    (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) → ∑ p ∈ Q, th p * Real.log (p : ℝ) ≤ Cth) ∧
    (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) → T * ∑ p ∈ Q, add p * Real.log (p : ℝ) ≤ Cadd)
def ErrSumGoodLog4 : Prop :=
  ∀ (PI : Finset ℕ), (∀ p ∈ PI, p.Prime) →
  ∀ (Y X2 A1 A2 kw T Cth Cadd : ℝ) (th add : ℕ → ℝ), 1 < Y → 0 < X2 → 0 ≤ A1 → 0 ≤ A2 → 0 ≤ kw →
    0 ≤ T → (∀ p, 0 ≤ th p) → (∀ p, 0 ≤ add p) → PrimeSumsLog4 Y X2 T Cth Cadd th add →
      ∑ p ∈ PI, Real.log (p : ℝ) * errGood Y X2 A1 A2 kw T th add p ≤
        2 * (A1 * Real.log Y + kw * Cth + Cadd + 2 * Real.log 4 * A2 / X2 + Real.log 4 * Y)
def OnSumLog4 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (Bad : Finset ℕ) (eb : ℕ → ℝ), (∀ p, 0 ≤ eb p) →
  ∀ (Y X2 A1 A2 kw T Cth Cadd : ℝ) (th add : ℕ → ℝ), 1 < Y → 0 < X2 → 0 ≤ A1 → 0 ≤ A2 → 0 ≤ kw →
    0 ≤ T → (∀ p, 0 ≤ th p) → (∀ p, 0 ≤ add p) → PrimeSumsLog4 Y X2 T Cth Cadd th add →
  ∀ (errl : HeightOneSpectrum (𝓞 K) → ℝ),
    (∀ w ∈ S, errl w ≤ if plc w ∈ Bad then eb (plc w) else errGood Y X2 A1 A2 kw T th add (plc w)) →
      ∑ w ∈ S, lw w * ((ramw w : ℝ) * errl w) ≤
        2 * (A1 * Real.log Y + kw * Cth + Cadd + 2 * Real.log 4 * A2 / X2 + Real.log 4 * Y) +
          ∑ p ∈ Bad, Real.log (p : ℝ) * eb p
def AbsorbOnLog4 : Prop :=
  ∀ (C Cb L xe f m b k ws Se Y X2 bad : ℝ), 1 ≤ C → 0 ≤ Cb → 1 ≤ L → L ≤ xe → 1 ≤ f → 1 ≤ m → 0 < b →
    1 ≤ k → Real.log k ≤ L → 0 ≤ ws → ws ≤ 2 * f * b → 0 ≤ Se → k * Se * L ≤ m * b → 1 < Y →
    Real.log Y ≤ 2 * L → Y ≤ m * b → k ≤ X2 → bad ≤ Cb * (f * m * b * L) →
      2 * (C * (Real.log k * m * ws + f * k * Se) * Real.log Y + C * k * ws * (C / k) + C * (m * b) +
          2 * Real.log 4 * (C * k * ws) / X2 + Real.log 4 * Y) + bad + 12 * (f * m * b) ≤
        (4 * C ^ 2 + 28 * C + Cb + 12) * xe * (f * m * b * L)
def TailC : Prop :=
  ∀ (c : ℝ), (∀ (Y : ℝ), 0 ≤ Y → ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ (p : ℝ) ≤ Y) →
      ∑ p ∈ Q, Real.log (p : ℝ) ≤ c * Y) →
    ∀ (X2 : ℝ), 0 < X2 → ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ X2 < (p : ℝ)) →
      ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ 2 * c / X2
def TailLog4 : Prop :=
  ∀ (X2 : ℝ), 0 < X2 → ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ X2 < (p : ℝ)) →
    ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ 2 * Real.log 4 / X2
def PrimeSumsG (c0 c Y X2 T Cth Cadd : ℝ) (th add : ℕ → ℝ) : Prop :=
  (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ (p : ℝ) ≤ Y) →
      ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ≤ Real.log Y + c0) ∧
    (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ (p : ℝ) ≤ Y) → ∑ p ∈ Q, Real.log (p : ℝ) ≤ c * Y) ∧
    (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ X2 < (p : ℝ)) →
      ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ 2 * c / X2) ∧
    (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) → ∑ p ∈ Q, th p * Real.log (p : ℝ) ≤ Cth) ∧
    (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) → T * ∑ p ∈ Q, add p * Real.log (p : ℝ) ≤ Cadd)
def ErrSumGoodG : Prop :=
  ∀ (c0 c : ℝ) (PI : Finset ℕ), (∀ p ∈ PI, p.Prime) →
  ∀ (Y X2 A1 A2 kw T Cth Cadd : ℝ) (th add : ℕ → ℝ), 1 < Y → 0 < X2 → 0 ≤ A1 → 0 ≤ A2 → 0 ≤ kw →
    0 ≤ T → (∀ p, 0 ≤ th p) → (∀ p, 0 ≤ add p) → PrimeSumsG c0 c Y X2 T Cth Cadd th add →
      ∑ p ∈ PI, Real.log (p : ℝ) * errGood Y X2 A1 A2 kw T th add p ≤
        2 * (A1 * (Real.log Y + c0) + kw * Cth + Cadd + 2 * c * A2 / X2 + c * Y)
def OnSumG : Prop :=
  ∀ (c0 c : ℝ) (K : Type) [Field K] [NumberField K] [StarRing K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (Bad : Finset ℕ) (eb : ℕ → ℝ), (∀ p, 0 ≤ eb p) →
  ∀ (Y X2 A1 A2 kw T Cth Cadd : ℝ) (th add : ℕ → ℝ), 1 < Y → 0 < X2 → 0 ≤ A1 → 0 ≤ A2 → 0 ≤ kw →
    0 ≤ T → (∀ p, 0 ≤ th p) → (∀ p, 0 ≤ add p) → PrimeSumsG c0 c Y X2 T Cth Cadd th add →
  ∀ (errl : HeightOneSpectrum (𝓞 K) → ℝ),
    (∀ w ∈ S, errl w ≤ if plc w ∈ Bad then eb (plc w) else errGood Y X2 A1 A2 kw T th add (plc w)) →
      ∑ w ∈ S, lw w * ((ramw w : ℝ) * errl w) ≤
        2 * (A1 * (Real.log Y + c0) + kw * Cth + Cadd + 2 * c * A2 / X2 + c * Y) +
          ∑ p ∈ Bad, Real.log (p : ℝ) * eb p
def AbsorbOnG : Prop :=
  ∀ (c0 c C Cb L xe f m b k ws Se Y X2 bad : ℝ), 0 ≤ c0 → 0 ≤ c → 1 ≤ C → 0 ≤ Cb → 1 ≤ L → L ≤ xe →
    1 ≤ f → 1 ≤ m → 0 < b → 1 ≤ k → Real.log k ≤ L → 0 ≤ ws → ws ≤ 2 * f * b → 0 ≤ Se →
    k * Se * L ≤ m * b → 1 < Y → Real.log Y ≤ 2 * L → Y ≤ m * b → k ≤ X2 → bad ≤ Cb * (f * m * b * L) →
      2 * (C * (Real.log k * m * ws + f * k * Se) * (Real.log Y + c0) + C * k * ws * (C / k) +
          C * (m * b) + 2 * c * (C * k * ws) / X2 + c * Y) + bad + 12 * (f * m * b) ≤
        (4 * C ^ 2 + (14 + 6 * c0 + 10 * c) * C + Cb + 12) * xe * (f * m * b * L)
def DepthSums (T Cth Cadd : ℝ) (th add : ℕ → ℝ) : Prop :=
  (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) → ∑ p ∈ Q, th p * Real.log (p : ℝ) ≤ Cth) ∧
    (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) → T * ∑ p ∈ Q, add p * Real.log (p : ℝ) ≤ Cadd)
def PrimeSumsFree : Prop :=
  ∀ (Y X2 T Cth Cadd : ℝ) (th add : ℕ → ℝ), 1 ≤ Y → 0 < X2 → DepthSums T Cth Cadd th add →
    PrimeSumsG (Real.log 4) (Real.log 4) Y X2 T Cth Cadd th add
def ErrSumGoodFree : Prop :=
  ∀ (PI : Finset ℕ), (∀ p ∈ PI, p.Prime) →
  ∀ (Y X2 A1 A2 kw T Cth Cadd : ℝ) (th add : ℕ → ℝ), 1 < Y → 0 < X2 → 0 ≤ A1 → 0 ≤ A2 → 0 ≤ kw →
    0 ≤ T → (∀ p, 0 ≤ th p) → (∀ p, 0 ≤ add p) → DepthSums T Cth Cadd th add →
      ∑ p ∈ PI, Real.log (p : ℝ) * errGood Y X2 A1 A2 kw T th add p ≤
        2 * (A1 * (Real.log Y + Real.log 4) + kw * Cth + Cadd + 2 * Real.log 4 * A2 / X2 +
          Real.log 4 * Y)
def OnSumFree : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (Bad : Finset ℕ) (eb : ℕ → ℝ), (∀ p, 0 ≤ eb p) →
  ∀ (Y X2 A1 A2 kw T Cth Cadd : ℝ) (th add : ℕ → ℝ), 1 < Y → 0 < X2 → 0 ≤ A1 → 0 ≤ A2 → 0 ≤ kw →
    0 ≤ T → (∀ p, 0 ≤ th p) → (∀ p, 0 ≤ add p) → DepthSums T Cth Cadd th add →
  ∀ (errl : HeightOneSpectrum (𝓞 K) → ℝ),
    (∀ w ∈ S, errl w ≤ if plc w ∈ Bad then eb (plc w) else errGood Y X2 A1 A2 kw T th add (plc w)) →
      ∑ w ∈ S, lw w * ((ramw w : ℝ) * errl w) ≤
        2 * (A1 * (Real.log Y + Real.log 4) + kw * Cth + Cadd + 2 * Real.log 4 * A2 / X2 +
          Real.log 4 * Y) + ∑ p ∈ Bad, Real.log (p : ℝ) * eb p
def AbsorbOnFree : Prop :=
  ∀ (C Cb L xe f m b k ws Se Y X2 bad : ℝ), 1 ≤ C → 0 ≤ Cb → 1 ≤ L → L ≤ xe → 1 ≤ f → 1 ≤ m → 0 < b →
    1 ≤ k → Real.log k ≤ L → 0 ≤ ws → ws ≤ 2 * f * b → 0 ≤ Se → k * Se * L ≤ m * b → 1 < Y →
    Real.log Y ≤ 2 * L → Y ≤ m * b → k ≤ X2 → bad ≤ Cb * (f * m * b * L) →
      2 * (C * (Real.log k * m * ws + f * k * Se) * (Real.log Y + Real.log 4) + C * k * ws * (C / k) +
          C * (m * b) + 2 * Real.log 4 * (C * k * ws) / X2 + Real.log 4 * Y) + bad + 12 * (f * m * b) ≤
        (4 * C ^ 2 + 37 * C + Cb + 12) * xe * (f * m * b * L)
end Formalism.EigenvalueLevelCeiling


