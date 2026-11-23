-- Prove2me | Definitions.Def_Formalism_MirabolicMackeyTheory_ErrSumGoodExact
-- name    : Formalism_MirabolicMackeyTheory_ErrSumGoodExact
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:53:26.335641+00:00
-- url     : https://prove2.me/theorems/6ebf74e6-3703-447e-9494-3b94c204a8c5
-- title:
--   Err Sum Good Exact
-- statement:
--   Definitions and structural lemmas for Err Sum Good Exact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/ErrSumGoodExact.lean

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementC
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
def ErrSumGoodExact : Prop :=
  ∀ (PI : Finset ℕ), (∀ p ∈ PI, p.Prime) →
  ∀ (Y X2 A1 A2 kw T Cth Cadd : ℝ) (th add : ℕ → ℝ), 1 < Y → 0 < X2 → 0 ≤ A1 → 0 ≤ A2 → 0 ≤ kw →
    0 ≤ T → (∀ p, 0 ≤ th p) → (∀ p, 0 ≤ add p) → DepthSums T Cth Cadd th add →
      ∑ p ∈ PI, Real.log (p : ℝ) * errGood Y X2 A1 A2 kw T th add p ≤
        2 * (A1 * Real.log Y + kw * Cth + Cadd + 2.04 * A2 / X2 + Real.log 4 * Y)
def OnSumExact : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (Bad : Finset ℕ) (eb : ℕ → ℝ), (∀ p, 0 ≤ eb p) →
  ∀ (Y X2 A1 A2 kw T Cth Cadd : ℝ) (th add : ℕ → ℝ), 1 < Y → 0 < X2 → 0 ≤ A1 → 0 ≤ A2 → 0 ≤ kw →
    0 ≤ T → (∀ p, 0 ≤ th p) → (∀ p, 0 ≤ add p) → DepthSums T Cth Cadd th add →
  ∀ (errl : HeightOneSpectrum (𝓞 K) → ℝ),
    (∀ w ∈ S, errl w ≤ if plc w ∈ Bad then eb (plc w) else errGood Y X2 A1 A2 kw T th add (plc w)) →
      ∑ w ∈ S, lw w * ((ramw w : ℝ) * errl w) ≤
        2 * (A1 * Real.log Y + kw * Cth + Cadd + 2.04 * A2 / X2 + Real.log 4 * Y) +
          ∑ p ∈ Bad, Real.log (p : ℝ) * eb p
def AbsorbOnExact : Prop :=
  ∀ (C Cb L xe f m b k ws Se Y X2 bad : ℝ), 1 ≤ C → 0 ≤ Cb → 1 ≤ L → L ≤ xe → 1 ≤ f → 1 ≤ m → 0 < b →
    1 ≤ k → Real.log k ≤ L → 0 ≤ ws → ws ≤ 2 * f * b → 0 ≤ Se → k * Se * L ≤ m * b → 1 < Y →
    Real.log Y ≤ 2 * L → Y ≤ m * b → k ≤ X2 → bad ≤ Cb * (f * m * b * L) →
      2 * (C * (Real.log k * m * ws + f * k * Se) * Real.log Y + C * k * ws * (C / k) + C * (m * b) +
          2.04 * (C * k * ws) / X2 + Real.log 4 * Y) + bad + 12 * (f * m * b) ≤
        (4 * C ^ 2 + 25 * C + Cb + 12) * xe * (f * m * b * L)
def LeadExact : Prop :=
  ∀ (C L f m b k ws Se Y X2 : ℝ), 1 ≤ C → 1 ≤ f → 1 ≤ m → 0 < b → 1 ≤ k → 0 ≤ ws → ws ≤ 2 * f * b →
    0 ≤ Se → k * Se * L ≤ m * b → 1 < Y → Real.log Y ≤ 2 * L → Y ≤ m * b → k ≤ X2 →
      2 * (C * (Real.log k * m * ws + f * k * Se) * Real.log Y + C * k * ws * (C / k) + C * (m * b) +
          2.04 * (C * k * ws) / X2 + Real.log 4 * Y) ≤
        4 * C * L * Real.log k * m * ws + (4 * C ^ 2 + 17 * C) * (f * m * b)
end Formalism.EigenvalueLevelCeiling


