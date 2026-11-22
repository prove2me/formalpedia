-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementN
-- name    : Formalism_GaussJetBounds_OneLetterGaussJets_StatementN
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:24:47.877535+00:00
-- url     : https://prove2.me/theorems/550a2d37-b547-49a0-9ba2-a19ee2fb0e0a
-- title:
--   Statement N
-- statement:
--   Definitions and structural lemmas for Statement N, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/OneLetterGaussJets/StatementN.lean

import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OddLevelGainSum
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
universe u v w
namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
open Formalism.IncomingBounds
def PropSix7 : Prop :=
  ∀ (l d : ℕ) [NeZero d], 3 ≤ l → 2 ≤ d → Even d →
    ∀ (TT : Finset (ZMod d)) (k : ℕ) (D w E : ZMod d → ℝ), 3 ≤ k →
      (∀ s, 0 < w s) → (∀ s, 0 ≤ E s ∧ E s ≤ 4 * w s) →
      (∀ s, s ∉ TT → D s = ((k : ℝ) - 1) * w s + E s) →
      (∀ s, s ∈ TT → D s = ((k : ℝ) - 1) * w s - 2 * w s + E s) →
      Fnum l d (fun s => ((k : ℝ) - 1) * w s) - 2 * gam l * (∑ s ∈ TT, w s) -
          8 / (l : ℝ) * (∑ s : ZMod d, w s) ≤ Fnum l d D ∧
        Fnum l d (fun s => ((k : ℝ) - 1) * w s) - 11 / (l : ℝ) * (∑ s : ZMod d, w s) ≤
          Fnum l d (fun s => ((k : ℝ) - 1) * w s) - 2 * gam l * (∑ s ∈ TT, w s) -
            8 / (l : ℝ) * (∑ s : ZMod d, w s)
def GainDominatesInnerSum : Prop :=
  ∀ (l d : ℕ) [NeZero d], 2 ≤ l → ∀ (TT : Finset (ZMod d)) (nu1 nu2 : ZMod d → ℕ) (s : ZMod d),
    oddLevelGainSum l d TT nu1 nu2 s ≤ topTerm l d TT nu1 nu2 s
def NormCor7 : Prop :=
  ∀ (l d : ℕ) [NeZero d], 3 ≤ l → 2 ≤ d → Even d →
    ∀ (TT : Finset (ZMod d)) (nu1 nu2 size : ZMod d → ℕ) (k : ℕ) (L : ℝ)
      (w E : ZMod d → ℝ) (pi y : ℝ), 0 < pi → pi < 1 → 3 ≤ k →
      (∀ s, 0 < w s) → (∀ s, 0 ≤ E s ∧ E s ≤ 4 * w s) →
      (∀ s, s ∉ TT → (Dl d TT nu1 size s : ℝ) = ((k : ℝ) - 1) * w s + E s) →
      (∀ s, s ∈ TT → (Dl d TT nu1 size s : ℝ) = ((k : ℝ) - 1) * w s - 2 * w s + E s) →
      y ≤ pi ^ ((∑ s ∈ TT, (topTerm l d TT nu1 nu2 s - gam l * (WcapOneLetter l d TT nu1 nu2 size s : ℝ))) +
          Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) - L) →
      y ≤ pi ^ ((∑ s ∈ TT, oddLevelGainSum l d TT nu1 nu2 s) + Fnum l d (fun s => ((k : ℝ) - 1) * w s) -
          11 / (l : ℝ) * (∑ s : ZMod d, w s) -
          gam l * (∑ s ∈ TT, (WcapOneLetter l d TT nu1 nu2 size s : ℝ)) - L)
end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds


