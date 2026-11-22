-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementA
-- name    : Formalism_GaussJetBounds_OneLetterGaussJets_StatementA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:24:57.436863+00:00
-- url     : https://prove2.me/theorems/33f5c684-d61c-4e35-8447-148d4d6306fa
-- title:
--   Statement A
-- statement:
--   Definitions and structural lemmas for Statement A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/OneLetterGaussJets/StatementA.lean

import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OddLevelGainSum
import Definitions.Def_Formalism_GaussJetBounds_StatementA
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
def ThmAAssembly7 : Prop :=
  ∀ (l d : ℕ) [NeZero d], 3 ≤ l → 2 ≤ d → Even d →
  ∀ (TT : Finset (ZMod d)) (nu1 nu2 size : ZMod d → ℕ), (∀ s, nu2 s ≤ nu1 s) →
    (∀ s, nu1 s ≤ size s) →
  ∀ sig : ZMod d → ℝ, IsOptDual l d (fun s => (Dl d TT nu1 size s : ℝ)) sig →
  ∀ (ι : Type) [Fintype ι] (lt : ι → ZMod d) (isTop : ι → Bool) (spec : ι → Option (ZMod d × ℤ))
    (κ : ι → ℕ),
    (∀ i, isTop i = true → lt i ∈ TT ∧ spec i = none) →
    (∀ s ∈ TT, (∑ i ∈ Finset.univ.filter (fun i => lt i = s ∧ isTop i = true), (κ i : ℝ)) =
      (nu1 s : ℝ)) →
    (∀ s, (∑ i ∈ Finset.univ.filter (fun i => lt i = s ∧ isTop i = false), (κ i : ℝ)) =
      (Dl d TT nu1 size s : ℝ)) →
    (∀ i s j, spec i = some (s, j) → s ∈ TT ∧ Odd j ∧ lt i = s + (j : ZMod d) ∧
      (0 < j → l ^ j.toNat ≤ nu1 s) ∧ (j < 0 → l ^ (-j).toNat ≤ Dl d TT nu1 size (lt i))) →
    (∀ (s : ZMod d) (j : ℤ), (∑ i ∈ Finset.univ.filter (fun i => spec i = some (s, j)), (κ i : ℝ)) ≤
      (capL d TT nu1 nu2 (s + (j : ZMod d)) : ℝ)) →
    ∃ eps : ZMod d → ℝ, (∀ s, 0 ≤ eps s) ∧
      (∀ s ∈ TT, ∀ e : ℕ, dTop d TT s = (e : ℕ∞) → ((l : ℝ) ^ e)⁻¹ ≤ eps s) ∧
      (∑ s ∈ TT, (topTerm l d TT nu1 nu2 s - gam l * (WcapOneLetter l d TT nu1 nu2 size s : ℝ))) +
          Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) ≤
        ∑ i, (κ i : ℝ) * (gam l - rowRad l sig eps lt isTop spec i)
def LabelCountBound : Prop :=
  ∀ (l d : ℕ) [NeZero d], 2 ≤ l → ∀ (TT : Finset (ZMod d)) (nu1 size : ZMod d → ℕ) (a : ℝ), 2 ≤ a →
    (∀ s ∈ TT, (nu1 s : ℝ) ≤ 2 * a) → ∀ s, (Dl d TT nu1 size s : ℝ) ≤ a ^ 2 →
      (JnumOneLetter l d TT nu1 size s : ℝ) ≤ 2 * Real.logb l a + 1
def LabFinite7 : Prop :=
  ∀ (l d : ℕ) [NeZero d], 2 ≤ l → ∀ (TT : Finset (ZMod d)) (nu1 size : ZMod d → ℕ) (s : ZMod d),
    {q : ZMod d × ℤ | IsLabOneLetter l d TT nu1 size s q.1 q.2}.Finite
def WcapLe7 : Prop :=
  ∀ (l d : ℕ) [NeZero d] (TT : Finset (ZMod d)) (nu1 nu2 size : ZMod d → ℕ) (s : ZMod d),
    WcapOneLetter l d TT nu1 nu2 size s ≤ Wcap l d TT nu1 nu2 size s
end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds


