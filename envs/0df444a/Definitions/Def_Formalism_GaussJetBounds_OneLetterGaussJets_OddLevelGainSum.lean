-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OddLevelGainSum
-- name    : Formalism_GaussJetBounds_OneLetterGaussJets_OddLevelGainSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:18:48.465718+00:00
-- url     : https://prove2.me/theorems/72622a48-7e9a-40a0-aaf7-a5ce44219461
-- title:
--   Odd Level Gain Sum
-- statement:
--   Definitions and structural lemmas for Odd Level Gain Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/OneLetterGaussJets/OddLevelGainSum.lean

import Definitions.Def_Formalism_GaussJetBounds_Statement
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
section TopData
variable (l d : ℕ) [NeZero d] (TT : Finset (ZMod d)) (nu1 nu2 size : ZMod d → ℕ)
def WcapOneLetter (s : ZMod d) : ℕ :=
  sSup ((fun i : ℕ => capL d TT nu1 nu2 (s - (i : ZMod d))) ''
    {i : ℕ | Odd i ∧ l ^ i ≤ Dl d TT nu1 size (s - (i : ZMod d))})
def IsLabOneLetter (s s0 : ZMod d) (j : ℤ) : Prop :=
  s0 ∈ TT ∧ Odd j ∧ s = s0 + (j : ZMod d) ∧ (0 < j → l ^ j.toNat ≤ nu1 s0) ∧
    (j < 0 → l ^ (-j).toNat ≤ Dl d TT nu1 size s)
def JnumOneLetter (s : ZMod d) : ℕ :=
  Set.ncard {q : ZMod d × ℤ | IsLabOneLetter l d TT nu1 size s q.1 q.2}
def kaMaxOneLetter : ℕ := max (TT.sup nu1) (Finset.univ.sup (capL d TT nu1 nu2))
open Classical in

def oddLevelGainSum (s : ZMod d) : ℝ :=
  ∑' e : ℕ,
    if Odd e ∧ ¬ (∃ s' ∈ TT, IsLeast {e' : ℕ | Odd e' ∧ s + (e' : ZMod d) = s'} e) then
      max (((nu1 s : ℝ) - nu2 s) / (l : ℝ) ^ e - capL d TT nu1 nu2 (s + (e : ZMod d))) 0
    else 0
end TopData
def digitLossOneLetter {ι : Type v} (l : ℕ) (κ : ι →₀ ℕ) : ℝ :=
  ∑ i ∈ κ.support, ((Nat.log l (κ i) : ℝ) + 1)
end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds


