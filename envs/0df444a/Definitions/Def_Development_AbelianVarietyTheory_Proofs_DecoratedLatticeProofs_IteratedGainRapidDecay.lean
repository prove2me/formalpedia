-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IteratedGainRapidDecay
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IteratedGainRapidDecay
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:42.480043+00:00
-- url     : https://prove2.me/theorems/b06ec477-d521-47a6-98eb-e928e143bbc6
-- title:
--   Iterated Gain Rapid Decay
-- statement:
--   Definitions and structural lemmas for Iterated Gain Rapid Decay, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IteratedGainRapidDecay.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
namespace GlobalTheory.IterGain
noncomputable def words {ι : Type} [DecidableEq ι] (B : Finset ι) : ℕ → Finset (List ι)
  | 0 => {[]}
  | k + 1 => insert [] ((words B k ×ˢ B).image (fun p => p.1 ++ [p.2]))
end GlobalTheory.IterGain
namespace GlobalTheory
end GlobalTheory


