-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleWeightSquareLengthLt
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleWeightSquareLengthLt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:03.790067+00:00
-- url     : https://prove2.me/theorems/56ccb7b4-7011-4271-ad4b-06d307a41085
-- title:
--   Shuffle Weight Square Length Lt
-- statement:
--   Definitions and structural lemmas for Shuffle Weight Square Length Lt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ShuffleWeightSquareLengthLt.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Zc.Comb
open Classical
universe u
namespace GlobalTheory.CompanionTheory.MultiSeg.Rank
variable {T : Type u}
def word (s : T → T) (t : T) (l : ℕ) : List T := (List.range l).reverse.map fun i => s^[i] t
def Con (s : T → T) (u : T) (d : ℕ) (x : List T) : Prop := u ∈ x ∧ s^[d] u ∈ x
noncomputable def rank (s : T → T) (m : Multiset (ASeg T)) (u : T) (d : ℕ) : ℕ :=
  m.countP (fun Δ => Con s u d (Δ.dec s))
def wd (d : ℕ) : ℕ := if d = 0 then 1 else 2
noncomputable def pairs (s : T → T) (Δ : ASeg T) : Finset (T × ℕ) :=
  ((Finset.range Δ.len).sigma fun d => Finset.range (Δ.len - d)).image
    fun p => (s^[p.2] Δ.start, p.1)
end GlobalTheory.CompanionTheory.MultiSeg.Rank


