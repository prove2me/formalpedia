-- Prove2me | Definitions.Def_TimeSpaceMA_TUZExtractor
-- name    : TimeSpaceMA_TUZExtractor
-- status  : Definition
-- author  : @bersubs
-- created : 2026-11-14T19:39:49.048321+00:00
-- url     : https://prove2.me/theorems/77d8ad41-11bc-477e-9750-d0e1e57e6db1
-- title:
--   Finite flat-source extractor events and binary evaluator
-- statement:
--   For a finite set $S$ of inputs, draw an element of $S$ and a seed independently and uniformly. The event predicate bounds the extractor output’s statistical distance from the uniform output law by testing every event.
--
--   A uniform evaluator receives the input width, entropy threshold, seed width, input label, and seed label. Widths are encoded in unary to charge for the full width of a binary word even when its numeric value is small. The finite graph view keeps the prescribed number of low output bits.
-- source:
--   Ta-Shma, Umans and Zuckerman, Lossless Condensers, Unbalanced Expanders, and Extractors, Combinatorica 27 (2007), Definition 1.1, §2.2 and Corollary 5.8(2), https://www.cs.tau.ac.il/~amnon/Papers/TUZ.C07.pdf

import Definitions.Def_TimeSpaceMA_RAM
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Basic
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Prod

namespace TimeSpaceMA

/-- One-sided statistical distance of a finite extractor output from uniform, tested on
all output events. The other direction follows by taking complements. -/
def FlatExtractorEvents {Input Seed Out : Type} [Fintype Seed] [Fintype Out] [DecidableEq Out]
    (E : Input → Seed → Out) (S : Finset Input) (ε : ℝ) : Prop :=
  ∀ A : Finset Out,
    ((S ×ˢ Finset.univ).filter (fun p : Input × Seed => E p.1 p.2 ∈ A)).card /
        ((S.card : ℝ) * (Fintype.card Seed : ℝ)) -
      (A.card : ℝ) / (Fintype.card Out : ℝ) ≤ ε

open Turing.MultiTapeTM

/-- An extractor query specifies input width, entropy threshold, seed width, input, and seed. -/
abbrev ExtractorInput := ℕ × ℕ × ℕ × ℕ × ℕ

/-- The widths are in unary. This measures evaluation in the length of the full input and
seed words, even when their numerical labels are zero. -/
abbrev encExtractorInput : ExtractorInput ↪ List Bool :=
  encPair encUnary (encPair encNat (encPair encUnary (encPair encNat encNat)))

/-- Read the prescribed number of output bits of the evaluator, padding by zeros when needed. -/
def extractorEdge (extract : ExtractorInput → ℕ) (Δ n k t : ℕ)
    (x : Fin (2^n)) (y : Fin (2^t)) : Fin (2^(k+t-Δ)) :=
  ⟨extract (n,k,t,x.val,y.val) % 2^(k+t-Δ), Nat.mod_lt _ (Nat.pow_pos (by decide))⟩

end TimeSpaceMA


