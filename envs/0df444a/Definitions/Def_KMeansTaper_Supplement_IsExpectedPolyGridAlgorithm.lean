-- Prove2me | Definitions.Def_KMeansTaper_Supplement_IsExpectedPolyGridAlgorithm
-- name    : KMeansTaper_Supplement_IsExpectedPolyGridAlgorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:45:25.344814+00:00
-- url     : https://prove2.me/theorems/c2f88ffc-25b8-4521-9496-e84910dac243
-- title:
--   Randomized expected-polynomial algorithms on grid openings
-- statement:
--   A **randomized expected-polynomial grid algorithm** is a finite randomized multi-tape machine together with the set of grid pieces it returns on each fair-coin stream. There are constants $C>0$ and $d\in\mathbb N$ such that its expected number of bit-level machine ticks on every encoded grid input $z$ is at most
--
--   $$
--   C\bigl(|\operatorname{enc}(z)|+1\bigr)^d.
--   $$
--
--   Whenever a run halts, its tape output is the membership mask of the associated set of grid pieces. This supplies the computational and probabilistic meaning of the algorithm in Theorem 5.7.
--
--   **Formalization Note** The machine is the published `IntQuotHNP.Supplement.MTMachine`, a finite transition table over an eight-symbol alphabet reading one fresh fair bit per tick. Its extended expected halting time is infinite if it fails to halt with positive probability. The base mission's Boolean `encodeGridInput` and piece mask are mapped to blank-safe tape words using symbols $1,2$ and delimiter $3$.
-- source:
--   Zhu, A tight approximation for metric k-means via squared tapered rounding, STOC 2027 submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3), Theorem 5.7 and proof, pp.12-13 (PDF pp.15-16)

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_KMeansTaper_encodePieces
import Definitions.Def_IntQuotHNP_Supplement_LasVegas

namespace KMeansTaper
namespace Supplement

open OAI.MetricKMedian (Instance)
open OAI.MatchingFPRAS (Symbol)
open IntQuotHNP.Supplement (MTMachine OutputsOn expectedTime haltTime)
open MeasureTheory

/-- A blank-safe tape encoding of a Boolean word: bits are symbols `1` and `2`, followed by
the delimiter `3`, in the published finite-alphabet Las Vegas machine model. -/
def encodeBoolWord (w : List Bool) : List Symbol :=
  w.map (fun b => if b then (2 : Symbol) else 1) ++ [3]

/-- The tape encoding of a set of grid pieces as its membership mask. -/
def encodeGridOutput (L : List (ℕ × ℕ)) (O : Finset (Fin L.length)) : List Symbol :=
  encodeBoolWord (List.ofFn (fun p : Fin L.length => decide (p ∈ O)))

/-- A randomized algorithm on encoded grid openings with expected running time polynomial in
the input length, together with the facility-set output determined by almost every fair-coin
stream.

This is the computation convention used for "randomized expected-polynomial algorithm" in
Theorem 5.7, p.12 (PDF p.15), of Zhu, *A tight approximation for metric k-means via squared
tapered rounding*, STOC 2027 submission (manuscript sha256
8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3).

**Formalization Note.** The machine is the published finite-table multi-tape machine
`IntQuotHNP.Supplement.MTMachine`: it reads one fresh fair bit per tick, and its extended expected
halting time is `⊤` if it fails to halt on a positive-measure set. Inputs use the published
`encodeGridInput`, mapped to the machine's eight-symbol alphabet; outputs are membership masks
of grid pieces. The polynomial and its constants may depend on the fixed theorem parameters but
not on the encoded instance. -/
def IsExpectedPolyGridAlgorithm (A : MTMachine)
    (out : (z : Σ _ : Instance, List (ℕ × ℕ)) → (ℕ → Bool) → Finset (Fin z.2.length)) : Prop :=
  (∃ C : ℝ, ∃ d : ℕ, 0 < C ∧ ∀ z,
    expectedTime A (encodeBoolWord (encodeGridInput z)) ≤
      ENNReal.ofReal (C * (((encodeBoolWord (encodeGridInput z)).length : ℝ) + 1) ^ d)) ∧
  ∀ z ω, haltTime A (encodeBoolWord (encodeGridInput z)) ω < ⊤ →
    OutputsOn A (encodeBoolWord (encodeGridInput z)) ω (encodeGridOutput z.2 (out z ω))

end Supplement
end KMeansTaper


