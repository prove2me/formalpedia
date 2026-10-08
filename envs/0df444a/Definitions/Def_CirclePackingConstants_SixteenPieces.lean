-- Prove2me | Definitions.Def_CirclePackingConstants_SixteenPieces
-- name    : CirclePackingConstants_SixteenPieces
-- status  : Definition
-- author  : @vebis
-- created : 2026-10-06T15:18:37.424001+00:00
-- url     : https://prove2.me/theorems/a5c7cb73-adf6-4774-b3bd-7d903fbb4328
-- title:
--   Soundness of covering certificates with three preassigned cells
-- statement:
--   This file proves the soundness of the covering certificates with three preassigned cells: if the depth-first search of `cov3`, started from the partial assignment $(n_0,n_1,n_2)=(a,b,c)$ with the remaining cells unassigned, succeeds, then every count vector with these first three entries, entries at most $2$, total $16$, and not all entries $1$, contains a placed pattern of the library `sixteenLib`. It refines `piece_sound` of `CirclePackingConstants_SixteenGlue`, which preassigns two cells.
--
--   **Formalization Note.** Only the axioms `propext`, `Classical.choice` and `Quot.sound` are used.
-- source:
--   G. Wengerodt, Die dichteste Packung von 16 Kreisen in einem Quadrat, Beitraege zur Algebra und Geometrie 16 (1983), 173-190 (optimality of the 4x4 grid); the occupancy-pattern decomposition, the pattern library and the certificates are computer generated for this formalization.

import Definitions.Def_CirclePackingConstants
import Definitions.Def_CirclePackingConstants_SixteenOcc
import Definitions.Def_CirclePackingConstants_BoxChecker
import Definitions.Def_CirclePackingConstants_SixteenGlue

open CirclePackingConstants CirclePackingConstants.Sixteen

namespace CPQ

theorem inv3_init3 (n : Nat → Nat) (a b c : Nat) (h0 : n 0 = a) (h1 : n 1 = b) (h2 : n 2 = c)
    (ha : a ≤ 2) (hb : b ≤ 2) (hc : c ≤ 2) :
    Inv3 n [a, b, c, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] (a + b + c) (a + b + c + 26) := by
  refine ⟨by simp, ?_, ?_, ?_⟩
  · intro d hd hle
    interval_cases d <;> simp_all [List.getD]
  · simp [Finset.sum_range_succ, lowF, List.getD, ha, hb, hc]
  · simp [Finset.sum_range_succ, upF, List.getD, ha, hb, hc]

/-- piece check with three preassigned cells -/
def pieceOK3 (tab : List (List PL)) (toks : List Nat) (a b c : Nat) : Bool :=
  (cov3 tab 400000 (unpackAll18 toks) [a, b, c, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] (a + b + c) (a + b + c + 26)).isSome

theorem piece_sound3 (lib : Lib) (tab : List (List PL)) (htab : tabOK lib tab = true) (toks : List Nat) (a b c : Nat)
    (hp : pieceOK3 tab toks a b c = true) (ha : a ≤ 2) (hb : b ≤ 2) (hc : c ≤ 2)
    (n : Nat → Nat) (hn : ∀ i, n i ≤ 2) (hsum : ∑ i ∈ Finset.range 16, n i = 16) (hne : ∃ i < 16, n i ≠ 1)
    (h0 : n 0 = a) (h1 : n 1 = b) (h2 : n 2 = c) : ∃ e s tx ty, Matches lib n e s tx ty := by
  unfold pieceOK3 at hp
  rcases hr : cov3 tab 400000 (unpackAll18 toks) [a, b, c, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] (a + b + c) (a + b + c + 26) with _ | rest
  · rw [hr] at hp; simp at hp
  · exact cov3_sound lib tab htab _ _ _ _ _ rest hr n (inv3_init3 n a b c h0 h1 h2 ha hb hc) hn hsum hne

end CPQ


