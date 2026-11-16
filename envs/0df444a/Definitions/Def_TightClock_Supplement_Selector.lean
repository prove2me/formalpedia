-- Prove2me | Definitions.Def_TightClock_Supplement_Selector
-- name    : TightClock_Supplement_Selector
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:07:42.505397+00:00
-- url     : https://prove2.me/theorems/b44df8cf-8cbc-449d-83f2-e4649e87500b
-- title:
--   Public selection rule for $\arg\max$
-- statement:
--   A **selection rule** picks, from every nonempty family $\mathcal C$ of sets of bidders and every score $f$, a member of $\mathcal C$ maximizing $f$. The auctions use it for every selection on the page: "Choose $j'\in\arg\min_{j\in G}C_j$, breaking ties in a fixed order" (Auction 1, applied to $-C$), "Choose $j'\in\arg\max_j\sum_{i\in A\cap G_j}p_i$" (Auction 3), "Select arbitrary $j\in\arg\max_j\sum_{i\in G_j\cap T}v_i$" (Auction 6), "Select arbitrary $S\in\arg\max_{S'\in\mathcal F}\sum_{i\in S'}Z_i$" (Auction 7), the first label of a random ordering (Auction 9), and the fixed group $G_1$ of Auction 1 (a constant score).
--
--   **Formalization Note** The rule may depend on the whole score vector, not only on the tied sets, so every fixed tie-breaking order is a selection rule. Each choice must be made on a measurable set of scores: this makes the welfare a random variable, so that its expectation is defined.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §3, p.14 (PDF p.17); Auction 1, p.16 (PDF p.19); Auction 3, p.18 (PDF p.21); Auction 6, p.23 (PDF p.26); Auction 7, p.25 (PDF p.28)

import Mathlib

set_option autoImplicit false

namespace TightClock.Supplement

/-- A public selection rule for `arg max`: for every nonempty family `C` of sets of bidders and every
score `f`, `pick C f` is a member of `C` maximizing `f`. It realizes "Select arbitrary
S ∈ arg max" (Auctions 6, 7), "Choose j′ ∈ arg max" (Auction 3) and, applied to `−f`, "Choose
j′ ∈ arg min ..., breaking ties in a fixed order" (Auction 1); `pick C (fun _ => 0)` is a fixed member
of `C` (the "G₁" of Auction 1, line 20). Afshinmehr et al., *Tight Approximation Bounds for Clock
Auctions*, manuscript (STOC 2027 submission), §3, p.14 (PDF 17): "All ties are broken according to
fixed public rules"; Auction 1 (p.16), Auction 3 (p.18), Auction 6 (p.23), Auction 7 (p.25).

**Formalization Note** The rule may depend on the whole score vector, not only on the tied sets.
It must be measurable in the score (each choice is made on a Borel set of scores), so that the
welfare is a random variable and its expectation is defined; every fixed tie-breaking order is such
a rule. -/
structure Selector (n : ℕ) where
  /-- The selected set. -/
  pick : Finset (Finset (Fin n)) → (Finset (Fin n) → ℝ) → Finset (Fin n)
  /-- It belongs to the family. -/
  pick_mem : ∀ (C : Finset (Finset (Fin n))) (f : Finset (Fin n) → ℝ), C.Nonempty → pick C f ∈ C
  /-- It maximizes the score over the family. -/
  pick_max : ∀ (C : Finset (Finset (Fin n))) (f : Finset (Fin n) → ℝ), C.Nonempty → ∀ S ∈ C, f S ≤ f (pick C f)
  /-- Each choice is made on a measurable set of scores. -/
  measurableSet_pick : ∀ (C : Finset (Finset (Fin n))) (S : Finset (Fin n)), MeasurableSet {f : Finset (Fin n) → ℝ | pick C f = S}

end TightClock.Supplement


