-- Prove2me | Definitions.Def_MoneyBurningTrade_IndependentSurplus_Regions
-- name    : MoneyBurningTrade_IndependentSurplus_Regions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:44:17.447365+00:00
-- url     : https://prove2.me/theorems/ff4f50fa-0af0-446a-b99f-07661408c3a2
-- title:
--   Definition 4.4 — profile regions and overlap count
-- statement:
--   For $1\le i\le n-3$, the profile region is
--
--   $$\mathcal R_i=\{(s,b):q_i\le s<q_i+\tau,\quad q_{i+2}-\tau<b\le q_{i+2}\}.$$
--
--   For a finite index set $I$, its region union is $\bigcup_{i\in I}\mathcal R_i$. The overlap count $h$ is the maximum, over every real price $p$, of the number of closed intervals $[q_i,q_{i+2}]$, $i\in I$, containing $p$. Counts include endpoint ties; $h$ is computed rather than fixed to two or three. A region's first-best contribution is $\int_A\max(b-s,0)\,dF$ for the actual joint law $F$.
-- source:
--   Moshe Babaioff, Noam Nisan, Ariel Shaulker, STOC 2027 submission #303 (October 2026), Definition 4.4 and Lemma 4.5, printed p. 25 (PDF p. 26); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/303.pdf

import Definitions.Def_MoneyBurningTrade_IndependentSurplus_Grid

open MeasureTheory

set_option autoImplicit false

namespace MoneyBurningTrade.IndependentSurplus

/-- The exact half-open rectangles R_i, Definition 4.4 p.25. -/
def profileRegion (G : Grid) (τ : ℝ) (i : ℕ) : Set (ℝ × ℝ) :=
  {p | G.q i ≤ p.1 ∧ p.1 < G.q i + τ ∧
    G.q (i + 2) - τ < p.2 ∧ p.2 ≤ G.q (i + 2)}

/-- The union indexed by I in condition 2 of Lemma 4.5. -/
def regionUnion (G : Grid) (τ : ℝ) (I : Finset ℕ) : Set (ℝ × ℝ) :=
  {p | ∃ i ∈ I, p ∈ profileRegion G τ i}

/-- Maximum number of the closed intervals [q_i,q_(i+2)] containing a real price.
The set of counts is nonempty and bounded by I.card, so this is an attained finite
maximum, including overlap at endpoints. The value is not fixed to 2 or 3. -/
noncomputable def overlap (G : Grid) (I : Finset ℕ) : ℕ := by
  classical
  exact sSup {c : ℕ | ∃ p : ℝ,
    c = (I.filter (fun i => G.q i ≤ p ∧ p ≤ G.q (i + 2))).card}

/-- First-best GFT contribution of a measurable region, Lemma 4.5. On the
bounded report square the integrand is bounded; μ may be correlated. -/
noncomputable def firstBestContribution (μ : Measure (ℝ × ℝ))
    (A : Set (ℝ × ℝ)) : ℝ := ∫ p in A, max (p.2 - p.1) 0 ∂μ

end MoneyBurningTrade.IndependentSurplus


