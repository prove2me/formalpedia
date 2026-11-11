-- Prove2me | Definitions.Def_LargeSupplyFPA_Asymptotic_Smoothing
-- name    : LargeSupplyFPA_Asymptotic_Smoothing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:02:53.29085+00:00
-- url     : https://prove2.me/theorems/d9f84e0c-40f0-4330-9eaf-67b599067d71
-- title:
--   Atom-smoothing construction Ẽ ((37)–(38), p. 29)
-- statement:
--   Let $\mathcal P$ be the set of atoms of the agents' marginal bid distributions, which is countable. Choose weights $s_p>0$ for $p\in\mathcal P$ with $\sum_{p\in\mathcal P}s_p<\omega$. A bid $b$ is mapped to the smoothed bid
--   $$\tilde b=b+\sum_{p\in\mathcal P,\,p<b}s_p\quad(b\notin\mathcal P),\qquad \tilde b=b+\sum_{p\in\mathcal P,\,p<b}s_p+s_b\,U\quad(b\in\mathcal P),$$
--   with $U$ uniform on $[0,1]$ and independent across atoms and agents ((37)–(38)). The smoothed marginal of agent $i$ draws $b\sim E_i$ and then $\tilde b$. $\tilde x_i$ is the interim allocation computed from the smoothed marginals.
--
--   **Formalization Note** The weights are a function $s:\mathbb R\to\mathbb R$; only its values on $\mathcal P$ matter, and summability over $\mathcal P$ is part of the admissibility predicate. The law of $\tilde b$ given $b$ is a Dirac mass, or the image of Lebesgue measure on $[0,1]$ under $u\mapsto b+\text{shift}(b)+s_b u$.
-- source:
--   Hartline, Shah, vonAllmen, Robust Analysis of First-Price Auctions with Large Supply, STOC 2027 submission (manuscript of November 3, 2026, sha256 2ad8363b…), p. 29, construction (37)–(38); p. 30, Lemma 7 (x̃_i)

import Mathlib
import Definitions.Def_LargeSupplyFPA_Asymptotic_Model

open MeasureTheory ProbabilityTheory

namespace LargeSupplyFPA.Asymptotic

/-- `P = ⋃_i P_i`, the set of atoms of the agents' marginal bid distributions. -/
def atomSet {n : ℕ} (V : Fin n → Measure ℝ) (E : Fin n → Kernel ℝ ℝ) : Set ℝ :=
  {p | ∃ i, marginalBid V E i {p} ≠ 0}

/-- Admissible smoothing weights for `ω`: `s p > 0` for every atom `p ∈ P`, and
`∑_{p ∈ P} s p < ω` (the sum converging). -/
def IsSmoothingWeights {n : ℕ} (V : Fin n → Measure ℝ) (E : Fin n → Kernel ℝ ℝ) (ω : ℝ)
    (s : ℝ → ℝ) : Prop :=
  (∀ p ∈ atomSet V E, 0 < s p) ∧ Summable (fun p : atomSet V E => s p) ∧
    ∑' p : atomSet V E, s p < ω

/-- The cumulative shift `∑_{p ∈ P, p < b} s p`. -/
noncomputable def atomShift {n : ℕ} (V : Fin n → Measure ℝ) (E : Fin n → Kernel ℝ ℝ)
    (s : ℝ → ℝ) (b : ℝ) : ℝ :=
  ∑' p : {p : ℝ // p ∈ atomSet V E ∧ p < b}, s p

open Classical in
/-- The law of the smoothed bid `b̃` given the original bid `b`: (37) if `b ∉ P`,
`b̃ = b + ∑_{p ∈ P, p < b} s p`; (38) if `b ∈ P`,
`b̃ = b + ∑_{p ∈ P, p < b} s p + s b · U` with `U` uniform on `[0, 1]`. -/
noncomputable def smoothedBidLaw {n : ℕ} (V : Fin n → Measure ℝ) (E : Fin n → Kernel ℝ ℝ)
    (s : ℝ → ℝ) (b : ℝ) : Measure ℝ :=
  if b ∈ atomSet V E then
    (volume.restrict (Set.Icc (0 : ℝ) 1)).map (fun u => b + atomShift V E s b + s b * u)
  else Measure.dirac (b + atomShift V E s b)

/-- Marginal bid distribution of agent `i` under the smoothed profile `Ẽ`: draw `b ∼ E_i`,
then `b̃` from `smoothedBidLaw` (the uniform variables independent across agents). -/
noncomputable def smoothedMarginal {n : ℕ} (V : Fin n → Measure ℝ) (E : Fin n → Kernel ℝ ℝ)
    (s : ℝ → ℝ) (i : Fin n) : Measure ℝ :=
  (marginalBid V E i).bind (smoothedBidLaw V E s)

/-- Interim allocation `x̃_i(b)` under the smoothed profile `Ẽ` in the `k`-unit auction. -/
noncomputable def smoothedAlloc {n : ℕ} (k : ℕ) (V : Fin n → Measure ℝ)
    (E : Fin n → Kernel ℝ ℝ) (s : ℝ → ℝ) (i : Fin n) (b : ℝ) : ℝ :=
  allocOf k (smoothedMarginal V E s) i b

end LargeSupplyFPA.Asymptotic


