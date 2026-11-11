-- Prove2me | Definitions.Def_TightContinualCounting_LowerBounds_parameters
-- name    : TightContinualCounting_LowerBounds_parameters
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:03:24.574678+00:00
-- url     : https://prove2.me/theorems/94f9ca41-8a1b-4bba-afeb-09ee80ecdcac
-- title:
--   Hamming distance, group slack, privacy window, and absolute proof witnesses
-- statement:
--   For binary vectors $x,x'$, their Hamming distance is the number of unequal coordinates. For $k\ge0$ define the accumulated additive privacy slack
--
--   $$
--   \delta_k=\delta\sum_{i=0}^{k-1}e^{i\varepsilon}.
--   $$
--
--   This gives $\delta k$ when $\varepsilon=0$ and avoids a zero denominator. Set $\eta=\max\{\varepsilon,\delta\}$, $L=\log(n\eta)$, and
--
--   $$
--   U=\begin{cases}1+L,&\delta=0,\\1+\min\{L,\log(\eta/\delta)\},&\delta\ne0.\end{cases}
--   \qquad c=\frac5{9\cdot2^{47}},\quad C_0=e^{5500}.
--   $$
--
--   The branch at zero implements the source's extended logarithm convention after taking the minimum. These definitions fix the privacy parameters and universal witnesses used by the main lower bound; no witness depends on the mechanism or input length.
--
--   **Formalization Note** All applications have nonnegative privacy parameters. The main premise $n\eta\ge C_0$ ensures $\eta>0$ and $L\ge5500$. The finite sum is zero for $k=0$. The logarithms outside this premise are total Lean operations and carry no source assertion.
-- source:
--   Charlie Harrison, Ethan Leeman, Tight Lower Bounds for Differentially Private Continual Counting, STOC 2027 submission #1453 (October 2026), Definition 2 p.4; Lemma 3 p.5; Theorem 1 p.3 and explicit witnesses p.15

import Mathlib

open scoped ENNReal

namespace TightContinualCounting.LowerBounds

/-- Replacement Hamming distance (Definition 2, p.4). -/
def hamming {n : ℕ} (x x' : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun i => x i ≠ x' i).card

/-- The geometric accumulated additive privacy slack (Lemma 3, p.5). -/
noncomputable def groupDelta (ε δ : ℝ) (k : ℕ) : ℝ :=
  δ * ∑ i ∈ Finset.range k, Real.exp ((i : ℝ) * ε)

/-- The finite interpretation of min with log(η/0)=+∞ (pp.3–4). -/
noncomputable def privacyWindow (n : ℕ) (ε δ : ℝ) : ℝ :=
  let η := max ε δ
  let L := Real.log ((n : ℝ) * η)
  if δ = 0 then 1 + L else 1 + min L (Real.log (η / δ))

/-- Absolute witness in the proof of Theorem 1, p.15. -/
noncomputable def lowerConstant : ℝ := 5 / (9 * 2 ^ 47)

/-- Absolute size threshold in the proof of Theorem 1, p.15. -/
noncomputable def sizeThreshold : ℝ := Real.exp 5500

end TightContinualCounting.LowerBounds


