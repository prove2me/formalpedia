-- Prove2me | Definitions.Def_ListReplicableBias_LowerBound_Supplement_Algorithms
-- name    : ListReplicableBias_LowerBound_Supplement_Algorithms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:23:19.586449+00:00
-- url     : https://prove2.me/theorems/a953e045-f48a-4689-9a79-11cbd33a7a5b
-- title:
--   Algorithms 1–3 — the random-shift estimator, its capped version and its boosted version
-- statement:
--   Parameters (PDF p. 9): $\varepsilon\in(0,1)$, $\eta\in(0,1/8)$, $m=\lceil\log_2(24d)\rceil$, and for rounds $j=1,\dots,m$
--   $$\alpha_j=\frac{\varepsilon}{2^{j+1}},\qquad n_j=\Big\lceil\frac{1}{2\alpha_j^2}\ln\frac{2dm}{\eta}\Big\rceil,\qquad M=\frac{1536d^2}{\varepsilon^2}\ln\frac{2dm}{\eta},\qquad B=\lceil4M\rceil .$$
--
--   **Algorithm 1** (PDF pp. 9–10), in the paper's block model: draw $U\sim\mathrm{Unif}([0,\varepsilon))$ and, independently, a block of $n_j$ tosses of coin $i$ for every coin $i$ and round $j$, with empirical mean $\hat p_i^{(j)}$. Coin $i$ succeeds in round $j$ if $U$ is $2\alpha_j$-good for $\hat p_i^{(j)}$; $Z_i$ is its first successful round. If every coin succeeds, the output is $Y=(R_U(\hat p_i^{(Z_i)}))_i$; otherwise $Y=\bot$. Coin $i$ is tossed in rounds $1,\dots,Z_i$ (all $m$ rounds if it never succeeds), and the number of tosses $N$ counts exactly those blocks. The events $G=\bigcap_i\{U\text{ is }3\alpha_m\text{-good for }p_i\}$ and $H=\bigcap_{i,j}\{\hat p_i^{(j)}\in[p_i-\alpha_j,p_i+\alpha_j]\}$ are sets of outcomes.
--
--   **Algorithm 2** (PDF p. 13): on the same outcome, output $\bot$ if Algorithm 1 needs more than $B$ tosses and Algorithm 1's output otherwise; its toss count is $\min(N,B)$.
--
--   **Algorithm 3** (PDF p. 14): with $\delta\in(0,1/2)$, $T=\lceil\log_2(2/\delta)\rceil$ and $\eta=\delta/4$, run $T$ independent copies of Algorithm 2 and output the first non-$\bot$ output, or $\bot$ if all fail; its toss count sums the runs up to and including the first success (all $T$ runs if none succeeds).
--
--   These are the concrete algorithms whose properties (Theorems 6.9, A.1, A.2) yield the upper bound of Theorem 6.8.
--
--   **Formalization Note** Rounds are indexed by `Fin m`, block $b$ being round $b+1$. Each toss of coin $i$ is a Bernoulli$(p_i)$ variable built from the published Bernoulli masses; the outcome law is the uniform shift times the product of all toss laws, and Algorithm 3's law is the product of $T$ copies. Results use these laws for $p\in[0,1]^d$ and $d\ge1$.
-- source:
--   Chen, Bastan, Pavan, Vinodchandran, The Price of List Replicability: Tight Bounds for Bias Estimation, STOC 2027 submission #681 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/681.pdf, Algorithm 1 and parameters, PDF pp. 9–10; events G, H, PDF p. 10; Algorithm 2, PDF p. 13; Algorithm 3, PDF p. 14

import Mathlib
import Definitions.Def_ListReplicableBias_LowerBound_Sampling
import Definitions.Def_ListReplicableBias_LowerBound_Supplement_Rounding

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Classical

namespace ListReplicableBias.LowerBound.Supplement

open ListReplicableBias.LowerBound

/-! ### Parameters of Algorithm 1 (PDF p. 9) and Algorithms 2, 3 (PDF pp. 13, 14) -/

/-- m = ⌈log₂(24d)⌉, PDF p. 9. -/
def numRounds (d : ℕ) : ℕ := ⌈Real.logb 2 (24 * (d : ℝ))⌉₊

/-- α_j = ε / 2^{j+1}, PDF p. 9; `j` is the paper's 1-based round number. -/
def accuracy (ε : ℝ) (j : ℕ) : ℝ := ε / 2 ^ (j + 1)

/-- n_j = ⌈(1/(2α_j²)) ln(2dm/η)⌉, PDF p. 9; `j` is the 1-based round number. -/
def blockSize (d : ℕ) (ε η : ℝ) (j : ℕ) : ℕ :=
  ⌈(1 / (2 * accuracy ε j ^ 2)) * Real.log (2 * (d : ℝ) * (numRounds d : ℝ) / η)⌉₊

/-- M = (1536 d²/ε²) ln(2dm/η), PDF pp. 9, 13. -/
def expectedBound (d : ℕ) (ε η : ℝ) : ℝ :=
  1536 * (d : ℝ) ^ 2 / ε ^ 2 * Real.log (2 * (d : ℝ) * (numRounds d : ℝ) / η)

/-- B = ⌈4M⌉, the cap of Algorithm 2, PDF p. 13. -/
def sampleCap (d : ℕ) (ε η : ℝ) : ℕ := ⌈4 * expectedBound d ε η⌉₊

/-- T = ⌈log₂(2/δ)⌉, the number of attempts of Algorithm 3, PDF p. 14. -/
def numAttempts (δ : ℝ) : ℕ := ⌈Real.logb 2 (2 / δ)⌉₊

/-! ### The outcome space of Algorithm 1 (block model of PDF p. 10)

An independent block of n_j tosses is assigned to every coin i and round j,
whether or not the algorithm uses it. Block `b : Fin m` is round `b + 1`. -/

/-- Index of one toss: coin i, round block b (round b + 1), toss s < n_{b+1}. -/
abbrev BitIndex (d : ℕ) (ε η : ℝ) : Type :=
  Fin d × (Σ b : Fin (numRounds d), Fin (blockSize d ε η (b.val + 1)))

/-- An outcome of Algorithm 1: the shift U and all block toss outcomes. -/
abbrev Outcome1 (d : ℕ) (ε η : ℝ) : Type := ℝ × (BitIndex d ε η → Bool)

/-- Bern(q) on Bool with the published Bernoulli masses (true has mass q). -/
def bernMeasure (q : ℝ) : Measure Bool :=
  ENNReal.ofReal (bernMass q true) • Measure.dirac true +
    ENNReal.ofReal (bernMass q false) • Measure.dirac false

/-- Independent tosses: every toss of coin i is Bern(p_i), all independent. -/
def bitsLaw (d : ℕ) (ε η : ℝ) (p : Fin d → ℝ) : Measure (BitIndex d ε η → Bool) :=
  Measure.pi (fun k : BitIndex d ε η => bernMeasure (p k.1))

/-- Law of Algorithm 1's outcome: U ~ Unif([0, ε)) independent of the tosses. -/
def alg1Law (d : ℕ) (ε η : ℝ) (p : Fin d → ℝ) : Measure (Outcome1 d ε η) :=
  (uniformShift ε).prod (bitsLaw d ε η p)

/-- Empirical mean p̂_i^{(j)} of block j = b + 1 of coin i (n_j tosses). -/
def empMean {d : ℕ} {ε η : ℝ} (x : BitIndex d ε η → Bool) (i : Fin d)
    (b : Fin (numRounds d)) : ℝ :=
  (∑ s : Fin (blockSize d ε η (b.val + 1)), if x (i, ⟨b, s⟩) then (1 : ℝ) else 0) /
    (blockSize d ε η (b.val + 1) : ℝ)

/-- Line 9 of Algorithm 1: in round b + 1, U is 2α_{b+1}-good for p̂_i^{(b+1)}. -/
def roundSucceeds {d : ℕ} {ε η : ℝ} (ω : Outcome1 d ε η) (i : Fin d)
    (b : Fin (numRounds d)) : Prop :=
  IsGoodShift ε (2 * accuracy ε (b.val + 1)) (empMean ω.2 i b) ω.1

/-- Coin i is active (tossed) in round b + 1 iff it failed the test in every
earlier round (rounds 1, …, Z_i, or all m rounds when it never succeeds). -/
def isActive {d : ℕ} {ε η : ℝ} (ω : Outcome1 d ε η) (i : Fin d)
    (b : Fin (numRounds d)) : Prop :=
  ∀ b' : Fin (numRounds d), b' < b → ¬ roundSucceeds ω i b'

/-- Z_i − 1: the first (0-based) round block in which coin i succeeds. -/
def firstSuccess {d : ℕ} {ε η : ℝ} (ω : Outcome1 d ε η) (i : Fin d)
    (h : ∃ b, roundSucceeds ω i b) : Fin (numRounds d) :=
  (Finset.univ.filter (fun b => roundSucceeds ω i b)).min'
    (by obtain ⟨b, hb⟩ := h; exact ⟨b, by simp [hb]⟩)

/-- Output Y of Algorithm 1: y_i = R_U(p̂_i^{(Z_i)}) when every coin succeeds,
and ⊥ (`none`) when some coin never succeeds in the m rounds. -/
def alg1Output {d : ℕ} {ε η : ℝ} (ω : Outcome1 d ε η) : Option (Fin d → ℝ) :=
  if h : ∀ i, ∃ b, roundSucceeds ω i b then
    some (fun i => roundShift ε ω.1 (empMean ω.2 i (firstSuccess ω i (h i))))
  else none

/-- Tosses N used by Algorithm 1: n_j for every round j in which coin i is active. -/
def alg1Tosses {d : ℕ} {ε η : ℝ} (ω : Outcome1 d ε η) : ℕ :=
  ∑ i : Fin d, ∑ b : Fin (numRounds d),
    if isActive ω i b then blockSize d ε η (b.val + 1) else 0

/-- Event G = ∩_i {U is 3α_m-good for p_i}, PDF p. 10. -/
def eventG (d : ℕ) (ε η : ℝ) (p : Fin d → ℝ) : Set (Outcome1 d ε η) :=
  {ω | ∀ i, IsGoodShift ε (3 * accuracy ε (numRounds d)) (p i) ω.1}

/-- Event H = ∩_{i,j} {p̂_i^{(j)} ∈ [p_i − α_j, p_i + α_j]}, PDF p. 10. -/
def eventH (d : ℕ) (ε η : ℝ) (p : Fin d → ℝ) : Set (Outcome1 d ε η) :=
  {ω | ∀ i (b : Fin (numRounds d)),
    empMean ω.2 i b ∈ Set.Icc (p i - accuracy ε (b.val + 1)) (p i + accuracy ε (b.val + 1))}

/-! ### Algorithm 2 (PDF p. 13): Algorithm 1 with a cap of B = ⌈4M⌉ tosses -/

/-- Output of Algorithm 2: ⊥ if Algorithm 1 needs more than B tosses. -/
def alg2Output {d : ℕ} {ε η : ℝ} (ω : Outcome1 d ε η) : Option (Fin d → ℝ) :=
  if sampleCap d ε η < alg1Tosses ω then none else alg1Output ω

/-- Tosses of Algorithm 2: those of Algorithm 1, stopped at the cap B. -/
def alg2Tosses {d : ℕ} {ε η : ℝ} (ω : Outcome1 d ε η) : ℕ :=
  min (alg1Tosses ω) (sampleCap d ε η)

/-! ### Algorithm 3 (PDF p. 14): up to T i.i.d. runs of Algorithm 2, η = δ/4 -/

/-- An outcome of Algorithm 3: T independent outcomes of Algorithm 2 (η = δ/4). -/
abbrev Outcome3 (d : ℕ) (ε δ : ℝ) : Type :=
  Fin (numAttempts δ) → Outcome1 d ε (δ / 4)

/-- Law of Algorithm 3: T i.i.d. copies of Algorithm 2's outcome law. -/
def alg3Law (d : ℕ) (ε δ : ℝ) (p : Fin d → ℝ) : Measure (Outcome3 d ε δ) :=
  Measure.pi (fun _ : Fin (numAttempts δ) => alg1Law d ε (δ / 4) p)

/-- Output of Algorithm 3: the first non-⊥ output among the T runs, else ⊥. -/
def alg3Output {d : ℕ} {ε δ : ℝ} (ω : Outcome3 d ε δ) : Option (Fin d → ℝ) :=
  if h : ∃ t, (alg2Output (ω t)).isSome then
    alg2Output (ω ((Finset.univ.filter (fun t => (alg2Output (ω t)).isSome)).min'
      (by obtain ⟨t, ht⟩ := h; exact ⟨t, by simp [ht]⟩)))
  else none

/-- Tosses of Algorithm 3: runs 1, …, K (K the first non-⊥ run), or all T runs. -/
def alg3Tosses {d : ℕ} {ε δ : ℝ} (ω : Outcome3 d ε δ) : ℕ :=
  ∑ t : Fin (numAttempts δ),
    if (∀ t' : Fin (numAttempts δ), t' < t → alg2Output (ω t') = none)
    then alg2Tosses (ω t) else 0

end ListReplicableBias.LowerBound.Supplement


