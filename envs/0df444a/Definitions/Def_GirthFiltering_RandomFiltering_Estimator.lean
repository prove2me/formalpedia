-- Prove2me | Definitions.Def_GirthFiltering_RandomFiltering_Estimator
-- name    : GirthFiltering_RandomFiltering_Estimator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:55:45.815409+00:00
-- url     : https://prove2.me/theorems/c357913a-4bd2-4768-86a1-fc7e5ecfe9cb
-- title:
--   Algorithm 1, independent repetitions, and parameter tuning
-- statement:
--   For a sampling parameter $s>0$ and failure probability $0<\delta<1$, define
--
--   $$
--   N=\lceil12e^s\ln(2/\delta)\rceil,\qquad
--   r=\lceil Ne^{-s}/2\rceil,\qquad B(n,m)=8mn(2m+1).
--   $$
--
--   After operational preprocessing, a positive core with $n',m'$ vertices and edges draws $N$ independent threshold samples and selects their $r$-th largest value $\widehat T$. With $b=s+\ln B(n',m')$, the numerical answer is $b/\widehat T$ when the selected threshold is positive and finite. Every other sampled-threshold outcome returns $+\infty$ explicitly. Forest and zero-cycle branches return $+\infty$ and zero before logarithms, sampling, or division.
--
--   The trial law is the finite product of the input label laws. Charged execution includes preprocessing, each sampled edge, threshold computation, final rank selection, and scalar parameter computations. Accuracy compares the output with the actual weighted girth. The confidence event includes both the exact order-statistic interval $s/g\le\widehat T\le b/g$ and the corresponding core-size approximation. It is a set defined from the output, not an assumption supplied to the algorithm.
--
--   For every real $k>1$, tuning uses $s=\ln B(n,m)/(k-1)$ with original input sizes. The large-factor function is $k(n)=c\ln n/\ln\ln n$. These are formulas for parameters; none asserts its own guarantee. Their domains and all performance claims are supplied by the theorem.
--
--   **Formalization Note** Ascending zero-based selection uses index $N-r$, with validity a theorem conclusion. All mathematical laws are continuous; out-of-range internal IDs and nonpositive thresholds have explicit defaults which the correctness proof must handle. No free girth oracle is used in the program.
-- source:
--   Yablon, Approximating the Girth of an Undirected, Weighted Graph for Larger Approximation Factors, STOC 2027 submission #59 (2026), pinned PDF sha256 cf63df259cbd099089184755e2c32f0d51f00dea322509f35766f4a91a4e021f, p. 3, Algorithm 1; p. 7, Section 3.2 probability and output displays; p. 8, Section 3.3 tuning displays; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/59.pdf

import Definitions.Def_GirthFiltering_RandomFiltering_ThresholdProgram
open scoped ENNReal

namespace GirthFiltering.RandomFiltering

noncomputable def sampleCount (s δ : ℝ) : ℕ :=
  ⌈12 * Real.exp s * Real.log (2 / δ)⌉₊

noncomputable def sampleRank (s δ : ℝ) : ℕ :=
  ⌈(sampleCount s δ : ℝ) * Real.exp (-s) / 2⌉₊

def sizeFactor (n m : ℕ) : ℝ := 8 * (m : ℝ) * (n : ℝ) * (2 * (m : ℝ) + 1)

abbrev Tape (G : WeightedGraph) (N : ℕ) := Fin N → Fin G.q → ℝ

noncomputable def trialLaw (G : WeightedGraph) (N : ℕ) :
    MeasureTheory.Measure (Tape G N) :=
  MeasureTheory.Measure.pi (fun _ : Fin N => inputLabelLaw G)

/-- Operational Algorithm 1, with the prescribed three-way threshold routine.
The pair contains its numerical answer and selected threshold. The state is
the accumulated charged work, including preprocessing and all random draws. -/
noncomputable def approximate (G : WeightedGraph) (s δ : ℝ)
    (ω : Tape G (sampleCount s δ)) : Charged (ℝ≥0∞ × EReal) := do
  tick
  match ← prepare G with
  | .forest => return (⊤, ⊥)
  | .zeroCycle => return (0, ⊥)
  | .positive nv es =>
    tick
    let N := sampleCount s δ
    let r := sampleRank s δ
    let ne ← cLength es
    let b := s + Real.log (sizeFactor nv ne)
    let ts ← cOfFn (fun j : Fin N => do
      tick
      findThreshold (← sampleEdges G es (ω j)))
    let t ← select ts (N - r)
    tick
    if (0 : EReal) < t ∧ t < ⊤ then
      return (ENNReal.ofReal (b / t.toReal), t)
    else
      return (⊤, t)

noncomputable def estimate (G : WeightedGraph) (s δ : ℝ)
    (ω : Tape G (sampleCount s δ)) : ℝ≥0∞ :=
  (runCharged (approximate G s δ ω)).1.1

noncomputable def selectedThreshold (G : WeightedGraph) (s δ : ℝ)
    (ω : Tape G (sampleCount s δ)) : EReal :=
  (runCharged (approximate G s δ ω)).1.2

noncomputable def executionCost (G : WeightedGraph) (s δ : ℝ)
    (ω : Tape G (sampleCount s δ)) : ℕ :=
  (runCharged (approximate G s δ ω)).2

noncomputable def Accurate (G : WeightedGraph) (factor : ℝ) (answer : ℝ≥0∞) : Prop :=
  girth G ≤ answer ∧ answer ≤ ENNReal.ofReal (factor * (girth G).toReal)

/-- The exact order-statistic interval and core-size approximation event.
This is an event specification, never an input to the estimator. -/
noncomputable def confidenceEvent (G : WeightedGraph) (s δ : ℝ) (nv ne : ℕ) :
    Set (Tape G (sampleCount s δ)) :=
  {ω | ((s / (girth G).toReal : ℝ) : EReal) ≤ selectedThreshold G s δ ω ∧
    selectedThreshold G s δ ω ≤
      (((s + Real.log (sizeFactor nv ne)) / (girth G).toReal : ℝ) : EReal) ∧
    Accurate G (1 + Real.log (sizeFactor nv ne) / s) (estimate G s δ ω)}

noncomputable def tunedParameter (G : WeightedGraph) (k : ℝ) : ℝ :=
  Real.log (sizeFactor G.n G.q) / (k - 1)

noncomputable def highFactor (n : ℕ) (c : ℝ) : ℝ :=
  c * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))

end GirthFiltering.RandomFiltering


