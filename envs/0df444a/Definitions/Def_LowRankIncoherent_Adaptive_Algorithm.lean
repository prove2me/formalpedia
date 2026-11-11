-- Prove2me | Definitions.Def_LowRankIncoherent_Adaptive_Algorithm
-- name    : LowRankIncoherent_Adaptive_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T13:18:00.232777+00:00
-- url     : https://prove2.me/theorems/075a3e39-fc20-46fc-8d7c-6711f33d2e89
-- title:
--   Algorithm 3: adaptive execution, clipping and nearest-channel output
-- statement:
--   The structural choices are a measurable tie-breaking rank truncation and a measurable nearest-channel selection. Neither takes the unknown channel as input. Admissibility concerns only truncation and exact minimization, never accuracy. Existence of these choices is a conclusion of the goal.
--
--   Algorithm 3 sets $s=ε/(64r)$, $T=\max\{1,\lceil\log_2a\rceil\}$, $δ'=δ/(T+1)$, $b_0=ab+(1+a/r)\log(6/δ')$, and $n=\lceil Kb_0/s^2\rceil$. Starting at $ρ_1=I_a/a$, each round samples two fresh batches at $σ_j=ρ_j/2+I_a/(2a)$. It clips every eigenvalue of $\widehat H_j+rI_a$ below $r/2$ and updates
--   $$ρ_{j+1}=\frac{\exp(\log ρ_j+\log A_j)}{\operatorname{tr}\exp(\log ρ_j+\log A_j)}.$$
--   The final input averages the $T$ queried inputs before their updates. A fresh last TwoBatch call gives $\widehat Z$, and the output minimizes diamond distance to $Φ_{\bar σ}(\widehat Z)$ over all channels, without imposing a rank bound.
--
--   The recursive execution measure stores only classical data, newest first, and performs exactly $Q=2n(T+1)$ channel uses and $T$ adaptive updates. It retains the clipping step on every outcome. Measurability, normalization, and the channel output guarantee are conclusions of the goal rather than fields of a supplied successful learner.
-- source:
--   Aadil Oufkir, Kean Chen, STOC 2027 submission #364 (October 2026), §3.2, (42), Algorithm 3 and Theorem 3.4, printed pp. 19–20 = PDF pp. 19–20; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/364.pdf

import Definitions.Def_LowRankIncoherent_Adaptive_Experiment

open Matrix MeasureTheory
open scoped MatrixOrder ComplexOrder ENNReal
noncomputable section

namespace LowRankIncoherent.Adaptive

/-- The standard countable disjoint union σ-algebra on finite classical transcripts. -/
instance transcriptMeasurable (α : Type) [MeasurableSpace α] : MeasurableSpace (List α) :=
  MeasurableSpace.map (fun z : Σ n : ℕ, Fin n → α => List.ofFn z.2) inferInstance

/-- Only the two unspecified structural choices in Algorithm 3: tied rank truncation
and a nearest-channel minimizer. Neither function takes the unknown channel. -/
structure Choices (a b : ℕ) where
  truncate : Joint a b → Joint a b
  nearest : Joint a b → Joint a b

/-- Structural requirements, with no accuracy or probability bound. Existence is a
conclusion of the goal, not a hypothesis or an oracle provided to the learner. -/
def Admissible {a b : ℕ} (r : ℕ) (p : Choices a b) : Prop :=
  Measurable p.truncate ∧
  (∀ X, X.IsHermitian → IsTruncation r X (p.truncate X)) ∧
  Measurable p.nearest ∧
  (∀ X, (unchoi (p.nearest X)) ∈ ChanTomoNB.QChan (a*b) a b ∧
    ∀ F ∈ ChanTomoNB.QChan (a*b) a b,
      ChanTomoNB.diamondDist (unchoi (p.nearest X)) (unchoi X) ≤
        ChanTomoNB.diamondDist F (unchoi X))

def update {a : ℕ} (ρ A : Input a) : Input a :=
  let V := expM (logM ρ + logM A)
  (1 / (rt V : ℂ)) • V

def clip {a : ℕ} (r : ℕ) (H : Input a) : Input a :=
  cfc (fun x : ℝ => max x ((r : ℝ)/2)) (H + (r : ℂ) • 1)

def rounds (a : ℕ) : ℕ := max 1 ⌈Real.log (a : ℝ) / Real.log 2⌉₊

def scale (r : ℕ) (ε : ℝ) : ℝ := ε / (64 * r)

def budgetB (a b r : ℕ) (δ : ℝ) : ℝ :=
  a*b + (1 + (a : ℝ)/r) * Real.log (6/δ)

def batchSize (K : ℝ) (a b r : ℕ) (s δ : ℝ) : ℕ := ⌈K * budgetB a b r δ / s^2⌉₊

def algN (K : ℝ) (a b r : ℕ) (ε δ : ℝ) : ℕ :=
  batchSize K a b r (scale r ε) (δ / (rounds a + 1))

def queries (K : ℝ) (a b r : ℕ) (ε δ : ℝ) : ℕ :=
  2 * algN K a b r ε δ * (rounds a + 1)

def printedBound (c : ℝ) (a b r : ℕ) (ε δ : ℝ) : ℝ :=
  c * ((r : ℝ)^2 / ε^2) * Real.log (2*a) *
    (a*b + (1 + (a : ℝ)/r) * Real.log (18 * Real.log (2*a) / δ))

/-- State recursion uses only the classical measurement transcript, including on bad
estimation events. Clipping is always executed, before the logarithm. -/
def rhoFrom {a b n : ℕ} (p : Choices a b) (r : ℕ) (s : ℝ) :
    List (BatchPair (Fin b × Fin a) n) → Input a
  | [] => (1 / (a : ℂ)) • 1
  | z :: zs =>
      let ρ := rhoFrom p r s zs
      let H := (twoBatch p.truncate (mixture ρ) s z).2
      update ρ (clip r H)

/-- Transcripts are stored newest first; each extension samples both batches freshly
conditional on its entire earlier classical transcript. -/
def selectionLaw {a b n : ℕ} (p : Choices a b) (E : Map a b) (r : ℕ) (s : ℝ) :
    ℕ → Measure (List (BatchPair (Fin b × Fin a) n))
  | 0 => Measure.dirac []
  | t+1 => (selectionLaw p E r s t).bind (fun zs =>
      (pairLaw (outputState E (mixture (rhoFrom p r s zs))) n).map (fun z => z :: zs))

/-- The average uses the input BEFORE each update, exactly σ_1,...,σ_T. -/
def sumInputs {a b n : ℕ} (p : Choices a b) (r : ℕ) (s : ℝ) :
    List (BatchPair (Fin b × Fin a) n) → Input a
  | [] => 0
  | _ :: zs => mixture (rhoFrom p r s zs) + sumInputs p r s zs

def finalInput {a b n : ℕ} (p : Choices a b) (r : ℕ) (s : ℝ)
    (zs : List (BatchPair (Fin b × Fin a) n)) : Input a :=
  (1 / (rounds a : ℂ)) • sumInputs p r s zs

/-- Full transcript includes T selection calls and one final, independent TwoBatch call. -/
def executionLaw {a b : ℕ} (K : ℝ) (p : Choices a b) (E : Map a b)
    (r : ℕ) (ε δ : ℝ) :
    Measure (List (BatchPair (Fin b × Fin a) (algN K a b r ε δ)) ×
      BatchPair (Fin b × Fin a) (algN K a b r ε δ)) :=
  (selectionLaw p E r (scale r ε) (rounds a)).bind (fun zs =>
    (pairLaw (outputState E (finalInput p r (scale r ε) zs)) (algN K a b r ε δ)).map
      (fun z => (zs,z)))

def decode {a b : ℕ} (K : ℝ) (p : Choices a b) (r : ℕ) (ε δ : ℝ)
    (data : List (BatchPair (Fin b × Fin a) (algN K a b r ε δ)) ×
      BatchPair (Fin b × Fin a) (algN K a b r ε δ)) : Joint a b :=
  let σ := finalInput p r (scale r ε) data.1
  let Z := (twoBatch p.truncate σ (scale r ε) data.2).1
  p.nearest (whiten σ Z)

end LowRankIncoherent.Adaptive


