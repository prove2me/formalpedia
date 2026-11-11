-- Prove2me | Definitions.Def_SatisfiableOrderingCSP_Optimal_Multislices
-- name    : SatisfiableOrderingCSP_Optimal_Multislices
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:47:51.949411+00:00
-- url     : https://prove2.me/theorems/e1a004d9-b977-489f-a711-a512eb2c3ef1
-- title:
--   Multislice noise, noisy influences, real rank prefixes, and buckets
-- statement:
--   A histogram records the count of each symbol, summing to the common string length. Its multislice contains exactly the strings with that histogram, with uniform mean. A balanced histogram has positive length and each supported frequency at least alpha. Noise selects the specified number of positions independently and uniformly in each supported symbol class and changes their symbols cyclically; noisy influence is the average squared change of the smoothed function under a transposition involving a fixed coordinate. Pairing laws permit arbitrary fiber names but require uniform unlabeled pair partitions. A score kernel assigns a probability measure on the real line to each string, representing arbitrary private randomness. Its rank prefix is the conditional probability of a score at most z, and continuity means continuity of the mixture CDF. Influential prefixes range over every real threshold and every base variable. Ordered buckets partition the real line into ordered intervals; acceptance requires the existence of distinct scores in the indicated intervals satisfying the predicate, including coincident bucket labels.
-- source:
--   Yury Makarychev (2026), Optimal Approximation Algorithms For Satisfiable Ordering CSPs, held STOC 2027 submission (not an acceptance claim), sha256:e49b7905adb41a36b93abcbd7818d1b18ca86a77dff069da884ba2f8e85775cc; citation_basis: published; §§7.4–7.5, Lemma 7.8; pp. 43–45, 48 (PDF 46–48, 51)

import Definitions.Def_SatisfiableOrderingCSP_Optimal_RichGames

open scoped BigOperators

namespace SatisfiableOrderingCSP.Optimal
noncomputable section
attribute [local instance] Classical.propDecidable

structure Histogram (n q : ℕ) where
  count : Fin q → ℕ
  total : ∑ a, count a = n

def Histogram.strings {n q : ℕ} (H : Histogram n q) : Finset (Fin n → Fin q) :=
  Finset.univ.filter fun x => ∀ a, (Finset.univ.filter fun i => x i = a).card = H.count a

def Histogram.mean {n q : ℕ} (H : Histogram n q) (f : (Fin n → Fin q) → ℝ) : ℝ :=
  (∑ x ∈ H.strings, f x) / (H.strings.card : ℝ)

def Histogram.Balanced {n q : ℕ} (H : Histogram n q) (α : ℝ) : Prop :=
  0 < n ∧ ∀ a, 0 < H.count a → α * n ≤ H.count a

def Histogram.support {n q : ℕ} (H : Histogram n q) : Finset (Fin q) :=
  Finset.univ.filter fun a => 0 < H.count a

def Histogram.nextSymbol {n q : ℕ} (H : Histogram n q) (a : Fin q) : Fin q :=
  if h : (H.support.filter (fun b => a < b)).Nonempty then
    (H.support.filter (fun b => a < b)).min' h
  else if h : H.support.Nonempty then H.support.min' h else a

def Histogram.noiseChoices {n q : ℕ} (H : Histogram n q) (d : ℕ) (x : Fin n → Fin q) :
    Finset (Fin q → Finset (Fin n)) :=
  Finset.univ.filter fun A => ∀ a,
    A a ⊆ (Finset.univ.filter fun i => x i = a) ∧
    (A a).card = if 0 < H.count a then d else 0

def Histogram.noise {n q : ℕ} (H : Histogram n q) (d : ℕ)
    (f : (Fin n → Fin q) → ℝ) (x : Fin n → Fin q) : ℝ :=
  let choices := H.noiseChoices d x
  (∑ A ∈ choices, f (fun i => if i ∈ A (x i) then H.nextSymbol (x i) else x i)) /
    (choices.card : ℝ)

def Histogram.influence {n q : ℕ} (H : Histogram n q)
    (f : (Fin n → Fin q) → ℝ) (i : Fin n) : ℝ :=
  (∑ j, H.mean (fun x => (f (x ∘ Equiv.swap i j) - f x)^2)) / (n : ℝ)

def Histogram.noisyInfluence {n q : ℕ} (H : Histogram n q) (d : ℕ)
    (f : (Fin n → Fin q) → ℝ) (i : Fin n) : ℝ := H.influence (H.noise d f) i

def Histogram.NoiseValid {n q : ℕ} (H : Histogram n q) (d : ℕ) : Prop :=
  0 < n ∧ 0 < d ∧ ∀ a, 0 < H.count a → d ≤ H.count a

def linkedCount (b : ℝ) (N : ℕ) : ℕ := ⌊b * N / 2⌋₊

def PairingLaw {N : ℕ} (p : (Fin N → Fin (N/2)) → ℝ) : Prop :=
  FuchsVdGraaf.IsProbDist p ∧ (∀ π, 0 < p π → TwoToOne π) ∧
  ∀ P ∈ pairPartitions N,
    (∑ π, if fiberPartition π = P then p π else 0) = 1 / ((pairPartitions N).card : ℝ)

def Histogram.EvenCounts {n q : ℕ} (H : Histogram n q) : Prop := ∀ a, Even (H.count a)

def HalfHistogram {N q : ℕ} (H : Histogram N q) (h : Histogram (N/2) q) : Prop :=
  ∀ a, 2 * h.count a = H.count a

/-- Conditional laws represent all private randomness without imposing a finite score support. -/
abbrev ScoreKernel (n q : ℕ) := (Fin n → Fin q) → MeasureTheory.ProbabilityMeasure ℝ

def rankPrefix {n q : ℕ} (R : ScoreKernel n q) (z : ℝ) (x : Fin n → Fin q) : ℝ :=
  (R x).toMeasure.real (Set.Iic z)

def ContinuousScore {n q : ℕ} (H : Histogram n q) (R : ScoreKernel n q) : Prop :=
  Continuous (fun z : ℝ => H.mean (rankPrefix R z))

def influentialPrefixes {n n₀ : ℕ} {q : Fin n₀ → ℕ}
    (H : (v : Fin n₀) → Histogram n (q v)) (d : ℕ)
    (R : (v : Fin n₀) → ScoreKernel n (q v)) (lam : ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun i => ∃ (v : Fin n₀) (z : ℝ),
    lam ≤ (H v).noisyInfluence d (rankPrefix (R v) z) i

structure OrderedBuckets (K : ℕ) where
  region : Fin K → Set ℝ
  partition : ∀ x : ℝ, ∃! a, x ∈ region a
  interval : ∀ a, Set.OrdConnected (region a)
  ordered : ∀ a b, a < b → ∀ x ∈ region a, ∀ y ∈ region b, x < y

def bucketAccepts {K : ℕ} (B : OrderedBuckets K) (φ : Predicate)
    (labels : Fin φ.arity → Fin K) : Prop :=
  ∃ x : Fin φ.arity → ℝ, Function.Injective x ∧
    (∀ i, x i ∈ B.region (labels i)) ∧ φ.Accepts x

end
end SatisfiableOrderingCSP.Optimal


