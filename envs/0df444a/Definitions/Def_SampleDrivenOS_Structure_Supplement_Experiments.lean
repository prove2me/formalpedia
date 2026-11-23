-- Prove2me | Definitions.Def_SampleDrivenOS_Structure_Supplement_Experiments
-- name    : SampleDrivenOS_Structure_Supplement_Experiments
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:39:09.171787+00:00
-- url     : https://prove2.me/theorems/57a28acb-9099-401a-8e4b-0f89f5b899c4
-- title:
--   Finite rank policies, sampling experiments and competitive ratios
-- statement:
--   Consider N totally ranked items with nonincreasing nonnegative weights Y₁,…,Y_N. A behavioral policy receives the history size h and the successive relative ranks of the online items among all items observed so far, including the history. Its acceptance probability lies in [0,1]; independent coins implement those probabilities. It has no access to unrevealed global ranks or the adversary's weights.
--
--   For a uniform permutation σ, its probability of first stopping at step i is its current acceptance probability multiplied by all earlier rejection probabilities. The realized reward is the selected weight; no stop returns 0. The offline reward is the largest weight outside the history, also defaulting to 0 when that set is empty. Dependent sampling uses the first h=⌊pN⌋ positions. Independent sampling is the binomial mixture over h of these uniform-permutation experiments.
--
--   Write R(A,Y) and O(Y) for the resulting expected algorithm and offline rewards. The values are
--   $$
--   \beta_{N,p}=\sup_A\inf_{Y:O(Y)>0}\frac{R(A,Y)}{O(Y)},\qquad
--   \alpha_{N,p}=\sup_A\inf_{Y:O(Y)>0}\frac{R(A,Y)}{O(Y)}
--   $$
--   with their respective sampling laws. Define β(p) as the infimum of β_{N,p} over positive N; Theorem 12 identifies this infimum with the limit. The independently defined continuous value α(p) is the published SDCLP value, not a synonym for β(p).
--
--   These definitions supply actual adapted policy expectations for the finite-to-continuous comparisons. Finite histories make behavioral randomization sufficient for every randomized rank policy.
--
--   **Formalization Note** Item labels and permutation positions use `Fin N`, hence start at zero; all paper-facing rank parameters are one-based. The zero instance is omitted only from ratios. For N≥1 and 0≤p<1 (or h<N), the denominator-positive weight domain is nonempty, and ratios and optimal values lie in [0,1]. Suprema and infima are consequently genuine bounded extrema. The zero default is the adversarial convention justified on printed p. 14; this is not the unrestricted known-values problem with possibly negative weights.
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, pp. 4–5, §§2.1–2.3; p. 14, zero-default convention

import Mathlib

open MeasureTheory Set
open scoped BigOperators

namespace SampleDrivenOS.Structure.Supplement

noncomputable section
open Classical

/-- A behavioral stopping policy. At an online arrival it knows the sample size and the
successive relative ranks of online arrivals among all items seen, including the sample.
The number of items is known. Independent coins implement the given probabilities. -/
structure RankPolicy (N : ℕ) where
  accept : ℕ → List ℕ → ℝ
  nonneg : ∀ h rs, 0 ≤ accept h rs
  le_one : ∀ h rs, accept h rs ≤ 1

/-- Global rank at a permutation position; the total extension is never used outside `[0,N)`. -/
def itemAt {N : ℕ} (σ : Equiv.Perm (Fin N)) (i : ℕ) : ℕ :=
  if hi : i < N then (σ ⟨i, hi⟩).val else N

def relativeRank {N : ℕ} (σ : Equiv.Perm (Fin N)) (i : ℕ) : ℕ :=
  1 + ((Finset.range i).filter (fun b => itemAt σ b < itemAt σ i)).card

/-- No global identities or unrevealed ranks are arguments to the policy. -/
def rankHistory {N : ℕ} (σ : Equiv.Perm (Fin N)) (h i : ℕ) : List ℕ :=
  ((List.range (i + 1)).drop h).map (relativeRank σ)

/-- Conditional probability of stopping at position i, obtained by executing the policy's
independent behavioral coins along this permutation. Positions and labels here are zero-based. -/
def stopMass {N : ℕ} (A : RankPolicy N) (σ : Equiv.Perm (Fin N)) (h i : ℕ) : ℝ :=
  if h ≤ i ∧ i < N then
    A.accept h (rankHistory σ h i) *
      ∏ s ∈ Finset.Ico h i, (1 - A.accept h (rankHistory σ h s))
  else 0

def rewardAt {N : ℕ} (A : RankPolicy N) (w : Fin N → ℝ)
    (σ : Equiv.Perm (Fin N)) (h : ℕ) : ℝ :=
  ∑ i : Fin N, stopMass A σ h i.val * w (σ i)

/-- Maximum online weight, with zero default. Inserting 0 makes the maximum defined also
for an empty online set and for the empty ground set. -/
def offlineAt {N : ℕ} (w : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) (h : ℕ) : ℝ :=
  (insert 0 ((Finset.univ.filter (fun i : Fin N => h ≤ i.val)).image (fun i => w (σ i)))).max'
    (by simp)

/-- Uniform permutation expectation. Even N=0 has one permutation. -/
def permAverage (N : ℕ) (f : Equiv.Perm (Fin N) → ℝ) : ℝ :=
  (∑ σ : Equiv.Perm (Fin N), f σ) / (Fintype.card (Equiv.Perm (Fin N)) : ℝ)

def dependentReward {N : ℕ} (h : ℕ) (A : RankPolicy N) (w : Fin N → ℝ) : ℝ :=
  permAverage N (fun σ => rewardAt A w σ h)

def dependentOffline {N : ℕ} (h : ℕ) (w : Fin N → ℝ) : ℝ :=
  permAverage N (fun σ => offlineAt w σ h)

def binomialMass (N h : ℕ) (p : ℝ) : ℝ :=
  (N.choose h : ℝ) * p ^ h * (1 - p) ^ (N - h)

/-- Bernoulli sampling is a binomial mixture of the uniform-size experiments; the policy
observes the realized history size. -/
def independentReward {N : ℕ} (p : ℝ) (A : RankPolicy N) (w : Fin N → ℝ) : ℝ :=
  ∑ h ∈ Finset.range (N + 1), binomialMass N h p * dependentReward h A w

def independentOffline {N : ℕ} (p : ℝ) (w : Fin N → ℝ) : ℝ :=
  ∑ h ∈ Finset.range (N + 1), binomialMass N h p * dependentOffline h w

def IsWeights {N : ℕ} (w : Fin N → ℝ) : Prop :=
  (∀ j, 0 ≤ w j) ∧ Antitone w

/-- The zero instance is omitted only because its offline denominator is zero. All positive
instances, without a normalization or a fixed gap between distinct weights, are retained. -/
def independentRatio {N : ℕ} (p : ℝ) (A : RankPolicy N) : ℝ :=
  sInf {r : ℝ | ∃ w : Fin N → ℝ, IsWeights w ∧ 0 < independentOffline p w ∧
    r = independentReward p A w / independentOffline p w}

def dependentRatio {N : ℕ} (h : ℕ) (A : RankPolicy N) : ℝ :=
  sInf {r : ℝ | ∃ w : Fin N → ℝ, IsWeights w ∧ 0 < dependentOffline h w ∧
    r = dependentReward h A w / dependentOffline h w}

def betaFinite (N : ℕ) (p : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ A : RankPolicy N, r = independentRatio p A}

def alphaFinite (N : ℕ) (p : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ A : RankPolicy N, r = dependentRatio ⌊p * (N : ℝ)⌋₊ A}

/-- Infimum of the finite independent optima. Theorem 12 identifies it as their limit,
and identifies it with the separately published continuous value. -/
def betaValue (p : ℝ) : ℝ := sInf (Set.range (fun n : ℕ => betaFinite (n + 1) p))

end
end SampleDrivenOS.Structure.Supplement


