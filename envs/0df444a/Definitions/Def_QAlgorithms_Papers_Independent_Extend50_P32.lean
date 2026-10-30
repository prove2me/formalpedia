-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P32
-- name    : QAlgorithms_Papers_Independent_Extend50_P32
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T09:29:07.737535+00:00
-- url     : https://prove2.me/theorems/1cef79e4-5403-4dac-89ef-68cf88da0b4f
-- title:
--   Definitions for Efficient quantum tomography II
-- statement:
--   The objects the formalized statements of *Efficient quantum tomography II* (arXiv:1612.00034) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `insertRow`: Bump the first strictly greater letter, retaining original occurrence IDs; equality does not bump (PDF pp.2,28-29).
--   - `insertRows`: Propagate insertion. Each log entry records row exited, input time, and bumped occurrence (PDF pp.4,28-29).
--   - `rskRun`: Execute actual RSK from the empty tableau; bump logs are chronological and carry original occurrence identities (PDF pp.2,4,28).
--   - `shape`: Computed Young row list, padded by zero via `row` (PDF p.2).
--   - `row`: Zero-padded real row length (PDF p.2).
--   - `rowPrefix`: First k row total (PDF p.11).
--   - `WeakDominates`: Prefix comparison of sorted Young rows, not containment (PDF p.4).
--   - `shapeDominates`: Dominance includes equal total size (PDF p.4).
--   - `bumpedTokens`: Chronological occurrences bumped out of zero-based row j (PDF pp.4,28).
--   - `bumpedWord`: Bump-order word, forgetting IDs after selection (PDF pp.4,28).
--   - `originalBumpedWord`: Stable original-word restriction to bumped occurrence IDs; equal values are never conflated (PDF pp.4,28).
--   - `wordMean`: Finite iid expectation, including the unique empty word (PDF p.2).
--   - `swMean`: Combinatorial SW expectation: pushforward of iid words by computed RSK, independent of physical weak-Schur probabilities (PDF p.2).
--   - `swMeanExt`: Extended SW expectation; zero-weight impossible words contribute zero even if their loss is infinite (PDF pp.2,12).
--   - `iidWordEventProbability`: Finite word-event probability (PDF pp.2,19).
--   - `prefixMass`: Prefix mass without renormalization (PDF p.11).
--   - `tail`: Mass strictly after the first k entries (PDF pp.7,11).
--   - `normalizedShapeRows`: Normalized padded rows; all normalized-diagram statements require n>0 (PDF pp.3-4).
--   - `h2`: Truncated classical Hellinger squared, no factor 1/2 (PDF p.12).
--   - `l2`: Truncated squared Euclidean loss (PDF p.12).
--   - `chiTerm`: Chi-squared summand: 0/0 contributes zero; a positive estimate at zero true probability contributes infinity (PDF p.12).
--   - `chi2`: Truncated chi-squared, estimate first and truth second (PDF p.12).
--   - `kl`: KL in nats: support violations give infinity and zero estimated mass gives zero. Signed summands are summed BEFORE conversion, not individually clipped (PDF p.12).
--   - `FullMetric`: Full loss choices (PDF pp.4,6).
--   - `fullLoss`: Source full losses, with their specified argument order (PDF p.12).
--   - `WeightedMetric`: Weighted truncated loss choices (PDF pp.4,7).
--   - `weightedLoss`: Already-truncated weighted loss (PDF p.4).
--   - `truncatedTV`: Truncated TV: half the first-k absolute differences, no tail bin. OW16, arXiv:1508.01907v2 PDF p.3, Theorem 1.7 explicitly defines this convention; this paper's PDF p.4 uses it by reference.
--   - `prefixExcess`: Unnormalized expected prefix excess (PDF pp.5,11,13).
--   - `normalizedExcess`: Normalized expected prefix excess (PDF p.22).
--   - `spectralPrefixExcessLimit`: Excess is infinite at any tied cutoff, including tied zero, following the p.15 proof. The sum is empty at k=d (PDF pp.14-15).
--   - `rowScale`: Uniform row scale nu_k (PDF p.3).
--   - `rowMSE`: Unnormalized row mean squared error (PDF pp.3,20).
--   - `rowVariance`: Variance about the row's own mean (PDF p.19).
--   - `histogram`: Word histogram (PDF pp.13-14).
--   - `modifiedDensity`: Relative SIGNED density phi, with alpha_j cancelled before evaluation at zero last mass. Used only with n>0 and distinct probabilities (PDF pp.13-15).
--   - `modifiedMean`: Modified multinomial signed expectation, not a probability measure (PDF p.14).
--   - `prefixWord`: Stable word restriction to the first k letters (PDF p.16).
--   - `suffixWord`: Stable word restriction to source letters >=k (PDF p.16).
--   - `quantumH2`: Quantum Hellinger squared for PSD matrices, including subnormalized reports, with no factor 1/2 (PDF pp.13,25).
--   - `affinity`: Quantum affinity, distinct from root fidelity (PDF p.13).
--   - `truncatedReport`: Rank-k Keyl report, WITHOUT renormalizing the truncated rows (PDF pp.22,25).
--   - `keylRisk`: Extended Hellinger risk under the concrete Keyl joint Born law, not Haar alone or a law chosen for accuracy (PDF pp.22-27).
--   - `keylSuccess`: Success under the same public Keyl decoder (PDF pp.6-7).
--   - `copyBudget`: Integer copy budget, rounding a real bound upward (PDF pp.6-7).
--   - `InducedPermutation`: Any measurable Birkhoff decomposition of |V_(a,i)|^2, with pi(i)=a. No accuracy property is assumed; the theorem is independent of the choice (PDF p.23).
--   - `keylMean`: Keyl real expectation. All uses below are bounded continuous statistics or bounded measurable permutation mixtures, hence integrable (PDF p.23).
--   - `permutationMean`: Conditional permutation expectation in eigenbasis B; weights use B dagger V, rather than a unitary in an unrelated basis (PDF pp.23,25).
--   - `eydRisk`: Physical EYD risk; weak-Schur projectors and decoder are fixed before the unknown state. The law depends only on its spectrum (PDF pp.5-6).
--   - `eydSuccess`: Success event for the same physical EYD experiment (PDF pp.6-7).
--   - `ProperIncreasingCurve`: Proper increasing graphs; no smoothness restriction (PDF p.30).
--   - `wordPoints`: Original-word graph points (PDF p.29).
--   - `firstBumpPoints`: Black skeleton points keep the input TIME of the bump as horizontal coordinate, rather than being reindexed in the shorter word (PDF p.29). This coordinate differs from the bumped occurrence's own original position.
--   - `IsChains`: Disjoint increasing chains as sets of occurrence indices; empty chains and the empty family are allowed (PDF pp.2,28).
--   - `CurvesThrough`: Proper graphs pass through every selected occurrence and are pairwise disjoint on the whole real line (PDF p.30).
--   - `AdmissibleChains`: Full admissibility invariant (19): chains are admissible and every inadmissible point is strictly southeast of the southeasternmost curve. No output-existence certificate is built into this predicate (PDF pp.28-30).
--   - `adjacentProbabilityMultiplier`: Adjacent multiplier in Lemmas 5.3-5.4; defined only for an actual pair of consecutive indices (PDF p.24).
--   - `flooredEntry`: Floored list from the proof of Corollary 5.5; its first k entries stay unchanged and the next entry is zeta under the cutoff assumptions (PDF p.25).
-- source:
--   Efficient quantum tomography II, arXiv:1612.00034v1, https://arxiv.org/abs/1612.00034v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Learning
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_KeylTomography
import Definitions.Def_QAlgorithms_Defs_SchurWeylMeasurements
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P38
import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P17

/-! O'Donnell--Wright, Efficient quantum tomography II, arXiv:1612.00034v1.
All citations use PDF pages. Internal letter/row indices are zero based;
a prefix parameter k counts k entries. New definitions belong only to this paper. -/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators ENNReal Matrix ComplexOrder Topology

namespace QAlgorithms.Papers.Independent.Extend50.P32

-- Reuse exact iid product mass and half-l1 TV from the pinned accepted library.
open QAlgorithms.Papers.Independent.Support50.P38 (wordMass tv)

-- For the density matrices below, the characteristic-polynomial identity
-- preserves all eigenvalues with multiplicity and is equivalent to unitary
-- diagonalization with these real eigenvalues. No accuracy is assumed.
open QAlgorithms.Papers.Independent.Gap20.P17 (HasSpectrum)

/-- Bump the first strictly greater letter, retaining original occurrence IDs;
equality does not bump (PDF pp.2,28-29). -/
def insertRow {A : Type*} [LinearOrder A] (a : A × ℕ) :
    List (A × ℕ) → List (A × ℕ) × Option (A × ℕ)
  | [] => ([a], none)
  | b :: row => if a.1 < b.1 then (a :: row, some b)
    else let r := insertRow a row; (b :: r.1, r.2)

/-- Propagate insertion. Each log entry records row exited, input time,
and bumped occurrence (PDF pp.4,28-29). -/
def insertRows {A : Type*} [LinearOrder A] (j t : ℕ) (a : A × ℕ) :
    List (List (A × ℕ)) → List (List (A × ℕ)) × List (ℕ × ℕ × (A × ℕ))
  | [] => ([[a]], [])
  | row :: rows =>
    let r := insertRow a row
    match r.2 with
    | none => (r.1 :: rows, [])
    | some b =>
      let s := insertRows (j + 1) t b rows
      (r.1 :: s.1, (j, t, b) :: s.2)

/-- Execute actual RSK from the empty tableau; bump logs are chronological
and carry original occurrence identities (PDF pp.2,4,28). -/
def rskRun {A : Type*} [LinearOrder A] (w : List A) :
    List (List (A × ℕ)) × List (ℕ × ℕ × (A × ℕ)) :=
  w.zipIdx.foldl (fun st a =>
    let r := insertRows 0 a.2 a st.1
    (r.1, st.2 ++ r.2)) ([], [])

/-- Computed Young row list, padded by zero via `row` (PDF p.2). -/
def shape {A : Type*} [LinearOrder A] (w : List A) : List ℕ :=
  (rskRun w).1.map List.length

/-- Zero-padded real row length (PDF p.2). -/
def row (s : List ℕ) (i : ℕ) : ℝ := ((s[i]?).getD 0 : ℕ)

/-- First k row total (PDF p.11). -/
def rowPrefix (s : List ℕ) (k : ℕ) : ℝ := (s.take k).sum

/-- Prefix comparison of sorted Young rows, not containment (PDF p.4). -/
def WeakDominates (s t : List ℕ) : Prop := ∀ k : ℕ, (t.take k).sum ≤ (s.take k).sum

/-- Dominance includes equal total size (PDF p.4). -/
def shapeDominates (s t : List ℕ) : Prop := s.sum = t.sum ∧ WeakDominates s t

/-- Chronological occurrences bumped out of zero-based row j (PDF pp.4,28). -/
def bumpedTokens {A : Type*} [LinearOrder A] (w : List A) (j : ℕ) : List (A × ℕ) :=
  ((rskRun w).2.filter (fun e => e.1 = j)).map (fun e => e.2.2)

/-- Bump-order word, forgetting IDs after selection (PDF pp.4,28). -/
def bumpedWord {A : Type*} [LinearOrder A] (w : List A) (j : ℕ) : List A :=
  (bumpedTokens w j).map Prod.fst

/-- Stable original-word restriction to bumped occurrence IDs; equal values
are never conflated (PDF pp.4,28). -/
def originalBumpedWord {A : Type*} [LinearOrder A] (w : List A) (j : ℕ) : List A :=
  (w.zipIdx.filter (fun a => a.2 ∈ (bumpedTokens w j).map Prod.snd)).map Prod.fst

/-- Finite iid expectation, including the unique empty word (PDF p.2). -/
def wordMean {d : ℕ} (alpha : Fin d → ℝ) (n : ℕ) (F : List (Fin d) → ℝ) : ℝ :=
  ∑ w : Fin n → Fin d, wordMass alpha w * F (List.ofFn w)

/-- Combinatorial SW expectation: pushforward of iid words by computed RSK,
independent of physical weak-Schur probabilities (PDF p.2). -/
def swMean {d : ℕ} (alpha : Fin d → ℝ) (n : ℕ) (F : List ℕ → ℝ) : ℝ :=
  wordMean alpha n (fun w => F (shape w))

/-- Extended SW expectation; zero-weight impossible words contribute zero
even if their loss is infinite (PDF pp.2,12). -/
def swMeanExt {d : ℕ} (alpha : Fin d → ℝ) (n : ℕ) (F : List ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ w : Fin n → Fin d, ENNReal.ofReal (wordMass alpha w) * F (shape (List.ofFn w))

/-- Finite word-event probability (PDF pp.2,19). -/
def iidWordEventProbability {d : ℕ} (alpha : Fin d → ℝ) (n : ℕ) (P : List (Fin d) → Prop) : ℝ := by
  classical
  exact wordMean alpha n (fun w => if P w then 1 else 0)

/-- Prefix mass without renormalization (PDF p.11). -/
def prefixMass {d : ℕ} (alpha : Fin d → ℝ) (k : ℕ) : ℝ :=
  ∑ i, if i.val < k then alpha i else 0

/-- Mass strictly after the first k entries (PDF pp.7,11). -/
def tail {d : ℕ} (alpha : Fin d → ℝ) (k : ℕ) : ℝ :=
  ∑ i, if k ≤ i.val then alpha i else 0

/-- Normalized padded rows; all normalized-diagram statements require n>0 (PDF pp.3-4). -/
def normalizedShapeRows {d : ℕ} (n : ℕ) (s : List ℕ) : Fin d → ℝ := fun i => row s i.val / n

/-- Truncated classical Hellinger squared, no factor 1/2 (PDF p.12). -/
def h2 {d : ℕ} (k : ℕ) (a b : Fin d → ℝ) : ℝ :=
  ∑ i, if i.val < k then (Real.sqrt (a i) - Real.sqrt (b i)) ^ 2 else 0

/-- Truncated squared Euclidean loss (PDF p.12). -/
def l2 {d : ℕ} (k : ℕ) (a b : Fin d → ℝ) : ℝ :=
  ∑ i, if i.val < k then (a i - b i) ^ 2 else 0

/-- Chi-squared summand: 0/0 contributes zero; a positive estimate at zero
true probability contributes infinity (PDF p.12). -/
def chiTerm (a b : ℝ) : ℝ≥0∞ :=
  if b = 0 then (if a = 0 then 0 else ⊤) else ENNReal.ofReal ((a - b) ^ 2 / b)

/-- Truncated chi-squared, estimate first and truth second (PDF p.12). -/
def chi2 {d : ℕ} (k : ℕ) (a b : Fin d → ℝ) : ℝ≥0∞ :=
  ∑ i, if i.val < k then chiTerm (a i) (b i) else 0

/-- KL in nats: support violations give infinity and zero estimated mass gives
zero. Signed summands are summed BEFORE conversion, not individually clipped (PDF p.12). -/
def kl {d : ℕ} (a b : Fin d → ℝ) : ℝ≥0∞ := by
  classical
  exact if ∃ i, a i ≠ 0 ∧ b i = 0 then ⊤ else ENNReal.ofReal
    (∑ i, if a i = 0 then 0 else a i * Real.log (a i / b i))

/-- Full loss choices (PDF pp.4,6). -/
inductive FullMetric where
  | hellinger | kullbackLeibler | chiSquared
  deriving DecidableEq

/-- Source full losses, with their specified argument order (PDF p.12). -/
def fullLoss {d : ℕ} (metric : FullMetric) (a b : Fin d → ℝ) : ℝ≥0∞ :=
  match metric with
  | .hellinger => ENNReal.ofReal (h2 d a b)
  | .kullbackLeibler => kl a b
  | .chiSquared => chi2 d a b

/-- Weighted truncated loss choices (PDF pp.4,7). -/
inductive WeightedMetric where
  | hellinger | chiSquared
  deriving DecidableEq

/-- Already-truncated weighted loss (PDF p.4). -/
def weightedLoss {d : ℕ} (metric : WeightedMetric) (k : ℕ) (a b : Fin d → ℝ) : ℝ≥0∞ :=
  match metric with
  | .hellinger => ENNReal.ofReal (h2 k a b)
  | .chiSquared => chi2 k a b

/-- Truncated TV: half the first-k absolute differences, no tail bin.
OW16, arXiv:1508.01907v2 PDF p.3, Theorem 1.7 explicitly defines this
convention; this paper's PDF p.4 uses it by reference. -/
def truncatedTV {d : ℕ} (k : ℕ) (a b : Fin d → ℝ) : ℝ :=
  (∑ i, if i.val < k then |a i - b i| else 0) / 2

/-- Unnormalized expected prefix excess (PDF pp.5,11,13). -/
def prefixExcess {d : ℕ} (alpha : Fin d → ℝ) (k n : ℕ) : ℝ :=
  swMean alpha n (fun s => rowPrefix s k) - prefixMass alpha k * n

/-- Normalized expected prefix excess (PDF p.22). -/
def normalizedExcess {d : ℕ} (alpha : Fin d → ℝ) (k n : ℕ) : ℝ := prefixExcess alpha k n / n

/-- Excess is infinite at any tied cutoff, including tied zero, following
the p.15 proof. The sum is empty at k=d (PDF pp.14-15). -/
def spectralPrefixExcessLimit {d : ℕ} (alpha : Fin d → ℝ) (k : ℕ) : ℝ≥0∞ :=
  ∑ i, ∑ j, if i.val < k ∧ k ≤ j.val then
    (if alpha i = alpha j then ⊤ else ENNReal.ofReal (alpha j / (alpha i - alpha j))) else 0

/-- Uniform row scale nu_k (PDF p.3). -/
def rowScale {d : ℕ} (alpha : Fin d → ℝ) (k : Fin d) : ℝ := min 1 (alpha k * d)

/-- Unnormalized row mean squared error (PDF pp.3,20). -/
def rowMSE {d : ℕ} (alpha : Fin d → ℝ) (n : ℕ) (k : Fin d) : ℝ :=
  swMean alpha n (fun s => (row s k.val - alpha k * n) ^ 2)

/-- Variance about the row's own mean (PDF p.19). -/
def rowVariance {d : ℕ} (alpha : Fin d → ℝ) (n : ℕ) (k : Fin d) : ℝ :=
  swMean alpha n (fun s => (row s k.val - swMean alpha n (fun t => row t k.val)) ^ 2)

/-- Word histogram (PDF pp.13-14). -/
def histogram {d : ℕ} (w : List (Fin d)) : Fin d → ℝ := fun i => (w.count i : ℕ)

/-- Relative SIGNED density phi, with alpha_j cancelled before evaluation at
zero last mass. Used only with n>0 and distinct probabilities (PDF pp.13-15). -/
def modifiedDensity {d : ℕ} (alpha : Fin d → ℝ) (n : ℕ) (h : Fin d → ℝ) : ℝ :=
  1 + ∑ i, ∑ j, if i < j then
    (alpha j * h i / alpha i - h j) / ((alpha i - alpha j) * n) else 0

/-- Modified multinomial signed expectation, not a probability measure (PDF p.14). -/
def modifiedMean {d : ℕ} (alpha : Fin d → ℝ) (n : ℕ) (F : (Fin d → ℝ) → ℝ) : ℝ :=
  wordMean alpha n (fun w => modifiedDensity alpha n (histogram w) * F (histogram w))

/-- Stable word restriction to the first k letters (PDF p.16). -/
def prefixWord {d : ℕ} (w : List (Fin d)) (k : ℕ) : List (Fin d) := w.filter (fun a => a.val < k)

/-- Stable word restriction to source letters >=k (PDF p.16). -/
def suffixWord {d : ℕ} (w : List (Fin d)) (k : ℕ) : List (Fin d) := w.filter (fun a => k - 1 ≤ a.val)

/-- Quantum Hellinger squared for PSD matrices, including subnormalized
reports, with no factor 1/2 (PDF pp.13,25). -/
def quantumH2 {d : ℕ} (rho sigma : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ((cfc Real.sqrt rho - cfc Real.sqrt sigma) ^ 2).trace.re

/-- Quantum affinity, distinct from root fidelity (PDF p.13). -/
def affinity {d : ℕ} (rho sigma : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  (cfc Real.sqrt rho * cfc Real.sqrt sigma).trace.re

/-- Rank-k Keyl report, WITHOUT renormalizing the truncated rows (PDF pp.22,25). -/
def truncatedReport {d n : ℕ} (hd : 0 < d) (hn : 0 < n) (k : ℕ)
    (s : Schur.Partition d n) (U : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  (U : Matrix _ _ ℂ) * Matrix.diagonal (fun i =>
    if i.val < k then (Schur.normalizedRows hd hn s i : ℂ) else 0) * star (U : Matrix _ _ ℂ)

/-- Extended Hellinger risk under the concrete Keyl joint Born law, not Haar
alone or a law chosen for accuracy (PDF pp.22-27). -/
def keylRisk {d n : ℕ} (hd : 0 < d) (hn : 0 < n) (k : ℕ)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hRho : IsDensityMatrix rho) : ℝ≥0∞ :=
  ∫⁻ o, ENNReal.ofReal (quantumH2 (truncatedReport hd hn k o.1 o.2) rho)
    ∂Tomography.keylJointLaw hd hn rho hRho

/-- Success under the same public Keyl decoder (PDF pp.6-7). -/
def keylSuccess {d n : ℕ} (hd : 0 < d) (hn : 0 < n) (k : ℕ)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hRho : IsDensityMatrix rho) (epsilon : ℝ) : ℝ≥0∞ :=
  Tomography.keylJointLaw hd hn rho hRho
    {o | quantumH2 (truncatedReport hd hn k o.1 o.2) rho ≤ epsilon}

/-- Integer copy budget, rounding a real bound upward (PDF pp.6-7). -/
def copyBudget (C rate : ℝ) : ℕ := ⌈C * rate⌉₊

/-- Any measurable Birkhoff decomposition of |V_(a,i)|^2, with pi(i)=a.
No accuracy property is assumed; the theorem is independent of the choice (PDF p.23). -/
structure InducedPermutation (d : ℕ) where
  weight : Matrix.unitaryGroup (Fin d) ℂ → Equiv.Perm (Fin d) → ℝ
  nonneg : ∀ U pi, 0 ≤ weight U pi
  total : ∀ U, ∑ pi, weight U pi = 1
  measurable : ∀ pi, Measurable (fun U => weight U pi)
  marginal : ∀ U i a, (∑ pi, if pi i = a then weight U pi else 0) =
    Complex.normSq ((U : Matrix _ _ ℂ) a i)

/-- Keyl real expectation. All uses below are bounded continuous statistics
or bounded measurable permutation mixtures, hence integrable (PDF p.23). -/
def keylMean {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hRho : IsDensityMatrix rho)
    (F : Matrix.unitaryGroup (Fin d) ℂ → ℝ) : ℝ :=
  ∫ o, F o.2 ∂Tomography.keylJointLaw hd hn rho hRho

/-- Conditional permutation expectation in eigenbasis B; weights use
B dagger V, rather than a unitary in an unrelated basis (PDF pp.23,25). -/
def permutationMean {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hRho : IsDensityMatrix rho)
    (B : Matrix.unitaryGroup (Fin d) ℂ) (P : InducedPermutation d)
    (F : Equiv.Perm (Fin d) → ℝ) : ℝ :=
  keylMean hd hn rho hRho (fun V => ∑ pi, P.weight (star B * V) pi * F pi)

/-- Physical EYD risk; weak-Schur projectors and decoder are fixed before
the unknown state. The law depends only on its spectrum (PDF pp.5-6). -/
def eydRisk {d n : ℕ} (hd : 0 < d) (hn : 0 < n) (alpha : Fin d → ℝ)
    (hAlpha : Learning.IsDistribution alpha) (hSorted : Antitone alpha)
    (loss : (Fin d → ℝ) → (Fin d → ℝ) → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ s, loss (Schur.normalizedRows hd hn s) alpha
    ∂Schur.weakSamplingLaw hd hn alpha hAlpha hSorted

/-- Success event for the same physical EYD experiment (PDF pp.6-7). -/
def eydSuccess {d n : ℕ} (hd : 0 < d) (hn : 0 < n) (alpha : Fin d → ℝ)
    (hAlpha : Learning.IsDistribution alpha) (hSorted : Antitone alpha)
    (loss : (Fin d → ℝ) → (Fin d → ℝ) → ℝ≥0∞) (epsilon : ℝ) : ℝ≥0∞ :=
  Schur.weakSamplingLaw hd hn alpha hAlpha hSorted
    {s | loss (Schur.normalizedRows hd hn s) alpha ≤ ENNReal.ofReal epsilon}

/-- Proper increasing graphs; no smoothness restriction (PDF p.30). -/
def ProperIncreasingCurve (f : ℝ → ℝ) : Prop :=
  Continuous f ∧ StrictMono f ∧ Tendsto f atTop atTop ∧ Tendsto f atBot atBot

/-- Original-word graph points (PDF p.29). -/
def wordPoints {A : Type*} (w : List A) : List (ℝ × A) :=
  w.zipIdx.map (fun a => ((a.2 : ℝ), a.1))

/-- Black skeleton points keep the input TIME of the bump as horizontal
coordinate, rather than being reindexed in the shorter word (PDF p.29).
This coordinate differs from the bumped occurrence's own original position. -/
def firstBumpPoints {A : Type*} [LinearOrder A] (w : List A) : List (ℝ × A) :=
  ((rskRun w).2.filter (fun e => e.1 = 0)).map (fun e => ((e.2.1 : ℝ), e.2.2.1))

/-- Disjoint increasing chains as sets of occurrence indices; empty chains
and the empty family are allowed (PDF pp.2,28). -/
def IsChains {A : Type*} [LinearOrder A] (w : List (ℝ × A)) {c : ℕ}
    (I : Fin c → Finset (Fin w.length)) : Prop :=
  (∀ j, ∀ u ∈ I j, ∀ v ∈ I j, u < v → (w.get u).2 ≤ (w.get v).2) ∧
    ∀ i j, i ≠ j → Disjoint (I i) (I j)

/-- Proper graphs pass through every selected occurrence and are pairwise
disjoint on the whole real line (PDF p.30). -/
def CurvesThrough {A : Type*} (e : A → ℝ) (w : List (ℝ × A)) {c : ℕ}
    (I : Fin c → Finset (Fin w.length)) (f : Fin c → ℝ → ℝ) : Prop :=
  (∀ j, ProperIncreasingCurve (f j)) ∧
    (∀ j, ∀ u ∈ I j, f j (w.get u).1 = e (w.get u).2) ∧
    ∀ i j, i ≠ j → ∀ x, f i x ≠ f j x

/-- Full admissibility invariant (19): chains are admissible and every
inadmissible point is strictly southeast of the southeasternmost curve.
No output-existence certificate is built into this predicate (PDF pp.28-30). -/
def AdmissibleChains {A : Type*} [LinearOrder A] (e : A → ℝ)
    (w : List (ℝ × A)) (admissible : Finset A) {c : ℕ}
    (I : Fin c → Finset (Fin w.length)) : Prop :=
  IsChains w I ∧ (∀ j, ∀ u ∈ I j, (w.get u).2 ∈ admissible) ∧
    ∃ f : Fin c → ℝ → ℝ, CurvesThrough e w I f ∧
      ∃ first : Fin c, (∀ j x, f first x ≤ f j x) ∧
        ∀ u : Fin w.length, (w.get u).2 ∉ admissible → e (w.get u).2 < f first (w.get u).1

/-! Sanity examples pin definitions, rather than proving the paper's results. -/

example : shape ([] : List ℕ) = [] := by rfl

example : shape ([1, 1] : List ℕ) = [2] := by rfl

example : bumpedWord ([2, 1] : List ℕ) 0 = [2] := by rfl

example : originalBumpedWord ([2, 1] : List ℕ) 0 = [2] := by rfl

example : firstBumpPoints ([2, 1] : List ℕ) = [(1, 2)] := by
  norm_num [firstBumpPoints, rskRun, insertRows, insertRow]

example : bumpedWord ([2, 3, 1, 0, 2] : List ℕ) 0 = [2, 1, 3] := by rfl

example : originalBumpedWord ([2, 3, 1, 0, 2] : List ℕ) 0 = [2, 3, 1] := by rfl

example {d : ℕ} (alpha : Fin d → ℝ) (F : List ℕ → ℝ) :
    swMean alpha 0 F = F [] := by
  simp [swMean, wordMean, wordMass, shape, rskRun]

example {d : ℕ} (a : Fin d → ℝ) : l2 d a a = 0 := by simp [l2]

example {d : ℕ} (rho : Matrix (Fin d) (Fin d) ℂ) : quantumH2 rho rho = 0 := by
  simp [quantumH2]

example : row [] 0 = 0 := by simp [row]

example : chiTerm 0 0 = 0 := by simp [chiTerm]

example : chiTerm 1 0 = ⊤ := by simp [chiTerm]

example {d : ℕ} (a : Fin d → ℝ) : h2 0 a a = 0 := by simp [h2]

example {d : ℕ} (a : Fin d → ℝ) : spectralPrefixExcessLimit a d = 0 := by simp [spectralPrefixExcessLimit]

example : ProperIncreasingCurve (fun x : ℝ => x) :=
  ⟨continuous_id, strictMono_id, tendsto_id, tendsto_id⟩

example {d n : ℕ} (hd : 0 < d) (hn : 0 < n) (s : Schur.Partition d n)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    truncatedReport hd hn d s U = Schur.estimate hd hn s U := by
  simp [truncatedReport, Schur.estimate, Schur.normalizedDiagram]

example {d n : ℕ} (hd : 0 < d) (hn : 0 < n) (s : Schur.Partition d n)
    (U : Matrix.unitaryGroup (Fin d) ℂ) : truncatedReport hd hn 0 s U = 0 := by
  simp [truncatedReport]

/-- Adjacent multiplier in Lemmas 5.3-5.4; defined only for an actual pair
of consecutive indices (PDF p.24). -/
def adjacentProbabilityMultiplier {d : ℕ} (alpha : Fin d → ℝ) (j : Fin (d - 1)) : ℝ :=
  (alpha ⟨j.val, by omega⟩ - alpha ⟨j.val + 1, by omega⟩) / alpha ⟨j.val, by omega⟩

/-- Floored list from the proof of Corollary 5.5; its first k entries stay
unchanged and the next entry is zeta under the cutoff assumptions (PDF p.25). -/
def flooredEntry {d : ℕ} (alpha : Fin d → ℝ) (zeta : ℝ) (j : ℕ) : ℝ :=
  if h : j < d then max (alpha ⟨j, h⟩) zeta else zeta

end QAlgorithms.Papers.Independent.Extend50.P32


