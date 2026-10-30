-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34
-- name    : QAlgorithms_Papers_Independent_Extend50_P34
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T16:37:17.43006+00:00
-- url     : https://prove2.me/theorems/0fa70ff7-86db-489b-9b93-9957d943a6af
-- title:
--   Definitions for Quantum Spectrum Testing
-- statement:
--   The objects the formalized statements of *Quantum Spectrum Testing* (arXiv:1501.05028) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `decreasingSpectrum`: Decreasing spectrum, padded to the ambient dimension (PDF pp.9-10).
--   - `unif`: The uniform spectrum; only positive dimensions occur in statements (PDF p.22).
--   - `classicalAccept`: Acceptance of a randomized classical test of n samples (PDF pp.10-11).
--   - `Far`: Separation from every property member; valid also for the empty property (PDF p.10).
--   - `IsSpectralProperty`: Symmetric closed properties consist of probability distributions (PDF pp.10-11).
--   - `QuantumTest`: Fixed collective n-copy effect, chosen before the unknown density matrix (PDF p.10).
--   - `QuantumTestable`: Attainable quantum testing guarantees, with no restriction on internal computation (PDF p.10).
--   - `ClassicalTest`: Fixed randomized classical test and its worst-input guarantees (PDF pp.10-11).
--   - `ClassicalTestable`: Attainable iid classical testing guarantees (PDF p.11).
--   - `supportProperty`: Support size at most r, as clarified by the abstract (PDF pp.1,5).
--   - `ownShape`: Unrestricted diagram viewed in the accepted Specht construction (PDF pp.11,16-18).
--   - `dim`: Specht dimension, distinct from the Schur/unitary-group dimension (PDF p.14).
--   - `extendedSchurPolynomial`: Schur polynomial extended by zero beyond the alphabet height (PDF p.15).
--   - `schurAt`: Schur polynomial evaluation (PDF p.15).
--   - `content`: Signed cell content j-i in zero-based coordinates (PDF p.13).
--   - `contentProduct`: Content product d-up-arrow-lambda (PDF p.13).
--   - `sw`: Physical Schur mass on all n, including zero copies; no renormalization (PDF pp.19-22).
--   - `swSpectrum`: Classical-spectrum Schur law via the diagonal density matrix (PDF pp.21-22).
--   - `expect`: Finite Schur expectation, with the law's physical mass (PDF p.26).
--   - `event`: Event mass without conditional renormalization (PDF pp.24,29).
--   - `schurVariance`: Centered variance on the finite Schur law (PDF p.52).
--   - `eydError`: EYD TV error; n>0 is required wherever used (PDF p.29).
--   - `chiSq`: Chi-squared divergence on a finite set (PDF p.9); applications have common support.
--   - `kl`: KL divergence on a finite set (PDF p.9); used only with supp p contained in supp q.
--   - `rankLaw`: Both rank laws embedded in the larger rank's shape space (PDF pp.44-55).
--   - `adjacentKL`: Common-space KL for adjacent uniform ranks, in the stated direction (PDF p.44).
--   - `adjacentTV`: Common-space TV for adjacent uniform ranks (PDF p.52).
--   - `insertRow`: Row insertion bumps the first strictly larger entry (PDF p.15).
--   - `insertTableau`: Recursive row bumping, adding a row when necessary (PDF p.15).
--   - `rsk`: RSK shape from the actual row-insertion algorithm; sorting is inert on valid output (PDF p.15).
--   - `greeneStatistic`: Length of the longest union of k disjoint weakly increasing subsequences (PDF pp.5,16).
--   - `greeneReport`: The d observable Greene statistics, indexed by k=1,...,d (PDF p.5).
--   - `GreeneTestable`: Classical tests whose decisions depend only on the Greene report (PDF p.5).
--   - `diagrams`: Every partition of given size and bounded height, as a finite diagram set (PDF p.11).
--   - `diagramsLE`: All diagrams of size at most K, including the empty partition (PDF pp.11,25).
--   - `observableWeight`: Source weight |mu|+length(mu) (PDF p.28).
--   - `falling`: Falling factorial; Nat subtraction gives the intended zero for k>n (PDF p.13).
--   - `powerParts`: Power-sum polynomial indexed by positive parts, including the empty product (PDF p.14).
--   - `fullCycle`: Full cycle type including fixed points; Mathlib cycleType alone omits them (PDF p.11).
--   - `character`: Character of an unrestricted diagram in the accepted physical Specht construction (PDF pp.16-18).
--   - `classCharacter`: Character on a cycle class, as its class average; no arbitrary representative (PDF p.17).
--   - `sharpParts`: Central character p-sharp, extended by zero when |mu| exceeds |lambda| (PDF p.25).
--   - `sharp`: Central character indexed by a partition (PDF p.25).
--   - `starShift`: Shifted power sum p-star with arbitrary shift c; rows are one-based in the source (PDF p.31).
--   - `starPower`: The canonical p-star uses c=-1/2 (PDF p.25).
--   - `shiftedSchur`: Shifted Schur observable from the Fourier characterization, Theorem 2.33 (PDF p.26).
--   - `multiplicityFact`: Product of multiplicity factorials, with the empty product equal to one (PDF p.47).
--   - `leading`: Explicit highest-weight term in p-star_k (PDF p.47).
--   - `remainder`: The error observable is computed, never supplied as a free variable (PDF p.47).
--   - `observable`: Evaluate a finite rational central-character expansion on every shape (PDF pp.47,51).
--   - `paninski`: Paninski's alternating perturbation, on even positive dimensions (PDF pp.34-35).
--   - `perturbed`: General perturbation Q_x, used only for sum x=0 and x_i≥-1 (PDF p.35).
--   - `mixednessStateAccept`: The Mixedness Tester's acceptance on an arbitrary state (PDF p.33).
--   - `rankAccept`: Rank Tester's acceptance probability on the actual input state (PDF p.56).
--   - `RankTesterWorks`: Source Rank Tester guarantee, including perfect completeness (PDF pp.56-58).
--   - `UniformRank`: Spectrum uniform on exactly r nonzero eigenvalues, in any basis (PDF p.7).
--   - `DistinguishesRanks`: Distinguish uniform ranks r and r+Delta, with one effect fixed before rho (PDF pp.7,43).
--   - `EYDLowerBound`: EYD lower-bound assertion with absolute constants quantified before d,epsilon,n (PDF pp.7,30).
--   - `groupOn`: Restricted symmetric group embedded by fixing the complement (PDF pp.27,37).
--   - `restrictedCycle`: Cycle type of a permutation restricted to R, including fixed points in R (PDF p.37).
--   - `classOn`: Permutations of a specified cycle class on R (PDF p.28).
--   - `classZ`: z_mu, including length-one cycles (PDF p.12).
--   - `factorizationCount`: Actual partial-permutation factorization count g, with union equal to [t] (PDF p.28).
--   - `structureConstant`: Source structure constant computed from Proposition 2.36, independently of Corollary 2.37 (PDF p.28).
--   - `OverlapRange`: The nonzero range of the overlap coefficient (PDF p.28).
--   - `overlapCoefficient`: C^t_{r1,r2}, with its source zero convention (PDF p.28).
--   - `classProductProbability`: Product cycle-class probability, used only in the valid overlap range (PDF p.28).
--   - `productCharacterMean`: Uniform permutation expectation for arbitrary prescribed supports (PDF p.37).
--   - `RemovesDomino`: Successive removal of a rim domino leaves a Young diagram (PDF p.40).
--   - `DominoBalanced`: Empty 2-core, using exactly the source's removable-domino definition (PDF p.40).
--   - `parityCells`: Even and odd content cells; signed parity is taken before subtraction can truncate (PDF p.40).
--   - `parityProduct`: Parity-restricted content product (PDF pp.42-43).
--   - `quotientRunner`: Beta numbers with an even bead cutoff; both Maya runners are retained (PDF pp.40-41).
--   - `twoQuotient`: Two quotient shapes, computed by the two alternating Maya runners (PDF p.41). The labels may swap under bead conventions; their multiset union is invariant.
--   - `evenDoubleFactorial`: Double factorial k!! for even k, including 0!!=1 (PDF p.42).
--   - `RankRegime`: The standing rank-adjacency regime, including the exact integer-compatible copy count (PDF p.44).
--   - `Usual`: Usual means BOTH width and height bounded by the real threshold (PDF p.45).
--   - `logObservable`: Truncated log observable with general denominator a (PDF pp.46-47).
--   - `logInfinite`: L-star-infinity is used only on usual diagrams, where this series converges (PDF p.46).
--   - `truncation`: Source truncation degree, chosen from r and omega (PDF pp.51-52).
--   - `UsualPlus`: Usual-plus uses the SAME r-based event for both adjacent laws (PDF p.54).
--   - `errorTerm`: Entire error term (39), computed from the actual remainder observable (PDF p.48).
--   - `ErrorConstants`: A family witnessing the bounds in Lemma 5.7 (PDF p.50).
--   - `chosenOmega`: A suitable subpolynomial choice, not an arbitrary function bounded by big-O (PDF p.52).
--   - `sharpMonomial`: Monomial in single-cycle central characters (PDF p.51).
--   - `russian`: Russian upper boundary: every rotated unit cell contributes its vertical tent thickness (PDF pp.12-13).
--   - `scaledBoundary`: Area-one scaled Russian boundary, separate from EYD's row vector (PDF p.22).
--   - `bianeArc`: Biane's curved part for positive parameter other than one (PDF p.23).
--   - `biane`: Explicit Biane curve including c=0 and c=1 (PDF p.23, Theorem 2.30).
--   - `boundaryDistance`: L1 boundary distance as a Lebesgue integral; explicit diagrams have bounded difference support (PDF p.60).
--   - `tildePower`: The kth local-extremum moment from the explicit Russian boundary (PDF p.25).
--   - `bianeMoment`: Deterministic Biane moment subtracted in q-tilde, computed from n,d,k (PDF p.62).
--   - `qTilde`: q-tilde is the actual boundary moment minus the deterministic Biane moment (PDF p.62).
--   - `Diverges`: f(d)=omega_d(1), with no prescribed convergence rate (PDF pp.59-60).
--   - `realObservable`: Finite real observables retain arbitrary fixed real coefficients (PDF p.63).
--   - `complexObservable`: Complex central-character expansions for coefficient statements in the complex algebra (PDF pp.24-25,51).
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, https://arxiv.org/abs/1501.05028v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SchurWeylMeasurements
import Definitions.Def_QAlgorithms_Defs_QuantumOutputMetrics
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P38
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P28

noncomputable section

open scoped Matrix BigOperators
open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.
open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)
open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Decreasing spectrum, padded to the ambient dimension (PDF pp.9-10). -/
def decreasingSpectrum {d : ℕ} (rho : Matrix (Fin d) (Fin d) ℂ) : Fin d → ℝ :=
  fun i => ascEigenvalues rho (Fin.cast (Fintype.card_fin d).symm i.rev)

/-- The uniform spectrum; only positive dimensions occur in statements (PDF p.22). -/
def unif (d : ℕ) : Fin d → ℝ := fun _ => 1 / d

/-- Acceptance of a randomized classical test of n samples (PDF pp.10-11). -/
def classicalAccept {d n : ℕ} (a : (Fin n → Fin d) → ℝ) (p : Fin d → ℝ) : ℝ :=
  ∑ w, wordMass p w * a w

/-- Separation from every property member; valid also for the empty property (PDF p.10). -/
def Far {d : ℕ} (P : Set (Fin d → ℝ)) (epsilon : ℝ) (p : Fin d → ℝ) : Prop :=
  ∀ q ∈ P, epsilon ≤ tv p q

/-- Symmetric closed properties consist of probability distributions (PDF pp.10-11). -/
def IsSpectralProperty {d : ℕ} (P : Set (Fin d → ℝ)) : Prop :=
  IsClosed P ∧ (∀ p ∈ P, Learning.IsDistribution p) ∧
    ∀ (p : Fin d → ℝ) (pi : Equiv.Perm (Fin d)), p ∘ pi ∈ P ↔ p ∈ P

/-- Fixed collective n-copy effect, chosen before the unknown density matrix (PDF p.10). -/
def QuantumTest {d n : ℕ} (P : Set (Fin d → ℝ)) (epsilon : ℝ)
    (oneSided : Bool) (M : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) : Prop :=
  IsEffect M ∧ ∀ rho : Matrix (Fin d) (Fin d) ℂ, IsDensityMatrix rho →
    (decreasingSpectrum rho ∈ P → if oneSided then effectProb M (piKron n rho) = 1
      else 2 / 3 ≤ effectProb M (piKron n rho)) ∧
    (Far P epsilon (decreasingSpectrum rho) → effectProb M (piKron n rho) ≤ 1 / 3)

/-- Attainable quantum testing guarantees, with no restriction on internal computation (PDF p.10). -/
def QuantumTestable (d n : ℕ) (P : Set (Fin d → ℝ)) (epsilon : ℝ)
    (oneSided : Bool := false) : Prop :=
  ∃ M, QuantumTest (n := n) P epsilon oneSided M

/-- Fixed randomized classical test and its worst-input guarantees (PDF pp.10-11). -/
def ClassicalTest {d n : ℕ} (P : Set (Fin d → ℝ)) (epsilon : ℝ)
    (oneSided : Bool) (a : (Fin n → Fin d) → ℝ) : Prop :=
  (∀ w, 0 ≤ a w ∧ a w ≤ 1) ∧ ∀ p, Learning.IsDistribution p →
    (p ∈ P → if oneSided then classicalAccept a p = 1
      else 2 / 3 ≤ classicalAccept a p) ∧
    (Far P epsilon p → classicalAccept a p ≤ 1 / 3)

/-- Attainable iid classical testing guarantees (PDF p.11). -/
def ClassicalTestable (d n : ℕ) (P : Set (Fin d → ℝ)) (epsilon : ℝ) : Prop :=
  ∃ a, ClassicalTest (n := n) P epsilon false a

example {d : ℕ} (a : (Fin 0 → Fin d) → ℝ) (p q : Fin d → ℝ) :
    classicalAccept a p = classicalAccept a q := by simp [classicalAccept, wordMass]

/-- Support size at most r, as clarified by the abstract (PDF pp.1,5). -/
def supportProperty (d r : ℕ) : Set (Fin d → ℝ) :=
  {p | Learning.IsDistribution p ∧ (Finset.univ.filter fun i => p i ≠ 0).card ≤ r}

/-- Unrestricted diagram viewed in the accepted Specht construction (PDF pp.11,16-18). -/
def ownShape (lambda : YoungDiagram) : Schur.Partition (lambda.colLen 0) lambda.card :=
  ⟨lambda, rfl, le_rfl⟩

/-- Specht dimension, distinct from the Schur/unitary-group dimension (PDF p.14). -/
def dim (lambda : YoungDiagram) : ℕ := Module.finrank ℂ (Schur.spechtSpace (ownShape lambda))

/-- Schur polynomial extended by zero beyond the alphabet height (PDF p.15). -/
def extendedSchurPolynomial (d : ℕ) (lambda : YoungDiagram) : MvPolynomial (Fin d) ℝ :=
  if h : lambda.colLen 0 ≤ d then Schur.schurPolynomial ⟨lambda, rfl, h⟩ else 0

/-- Schur polynomial evaluation (PDF p.15). -/
def schurAt {d : ℕ} (lambda : YoungDiagram) (x : Fin d → ℝ) : ℝ :=
  MvPolynomial.eval x (extendedSchurPolynomial d lambda)

/-- Signed cell content j-i in zero-based coordinates (PDF p.13). -/
def content (c : ℕ × ℕ) : ℤ := (c.2 : ℤ) - c.1

/-- Content product d-up-arrow-lambda (PDF p.13). -/
def contentProduct (d : ℝ) (lambda : YoungDiagram) : ℝ :=
  ∏ c ∈ lambda.cells, (d + content c)

/-- Physical Schur mass on all n, including zero copies; no renormalization (PDF pp.19-22). -/
def sw {d n : ℕ} (rho : Matrix (Fin d) (Fin d) ℂ) (lambda : Schur.Partition d n) : ℝ :=
  effectProb (Schur.isotypicProjector lambda) (piKron n rho)

/-- Classical-spectrum Schur law via the diagonal density matrix (PDF pp.21-22). -/
def swSpectrum {d n : ℕ} (p : Fin d → ℝ) : Schur.Partition d n → ℝ :=
  sw (Matrix.diagonal fun i => (p i : ℂ))

/-- Finite Schur expectation, with the law's physical mass (PDF p.26). -/
def expect {d n : ℕ} (p : Fin d → ℝ) (F : YoungDiagram → ℝ) : ℝ :=
  ∑ lambda : Schur.Partition d n, swSpectrum p lambda * F lambda.val

/-- Event mass without conditional renormalization (PDF pp.24,29). -/
def event {d n : ℕ} (p : Fin d → ℝ) (A : YoungDiagram → Prop) : ℝ :=
  expect (n := n) p (fun lambda => if A lambda then 1 else 0)

/-- Centered variance on the finite Schur law (PDF p.52). -/
def schurVariance {d n : ℕ} (p : Fin d → ℝ) (F : YoungDiagram → ℝ) : ℝ :=
  expect (n := n) p (fun lambda => (F lambda - expect (n := n) p F) ^ 2)

/-- EYD TV error; n>0 is required wherever used (PDF p.29). -/
def eydError {d : ℕ} (n : ℕ) (p : Fin d → ℝ) (lambda : YoungDiagram) : ℝ :=
  tv (fun i : Fin d => (lambda.rowLen i : ℝ) / n) p

/-- Chi-squared divergence on a finite set (PDF p.9); applications have common support. -/
def chiSq {a : Type*} [Fintype a] (p q : a → ℝ) : ℝ :=
  ∑ i, if q i = 0 then 0 else q i * (p i / q i - 1) ^ 2

/-- KL divergence on a finite set (PDF p.9); used only with supp p contained in supp q. -/
def kl {a : Type*} [Fintype a] (p q : a → ℝ) : ℝ :=
  ∑ i, if p i = 0 then 0 else p i * Real.log (p i / q i)

/-- Both rank laws embedded in the larger rank's shape space (PDF pp.44-55). -/
def rankLaw (r n D : ℕ) : Schur.Partition D n → ℝ :=
  swSpectrum (fun i : Fin D => if i.val < r then (1 : ℝ) / r else 0)

/-- Common-space KL for adjacent uniform ranks, in the stated direction (PDF p.44). -/
def adjacentKL (r n : ℕ) : ℝ := kl (rankLaw r n (r+1)) (rankLaw (r+1) n (r+1))

/-- Common-space TV for adjacent uniform ranks (PDF p.52). -/
def adjacentTV (r n : ℕ) : ℝ := tv (rankLaw r n (r+1)) (rankLaw (r+1) n (r+1))

example {a : Type} [Fintype a] (p : a → ℝ) : tv p p = 0 := by simp [tv]

example (d : ℕ) (p : Fin d → ℝ) (w : Fin 0 → Fin d) : wordMass p w = 1 := by
  simp [wordMass]

example (d : ℕ) (lambda : YoungDiagram) (h : d < lambda.colLen 0) :
    extendedSchurPolynomial d lambda = 0 := by simp [extendedSchurPolynomial, not_le.mpr h]

example : content (1, 0) = -1 := by norm_num [content]

example {a : Type*} [Fintype a] (p : a → ℝ) : chiSq p p = 0 := by
  classical
  unfold chiSq
  apply Finset.sum_eq_zero
  intro i hi
  by_cases h : p i = 0 <;> simp [chiSq, h]

/-- Row insertion bumps the first strictly larger entry (PDF p.15). -/
def insertRow (b : ℕ) : List ℕ → List ℕ × Option ℕ
  | [] => ([b], none)
  | a :: rest => if b < a then (b :: rest, some a) else
      let out := insertRow b rest
      (a :: out.1, out.2)

/-- Recursive row bumping, adding a row when necessary (PDF p.15). -/
def insertTableau (b : ℕ) : List (List ℕ) → List (List ℕ)
  | [] => [[b]]
  | row :: rows =>
      let out := insertRow b row
      out.1 :: (match out.2 with | none => rows | some c => insertTableau c rows)

/-- RSK shape from the actual row-insertion algorithm; sorting is inert on valid output (PDF p.15). -/
def rsk {d n : ℕ} (w : Fin n → Fin d) : YoungDiagram :=
  let rows := (List.ofFn fun i => (w i).val).foldl (fun T b => insertTableau b T) []
  YoungDiagram.ofRowLens ((rows.map List.length).mergeSort (· ≥ ·))
    (List.sortedGE_mergeSort)

/-- Length of the longest union of k disjoint weakly increasing subsequences (PDF pp.5,16). -/
def greeneStatistic {d n : ℕ} (w : Fin n → Fin d) (k : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin n))).filter fun (S : Finset (Fin n)) =>
    ∃ color : {i : Fin n // i ∈ S} → Fin k,
      ∀ i j : {i : Fin n // i ∈ S}, i.val < j.val → color i = color j →
        w i.val ≤ w j.val).sup Finset.card

/-- The d observable Greene statistics, indexed by k=1,...,d (PDF p.5). -/
def greeneReport {d n : ℕ} (w : Fin n → Fin d) : Fin d → ℕ :=
  fun k => greeneStatistic w (k.val + 1)

/-- Classical tests whose decisions depend only on the Greene report (PDF p.5). -/
def GreeneTestable (d n : ℕ) (P : Set (Fin d → ℝ)) (epsilon : ℝ) : Prop :=
  ∃ a : (Fin d → ℕ) → ℝ, (∀ x, 0 ≤ a x ∧ a x ≤ 1) ∧
    ClassicalTest (n := n) P epsilon false (fun w => a (greeneReport w))

/-- Every partition of given size and bounded height, as a finite diagram set (PDF p.11). -/
def diagrams (d k : ℕ) : Finset YoungDiagram :=
  (Finset.univ : Finset (Schur.Partition d k)).image Subtype.val

/-- All diagrams of size at most K, including the empty partition (PDF pp.11,25). -/
def diagramsLE (K : ℕ) : Finset YoungDiagram :=
  (Finset.range (K+1)).biUnion fun k => diagrams K k

/-- Source weight |mu|+length(mu) (PDF p.28). -/
def observableWeight (mu : YoungDiagram) : ℕ := mu.card + mu.colLen 0

/-- Falling factorial; Nat subtraction gives the intended zero for k>n (PDF p.13). -/
def falling (n k : ℕ) : ℝ := (n.descFactorial k : ℝ)

/-- Power-sum polynomial indexed by positive parts, including the empty product (PDF p.14). -/
def powerParts {d : ℕ} (mu : Multiset ℕ) (p : Fin d → ℝ) : ℝ :=
  (mu.map fun k => ∑ i, p i ^ k).prod

/-- Full cycle type including fixed points; Mathlib cycleType alone omits them (PDF p.11). -/
def fullCycle {n : ℕ} (pi : Equiv.Perm (Fin n)) : Multiset ℕ :=
  pi.cycleType + Multiset.replicate (n - pi.support.card) 1

/-- Character of an unrestricted diagram in the accepted physical Specht construction (PDF pp.16-18). -/
def character (lambda : YoungDiagram) (pi : Equiv.Perm (Fin lambda.card)) : ℝ :=
  (Schur.spechtCharacter (ownShape lambda) pi).re

/-- Character on a cycle class, as its class average; no arbitrary representative (PDF p.17). -/
def classCharacter (lambda : YoungDiagram) (mu : Multiset ℕ) : ℝ :=
  let S := (Finset.univ : Finset (Equiv.Perm (Fin lambda.card))).filter
    (fun pi => fullCycle pi = mu)
  (∑ pi ∈ S, character lambda pi) / S.card

/-- Central character p-sharp, extended by zero when |mu| exceeds |lambda| (PDF p.25). -/
def sharpParts (mu : Multiset ℕ) (lambda : YoungDiagram) : ℝ :=
  if mu.sum ≤ lambda.card then
    falling lambda.card mu.sum *
      classCharacter lambda (mu + Multiset.replicate (lambda.card - mu.sum) 1) / dim lambda
  else 0

/-- Central character indexed by a partition (PDF p.25). -/
def sharp (mu lambda : YoungDiagram) : ℝ := sharpParts (mu.rowLens : Multiset ℕ) lambda

/-- Shifted power sum p-star with arbitrary shift c; rows are one-based in the source (PDF p.31). -/
def starShift (k : ℕ) (c : ℝ) (lambda : YoungDiagram) : ℝ :=
  ∑ i ∈ Finset.range (lambda.colLen 0),
    (((lambda.rowLen i : ℝ) - (i+1) - c)^k - (-(i+1 : ℝ) - c)^k)

/-- The canonical p-star uses c=-1/2 (PDF p.25). -/
def starPower (k : ℕ) (lambda : YoungDiagram) : ℝ := starShift k (-1/2) lambda

/-- Shifted Schur observable from the Fourier characterization, Theorem 2.33 (PDF p.26). -/
def shiftedSchur (mu lambda : YoungDiagram) : ℝ :=
  (∑ pi : Equiv.Perm (Fin mu.card),
    character mu pi * sharpParts (fullCycle pi) lambda) / mu.card.factorial

/-- Product of multiplicity factorials, with the empty product equal to one (PDF p.47). -/
def multiplicityFact (mu : YoungDiagram) : ℕ :=
  ∏ j ∈ Finset.range (mu.card+1), (mu.rowLens.count j).factorial

/-- Explicit highest-weight term in p-star_k (PDF p.47). -/
def leading (k : ℕ) (lambda : YoungDiagram) : ℝ :=
  ∑ mu ∈ (diagramsLE (k+1)).filter (fun mu => observableWeight mu = k+1),
    falling k (mu.colLen 0 - 1) / multiplicityFact mu * sharp mu lambda

/-- The error observable is computed, never supplied as a free variable (PDF p.47). -/
def remainder (k : ℕ) (lambda : YoungDiagram) : ℝ := starPower k lambda - leading k lambda

/-- Evaluate a finite rational central-character expansion on every shape (PDF pp.47,51). -/
def observable (a : YoungDiagram →₀ ℚ) (lambda : YoungDiagram) : ℝ :=
  a.sum fun mu c => (c : ℝ) * sharp mu lambda

example : insertRow 1 [1,2] = ([1,1], some 2) := by norm_num [insertRow]

example : insertTableau 1 [[2],[3]] = [[1],[2],[3]] := by norm_num [insertTableau, insertRow]

example {n : ℕ} : fullCycle (1 : Equiv.Perm (Fin n)) = Multiset.replicate n 1 := by
  simp [fullCycle]

example (lambda : YoungDiagram) : starShift 0 0 lambda = 0 := by simp [starShift]

example (lambda : YoungDiagram) : observable 0 lambda = 0 := by simp [observable]

example (d : ℕ) (w : Fin 0 → Fin d) : rsk w = ⊥ := by
  apply YoungDiagram.ext
  simp [rsk, YoungDiagram.ofRowLens, YoungDiagram.cellsOfRowLens]

/-- Paninski's alternating perturbation, on even positive dimensions (PDF pp.34-35). -/
def paninski (d : ℕ) (epsilon : ℝ) : Fin d → ℝ :=
  fun i => (1 + (if Even i.val then 2*epsilon else -2*epsilon)) / d

/-- General perturbation Q_x, used only for sum x=0 and x_i≥-1 (PDF p.35). -/
def perturbed {d : ℕ} (x : Fin d → ℝ) : Fin d → ℝ := fun i => (1+x i)/d

/-- The Mixedness Tester's acceptance on an arbitrary state (PDF p.33). -/
def mixednessStateAccept {d : ℕ} (n : ℕ) (epsilon : ℝ)
    (rho : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ∑ lambda : Schur.Partition d n, sw rho lambda *
    (if sharpParts {2} lambda.val ≤ (1+epsilon^2/2)*(n : ℝ)*(n-1 : ℕ)/d then 1 else 0)

/-- Rank Tester's acceptance probability on the actual input state (PDF p.56). -/
def rankAccept {d : ℕ} (n r : ℕ) (rho : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ∑ lambda : Schur.Partition d n, sw rho lambda *
    (if lambda.val.colLen 0 ≤ r then 1 else 0)

/-- Source Rank Tester guarantee, including perfect completeness (PDF pp.56-58). -/
def RankTesterWorks (d n r : ℕ) (epsilon : ℝ) : Prop :=
  ∀ rho : Matrix (Fin d) (Fin d) ℂ, IsDensityMatrix rho →
    (decreasingSpectrum rho ∈ supportProperty d r → rankAccept n r rho = 1) ∧
    (Far (supportProperty d r) epsilon (decreasingSpectrum rho) → rankAccept n r rho ≤ 1/3)

/-- Spectrum uniform on exactly r nonzero eigenvalues, in any basis (PDF p.7). -/
def UniformRank {d : ℕ} (r : ℕ) (rho : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∃ pi : Equiv.Perm (Fin d), ∀ i,
    decreasingSpectrum rho (pi i) = if i.val < r then (1 : ℝ)/r else 0

/-- Distinguish uniform ranks r and r+Delta, with one effect fixed before rho (PDF pp.7,43). -/
def DistinguishesRanks (d n r Delta : ℕ) : Prop :=
  ∃ M : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ, IsEffect M ∧
    ∀ rho : Matrix (Fin d) (Fin d) ℂ, IsDensityMatrix rho →
      (UniformRank r rho → effectProb M (piKron n rho) ≤ 1/3) ∧
      (UniformRank (r+Delta) rho → 2/3 ≤ effectProb M (piKron n rho))

/-- EYD lower-bound assertion with absolute constants quantified before d,epsilon,n (PDF pp.7,30). -/
def EYDLowerBound : Prop :=
  ∃ delta epsilon0 a : ℝ, 0 < delta ∧ delta < 1 ∧ 0 < epsilon0 ∧ epsilon0 < 1 ∧ 0 < a ∧
    ∃ d0 : ℕ, 2 ≤ d0 ∧ ∀ d : ℕ, d0 ≤ d →
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon0 →
        ∀ n : ℕ, 0 < n → (n : ℝ) < a*d^2/epsilon^2 →
          delta ≤ event (n := n) (unif d) (fun lambda => epsilon < eydError n (unif d) lambda)

example (d n : ℕ) : paninski d 0 = unif d := by
  funext i
  simp [paninski, unif]

example (d : ℕ) : perturbed (fun _ : Fin d => 0) = unif d := by
  funext i
  simp [perturbed, unif]

/-- Restricted symmetric group embedded by fixing the complement (PDF pp.27,37). -/
def groupOn {t : ℕ} (R : Finset (Fin t)) : Finset (Equiv.Perm (Fin t)) :=
  Finset.univ.filter fun w => ∀ i, i ∉ R → w i = i

/-- Cycle type of a permutation restricted to R, including fixed points in R (PDF p.37). -/
def restrictedCycle {t : ℕ} (R : Finset (Fin t)) (w : Equiv.Perm (Fin t)) : Multiset ℕ :=
  w.cycleType + Multiset.replicate (R.card - w.support.card) 1

/-- Permutations of a specified cycle class on R (PDF p.28). -/
def classOn {t : ℕ} (R : Finset (Fin t)) (mu : YoungDiagram) : Finset (Equiv.Perm (Fin t)) :=
  (groupOn R).filter fun w => restrictedCycle R w = (mu.rowLens : Multiset ℕ)

/-- z_mu, including length-one cycles (PDF p.12). -/
def classZ (mu : YoungDiagram) : ℕ :=
  ∏ j ∈ Finset.Icc 1 mu.card, j^(mu.rowLens.count j) * (mu.rowLens.count j).factorial

/-- Actual partial-permutation factorization count g, with union equal to [t] (PDF p.28). -/
def factorizationCount (mu nu tau : YoungDiagram)
    (w : Equiv.Perm (Fin tau.card)) : ℕ :=
  let choices : Finset ((Finset (Fin tau.card) × Equiv.Perm (Fin tau.card)) ×
      (Finset (Fin tau.card) × Equiv.Perm (Fin tau.card))) := Finset.univ
  (choices.filter fun pair =>
    pair.1.1 ∪ pair.2.1 = Finset.univ ∧ pair.1.1.card = mu.card ∧ pair.2.1.card = nu.card ∧
    pair.1.2 ∈ classOn pair.1.1 mu ∧ pair.2.2 ∈ classOn pair.2.1 nu ∧
    pair.1.2 * pair.2.2 = w).card

/-- Source structure constant computed from Proposition 2.36, independently of Corollary 2.37 (PDF p.28). -/
def structureConstant (mu nu tau : YoungDiagram) : ℝ :=
  let S := (Finset.univ : Finset (Equiv.Perm (Fin tau.card))).filter
    (fun w => fullCycle w = (tau.rowLens : Multiset ℕ))
  ((classZ mu : ℝ)*classZ nu/classZ tau) *
    ((∑ w ∈ S, (factorizationCount mu nu tau w : ℝ))/S.card)

/-- The nonzero range of the overlap coefficient (PDF p.28). -/
def OverlapRange (r1 r2 t : ℕ) : Prop :=
  0 < r1 ∧ 0 < r2 ∧ 0 < t ∧ r1 ≤ t ∧ r2 ≤ t ∧ t ≤ r1+r2

/-- C^t_{r1,r2}, with its source zero convention (PDF p.28). -/
def overlapCoefficient (r1 r2 t : ℕ) : ℝ :=
  if OverlapRange r1 r2 t then
    (r1.factorial : ℝ)*r2.factorial /
      ((t-r1).factorial*(t-r2).factorial*(r1+r2-t).factorial : ℕ)
  else 0

/-- Product cycle-class probability, used only in the valid overlap range (PDF p.28). -/
def classProductProbability (mu nu tau : YoungDiagram)
    (_h : OverlapRange mu.card nu.card tau.card) : ℝ :=
  let R1 := Finset.univ.filter (fun i : Fin tau.card => i.val < mu.card)
  let R2 := Finset.univ.filter (fun i : Fin tau.card => tau.card-nu.card ≤ i.val)
  let A := classOn R1 mu
  let B := classOn R2 nu
  ((A.product B).filter (fun w => fullCycle (w.1*w.2) = (tau.rowLens : Multiset ℕ))).card /
    ((A.card : ℝ)*B.card)

/-- Uniform permutation expectation for arbitrary prescribed supports (PDF p.37). -/
def productCharacterMean {d t : ℕ} (q : Fin d → ℝ) (mu nu : YoungDiagram)
    (R1 R2 : Finset (Fin t)) : ℝ :=
  (∑ w1 ∈ groupOn R1, ∑ w2 ∈ groupOn R2,
    classCharacter mu (restrictedCycle R1 w1) *
      classCharacter nu (restrictedCycle R2 w2) * powerParts (fullCycle (w1*w2)) q) /
        (((groupOn R1).card : ℝ)*(groupOn R2).card)

/-- Successive removal of a rim domino leaves a Young diagram (PDF p.40). -/
def RemovesDomino (mu nu : YoungDiagram) : Prop :=
  nu.cells ⊆ mu.cells ∧ ∃ a b : ℕ × ℕ, a ≠ b ∧
    mu.cells \ nu.cells = {a,b} ∧
    ((a.1=b.1 ∧ (a.2+1=b.2 ∨ b.2+1=a.2)) ∨
      (a.2=b.2 ∧ (a.1+1=b.1 ∨ b.1+1=a.1)))

/-- Empty 2-core, using exactly the source's removable-domino definition (PDF p.40). -/
def DominoBalanced (mu : YoungDiagram) : Prop :=
  Relation.ReflTransGen RemovesDomino mu ⊥

/-- Even and odd content cells; signed parity is taken before subtraction can truncate (PDF p.40). -/
def parityCells (mu : YoungDiagram) (even : Bool) : Finset (ℕ × ℕ) :=
  mu.cells.filter fun c => if even then Even (content c) else Odd (content c)

/-- Parity-restricted content product (PDF pp.42-43). -/
def parityProduct (d : ℝ) (mu : YoungDiagram) (even : Bool) : ℝ :=
  ∏ c ∈ parityCells mu even, (d + content c)

/-- Beta numbers with an even bead cutoff; both Maya runners are retained (PDF pp.40-41). -/
def quotientRunner (mu : YoungDiagram) (b : ℕ) : List ℕ :=
  let L := 2*mu.colLen 0
  let beta := (List.range L).map fun i => mu.rowLen i + L - 1 - i
  let runner := ((beta.filter fun x => x % 2 = b).map fun x => x/2).mergeSort (· ≥ ·)
  runner.zipIdx |>.map (fun pair => pair.1 - (runner.length - 1 - pair.2))

/-- Two quotient shapes, computed by the two alternating Maya runners (PDF p.41).
The labels may swap under bead conventions; their multiset union is invariant. -/
def twoQuotient (mu : YoungDiagram) (b : Fin 2) : YoungDiagram :=
  YoungDiagram.ofRowLens ((quotientRunner mu b).mergeSort (· ≥ ·))
    (List.sortedGE_mergeSort)

/-- Double factorial k!! for even k, including 0!!=1 (PDF p.42). -/
def evenDoubleFactorial (k : ℕ) : ℝ := (2 : ℝ)^(k/2) * (k/2).factorial

example : DominoBalanced (⊥ : YoungDiagram) := Relation.ReflTransGen.refl

example : evenDoubleFactorial 2 = 2 := by norm_num [evenDoubleFactorial]

example (r1 r2 t : ℕ) (h : ¬ OverlapRange r1 r2 t) :
    overlapCoefficient r1 r2 t = 0 := by simp [overlapCoefficient, h]

/-- The standing rank-adjacency regime, including the exact integer-compatible copy count (PDF p.44). -/
def RankRegime (r n : ℕ) (omega : ℝ) : Prop :=
  0 < r ∧ 0 < n ∧ 200 ≤ omega ∧ omega ≤ Real.sqrt r ∧
    (n : ℝ) = (r : ℝ)^2 / omega^2

/-- Usual means BOTH width and height bounded by the real threshold (PDF p.45). -/
def Usual (r : ℕ) (omega : ℝ) (lambda : YoungDiagram) : Prop :=
  (lambda.rowLen 0 : ℝ) ≤ 10*r/omega ∧ (lambda.colLen 0 : ℝ) ≤ 10*r/omega

/-- Truncated log observable with general denominator a (PDF pp.46-47). -/
def logObservable (a : ℝ) (C : ℕ) (lambda : YoungDiagram) : ℝ :=
  ∑ k ∈ Finset.Icc 2 C, (-1 : ℝ)^k * starPower k lambda / ((k : ℝ)*a^k)

/-- L-star-infinity is used only on usual diagrams, where this series converges (PDF p.46). -/
def logInfinite (r : ℕ) (lambda : YoungDiagram) : ℝ :=
  ∑' k : ℕ, if 2 ≤ k then
    (-1 : ℝ)^k * starPower k lambda / ((k : ℝ)*((r : ℝ)+1/2)^k) else 0

/-- Source truncation degree, chosen from r and omega (PDF pp.51-52). -/
def truncation (r : ℕ) (omega : ℝ) : ℕ :=
  ⌈3*Real.log (10*r)/Real.log (omega/10)⌉₊

/-- Usual-plus uses the SAME r-based event for both adjacent laws (PDF p.54). -/
def UsualPlus (r : ℕ) (omega : ℝ) (lambda : YoungDiagram) : Prop :=
  Usual r omega lambda ∧ |logInfinite r lambda| ≤ 2

/-- Entire error term (39), computed from the actual remainder observable (PDF p.48). -/
def errorTerm (r n C : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 C, (-1 : ℝ)^k * expect (n := n) (unif r) (remainder k) /
    ((k : ℝ)*(r : ℝ)^k)

/-- A family witnessing the bounds in Lemma 5.7 (PDF p.50). -/
def ErrorConstants (A : ℕ → ℝ) : Prop :=
  ∀ C : ℕ, 2 ≤ C → 0 ≤ A C ∧ ∀ r n : ℕ, ∀ omega : ℝ,
    RankRegime r n omega → |errorTerm r n C| ≤ A C/omega^2

/-- A suitable subpolynomial choice, not an arbitrary function bounded by big-O (PDF p.52). -/
def chosenOmega (B : ℝ) (r : ℕ) : ℝ :=
  Real.exp (B*Real.rpow (Real.log r) (67/100 : ℝ))

/-- Monomial in single-cycle central characters (PDF p.51). -/
def sharpMonomial (mu lambda : YoungDiagram) : ℝ :=
  (mu.rowLens.map fun k => sharpParts {k} lambda).prod

example (a : ℝ) (lambda : YoungDiagram) : logObservable a 1 lambda = 0 := by
  simp [logObservable]

example (r n : ℕ) : errorTerm r n 1 = 0 := by simp [errorTerm]

example (r : ℕ) (omega : ℝ) (lambda : YoungDiagram) (h : UsualPlus r omega lambda) :
    Usual r omega lambda := h.1

/-- Russian upper boundary: every rotated unit cell contributes its vertical tent thickness (PDF pp.12-13). -/
def russian (lambda : YoungDiagram) (x : ℝ) : ℝ :=
  |x| + ∑ c ∈ lambda.cells, 2*max 0 (1 - |x - content c|)

/-- Area-one scaled Russian boundary, separate from EYD's row vector (PDF p.22). -/
def scaledBoundary (lambda : YoungDiagram) (x : ℝ) : ℝ :=
  russian lambda (Real.sqrt lambda.card * x) / Real.sqrt lambda.card

/-- Biane's curved part for positive parameter other than one (PDF p.23). -/
def bianeArc (c x : ℝ) : ℝ :=
  2/Real.pi * (x*Real.arcsin ((x+c)/(2*Real.sqrt (1+c*x))) +
    (1/c)*Real.arccos ((2+c*x-c^2)/(2*Real.sqrt (1+c*x))) +
      Real.sqrt (4-(x-c)^2)/2)

/-- Explicit Biane curve including c=0 and c=1 (PDF p.23, Theorem 2.30). -/
def biane (c x : ℝ) : ℝ :=
  if c = 0 then
    if |x| ≤ 2 then 2/Real.pi*(x*Real.arcsin (x/2)+Real.sqrt (4-x^2)) else |x|
  else if c = 1 then
    if |x-1| ≤ 2 then (x+1)/2 +
      ((x-1)*Real.arcsin ((x-1)/2)+Real.sqrt (4-(x-1)^2))/Real.pi else |x|
  else if 1 < c ∧ -1/c < x ∧ x < c-2 then x+2/c
  else if |x-c| ≤ 2 then bianeArc c x else |x|

/-- L1 boundary distance as a Lebesgue integral; explicit diagrams have bounded difference support (PDF p.60). -/
def boundaryDistance (f g : ℝ → ℝ) : ℝ := ∫ x, |f x-g x|

/-- The kth local-extremum moment from the explicit Russian boundary (PDF p.25). -/
def tildePower (k : ℕ) (lambda : YoungDiagram) : ℝ :=
  (k : ℝ)*(k-1 : ℕ) * ∫ x : ℝ, x^(k-2) * ((russian lambda x - |x|)/2)

/-- Deterministic Biane moment subtracted in q-tilde, computed from n,d,k (PDF p.62). -/
def bianeMoment (k n d : ℕ) : ℝ :=
  ∑ ell ∈ Finset.Icc 1 ((k+1)/2),
    falling k (2*ell-1) /
      (((k+1-ell)*(ell.factorial)*((ell-1).factorial) : ℕ) : ℝ) *
        Real.rpow n ((k : ℝ)/2+1-ell)/(d : ℝ)^(k+1-2*ell)

/-- q-tilde is the actual boundary moment minus the deterministic Biane moment (PDF p.62). -/
def qTilde (k n d : ℕ) (lambda : YoungDiagram) : ℝ :=
  tildePower (k+1) lambda / ((k+1 : ℝ)*Real.rpow n ((k : ℝ)/2)) - bianeMoment k n d

/-- f(d)=omega_d(1), with no prescribed convergence rate (PDF pp.59-60). -/
def Diverges (f : ℕ → ℕ) : Prop :=
  ∀ M : ℕ, ∃ d0 : ℕ, ∀ d : ℕ, d0 ≤ d → M ≤ f d

/-- Finite real observables retain arbitrary fixed real coefficients (PDF p.63). -/
def realObservable (a : YoungDiagram →₀ ℝ) (lambda : YoungDiagram) : ℝ :=
  a.sum fun mu c => c * sharp mu lambda

/-- Complex central-character expansions for coefficient statements in the complex algebra (PDF pp.24-25,51). -/
def complexObservable (a : YoungDiagram →₀ ℂ) (lambda : YoungDiagram) : ℂ :=
  a.sum fun mu c => c * (sharp mu lambda : ℂ)

example (x : ℝ) : russian ⊥ x = |x| := by simp [russian]

example : biane 0 3 = 3 := by norm_num [biane]

example (lambda : YoungDiagram) : realObservable 0 lambda = 0 := by simp [realObservable]

example (lambda : YoungDiagram) : complexObservable 0 lambda = 0 := by simp [complexObservable]

end QAlgorithms.Papers.Independent.Extend50.P34


