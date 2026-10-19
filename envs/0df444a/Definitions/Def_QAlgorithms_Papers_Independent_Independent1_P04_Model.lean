-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P04_Model
-- name    : QAlgorithms_Papers_Independent_Independent1_P04_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:22:08.625622+00:00
-- url     : https://prove2.me/theorems/fcf8f1be-2140-4fa0-bbc7-51b02ff5760a
-- title:
--   Quantifying Coherence: supporting definitions
-- statement:
--   Reviewed paper-local supporting definitions and conventions. The attached text aggregates the existing blind readbacks of every definition; it makes no theorem proof claim.
-- source:
--   Quantifying Coherence, arXiv:1311.0275v3. PDF SHA-256: c70b296ff2628a49bfb6ffd3e0abb02ad1aa50162dec040cf32047eb3a450825. Exact locators remain in declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_BasisCoherence
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
/-! Quantifying Coherence, arXiv:1311.0275v3. Fixed bases and arbitrary finite dimensions.
Local predicates apply to density matrices only; invalid matrices carry no coherence guarantees. -/

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Independent1.P04

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

abbrev CoherenceMatrix (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

def BasisDiagonal {I : Type*} (X : Matrix I I ℂ) : Prop :=
  ∀ i j, i ≠ j → X i j = 0

def IncoherentState {d : ℕ} (X : CoherenceMatrix d) : Prop :=
  IsDensityMatrix X ∧ BasisDiagonal X

def dephasedMatrix {d : ℕ} (X : CoherenceMatrix d) : CoherenceMatrix d :=
  Matrix.diagonal fun i => X i i

def PreservesDiagonalBranch {I J : Type*} [Fintype I] [Fintype J]
    (K : Matrix J I ℂ) : Prop :=
  ∀ X : Matrix I I ℂ, X.PosSemidef → BasisDiagonal X → BasisDiagonal (conjSuperop K X)

def IncoherentInstrument {d a : ℕ} (dims : Fin a → ℕ)
    (K : (i : Fin a) → Matrix (Fin (dims i)) (Fin d) ℂ) : Prop :=
  (∑ i, (K i)ᴴ * K i = 1) ∧ ∀ i, PreservesDiagonalBranch (K i)

def branchProbability {I J : Type*} [Fintype I] [Fintype J]
    (K : Matrix J I ℂ) (rho : Matrix I I ℂ) : ℝ := (conjSuperop K rho).trace.re

def selectiveContribution (C : (d : ℕ) → CoherenceMatrix d → ℝ)
    {d e : ℕ} (K : Matrix (Fin e) (Fin d) ℂ) (rho : CoherenceMatrix d) : ℝ :=
  let p := branchProbability K rho
  if 0 < p then p * C e ((p⁻¹ : ℂ) • conjSuperop K rho) else 0

def ensembleMixture {d a : ℕ} (p : Fin a → ℝ) (rho : Fin a → CoherenceMatrix d) :
    CoherenceMatrix d := ∑ i, (p i : ℂ) • rho i

def CoherenceNonnegative (C : (d : ℕ) → CoherenceMatrix d → ℝ) : Prop :=
  ∀ d, 0 < d → ∀ rho, IsDensityMatrix rho → 0 ≤ C d rho

def CoherenceFaithful (C : (d : ℕ) → CoherenceMatrix d → ℝ) : Prop :=
  ∀ d, 0 < d → ∀ rho, IsDensityMatrix rho → (C d rho = 0 ↔ IncoherentState rho)

def CoherenceConvex (C : (d : ℕ) → CoherenceMatrix d → ℝ) : Prop :=
  ∀ d, 0 < d → ∀ a (p : Fin a → ℝ) (rho : Fin a → CoherenceMatrix d),
    Learning.IsDistribution p → (∀ i, IsDensityMatrix (rho i)) →
      C d (ensembleMixture p rho) ≤ ∑ i, p i * C d (rho i)

def CoherenceSelective (C : (d : ℕ) → CoherenceMatrix d → ℝ) : Prop :=
  ∀ d, 0 < d → ∀ a (dims : Fin a → ℕ), (∀ i, 0 < dims i) →
    ∀ K : (i : Fin a) → Matrix (Fin (dims i)) (Fin d) ℂ,
    IncoherentInstrument dims K → ∀ rho, IsDensityMatrix rho →
      (∑ i, selectiveContribution C (K i) rho) ≤ C d rho

def CoherenceMonotone (C : (d : ℕ) → CoherenceMatrix d → ℝ) : Prop :=
  ∀ d e, 0 < d → 0 < e → ∀ a (K : Fin a → Matrix (Fin e) (Fin d) ℂ),
    IncoherentInstrument (fun _ => e) K → ∀ rho, IsDensityMatrix rho →
      C e (krausApply K rho) ≤ C d rho

def AttainedIncoherentMinimum {d : ℕ} (D : CoherenceMatrix d → CoherenceMatrix d → ℝ)
    (rho : CoherenceMatrix d) : Prop :=
  ∃ delta, IncoherentState delta ∧ ∀ sigma, IncoherentState sigma → D rho delta ≤ D rho sigma

def distanceCandidate {d : ℕ} (D : CoherenceMatrix d → CoherenceMatrix d → ℝ)
    (rho : CoherenceMatrix d) : ℝ :=
  sInf {v | ∃ delta, IncoherentState delta ∧ v = D rho delta}

def AttainedCandidateSpec {d : ℕ} (D : CoherenceMatrix d → CoherenceMatrix d → ℝ)
    (rho : CoherenceMatrix d) : Prop :=
  ∃ delta, IncoherentState delta ∧ distanceCandidate D rho = D rho delta ∧
    ∀ sigma, IncoherentState sigma → distanceCandidate D rho ≤ D rho sigma

def DistanceMinimumDomain (D : (d : ℕ) → CoherenceMatrix d → CoherenceMatrix d → ℝ) : Prop :=
  ∀ d, 0 < d → ∀ rho sigma, IsDensityMatrix rho → IsDensityMatrix sigma →
    0 ≤ D d rho sigma

def DistanceAttainment (D : (d : ℕ) → CoherenceMatrix d → CoherenceMatrix d → ℝ) : Prop :=
  ∀ d, 0 < d → ∀ rho, IsDensityMatrix rho → AttainedIncoherentMinimum (D d) rho

def DistanceContractive (D : (d : ℕ) → CoherenceMatrix d → CoherenceMatrix d → ℝ) : Prop :=
  ∀ d e, 0 < d → 0 < e → ∀ Phi : Superop (Fin d) (Fin e), IsChannel Phi →
    ∀ rho sigma, IsDensityMatrix rho → IsDensityMatrix sigma →
      D e (Phi rho) (Phi sigma) ≤ D d rho sigma

def DistanceJointConvex (D : (d : ℕ) → CoherenceMatrix d → CoherenceMatrix d → ℝ) : Prop :=
  ∀ d, 0 < d → ∀ a (p : Fin a → ℝ) (rho sigma : Fin a → CoherenceMatrix d),
    Learning.IsDistribution p → (∀ i, IsDensityMatrix (rho i)) →
    (∀ i, IsDensityMatrix (sigma i)) →
      D d (ensembleMixture p rho) (ensembleMixture p sigma) ≤ ∑ i, p i * D d (rho i) (sigma i)

/-- An arbitrary complex vector-space norm, without multiplicative or unitary-invariance axioms. -/
structure CoherenceMatrixNorm (d : ℕ) where
  value : CoherenceMatrix d → ℝ
  nonnegative : ∀ X, 0 ≤ value X
  definite : ∀ X, value X = 0 ↔ X = 0
  triangle : ∀ X Y, value (X+Y) ≤ value X+value Y
  homogeneous : ∀ (c : ℂ) X, value (c • X) = ‖c‖ * value X

def entrywiseDistance {d : ℕ} (X Y : CoherenceMatrix d) : ℝ := ∑ i, ∑ j, ‖X i j-Y i j‖

def squaredHSDistance {d : ℕ} (X Y : CoherenceMatrix d) : ℝ := ∑ i, ∑ j, ‖X i j-Y i j‖^2

def squaredOffDiagonal {d : ℕ} (X : CoherenceMatrix d) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i ≠ j), ‖X i j‖^2

def naturalEntropy {d : ℕ} (rho : CoherenceMatrix d) : ℝ := Real.log 2 * vnEntropy rho

def entropyCoherence (d : ℕ) (rho : CoherenceMatrix d) : ℝ :=
  naturalEntropy (dephasedMatrix rho)-naturalEntropy rho

def uniformCoherentVector (d : ℕ) : EuclideanSpace ℂ (Fin d) :=
  WithLp.toLp 2 fun _ => ((Real.sqrt d)⁻¹ : ℂ)

def cyclicPureKraus {d : ℕ} (c : EuclideanSpace ℂ (Fin d)) (a : Fin d) : CoherenceMatrix d :=
  Matrix.of fun i j => if j.val = (i.val+a.val)%d then c i else 0

def cyclicMixedKraus {d a : ℕ} (p : Fin a → ℝ) (c : Fin a → EuclideanSpace ℂ (Fin d))
    (index : Fin a × Fin d) : CoherenceMatrix d :=
  (Real.sqrt (p index.1) : ℂ) • cyclicPureKraus (c index.1) index.2

def qubitResourceKraus (U : Matrix Bool Bool ℂ) (b : Bool) :
    Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  Matrix.of fun p q => if p.2 = b ∧ q.2 = xor p.1 b then U p.1 q.1 else 0

def flaggedOutput {d e a : ℕ} (K : Fin a → Matrix (Fin e) (Fin d) ℂ)
    (rho : CoherenceMatrix d) : CoherenceMatrix (a*e) :=
  (Matrix.of fun p q : Fin a × Fin e =>
    if p.1 = q.1 then conjSuperop (K p.1) rho p.2 q.2 else 0).submatrix
      finProdFinEquiv.symm finProdFinEquiv.symm

def hsCounterexample : CoherenceMatrix 3 :=
  !![1/4,0,1/4; 0,1/2,0; 1/4,0,1/4]

def hsCounterKraus (alpha beta : ℂ) : Fin 2 → CoherenceMatrix 3 :=
  ![!![0,1,0; 0,0,0; 0,0,alpha], !![1,0,0; 0,0,beta; 0,0,0]]

def fidelityDistance (d : ℕ) (rho sigma : CoherenceMatrix d) : ℝ :=
  1-rootFidelity rho sigma

def fullTraceDistance (d : ℕ) (rho sigma : CoherenceMatrix d) : ℝ := traceNorm (rho-sigma)

example {d : ℕ} (X : CoherenceMatrix d) : BasisDiagonal (dephasedMatrix X) := by
  intro i j h
  simp [dephasedMatrix, Matrix.diagonal_apply, h]

example {d : ℕ} (K : CoherenceMatrix d) (rho : CoherenceMatrix d)
    (C : (e : ℕ) → CoherenceMatrix e → ℝ) (h : branchProbability K rho = 0) :
    selectiveContribution C K rho = 0 := by simp [selectiveContribution,h]

example {d : ℕ} (X : CoherenceMatrix d) : entrywiseDistance X X = 0 ∧
    squaredHSDistance X X = 0 := by simp [entrywiseDistance,squaredHSDistance]

example : uniformCoherentVector 1 0 = 1 := by simp [uniformCoherentVector]

example (c : EuclideanSpace ℂ (Fin 1)) : cyclicPureKraus c 0 0 0 = c 0 := by
  simp [cyclicPureKraus]

example (U : Matrix Bool Bool ℂ) : qubitResourceKraus U false (true,false) (false,true) =
    U true false := by simp [qubitResourceKraus]

example {d : ℕ} (N : CoherenceMatrixNorm d) : N.value 0 = 0 := N.definite 0 |>.mpr rfl

example {d : ℕ} (p : Fin 0 → ℝ) (rho : Fin 0 → CoherenceMatrix d) :
    ensembleMixture p rho = 0 := by simp [ensembleMixture]

example : entropyCoherence 1 (1 : CoherenceMatrix 1) = 0 := by
  have h : dephasedMatrix (1 : CoherenceMatrix 1) = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simp [dephasedMatrix]
  simp [entropyCoherence,h]

example : hsCounterKraus 0 1 0 2 2 = 0 ∧ hsCounterKraus 0 1 1 1 2 = 1 := by
  simp [hsCounterKraus]




















end QAlgorithms.Papers.Independent.Independent1.P04


