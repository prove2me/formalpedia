-- Prove2me | Definitions.Def_NuclearTensor_Membership_Supplement_Tasks
-- name    : NuclearTensor_Membership_Supplement_Tasks
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:42:08.798094+00:00
-- url     : https://prove2.me/theorems/b925e366-4b0f-43c8-a642-c438ebb01e74
-- title:
--   Optimization, tomography, separability and channel contracts
-- statement:
--   The task predicates specify the two clauses of LocalSearch, product-overlap covers, signed product optimization, tomography supported on a known product-basis subspace, Frobenius separability testing, and arbitrary-reference implementation of the local filters and Schur compression.
--
--   A $\theta$-cover uses amplitude overlap $|\langle x,c\rangle|\ge\theta^2/64$, rather than that bound on squared overlap. On the success event, LocalSearch compares against all regional unit products when the regional maximum reaches $\epsilon$, and estimates the returned value within $\epsilon$ regardless of whether that threshold is reached. Tomography describes its output by a $D\times D$ coefficient matrix in the supplied subspace basis.
--
--   The local mass and flagged channel are
--
--   $$A_j=\operatorname{Tr}_{-j}(\rho^2),\quad F_j=f_a(A_j),\quad a=2048k^2/\eta^4,$$
--   $$\Phi_j(X)=F_jXF_j+\operatorname{Tr}((I-F_j^2)X)|\perp\rangle\langle\perp|.$$
--
--   The Schur predicate is the exact common-unitary Haar-averaged identity with arbitrary reference systems. A supplied tester receives the tensor power of a single state and executes finite code without additional copies. These contracts carry mathematical requirements, not assumed algorithmic services.
--
--   **Formalization Note** Haar measures are probability measures on the Borel unitary group, invariant under left translation; their existence is included in the Schur predicate. The empty tensor power is the scalar identity, including copy count zero. The ideal compression channel is existential, as in Lemma 7.5; no Schur transform is a primitive instruction.
-- source:
--   Martino Bernasconi, Giulio Malavolta, STOC 2027 submission #945 (October 2026), pp. 9, 21–35, 38–51; Section 2, Definitions 6.2–6.3, Section 7.1 and Appendices A–C.

import Definitions.Def_NuclearTensor_Membership_Supplement_QuantumPrograms

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

namespace NuclearTensor.Membership.Supplement

/-- Validity of returned classical descriptions is unconditional, including failed runs. -/
def returnsProduct (d k : ℕ) (s : Configuration) : Prop :=
  ∃ x ∈ unitProducts d k, outputReals s = encodeProducts x

def returnsProductValue (d k : ℕ) (s : Configuration) : Prop :=
  ∃ (x : Fin k → CVec d) (v : ℝ), x ∈ unitProducts d k ∧
    outputReals s = encodeProducts x ++ [v]

def returnsCover (d k : ℕ) (s : Configuration) : Prop :=
  ∃ C : List (Fin k → CVec d), (∀ c ∈ C, c ∈ unitProducts d k) ∧
    outputIntegers s = [C.length] ∧ outputReals s = (C.map encodeProducts).flatten

def returnsMatrix (D : ℕ) (s : Configuration) : Prop :=
  ∃ B : CMat D, outputReals s = encodeMatrix B

def returnsEstimates (k : ℕ) (s : Configuration) : Prop :=
  ∃ e : Fin k → ℝ, outputReals s = List.ofFn e

def returnsDecision (s : Configuration) : Prop := ∃ b : Bool, outputsDecision s b

def prefixOverlap {d m : ℕ} (a : Fin (m - 1) → CVec d) (x : Fin m → CVec d) : ℝ :=
  ‖∏ j : Fin (m - 1), if h : j.val < m then ∑ i, conj (a j i) * x ⟨_, h⟩ i else 0‖ ^ 2

def region {d m : ℕ} (a : Fin (m - 1) → CVec d) (α : ℝ) : Set (Fin m → CVec d) :=
  {x | x ∈ unitProducts d m ∧ α ≤ prefixOverlap a x}

/-- Both clauses of Definition 6.3. The regional condition is empty when alpha>1.
No assertion that the answer belongs to the region is imposed by the source. -/
def localSearchOutput {d m T : ℕ} (ω : CMat (d ^ m)) (K : SignedOperator d m T)
    (a : Fin (m - 1) → CVec d) (α ε : ℝ) (s : Configuration) : Prop :=
  ∃ (x : Fin m → CVec d) (v : ℝ), x ∈ unitProducts d m ∧
    outputReals s = encodeProducts x ++ [v] ∧
    ((∃ y ∈ region a α, ε ≤ value (ω - K.matrix) y) →
      ∀ y ∈ region a α, value (ω - K.matrix) y - ε ≤ value (ω - K.matrix) x) ∧
    |v - value (ω - K.matrix) x| ≤ ε

def overlapCover {d k : ℕ} (ρ : CMat (d ^ k)) (θ : ℝ) (C : List (Fin k → CVec d)) : Prop :=
  (∀ c ∈ C, c ∈ unitProducts d k) ∧
  ∀ x ∈ unitProducts d k, θ ≤ value ρ x → ∃ c ∈ C, θ ^ 2 / 64 ≤ amplitude x c

def coverOutput {d k : ℕ} (ρ : CMat (d ^ k)) (θ : ℝ) (s : Configuration) : Prop :=
  ∃ C : List (Fin k → CVec d), outputIntegers s = [C.length] ∧
    outputReals s = (C.map encodeProducts).flatten ∧ overlapCover ρ θ C

def signedOutput {d k T : ℕ} (ρ : CMat (d ^ k)) (S : Mixture d k T)
    (η : ℝ) (s : Configuration) : Prop :=
  ∃ x ∈ unitProducts d k, outputReals s = encodeProducts x ∧
    ∀ y ∈ unitProducts d k, value (ρ - S.matrix) y - η ^ 2 ≤ value (ρ - S.matrix) x

/-- The output is a D-by-D coefficient matrix, not an exponential ambient array.
The known product basis is part of the classical description of the represented operator. -/
def tomographyOutput {d m D : ℕ} (ω : CMat (d ^ m)) (V : ProductSubspace d m D)
    (ε : ℝ) (s : Configuration) : Prop :=
  ∃ B : CMat D, outputReals s = encodeMatrix B ∧
    hsNorm (V.lift B - V.projector * ω * V.projector) ≤ ε

def testerCorrect {d k : ℕ} (P : QProgram) (σ : Spectral) (A r : ℕ)
    (η failure copies time : ℝ) : Prop :=
  ∀ ρ : CMat (d ^ k), IsDensity ρ → quantumAlgorithm ρ σ A r P [d, k] [η]
    copies time failure (fun s => ∃ b, outputsDecision s b ∧ sepDecision η ρ b) returnsDecision

/-- Eq. (9), the cutoff a=2^11 k^2/eta^4, and the continuous ramp of Section 7. -/
def cutoff (k : ℕ) (η : ℝ) : ℝ := 2048 * (k : ℝ) ^ 2 / η ^ 4

def ramp (a t : ℝ) : ℝ := if t ≤ a⁻¹ then 0 else if 2 / a ≤ t then 1 else a * t - 1

def spectralFunction {d : ℕ} (f : ℝ → ℝ) (M : CMat d) : CMat d :=
  if h : M.IsHermitian then
    ∑ i, (f (h.eigenvalues i) : ℂ) • pure (fun j => h.eigenvectorBasis i j)
  else 0

def localMass {d k : ℕ} (ρ : CMat (d ^ k)) (j : Fin k) : CMat d := partialTrace (ρ * ρ) j

def localFilter {d k : ℕ} (ρ : CMat (d ^ k)) (η : ℝ) (j : Fin k) : CMat d :=
  spectralFunction (ramp (cutoff k η)) (localMass ρ j)

def discarded {d k : ℕ} (ρ : CMat (d ^ k)) (η : ℝ) (j : Fin k) : ℝ :=
  hsInner (1 - localFilter ρ η j * localFilter ρ η j) (localMass ρ j)

/-- The final basis coordinate is the orthogonal erasure flag. -/
def flagged {d : ℕ} (F : CMat d) (X : CMat d) : CMat (d + 1) := fun i j =>
  if h : i.val < d ∧ j.val < d then (F * X * F) ⟨_, h.1⟩ ⟨_, h.2⟩
  else if i.val = d ∧ j.val = d then Matrix.trace ((1 - F * F) * X) else 0

def estimatesOutput {d k : ℕ} (ρ : CMat (d ^ k)) (η ε : ℝ) (s : Configuration) : Prop :=
  ∃ e : Fin k → ℝ, outputReals s = List.ofFn e ∧ ∀ j, |e j - discarded ρ η j| ≤ ε

/-- Tensor power of a rectangular matrix, in the same row-major convention. -/
def tensorPower {a b : ℕ} (N : ℕ) (V : Matrix (Fin b) (Fin a) ℂ) : Matrix (Fin (b ^ N)) (Fin (a ^ N)) ℂ :=
  fun I J => ∏ t : Fin N, if h : digit b N I.val t.val < b ∧ digit a N J.val t.val < a then
    V ⟨_, h.1⟩ ⟨_, h.2⟩ else 0

abbrev UGroup (q : ℕ) := Matrix.unitaryGroup (Fin q) ℂ

instance unitaryMeasurableSpace (q : ℕ) : MeasurableSpace (UGroup q) := borel _

/-- The measure is normalized Haar measure, required explicitly in the compression theorem.
Coordinatewise integration gives the ordinary finite-dimensional operator integral. -/
def haarTwirl (q N : ℕ) (μ : MeasureTheory.Measure (UGroup q)) (X : CMat (q ^ N)) : CMat (q ^ N) :=
  fun i j => ∫ U, ((tensorPower N (U : CMat q)) * X *
    (tensorPower N (U : CMat q)).conjTranspose) i j ∂μ

def schurIdentity {D q N : ℕ} (C : CMat (D ^ N) → CMat (q ^ N)) : Prop :=
  IsChannel C ∧
    (∃ μ : MeasureTheory.Measure (UGroup q), MeasureTheory.IsProbabilityMeasure μ ∧
      MeasureTheory.Measure.IsMulLeftInvariant μ) ∧ ∀ μ : MeasureTheory.Measure (UGroup q),
    MeasureTheory.IsProbabilityMeasure μ → MeasureTheory.Measure.IsMulLeftInvariant μ →
    ∀ (R : ℕ) (V : Matrix (Fin D) (Fin q) ℂ), V.conjTranspose * V = 1 →
    ∀ X : Matrix (Fin (q ^ N) × Fin R) (Fin (q ^ N) × Fin R) ℂ,
      ClonableQMASep.Main.IsDensity X →
      amplify (haarTwirl q N μ) R
        (amplify C R (amplify (fun Y => tensorPower N V * Y * (tensorPower N V).conjTranspose) R X)) =
        amplify (haarTwirl q N μ) R X

/-- A supplied N-copy tester is finite code acting coherently on those N registers.
The input is the tensor power of one unknown state, not a list of unrelated states. -/
def testerOnCopies {d k : ℕ} (P : QProgram) (σ : Spectral) (A r N : ℕ)
    (η failure time : ℝ) : Prop :=
  ∀ ρ : CMat (d ^ k), IsDensity ρ → ∃ fuel L,
    qRun dummyState σ A r P [] fuel
      (initialQuantum [d, k, N] [η] (encodeJoint (R := 1)
        (fun xr ys => tensorPower N ρ xr.1 ys.1))) = some L ∧
      validLaw L ∧ charged L 0 time ∧ (∀ s ∈ L, returnsDecision s.classical) ∧
      eventProbability L (fun s => ∃ b, outputsDecision s b ∧ sepDecision η ρ b) ≥ 1 - failure

def reducedDimension (k : ℕ) (η : ℝ) : ℕ := max 1 (Nat.ceil (cutoff k η))

/-- Concrete source parameters, also used to fix the interpretation of O/Theta. -/
def optimizerTheta (η : ℝ) : ℝ := min (η ^ 2 / 8) 1
def optimizerAlpha (η : ℝ) : ℝ := (optimizerTheta η / 16) ^ 4
def optimizerEpsilon (η : ℝ) : ℝ := optimizerTheta η / 16

def reductionEstimateAccuracy (k : ℕ) (η : ℝ) : ℝ := η ^ 2 / (128 * k)
def reductionRejectThreshold (k : ℕ) (η : ℝ) : ℝ := 3 * η ^ 2 / (64 * k)

end NuclearTensor.Membership.Supplement


