-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P14
-- name    : QAlgorithms_Papers_Independent_Claimed50_P14
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T09:26:05.790261+00:00
-- url     : https://prove2.me/theorems/e149fbff-9222-4176-834e-24a1d50d641e
-- title:
--   Definitions for Quantum learning algorithms for quantum measurements
-- statement:
--   The objects the formalized statements of *Quantum learning algorithms for quantum measurements* (arXiv:1103.0480) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Labels`
--   - `TrainingWires`
--   - `Branches`
--   - `LearningBlock`
--   - `SU`
--   - `specialUnitaryHaar`: PDF pp.3-4: whole-group probability Haar on the actual SU(d), not U(d).
--   - `measurementFamily`: PDF p.3, (8): the labeled rank-one measurement; matrices also admit unitary extensions.
--   - `learningMeasurementChannel`: PDF p.3, (10): only the classical label survives the device.
--   - `learningMeasurementChoi`: PDF p.3, (11): output-classical first, unnormalized Choi operator.
--   - `ParallelTraining`: PDF p.3, (14): a parallel preparation is a density on all original input wires, with identities on all classical output wires. No target coordinate occurs here.
--   - `CausalTraining`: PDF pp.2-3, (3),(14): full causal trace recursion. The parameter k allows only the earliest k calls to be grouped in one parallel preparation; k=0 is the unrestricted sequential domain, k=N the all-parallel domain. The zero prefix is scalar.
--   - `LearningInstrument`: PDF pp.2-3, (6),(14): positive branches with the entire causal normalization. The target is last: its identity factors out of the deterministic sum. Finite quantum memories are unrestricted, as in the comb characterization in the source.
--   - `outcomeBlocks`: PDF p.4, (22): actual diagonal classical slice, with target then source inputs.
--   - `outcomeDephasing`: PDF p.4, (19): classical dephasing in the fixed basis.
--   - `IsDiagonal`: PDF p.4, (18): full classical diagonality.
--   - `inputTensorPower`: PDF p.3, (12): the N-fold source-input action, newest call first.
--   - `replicatedPOVM`: PDF pp.3-4, (13),(21): link-product contraction INCLUDING the final transpose. The same U is inserted at every source slot.
--   - `povmDistance`: PDF p.3, (15): normalized pure-state Haar distance. The accepted state law is on unit vectors and has total mass one; its global phases do not affect Born weights. Outcome cardinality m is independent of Hilbert dimension h.
--   - `learningDistance`: PDF p.4, (17): normalized SU(d) prior, using the delayed-input replica.
--   - `learningScore`: PDF p.7, (50), and p.10, Remark 1: Haar-averaged overlap for arbitrary learners. On covariant learners it is exactly the displayed seed overlap (50). The averaging is necessary for unrestricted comparisons: a fixed computational measurement has seed overlap one but is not a perfect unknown-measurement learner.
--   - `covariantRepresentation`: PDF p.4, (23): conjugate target, direct source inputs, classical identity.
--   - `covariantTwirl`: PDF p.4, (25): constructive special-unitary twirl.
--   - `IsLearningCovariant`: PDF p.4, (23).
--   - `relabelClassical`: PDF p.5, (28),(30): classical coordinate permutation; no quantum wire is reordered.
--   - `relabelAverage`: PDF p.5, (30): finite relabeling average after covariance.
--   - `IsRelabelInvariant`: PDF p.5, (28).
--   - `IsLearningSymmetric`: PDF pp.6-7: all three reductions retained in subsequent optimizations.
--   - `IsOptimal`: PDF p.4: global D-optimality, with attainment rather than a real supremum.
--   - `outcomeOrbit`: PDF p.5, (33): one label permutation on every coordinate; no slot permutation.
--   - `BoundedPartitions`: PDF p.6: a partition is precisely an equivalence relation on the positions.
--   - `swapInput`: PDF p.9: swap source quantum input wires 2 and 0, leaving the target fixed.
--   - `swapLearner`: PDF p.9, Lemma 6: swap source outcome labels AND source inputs.
--   - `swapAverage`: PDF p.9: constructive averaging, on full source wires.
--   - `oneUseProjector`: PDF p.6, (38): trivial-representation projector on target and one source input.
--   - `oneUseOptimalInstrument`: PDF p.8, (60): concrete optimal blocks, with no normalized-Choi conversion.
--   - `oneUseProbe`: PDF p.8, (63): normalized maximally entangled probe, target/memory ordering.
--   - `oneUseRetrieval`: PDF p.8, (63)-(64): retrieve on the target and stored half of the probe; Pp outcome returns j; Pq outcome is uniform on labels other than j.
--   - `oneUseOperationalProbability`: PDF p.8: physical probability of the stated one-use realization, summing training outcomes. Conditional stored density is E_j(U)^T/d (subnormalized).
--   - `sourceSwap`: PDF pp.6,9: symmetric and antisymmetric projectors of the two source inputs.
--   - `sourceSymmetric`
--   - `sourceAntisymmetric`
--   - `dplus`: PDF p.9, (75): dimensions are real, avoiding truncated natural subtraction.
--   - `dminus`
--   - `FixedInputParameters`: PDF p.9, (75): actual input density coefficients.
--   - `twoUseScalarObjective`: PDF pp.9,12, corrected from the sector optima (A6)-(A12). The printed (82),(A14) misses +4 for d>=3 and counts an absent gamma sector at d=2.
--   - `alphaVector`: PDF p.6, (40),(42): actual alpha embedding vectors. Column 0 is plus, column 1 is minus; only source input wires are interchanged in the second term.
--   - `alphaEmbedding`: PDF p.6, (40),(42): matrix multiplicity blocks mapped into physical wires.
--   - `betaProjector`
--   - `gammaProjector`
--   - `twoUsePattern`: PDF pp.8-9, (68): xxx,xxy,xyx,xyy,xyz in that order.
--   - `patternMultiplicity`: PDF p.11, (A2): multiplicity of source labels at fixed replica label.
--   - `TwoUseBlocks`: PDF p.11: rescaled alpha matrices and beta/gamma scalars, not abstract free irreps.
--   - `physicalTwoUseBlock`: PDF pp.6,11, (39)-(42),(A2): reconstruct the physical block using the actual embedding. The absent xyz class is never evaluated by twoUsePattern when d=2.
--   - `blockInstrument`: PDF pp.8-9, (66),(68): full instrument assembled from positive rescaled blocks.
--   - `twoUseAttainingBlocks`: PDF p.12: explicit simultaneously attaining rescaled blocks, with corrected qubit beta xxy=xyx=tp/2. The qubit gamma and xyz sectors are zero.
--   - `FeasibleBlocks`: PDF p.11, (A4),(A5): fixed-input positive swap-symmetric blocks. At d=2 remove the gamma and xyz sectors entirely; their coefficients are fixed to zero.
--   - `deltaAlpha`: PDF p.11, (A1), including the factor 1/2 on the alpha xxy matrix.
--   - `deltaBeta`
--   - `deltaGamma`
--   - `sectorAlpha`: PDF p.11, (A3): sector scores for the actual rescaled multiplicity blocks.
--   - `sectorBeta`
--   - `sectorGamma`
-- source:
--   Quantum learning algorithms for quantum measurements, arXiv:1103.0480v2, https://arxiv.org/abs/1103.0480v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities

/-!
Statements from Bisio et al., arXiv:1103.0480v2.
Choi matrices are unnormalized; newest source call is coordinate zero.
All learner matrices are chosen independently of the unknown special unitary.
Compilation is pending the batch mechanical handoff.
-/

noncomputable section

open MeasureTheory TopologicalSpace
open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Claimed50.P14

abbrev Labels (d N : ℕ) := Fin N → Fin d

abbrev TrainingWires (d N : ℕ) := Fin d × (Labels d N × Labels d N)

abbrev Branches (d N : ℕ) := Fin d → Matrix (TrainingWires d N) (TrainingWires d N) ℂ

abbrev LearningBlock (d N : ℕ) := Matrix (Fin d × Labels d N) (Fin d × Labels d N) ℂ

abbrev SU (d : ℕ) := Matrix.specialUnitaryGroup (Fin d) ℂ

/-- PDF p.4, (25): the finite matrix space has its entrywise continuous norm.
Expose the underlying finite function space to instance search; this fixes only
infrastructure for Bochner integrability, without changing the twirl. -/
local instance learningMatrixContinuousENorm (d N : ℕ) :
    ContinuousENorm (Matrix (TrainingWires d N) (TrainingWires d N) ℂ) :=
  inferInstanceAs (ContinuousENorm (TrainingWires d N → TrainingWires d N → ℂ))

instance suMeasurable (d : ℕ) : MeasurableSpace (SU d) := borel _

instance suBorel (d : ℕ) : BorelSpace (SU d) := ⟨rfl⟩

instance suContinuousInv (d : ℕ) : ContinuousInv (SU d) where
  continuous_inv := continuous_induced_rng.mpr continuous_subtype_val.star

instance suTopologicalGroup (d : ℕ) : IsTopologicalGroup (SU d) where

instance suCompact (d : ℕ) : CompactSpace (SU d) := by
  have hc : IsClosed (Matrix.specialUnitaryGroup (Fin d) ℂ : Set ((Matrix (Fin d) (Fin d) ℂ))) :=
    isClosed_unitary.inter (isClosed_eq
      (show Continuous (fun A : Matrix (Fin d) (Fin d) ℂ => A.det) from
        continuous_id.matrix_det) continuous_const)
  have hb : Bornology.IsBounded (Matrix.specialUnitaryGroup (Fin d) ℂ : Set ((Matrix (Fin d) (Fin d) ℂ))) :=
    (show Bornology.IsBounded (Metric.closedBall (0 : (Matrix (Fin d) (Fin d) ℂ)) 1) from
      Metric.isBounded_closedBall).subset (by
        intro U hU
        simp only [Metric.mem_closedBall, dist_zero_right]
        exact entrywise_sup_norm_bound_of_unitary hU.1)
  exact isCompact_iff_compactSpace.mp (Metric.isCompact_of_isClosed_isBounded hc hb)

/-- PDF pp.3-4: whole-group probability Haar on the actual SU(d), not U(d). -/
def specialUnitaryHaar (d : ℕ) : Measure (SU d) :=
  Measure.haarMeasure (⟨⟨Set.univ, isCompact_univ⟩, by simp⟩ : PositiveCompacts _)

example (d : ℕ) : specialUnitaryHaar d Set.univ = 1 := Measure.haarMeasure_self

/-- PDF p.3, (8): the labeled rank-one measurement; matrices also admit unitary extensions. -/
def measurementFamily {d : ℕ} (U : (Matrix (Fin d) (Fin d) ℂ)) (i : Fin d) : (Matrix (Fin d) (Fin d) ℂ) :=
  fun a b => U a i * conj (U b i)

/-- PDF p.3, (10): only the classical label survives the device. -/
def learningMeasurementChannel {d : ℕ} (U rho : (Matrix (Fin d) (Fin d) ℂ)) : (Matrix (Fin d) (Fin d) ℂ) :=
  Matrix.diagonal (fun i => ((measurementFamily U i) * rho).trace)

/-- PDF p.3, (11): output-classical first, unnormalized Choi operator. -/
def learningMeasurementChoi {d : ℕ} (U : (Matrix (Fin d) (Fin d) ℂ)) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  fun a b => if a.1 = b.1 then measurementFamily U a.1 b.2 a.2 else 0

example (d : ℕ) (i a b : Fin d) :
    measurementFamily (1 : (Matrix (Fin d) (Fin d) ℂ)) i a b =
      (if a = i then 1 else 0) * (if b = i then 1 else 0) := by
  simp [measurementFamily, Matrix.one_apply]

/-- PDF p.3, (14): a parallel preparation is a density on all original input wires,
with identities on all classical output wires. No target coordinate occurs here. -/
def ParallelTraining {d N : ℕ}
    (A : Matrix (Labels d N × Labels d N) (Labels d N × Labels d N) ℂ) : Prop :=
  ∃ rho : Matrix (Labels d N) (Labels d N) ℂ,
    rho.PosSemidef ∧ rho.trace = 1 ∧
    ∀ j a k b, A (j,a) (k,b) = if j = k then rho a b else 0

/-- PDF pp.2-3, (3),(14): full causal trace recursion. The parameter k allows
only the earliest k calls to be grouped in one parallel preparation; k=0 is the
unrestricted sequential domain, k=N the all-parallel domain. The zero prefix is scalar. -/
def CausalTraining (d k : ℕ) : (N : ℕ) →
    Matrix (Labels d N × Labels d N) (Labels d N × Labels d N) ℂ → Prop
  | 0, A => A = 1
  | n+1, A =>
    A.PosSemidef ∧
    if n+1 ≤ k then ParallelTraining A else
      ∃ B : Matrix (Fin d × (Labels d n × Labels d n))
        (Fin d × (Labels d n × Labels d n)) ℂ,
      ∃ C : Matrix (Labels d n × Labels d n) (Labels d n × Labels d n) ℂ,
        B.PosSemidef ∧ CausalTraining d k n C ∧
        (∀ j a l b, A (j,a) (l,b) =
          if j 0 = l 0 then
            B (a 0,(Fin.tail j,Fin.tail a)) (b 0,(Fin.tail l,Fin.tail b)) else 0) ∧
        (∀ j a l b, (∑ x : Fin d, B (x,(j,a)) (x,(l,b))) = C (j,a) (l,b))

/-- PDF pp.2-3, (6),(14): positive branches with the entire causal normalization.
The target is last: its identity factors out of the deterministic sum. Finite
quantum memories are unrestricted, as in the comb characterization in the source. -/
def LearningInstrument {d N : ℕ} (k : ℕ) (R : Branches d N) : Prop :=
  (∀ i, (R i).PosSemidef) ∧
  ∃ A : Matrix (Labels d N × Labels d N) (Labels d N × Labels d N) ℂ,
    CausalTraining d k N A ∧
    ∀ t j a s l b, (∑ i, R i (t,(j,a)) (s,(l,b))) =
      if t = s then A (j,a) (l,b) else 0

example (d k : ℕ) : CausalTraining d k 0 1 := rfl

/-- PDF p.4, (22): actual diagonal classical slice, with target then source inputs. -/
def outcomeBlocks {d N : ℕ} (R : Branches d N) (i : Fin d) (j : Labels d N) : LearningBlock d N :=
  fun a b => R i (a.1,(j,a.2)) (b.1,(j,b.2))

/-- PDF p.4, (19): classical dephasing in the fixed basis. -/
def outcomeDephasing {d N : ℕ} (R : Branches d N) : Branches d N :=
  fun i a b => if a.2.1 = b.2.1 then R i a b else 0

/-- PDF p.4, (18): full classical diagonality. -/
def IsDiagonal {d N : ℕ} (R : Branches d N) : Prop := R = outcomeDephasing R

/-- PDF p.3, (12): the N-fold source-input action, newest call first. -/
def inputTensorPower {d N : ℕ} (U : (Matrix (Fin d) (Fin d) ℂ)) : Matrix (Labels d N) (Labels d N) ℂ :=
  fun a b => ∏ n, U (a n) (b n)

/-- PDF pp.3-4, (13),(21): link-product contraction INCLUDING the final transpose.
The same U is inserted at every source slot. -/
def replicatedPOVM {d N : ℕ} (R : Branches d N) (U : (Matrix (Fin d) (Fin d) ℂ)) (i : Fin d) : (Matrix (Fin d) (Fin d) ℂ) :=
  fun t s => ∑ j : Labels d N, ∑ a : Labels d N, ∑ b : Labels d N,
    conj (inputTensorPower U a j) *
      R i (s,(j,a)) (t,(j,b)) * inputTensorPower U b j

/-- PDF p.3, (15): normalized pure-state Haar distance. The accepted state law
is on unit vectors and has total mass one; its global phases do not affect Born weights.
Outcome cardinality m is independent of Hilbert dimension h. -/
def povmDistance {h m : ℕ} (hh : 0 < h) (P Q : Fin m → (Matrix (Fin h) (Fin h) ℂ)) : ℝ :=
  ∫ psi, ∑ i, (effectProb (P i - Q i) (pureDensity psi)) ^ 2
    ∂QAlgorithms.QuditFidelity.haarPureStateLaw h hh

/-- PDF p.4, (17): normalized SU(d) prior, using the delayed-input replica. -/
def learningDistance {d N : ℕ} (hd : 0 < d) (R : Branches d N) : ℝ :=
  ∫ U : SU d, povmDistance hd (measurementFamily (U : (Matrix (Fin d) (Fin d) ℂ)))
    (replicatedPOVM R (U : (Matrix (Fin d) (Fin d) ℂ))) ∂specialUnitaryHaar d

/-- PDF p.7, (50), and p.10, Remark 1: Haar-averaged overlap for arbitrary
learners. On covariant learners it is exactly the displayed seed overlap (50).
The averaging is necessary for unrestricted comparisons: a fixed computational
measurement has seed overlap one but is not a perfect unknown-measurement learner. -/
def learningScore {d N : ℕ} (R : Branches d N) : ℝ :=
  ∫ U : SU d, (∑ i, effectProb (measurementFamily (U : (Matrix (Fin d) (Fin d) ℂ)) i)
    (replicatedPOVM R (U : (Matrix (Fin d) (Fin d) ℂ)) i)) / d ∂specialUnitaryHaar d

/-- PDF p.4, (23): conjugate target, direct source inputs, classical identity. -/
def covariantRepresentation {d N : ℕ} (U : (Matrix (Fin d) (Fin d) ℂ)) : Matrix (TrainingWires d N) (TrainingWires d N) ℂ :=
  fun a b => if a.2.1 = b.2.1 then
    conj (U a.1 b.1) * inputTensorPower U a.2.2 b.2.2 else 0

/-- PDF p.4, (25): constructive special-unitary twirl. -/
def covariantTwirl {d N : ℕ} (R : Branches d N) : Branches d N :=
  fun i => ∫ U : SU d,
    covariantRepresentation (U : (Matrix (Fin d) (Fin d) ℂ)) * R i *
      (covariantRepresentation (U : (Matrix (Fin d) (Fin d) ℂ)))ᴴ ∂specialUnitaryHaar d

/-- PDF p.4, (23). -/
def IsLearningCovariant {d N : ℕ} (R : Branches d N) : Prop :=
  ∀ U : SU d, ∀ i, R i * covariantRepresentation (U : (Matrix (Fin d) (Fin d) ℂ)) =
    covariantRepresentation (U : (Matrix (Fin d) (Fin d) ℂ)) * R i

/-- PDF p.5, (28),(30): classical coordinate permutation; no quantum wire is reordered. -/
def relabelClassical {d N : ℕ} (R : Branches d N)
    (sigma : Equiv.Perm (Fin d)) : Branches d N :=
  fun i a b => R (sigma i) (a.1,(sigma ∘ a.2.1,a.2.2))
    (b.1,(sigma ∘ b.2.1,b.2.2))

/-- PDF p.5, (30): finite relabeling average after covariance. -/
def relabelAverage {d N : ℕ} (R : Branches d N) : Branches d N :=
  (Fintype.card (Equiv.Perm (Fin d)) : ℂ)⁻¹ • ∑ sigma, relabelClassical R sigma

/-- PDF p.5, (28). -/
def IsRelabelInvariant {d N : ℕ} (R : Branches d N) : Prop :=
  ∀ sigma : Equiv.Perm (Fin d), R = relabelClassical R sigma

/-- PDF pp.6-7: all three reductions retained in subsequent optimizations. -/
def IsLearningSymmetric {d N : ℕ} (R : Branches d N) : Prop :=
  IsDiagonal R ∧ IsLearningCovariant R ∧ IsRelabelInvariant R

/-- PDF p.4: global D-optimality, with attainment rather than a real supremum. -/
def IsOptimal {d N : ℕ} (hd : 0 < d) (R : Branches d N) : Prop :=
  LearningInstrument 0 R ∧ ∀ S : Branches d N, LearningInstrument 0 S →
    learningDistance hd R ≤ learningDistance hd S

/-- PDF p.5, (33): one label permutation on every coordinate; no slot permutation. -/
def outcomeOrbit (d N : ℕ) : Setoid (Labels d (N+1)) where
  r x y := ∃ sigma : Equiv.Perm (Fin d), y = sigma ∘ x
  iseqv := ⟨fun x => ⟨1,rfl⟩,
    by
      intro x y h
      obtain ⟨sigma,rfl⟩ := h
      exact ⟨sigma.symm, by ext i; simp⟩,
    by
      intro x y z hxy hyz
      obtain ⟨sigma,rfl⟩ := hxy
      obtain ⟨tau,rfl⟩ := hyz
      exact ⟨sigma.trans tau,rfl⟩⟩

/-- PDF p.6: a partition is precisely an equivalence relation on the positions. -/
def BoundedPartitions (d N : ℕ) :=
  {s : Setoid (Fin (N+1)) // Nat.card (Quotient s) ≤ d}

/-- PDF p.9: swap source quantum input wires 2 and 0, leaving the target fixed. -/
def swapInput {d : ℕ} (a : Labels d 2) : Labels d 2 := fun n => a (Fin.rev n)

/-- PDF p.9, Lemma 6: swap source outcome labels AND source inputs. -/
def swapLearner {d : ℕ} (R : Branches d 2) : Branches d 2 :=
  fun i a b => R i (a.1,(swapInput a.2.1,swapInput a.2.2))
    (b.1,(swapInput b.2.1,swapInput b.2.2))

/-- PDF p.9: constructive averaging, on full source wires. -/
def swapAverage {d : ℕ} (R : Branches d 2) : Branches d 2 :=
  (1/2 : ℂ) • (R + swapLearner R)

example {d : ℕ} (a : Labels d 2) : swapInput (swapInput a) = a := by
  ext n
  simp [swapInput]

/-- PDF p.6, (38): trivial-representation projector on target and one source input. -/
def oneUseProjector (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  fun a b => if a.1 = a.2 ∧ b.1 = b.2 then (d : ℂ)⁻¹ else 0

/-- PDF p.8, (60): concrete optimal blocks, with no normalized-Choi conversion. -/
def oneUseOptimalInstrument (d : ℕ) : Branches d 1 :=
  fun i a b => if a.2.1 = b.2.1 then
    if i = a.2.1 0 then
      (d : ℂ)⁻¹ * oneUseProjector d (a.1,a.2.2 0) (b.1,b.2.2 0)
    else
      ((d : ℂ) * (d-1 : ℂ))⁻¹ *
        ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) - oneUseProjector d)
          (a.1,a.2.2 0) (b.1,b.2.2 0)
  else 0

/-- PDF p.8, (63): normalized maximally entangled probe, target/memory ordering. -/
def oneUseProbe (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  oneUseProjector d

/-- PDF p.8, (63)-(64): retrieve on the target and stored half of the probe;
Pp outcome returns j; Pq outcome is uniform on labels other than j. -/
def oneUseRetrieval (d : ℕ) (i j : Fin d) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  if i = j then oneUseProjector d else
    (d-1 : ℂ)⁻¹ • (1 - oneUseProjector d)

/-- PDF p.8: physical probability of the stated one-use realization, summing
training outcomes. Conditional stored density is E_j(U)^T/d (subnormalized). -/
def oneUseOperationalProbability {d : ℕ} (U rho : (Matrix (Fin d) (Fin d) ℂ)) (i : Fin d) : ℝ :=
  ∑ j, effectProb (oneUseRetrieval d i j)
    (Matrix.kronecker rho ((d : ℂ)⁻¹ • (measurementFamily U j)ᵀ))

/-- PDF pp.6,9: symmetric and antisymmetric projectors of the two source inputs. -/
def sourceSwap (d : ℕ) : Matrix (Labels d 2) (Labels d 2) ℂ :=
  fun a b => if a = swapInput b then 1 else 0

def sourceSymmetric (d : ℕ) : Matrix (Labels d 2) (Labels d 2) ℂ :=
  (1/2 : ℂ) • (1 + sourceSwap d)

def sourceAntisymmetric (d : ℕ) : Matrix (Labels d 2) (Labels d 2) ℂ :=
  (1/2 : ℂ) • (1 - sourceSwap d)

/-- PDF p.9, (75): dimensions are real, avoiding truncated natural subtraction. -/
def dplus (d : ℕ) : ℝ := (d : ℝ) * (d+1) / 2

def dminus (d : ℕ) : ℝ := (d : ℝ) * (d-1) / 2

/-- PDF p.9, (75): actual input density coefficients. -/
def FixedInputParameters (d : ℕ) (tp tm : ℝ) : Prop :=
  0 ≤ tp ∧ 0 ≤ tm ∧ dplus d * tp + dminus d * tm = 1

/-- PDF pp.9,12, corrected from the sector optima (A6)-(A12).
The printed (82),(A14) misses +4 for d>=3 and counts an absent gamma sector at d=2. -/
def twoUseScalarObjective (d : ℕ) (tp tm : ℝ) : ℝ :=
  if d = 2 then (13/6 : ℝ)*tp + tm/2 + Real.sqrt (tp*tm/3)
  else ((d : ℝ)^2 + 3*d + 4)/(2*(d+1))*tp +
    Real.sqrt ((d-1 : ℝ)/(d+1)) * Real.sqrt (tp*tm) + (d : ℝ)/2*tm

/-- PDF p.6, (40),(42): actual alpha embedding vectors. Column 0 is plus,
column 1 is minus; only source input wires are interchanged in the second term. -/
def alphaVector (d : ℕ) (sign : Fin 2) (m : Fin d) (a : Fin d × Labels d 2) : ℂ :=
  ((if a.1 = a.2 0 ∧ m = a.2 1 then 1 else 0) +
    (if sign = 0 then 1 else -1) *
      (if m = a.2 0 ∧ a.1 = a.2 1 then 1 else 0)) /
    (Real.sqrt (2*((d : ℝ) + if sign = 0 then 1 else -1)) : ℂ)

/-- PDF p.6, (40),(42): matrix multiplicity blocks mapped into physical wires. -/
def alphaEmbedding (d : ℕ) (A : (Matrix (Fin 2) (Fin 2) ℂ)) : LearningBlock d 2 :=
  fun a b => ∑ m : Fin d, ∑ x : Fin 2, ∑ y : Fin 2,
    alphaVector d x m a * A x y * conj (alphaVector d y m b)

def betaProjector (d : ℕ) : LearningBlock d 2 :=
  Matrix.kronecker (1 : (Matrix (Fin d) (Fin d) ℂ)) (sourceSymmetric d) -
    alphaEmbedding d (Matrix.single 0 0 1)

def gammaProjector (d : ℕ) : LearningBlock d 2 :=
  Matrix.kronecker (1 : (Matrix (Fin d) (Fin d) ℂ)) (sourceAntisymmetric d) -
    alphaEmbedding d (Matrix.single 1 1 1)

/-- PDF pp.8-9, (68): xxx,xxy,xyx,xyy,xyz in that order. -/
def twoUsePattern {d : ℕ} (i : Fin d) (j : Labels d 2) : Fin 5 :=
  if i = j 0 then (if j 0 = j 1 then 0 else 1)
  else if i = j 1 then 2 else if j 0 = j 1 then 3 else 4

/-- PDF p.11, (A2): multiplicity of source labels at fixed replica label. -/
def patternMultiplicity (d : ℕ) (p : Fin 5) : ℝ :=
  if p = 0 then 1 else if p = 4 then (d-1 : ℝ)*(d-2) else d-1

/-- PDF p.11: rescaled alpha matrices and beta/gamma scalars, not abstract free irreps. -/
structure TwoUseBlocks where
  alpha : Fin 5 → (Matrix (Fin 2) (Fin 2) ℂ)
  beta : Fin 5 → ℝ
  gamma : Fin 5 → ℝ

/-- PDF pp.6,11, (39)-(42),(A2): reconstruct the physical block using the actual
embedding. The absent xyz class is never evaluated by twoUsePattern when d=2. -/
def physicalTwoUseBlock (d : ℕ) (B : TwoUseBlocks) (p : Fin 5) : LearningBlock d 2 :=
  if d = 2 ∧ p = 4 then 0 else
  ((patternMultiplicity d p : ℂ)⁻¹) •
    (alphaEmbedding d (B.alpha p) + (B.beta p : ℂ) • betaProjector d +
      (B.gamma p : ℂ) • gammaProjector d)

/-- PDF pp.8-9, (66),(68): full instrument assembled from positive rescaled blocks. -/
def blockInstrument (d : ℕ) (B : TwoUseBlocks) : Branches d 2 :=
  fun i a b => if a.2.1 = b.2.1 then
    physicalTwoUseBlock d B (twoUsePattern i a.2.1) (a.1,a.2.2) (b.1,b.2.2) else 0

/-- PDF p.12: explicit simultaneously attaining rescaled blocks, with corrected
qubit beta xxy=xyx=tp/2. The qubit gamma and xyz sectors are zero. -/
def twoUseAttainingBlocks (d : ℕ) (tp tm : ℝ) : TwoUseBlocks :=
  let A : (Matrix (Fin 2) (Fin 2) ℂ) := !![(tp : ℂ), (Real.sqrt (tp*tm) : ℂ);
    (Real.sqrt (tp*tm) : ℂ), (tm : ℂ)]
  let Z : (Matrix (Fin 2) (Fin 2) ℂ) := !![1,0;0,-1]
  let X : (Matrix (Fin 2) (Fin 2) ℂ) := ((d-1 : ℂ)/2) • A
  { alpha := fun p => if p = 0 then !![(tp : ℂ),0;0,(tm : ℂ)]
      else if p = 1 then X else if p = 2 then Z * X * Z else 0
    beta := fun p => if p = 3 then tp else
      if d = 2 then (if p = 1 ∨ p = 2 then tp/2 else 0)
      else if p = 4 then (d-1)*tp else 0
    gamma := fun p => if d = 2 then 0 else
      if p = 3 then tm else if p = 4 then (d-1)*tm else 0 }

/-- PDF p.11, (A4),(A5): fixed-input positive swap-symmetric blocks. At d=2
remove the gamma and xyz sectors entirely; their coefficients are fixed to zero. -/
def FeasibleBlocks (d : ℕ) (tp tm : ℝ) (B : TwoUseBlocks) : Prop :=
  FixedInputParameters d tp tm ∧
  (∀ p, (B.alpha p).PosSemidef ∧ 0 ≤ B.beta p ∧ 0 ≤ B.gamma p) ∧
  (let Z : (Matrix (Fin 2) (Fin 2) ℂ) := !![1,0;0,-1]
   B.alpha 2 = Z * B.alpha 1 * Z ∧
   B.alpha 0 = Z * B.alpha 0 * Z ∧ B.alpha 3 = Z * B.alpha 3 * Z ∧
   B.alpha 4 = Z * B.alpha 4 * Z ∧ B.beta 2 = B.beta 1 ∧ B.gamma 2 = B.gamma 1) ∧
  B.alpha 0 + B.alpha 3 = !![(tp : ℂ),0;0,(tm : ℂ)] ∧
  B.alpha 1 + B.alpha 2 + B.alpha 4 =
    !![(((d-1 : ℝ)*tp : ℝ) : ℂ),0;0,(((d-1 : ℝ)*tm : ℝ) : ℂ)] ∧
  B.beta 0 + B.beta 3 = tp ∧ 2*B.beta 1 + B.beta 4 = (d-1)*tp ∧
  (if d = 2 then
    (∀ p, B.gamma p = 0) ∧ B.alpha 4 = 0 ∧ B.beta 4 = 0
   else B.gamma 0 + B.gamma 3 = tm ∧ 2*B.gamma 1 + B.gamma 4 = (d-1)*tm)

/-- PDF p.11, (A1), including the factor 1/2 on the alpha xxy matrix. -/
def deltaAlpha (d : ℕ) (p : Fin 5) : (Matrix (Fin 2) (Fin 2) ℂ) :=
  let X : (Matrix (Fin 2) (Fin 2) ℂ) := (1/2 : ℂ) •
    !![((d+1 : ℂ)⁻¹), ((Real.sqrt ((d : ℝ)^2-1) : ℂ)⁻¹);
       ((Real.sqrt ((d : ℝ)^2-1) : ℂ)⁻¹), ((d-1 : ℂ)⁻¹)]
  let Z : (Matrix (Fin 2) (Fin 2) ℂ) := !![1,0;0,-1]
  if p = 0 then !![(2/(d+1 : ℂ)),0;0,0]
  else if p = 1 then X else if p = 2 then Z * X * Z else 0

def deltaBeta (d : ℕ) (p : Fin 5) : ℝ :=
  if p = 0 then (d-1 : ℝ)/(d+1) else if p = 3 then 1
  else if p = 4 then 1/2 else (d : ℝ)/(2*(d+1))

def deltaGamma (d : ℕ) (p : Fin 5) : ℝ :=
  if p = 0 ∨ p = 3 then 0 else if p = 4 then 1/2
  else (d-2 : ℝ)/(2*(d-1))

/-- PDF p.11, (A3): sector scores for the actual rescaled multiplicity blocks. -/
def sectorAlpha (d : ℕ) (B : TwoUseBlocks) : ℝ :=
  ∑ p, ((deltaAlpha d p * B.alpha p).trace).re

def sectorBeta (d : ℕ) (B : TwoUseBlocks) : ℝ := ∑ p, deltaBeta d p * B.beta p

def sectorGamma (d : ℕ) (B : TwoUseBlocks) : ℝ := ∑ p, deltaGamma d p * B.gamma p

example (tp tm : ℝ) : (twoUseAttainingBlocks 2 tp tm).beta 1 = tp/2 := by
  simp [twoUseAttainingBlocks]

example (tp tm : ℝ) : (twoUseAttainingBlocks 2 tp tm).gamma 0 = 0 := by
  simp [twoUseAttainingBlocks]

/-- PDF p.4: taking a classical slice after dephasing keeps the original block. -/
example {d N : ℕ} (R : Branches d N) (i : Fin d) (j : Labels d N) :
    outcomeBlocks (outcomeDephasing R) i j = outcomeBlocks R i j := by
  ext a b
  simp [outcomeBlocks, outcomeDephasing]

/-- PDF p.3: the auxiliary zero-call contraction has no oracle dependence. -/
example {d : ℕ} (R : Branches d 0) (U V : (Matrix (Fin d) (Fin d) ℂ)) :
    replicatedPOVM R U = replicatedPOVM R V := by
  funext i t s
  simp [replicatedPOVM, inputTensorPower]

/-- PDF p.8: the positive Bell outcome reports the stored training label. -/
example (d : ℕ) (j : Fin d) : oneUseRetrieval d j j = oneUseProjector d := by
  simp [oneUseRetrieval]

/-! Each following theorem corresponds to exactly one nondeferred inventory node. -/

end QAlgorithms.Papers.Independent.Claimed50.P14


