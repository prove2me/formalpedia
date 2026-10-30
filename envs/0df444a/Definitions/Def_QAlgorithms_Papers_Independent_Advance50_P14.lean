-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P14
-- name    : QAlgorithms_Papers_Independent_Advance50_P14
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T10:12:23.400778+00:00
-- url     : https://prove2.me/theorems/defeb77d-4720-4a2d-ba3f-17303335236c
-- title:
--   Definitions for A reversible theory of entanglement and its relation to the second law
-- statement:
--   The objects the formalized statements of *A reversible theory of entanglement and its relation to the second law* (arXiv:0710.5827) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `MultipartiteRegister`: PDF pp.2–3: an m-party finite system with positive local dimensions.
--   - `PartyOperator`: PDF p.2: operators on the full multipartite Hilbert space.
--   - `IsMultipartiteSeparable`: PDF p.3, Eq.(1): full multipartite separability, using the frozen finite mixed-product decomposition after a local basis enumeration. The coordinate bijections impose no restriction on positive finite local dimensions. The global density guard records the source domain explicitly.
--   - `SeparableCone`: PDF p.2: cone of the separable states, including the zero operator.
--   - `globalRobustness`: PDF p.4: global robustness uses arbitrary density-matrix noise.
--   - `standardRobustness`: PDF p.16: standard robustness uses separable noise. The printed s∈R is corrected to s≥0, as required by a mixing weight; negative s<-1 would make the printed minimization unbounded even on a separable state.
--   - `logRobustness`: PDF p.7 and p.16: logarithmic global/standard robustness, in bits.
--   - `multipartiteRelativeEntanglement`: PDF p.4: E_R, finite on density matrices of any fixed finite system.
--   - `powerRegister`: PDF p.6: n copies, with all copies of each party grouped together. For n=0 each local space is one-dimensional, rather than the zero vector space.
--   - `powerDensity`: PDF p.6: the actual tensor power, including the scalar identity at n=0.
--   - `regularizedMultipartiteEntanglement`: PDF p.6, Eq.(2): positive-block regularization; the theorem asserts convergence of the displayed entropy ratios to this constructed infimum.
--   - `bellRegister`: PDF pp.3,6: a K-by-K Bell register shared by parties 1 and 2. Omitted parties are trivial. Positivity of K excludes the empty Hilbert space.
--   - `partyBellDensity`: PDF p.3: normalized Phi(K), with K=1 the scalar density matrix.
--   - `currencyRegister`: PDF p.6: integer k Bell-pair currency, canonically regrouped as Phi(2^k).
--   - `currencyDensity`: PDF p.6: k actual normalized Bell pairs; k=0 is the trivial register.
--   - `NonEntangling`: PDF p.3, Definition II.1: CPTP and separability preserving on the specified input/output partitions, without a quantification over ancillary systems.
--   - `EpsilonNonEntangling`: PDF p.6, Definition III.1: uniform global-robustness leakage bound.
--   - `TraceNonEntangling`: PDF p.15, Eq.(20): full trace-norm leakage, uniformly over free inputs. The nearest separable output exists by finite-dimensional compactness.
--   - `LeakageModel`: PDF pp.6,12,15: the three distinct operational leakage conventions.
--   - `AllowedLeakageMap`: PDF pp.6,12,15: the allowed finite-block operation for the selected model.
--   - `FormationProtocol`: PDF p.6, Definition III.2: feasible formation counts and actual CPTP maps. All limits use positive input blocklength n+1. Leakage vanishes absolutely.
--   - `DistillationProtocol`: PDF p.6, Definition III.3 and p.12, Eq.(14): feasible distillation counts.
--   - `asymptoticFormationCost`: PDF p.6: cost is an infimum of extended limsup integer-copy rates. No existence of an optimizing protocol is assumed.
--   - `distillableEntanglement`: PDF pp.6,12: yield is a SUPREMUM of extended liminf integer-copy rates. The word 'infimum' below Definition III.3 is a typo; its display and proof use sup.
--   - `AsymptoticConverts`: PDF p.7, Eqs.(3)-(4): conversion with explicit discarded copy counts. The dimensions and even the number of parties may differ between A and B.
--   - `smoothedRegularizedRobustness`: PDF p.7, Eq.(6), and p.16, Eq.(21): smoothing and regularization of log robustness. Approximation by states is equivalent to choosing smoothing radii tending to zero; the infimum ranges over all such sequences.
--   - `positivePartTrace`: PDF p.2: trace of the positive part of a Hermitian matrix.
--   - `singletFractionOf`: PDF p.11, Eq.(12): singlet fraction of an actual map.
--   - `singletFractions`: PDF pp.11,15: feasible singlet fractions, under the specified leakage model.
--   - `singletDualObjective`: PDF p.11, Eq.(13), and corrected p.15 formula: dual objective on cone(S).
--   - `PhysicalState`: PDF p.17: a physical state, including its finite partition and normalization.
--   - `WeightedFamily`: PDF pp.17–18: a formal finite product of states with nonnegative real copy weights. Real powers are rates and do not mean fractional matrix powers.
--   - `batchRegister`: PDF p.18: actual block space for integer counts of each component.
--   - `batchDensity`: PDF p.18: tensor product of the specified integer numbers of component states.
--   - `RealizesWeights`: PDF pp.17–18: integer copy sequences realizing the real weights. A zero weight means EXACTLY zero copies, hence a trivial register.
--   - `WeightedConverts`: PDF p.18: the actual asymptotic transformation of finite weighted products. The output's o(n) losses are absorbed in its integer sequences of the same limiting rates. Every map is between its actual block spaces.
--   - `scaleFamily`: PDF p.17: scaling multiplies all component copy weights.
--   - `singleFamily`: PDF p.17: a single state with its formal copy weight.
--   - `pairFamily`: PDF pp.17–18: a two-component tensor product with independent copy weights.
--   - `tensorRegister`: PDF pp.19–20: local tensor product, preserving the m-party partition.
--   - `partyTensorDensity`: PDF pp.19–20: actual product density in the grouped local basis.
--   - `TensorConsistency`: PDF p.19, axiom 6: a GLOBAL property over every pair of compatible finite multipartite transformations. No tensor closure is assumed in SEPP.
--   - `NoCatalysisAt`: PDF p.19, Eq.(24), and p.20: absence of catalysis in the m-party theory. The SAME arbitrary normalized catalyst pi is returned asymptotically.
-- source:
--   A reversible theory of entanglement and its relation to the second law, arXiv:0710.5827v3, https://arxiv.org/abs/0710.5827v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P54
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33

/-!
Statements from arXiv:0710.5827v3. All new definitions are local to this paper.
Accepted libraries supply the product basis, matrix operators, full multipartite
separability (through local basis enumeration), support-aware relative entropy
in bits, the Bell projector and the spectral positive part. Bipartite REE is
not used for the full multipartite partition. Other same-named accepted objects
have different domains or operation classes; the local names distinguish them.
Finite local basis types carry both finiteness and nonemptiness. Copies are
regrouped by party; no ancillary closure of the operation class is imposed.
Real extrema below are used only for valid finite-dimensional density matrices:
robustness has a nonempty, nonnegative feasible set, and E_R is finite by
comparison with the full-rank product maximally mixed state. Operational
extrema and rate limsups/liminfs use ENNReal, including infinite yield.
Source corrections are identified at the affected declarations and in the audit.
-/

noncomputable section

open Filter
open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis)
open scoped Matrix ComplexOrder ENNReal NNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Advance50.P14

/-- PDF pp.2–3: an m-party finite system with positive local dimensions. -/
structure MultipartiteRegister (m : ℕ) where
  two_le : 2 ≤ m
  Local : Fin m → Type
  finite : ∀ i, Fintype (Local i)
  nonempty : ∀ i, Nonempty (Local i)

attribute [instance] MultipartiteRegister.finite MultipartiteRegister.nonempty

/-- PDF p.2: operators on the full multipartite Hilbert space. -/
abbrev PartyOperator {m : ℕ} (A : MultipartiteRegister m) :=
  QAlgorithms.Papers.Independent.Information100.P58.Operator (RegisterBasis A.Local)

/-- PDF p.3, Eq.(1): full multipartite separability, using the frozen finite
mixed-product decomposition after a local basis enumeration. The coordinate
bijections impose no restriction on positive finite local dimensions.
The global density guard records the source domain explicitly. -/
def IsMultipartiteSeparable {m : ℕ} (A : MultipartiteRegister m) (rho : PartyOperator A) : Prop :=
  IsDensityMatrix rho ∧
    ∃ (s : QAlgorithms.Papers.Independent.Claimed50.P33.FiniteState m)
      (e : (i : Fin m) → A.Local i ≃ Fin (s.dims i)),
      QAlgorithms.Papers.Independent.Claimed50.P33.IsMixedFullySeparable s ∧
      ∀ x y : RegisterBasis A.Local, rho x y =
        s.rho (fun i => e i (x i)) (fun i => e i (y i))

/-- PDF p.2: cone of the separable states, including the zero operator. -/
def SeparableCone {m : ℕ} (A : MultipartiteRegister m) (Z : PartyOperator A) : Prop :=
  ∃ t : ℝ, 0 ≤ t ∧ ∃ sigma : PartyOperator A, IsMultipartiteSeparable A sigma ∧ Z = (t : ℂ) • sigma

/-- PDF p.4: global robustness uses arbitrary density-matrix noise. -/
def globalRobustness {m : ℕ} (A : MultipartiteRegister m) (rho : PartyOperator A) : ℝ :=
  sInf {s : ℝ | 0 ≤ s ∧ ∃ pi : PartyOperator A, IsDensityMatrix pi ∧
    IsMultipartiteSeparable A (((1 + s : ℝ)⁻¹ : ℂ) • (rho + (s : ℂ) • pi))}

/-- PDF p.16: standard robustness uses separable noise. The printed s∈R
is corrected to s≥0, as required by a mixing weight; negative s<-1 would
make the printed minimization unbounded even on a separable state. -/
def standardRobustness {m : ℕ} (A : MultipartiteRegister m) (rho : PartyOperator A) : ℝ :=
  sInf {s : ℝ | 0 ≤ s ∧ ∃ pi : PartyOperator A, IsMultipartiteSeparable A pi ∧
    IsMultipartiteSeparable A (((1 + s : ℝ)⁻¹ : ℂ) • (rho + (s : ℂ) • pi))}

/-- PDF p.7 and p.16: logarithmic global/standard robustness, in bits. -/
def logRobustness {m : ℕ} (standard : Bool) (A : MultipartiteRegister m) (rho : PartyOperator A) : ℝ :=
  Real.logb 2 (1 + if standard then standardRobustness A rho else globalRobustness A rho)

/-- PDF p.4: E_R, finite on density matrices of any fixed finite system. -/
def multipartiteRelativeEntanglement {m : ℕ} (A : MultipartiteRegister m) (rho : PartyOperator A) : ℝ :=
  (sInf {e : ℝ≥0∞ | ∃ sigma : PartyOperator A, IsMultipartiteSeparable A sigma ∧
    e = QAlgorithms.Papers.Independent.Information100.P54.relativeEntropyBits rho sigma}).toReal

/-- PDF p.6: n copies, with all copies of each party grouped together.
For n=0 each local space is one-dimensional, rather than the zero vector space. -/
def powerRegister {m : ℕ} (A : MultipartiteRegister m) (n : ℕ) : MultipartiteRegister m where
  two_le := A.two_le
  Local i := Fin n → A.Local i
  finite _ := inferInstance
  nonempty _ := inferInstance

/-- PDF p.6: the actual tensor power, including the scalar identity at n=0. -/
def powerDensity {m : ℕ} (A : MultipartiteRegister m) (rho : PartyOperator A) (n : ℕ) :
    PartyOperator (powerRegister A n) :=
  fun x y => ∏ t : Fin n, rho (fun i => x i t) (fun i => y i t)

/-- PDF p.6, Eq.(2): positive-block regularization; the theorem asserts
convergence of the displayed entropy ratios to this constructed infimum. -/
def regularizedMultipartiteEntanglement {m : ℕ} (A : MultipartiteRegister m) (rho : PartyOperator A) : ℝ :=
  sInf {v : ℝ | ∃ n : ℕ, v = multipartiteRelativeEntanglement (powerRegister A (n + 1))
    (powerDensity A rho (n + 1)) / (n + 1 : ℝ)}

/-- PDF pp.3,6: a K-by-K Bell register shared by parties 1 and 2.
Omitted parties are trivial. Positivity of K excludes the empty Hilbert space. -/
def bellRegister (K : ℕ) (hK : 0 < K) : MultipartiteRegister 2 where
  two_le := le_refl 2
  Local _ := Fin K
  finite _ := inferInstance
  nonempty _ := ⟨⟨0, hK⟩⟩

/-- PDF p.3: normalized Phi(K), with K=1 the scalar density matrix. -/
def partyBellDensity (K : ℕ) (hK : 0 < K) : PartyOperator (bellRegister K hK) :=
  (QAlgorithms.Papers.Independent.Information100.P54.maximallyEntangledProjector K).submatrix
    (fun x : RegisterBasis (bellRegister K hK).Local => (x 0, x 1))
    (fun x : RegisterBasis (bellRegister K hK).Local => (x 0, x 1))

/-- PDF p.6: integer k Bell-pair currency, canonically regrouped as Phi(2^k). -/
def currencyRegister (k : ℕ) : MultipartiteRegister 2 := bellRegister (2 ^ k) (by positivity)

/-- PDF p.6: k actual normalized Bell pairs; k=0 is the trivial register. -/
def currencyDensity (k : ℕ) : PartyOperator (currencyRegister k) :=
  partyBellDensity (2 ^ k) (by positivity)

/-- PDF p.3, Definition II.1: CPTP and separability preserving on the specified
input/output partitions, without a quantification over ancillary systems. -/
def NonEntangling {m l : ℕ} (A : MultipartiteRegister m) (B : MultipartiteRegister l)
    (L : Superop (RegisterBasis A.Local) (RegisterBasis B.Local)) : Prop :=
  IsChannel L ∧ ∀ sigma : PartyOperator A, IsMultipartiteSeparable A sigma → IsMultipartiteSeparable B (L sigma)

/-- PDF p.6, Definition III.1: uniform global-robustness leakage bound. -/
def EpsilonNonEntangling {m l : ℕ} (A : MultipartiteRegister m) (B : MultipartiteRegister l)
    (epsilon : ℝ) (L : Superop (RegisterBasis A.Local) (RegisterBasis B.Local)) : Prop :=
  0 ≤ epsilon ∧ IsChannel L ∧
    ∀ sigma : PartyOperator A, IsMultipartiteSeparable A sigma → globalRobustness B (L sigma) ≤ epsilon

/-- PDF p.15, Eq.(20): full trace-norm leakage, uniformly over free inputs.
The nearest separable output exists by finite-dimensional compactness. -/
def TraceNonEntangling {m l : ℕ} (A : MultipartiteRegister m) (B : MultipartiteRegister l)
    (epsilon : ℝ) (L : Superop (RegisterBasis A.Local) (RegisterBasis B.Local)) : Prop :=
  0 ≤ epsilon ∧ IsChannel L ∧ ∀ sigma : PartyOperator A, IsMultipartiteSeparable A sigma →
    ∃ pi : PartyOperator B, IsMultipartiteSeparable B pi ∧ traceNorm (L sigma - pi) ≤ epsilon

/-- PDF pp.6,12,15: the three distinct operational leakage conventions. -/
inductive LeakageModel where
  | ane
  | strict
  | trace

/-- PDF pp.6,12,15: the allowed finite-block operation for the selected model. -/
def AllowedLeakageMap {m l : ℕ} (model : LeakageModel) (A : MultipartiteRegister m) (B : MultipartiteRegister l)
    (epsilon : ℝ) (L : Superop (RegisterBasis A.Local) (RegisterBasis B.Local)) : Prop :=
  match model with
  | .ane => EpsilonNonEntangling A B epsilon L
  | .strict => 0 ≤ epsilon ∧ NonEntangling A B L
  | .trace => TraceNonEntangling A B epsilon L

/-- PDF p.6, Definition III.2: feasible formation counts and actual CPTP maps.
All limits use positive input blocklength n+1. Leakage vanishes absolutely. -/
def FormationProtocol {m : ℕ} (model : LeakageModel) (A : MultipartiteRegister m) (rho : PartyOperator A)
    (k : ℕ → ℕ) : Prop :=
  ∃ epsilon : ℕ → ℝ,
    ∃ L : (n : ℕ) → Superop (RegisterBasis (currencyRegister (k n)).Local)
      (RegisterBasis (powerRegister A (n + 1)).Local),
    (∀ n, AllowedLeakageMap model (currencyRegister (k n)) (powerRegister A (n + 1))
      (epsilon n) (L n)) ∧ Tendsto epsilon atTop (nhds 0) ∧
    Tendsto (fun n => traceNorm (L n (currencyDensity (k n)) -
      powerDensity A rho (n + 1))) atTop (nhds 0)

/-- PDF p.6, Definition III.3 and p.12, Eq.(14): feasible distillation counts. -/
def DistillationProtocol {m : ℕ} (model : LeakageModel) (A : MultipartiteRegister m) (rho : PartyOperator A)
    (k : ℕ → ℕ) : Prop :=
  ∃ epsilon : ℕ → ℝ,
    ∃ L : (n : ℕ) → Superop (RegisterBasis (powerRegister A (n + 1)).Local)
      (RegisterBasis (currencyRegister (k n)).Local),
    (∀ n, AllowedLeakageMap model (powerRegister A (n + 1)) (currencyRegister (k n))
      (epsilon n) (L n)) ∧ Tendsto epsilon atTop (nhds 0) ∧
    Tendsto (fun n => traceNorm (L n (powerDensity A rho (n + 1)) -
      currencyDensity (k n))) atTop (nhds 0)

/-- PDF p.6: cost is an infimum of extended limsup integer-copy rates.
No existence of an optimizing protocol is assumed. -/
def asymptoticFormationCost {m : ℕ} (model : LeakageModel) (A : MultipartiteRegister m) (rho : PartyOperator A) : ℝ≥0∞ :=
  sInf {v | ∃ k : ℕ → ℕ, FormationProtocol model A rho k ∧
    v = limsup (fun n => (k n : ℝ≥0∞) / (n + 1 : ℝ≥0∞)) atTop}

/-- PDF pp.6,12: yield is a SUPREMUM of extended liminf integer-copy rates.
The word 'infimum' below Definition III.3 is a typo; its display and proof use sup. -/
def distillableEntanglement {m : ℕ} (model : LeakageModel) (A : MultipartiteRegister m)
    (rho : PartyOperator A) : ℝ≥0∞ :=
  sSup {v | ∃ k : ℕ → ℕ, DistillationProtocol model A rho k ∧
    v = liminf (fun n => (k n : ℝ≥0∞) / (n + 1 : ℝ≥0∞)) atTop}

/-- PDF p.7, Eqs.(3)-(4): conversion with explicit discarded copy counts.
The dimensions and even the number of parties may differ between A and B. -/
def AsymptoticConverts {m l : ℕ} (A : MultipartiteRegister m) (rho : PartyOperator A)
    (B : MultipartiteRegister l) (sigma : PartyOperator B) : Prop :=
  ∃ d : ℕ → ℕ, (∀ n, d n ≤ n + 1) ∧
    Tendsto (fun n => (d n : ℝ) / (n + 1 : ℝ)) atTop (nhds 0) ∧
    ∃ epsilon : ℕ → ℝ,
    ∃ L : (n : ℕ) → Superop (RegisterBasis (powerRegister A (n + 1)).Local)
      (RegisterBasis (powerRegister B (n + 1 - d n)).Local),
    (∀ n, EpsilonNonEntangling (powerRegister A (n + 1))
      (powerRegister B (n + 1 - d n)) (epsilon n) (L n)) ∧
    Tendsto epsilon atTop (nhds 0) ∧
    Tendsto (fun n => traceNorm (L n (powerDensity A rho (n + 1)) -
      powerDensity B sigma (n + 1 - d n))) atTop (nhds 0)

/-- PDF p.7, Eq.(6), and p.16, Eq.(21): smoothing and regularization of
log robustness. Approximation by states is equivalent to choosing smoothing
radii tending to zero; the infimum ranges over all such sequences. -/
def smoothedRegularizedRobustness {m : ℕ} (standard : Bool)
    (A : MultipartiteRegister m) (rho : PartyOperator A) : ℝ≥0∞ :=
  sInf {v | ∃ tau : (n : ℕ) → PartyOperator (powerRegister A (n + 1)),
    (∀ n, IsDensityMatrix (tau n)) ∧
    Tendsto (fun n => traceNorm (tau n - powerDensity A rho (n + 1))) atTop (nhds 0) ∧
    v = limsup (fun n => ENNReal.ofReal
      (logRobustness standard (powerRegister A (n + 1)) (tau n)) /
      (n + 1 : ℝ≥0∞)) atTop}

/-- PDF p.2: trace of the positive part of a Hermitian matrix. -/
def positivePartTrace {m : ℕ} (A : MultipartiteRegister m) (X : PartyOperator A) : ℝ :=
  (QAlgorithms.Papers.Independent.Information100.P07.positivePart X).trace.re

/-- PDF p.11, Eq.(12): singlet fraction of an actual map. -/
def singletFractionOf {m : ℕ} (A : MultipartiteRegister m) (rho : PartyOperator A)
    (K : ℕ) (hK : 0 < K) (L : Superop (RegisterBasis A.Local) (RegisterBasis (bellRegister K hK).Local)) : ℝ :=
  (partyBellDensity K hK * L rho).trace.re

/-- PDF pp.11,15: feasible singlet fractions, under the specified leakage model. -/
def singletFractions {m : ℕ} (model : LeakageModel) (A : MultipartiteRegister m) (rho : PartyOperator A)
    (K : ℕ) (hK : 0 < K) (epsilon : ℝ) : Set ℝ :=
  {f | ∃ L : Superop (RegisterBasis A.Local) (RegisterBasis (bellRegister K hK).Local),
    AllowedLeakageMap model A (bellRegister K hK) epsilon L ∧ f = singletFractionOf A rho K hK L}

/-- PDF p.11, Eq.(13), and corrected p.15 formula: dual objective on cone(S). -/
def singletDualObjective {m : ℕ} (A : MultipartiteRegister m) (rho Z : PartyOperator A)
    (coefficient : ℝ) : ℝ := positivePartTrace A (rho - Z) + Z.trace.re * coefficient

/-- PDF p.17: a physical state, including its finite partition and normalization. -/
structure PhysicalState (m : ℕ) where
  system : MultipartiteRegister m
  density : PartyOperator system
  valid : IsDensityMatrix density

/-- PDF pp.17–18: a formal finite product of states with nonnegative real copy
weights. Real powers are rates and do not mean fractional matrix powers. -/
structure WeightedFamily (m q : ℕ) where
  two_le : 2 ≤ m
  state : Fin q → PhysicalState m
  weight : Fin q → ℝ≥0

/-- PDF p.18: actual block space for integer counts of each component. -/
def batchRegister {m q : ℕ} (X : WeightedFamily m q) (k : Fin q → ℕ) : MultipartiteRegister m where
  two_le := X.two_le
  Local i := (j : Fin q) → Fin (k j) → (X.state j).system.Local i
  finite _ := inferInstance
  nonempty _ := inferInstance

/-- PDF p.18: tensor product of the specified integer numbers of component states. -/
def batchDensity {m q : ℕ} (X : WeightedFamily m q) (k : Fin q → ℕ) :
    PartyOperator (batchRegister X k) :=
  fun x y => ∏ j : Fin q, ∏ t : Fin (k j),
    (X.state j).density (fun i => x i j t) (fun i => y i j t)

/-- PDF pp.17–18: integer copy sequences realizing the real weights.
A zero weight means EXACTLY zero copies, hence a trivial register. -/
def RealizesWeights {m q : ℕ} (X : WeightedFamily m q) (k : ℕ → Fin q → ℕ) : Prop :=
  (∀ j, Tendsto (fun n => (k n j : ℝ) / (n + 1 : ℝ))
    atTop (nhds (X.weight j : ℝ))) ∧
  (∀ j, X.weight j = 0 → ∀ n, k n j = 0)

/-- PDF p.18: the actual asymptotic transformation of finite weighted products.
The output's o(n) losses are absorbed in its integer sequences of the same
limiting rates. Every map is between its actual block spaces. -/
def WeightedConverts {m p q : ℕ} (X : WeightedFamily m p) (Y : WeightedFamily m q) : Prop :=
  ∃ a : ℕ → Fin p → ℕ, ∃ b : ℕ → Fin q → ℕ,
    RealizesWeights X a ∧ RealizesWeights Y b ∧
    ∃ epsilon : ℕ → ℝ,
    ∃ L : (n : ℕ) → Superop (RegisterBasis (batchRegister X (a n)).Local)
      (RegisterBasis (batchRegister Y (b n)).Local),
    (∀ n, EpsilonNonEntangling (batchRegister X (a n)) (batchRegister Y (b n))
      (epsilon n) (L n)) ∧ Tendsto epsilon atTop (nhds 0) ∧
    Tendsto (fun n => traceNorm (L n (batchDensity X (a n)) - batchDensity Y (b n)))
      atTop (nhds 0)

/-- PDF p.17: scaling multiplies all component copy weights. -/
def scaleFamily {m q : ℕ} (t : ℝ≥0) (X : WeightedFamily m q) : WeightedFamily m q where
  two_le := X.two_le
  state := X.state
  weight j := t * X.weight j

/-- PDF p.17: a single state with its formal copy weight. -/
def singleFamily {m : ℕ} (X : PhysicalState m) (t : ℝ≥0) : WeightedFamily m 1 where
  two_le := X.system.two_le
  state _ := X
  weight _ := t

/-- PDF pp.17–18: a two-component tensor product with independent copy weights. -/
def pairFamily {m : ℕ} (X Y : PhysicalState m) (t q : ℝ≥0) : WeightedFamily m 2 where
  two_le := X.system.two_le
  state := ![X, Y]
  weight := ![t, q]

/-- PDF pp.19–20: local tensor product, preserving the m-party partition. -/
def tensorRegister {m : ℕ} (A B : MultipartiteRegister m) : MultipartiteRegister m where
  two_le := A.two_le
  Local i := A.Local i × B.Local i
  finite _ := inferInstance
  nonempty _ := inferInstance

/-- PDF pp.19–20: actual product density in the grouped local basis. -/
def partyTensorDensity {m : ℕ} (A B : MultipartiteRegister m) (rho : PartyOperator A) (pi : PartyOperator B) :
    PartyOperator (tensorRegister A B) :=
  fun x y => rho (fun i => (x i).1) (fun i => (y i).1) *
    pi (fun i => (x i).2) (fun i => (y i).2)

/-- PDF p.19, axiom 6: a GLOBAL property over every pair of compatible
finite multipartite transformations. No tensor closure is assumed in SEPP. -/
def TensorConsistency : Prop :=
  ∀ m : ℕ, ∀ A B C D : MultipartiteRegister m,
    ∀ (rho : PartyOperator A) (sigma : PartyOperator B) (pi : PartyOperator C) (tau : PartyOperator D),
    IsDensityMatrix rho → IsDensityMatrix sigma → IsDensityMatrix pi → IsDensityMatrix tau →
    AsymptoticConverts A rho B sigma → AsymptoticConverts C pi D tau →
    AsymptoticConverts (tensorRegister A C) (partyTensorDensity A C rho pi)
      (tensorRegister B D) (partyTensorDensity B D sigma tau)

/-- PDF p.19, Eq.(24), and p.20: absence of catalysis in the m-party theory.
The SAME arbitrary normalized catalyst pi is returned asymptotically. -/
def NoCatalysisAt (m : ℕ) : Prop :=
  ∀ A B C : MultipartiteRegister m, ∀ (rho : PartyOperator A) (sigma : PartyOperator B) (pi : PartyOperator C),
    IsDensityMatrix rho → IsDensityMatrix sigma → IsDensityMatrix pi →
    AsymptoticConverts (tensorRegister A C) (partyTensorDensity A C rho pi)
      (tensorRegister B C) (partyTensorDensity B C sigma pi) → AsymptoticConverts A rho B sigma

/-- PDF p.6: the empty tensor power has scalar value one. -/
example {m : ℕ} (A : MultipartiteRegister m) (rho : PartyOperator A)
    (x y : RegisterBasis (powerRegister A 0).Local) : powerDensity A rho 0 x y = 1 := by
  simp [powerDensity]

/-- PDF p.2: the unnormalized separable cone includes zero. -/
example {m : ℕ} (A : MultipartiteRegister m) (sigma : PartyOperator A) (h : IsMultipartiteSeparable A sigma) :
    SeparableCone A 0 := by
  exact ⟨0, le_refl 0, sigma, h, by simp⟩

/-- PDF p.3: Phi(1)=1 on its one-dimensional register. -/
example (x y : RegisterBasis (bellRegister 1 (by omega)).Local) :
    partyBellDensity 1 (by omega) x y = 1 := by
  have hx : (x 0 : Fin 1) = x 1 :=
    @Subsingleton.elim (Fin 1) inferInstance (x 0) (x 1)
  have hy : (y 0 : Fin 1) = y 1 :=
    @Subsingleton.elim (Fin 1) inferInstance (y 0) (y 1)
  simp [partyBellDensity, Matrix.submatrix,
    QAlgorithms.Papers.Independent.Information100.P54.maximallyEntangledProjector, hx, hy]
  exact ⟨rfl, rfl⟩

/-- PDF p.2: the positive-part trace of zero is zero. -/
example {m : ℕ} (A : MultipartiteRegister m) : positivePartTrace A 0 = 0 := by
  simp [positivePartTrace, QAlgorithms.Papers.Independent.Information100.P07.positivePart, cfc_zero]

/-- PDF p.17: scaling by one leaves every copy weight unchanged. -/
example {m q : ℕ} (X : WeightedFamily m q) (j : Fin q) :
    (scaleFamily 1 X).weight j = X.weight j := by
  simp [scaleFamily]

end QAlgorithms.Papers.Independent.Advance50.P14


