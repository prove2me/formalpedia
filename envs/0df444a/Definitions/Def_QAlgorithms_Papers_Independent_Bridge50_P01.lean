-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P01
-- name    : QAlgorithms_Papers_Independent_Bridge50_P01
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T11:15:22.645044+00:00
-- url     : https://prove2.me/theorems/a58ede64-11fa-4c3e-80e5-87d4001c5545
-- title:
--   Definitions for On the Second-Order Asymptotics for Entanglement-Assisted Communication
-- statement:
--   The objects the formalized statements of *On the Second-Order Asymptotics for Entanglement-Assisted Communication* (arXiv:1405.1797) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `negLog2`: PDF p.7, Eqs.(4.6)–(4.7): extended negative logarithm. A zero type-II error gives positive infinity, including sigma = 0.
--   - `tensorIdentity`: PDF pp.4,9: N tensor identity on the second register, on all operators. In particular, all off-diagonal reference blocks are retained.
--   - `PureSharedEACode`: PDF p.4, Eqs.(2.2)–(2.3): arbitrary finite pure entanglement on isomorphic assistance spaces, local message-dependent CPTP encoders, joint receiver POVM. The whole code is selected before the uniform message; no feedback is present.
--   - `pureSharedCodeSuccess`: PDF p.4, Eq.(2.3): uniform average success probability.
--   - `codingBits`: PDF p.4, Definition 1: exact integer-message one-shot boundary, in bits. For a CPTP N on nonzero finite registers and epsilon in (0,1), the set is nonempty (m=1) and bounded: m(1-epsilon) ≤ |A|^2. Thus this real supremum is the logarithm of the attained maximum integer message count, not a continuous-message relaxation. Assistance dimension is unbounded but finite.
--   - `operatorLog2`: PDF p.5, Eqs.(2.5)–(2.6): logarithm of a PSD matrix, in bits. Zero eigenvalues are assigned zero; the trace expressions are used only on support-included pairs (in particular a state and its product marginals).
--   - `relativeVariance`: PDF p.5, Eq.(2.6): centered relative-information variance in bits squared.
--   - `mutualVariance`: PDF p.5: mutual-information variance; support inclusion is automatic for densities.
--   - `PureResource`: PDF pp.3,5: every pure resource state on two isomorphic input-size registers. The norm requirement excludes the zero vector.
--   - `resourceOutput`: PDF p.5, Eq.(2.8): channel output with the untouched reference second.
--   - `eacSingleLetterCapacity`: PDF p.5, Eq.(2.8): the independently optimized single-letter EAC capacity. On the theorem domain, this is the capacity (2.7) by the cited BSST formula. The unit sphere is nonempty compact and mutual information is continuous, so the real supremum is a finite attained maximum. It is NOT defined at a chosen maximally entangled state.
--   - `optimizerVariances`: PDF p.5, Definition 2: variances over ALL capacity-achieving pure resources. For finite CPTP channels on nonzero spaces these optimizer sets are nonempty, and the variance extrema are finite and attained.
--   - `varianceMin`: PDF p.5, Eq.(2.10): minimum optimizer variance, independent of epsilon.
--   - `varianceMax`: PDF p.5, Eq.(2.10): maximum optimizer variance, independent of epsilon.
--   - `epsilonVariance`: PDF p.5, Theorem 3: equality epsilon=1/2 belongs to the maximum branch.
--   - `IsLogRemainder`: PDF pp.5,12,16: an existential O(log n) remainder, with constants before n. Finite initial terms are unconstrained; n0≥2 prevents a zero log bound.
--   - `eaOperationalDispersion`: PDF p.6, Eq.(3.3): operational epsilon-dispersion, on epsilon≠1/2. The EReal limsup retains infinity if the squared offset is unbounded.
--   - `IsProjectiveRepresentation`: PDF p.15: a continuous projective unitary representation. The multiplication law is modulo unit scalar phases. Continuity is in the projective sense, expressed by continuity of conjugation on each operator; no global continuous choice of phases is required.
--   - `InputActionIrreducible`: PDF p.15: irreducibility of ONLY the input representation.
--   - `IsInputOutputCovariant`: PDF p.15, Eq.(4.72): covariance for every input density matrix.
--   - `BlockResource`: PDF pp.9–12, corrected local meaning of (4.16): separate complete local orthogonal decompositions, with matching dimensions and arbitrary local ON bases. The full tensor product also contains unmatched block pairs. The map label and the two bases describe both decompositions without assuming a false decomposition of the full tensor space.
--   - `blockDimension`: PDF p.9: positive dimension of the t-th matched local block.
--   - `blockEntangled`: PDF p.9, Eq.(4.17): maximally entangled vector within a matched block. Schmidt coefficients may differ between blocks after weighting.
--   - `blockTheta`: PDF p.9, Eq.(4.17): the constructed coherent resource superposition.
--   - `blockMixed`: PDF p.9: maximally mixed state on a block in the specified local basis.
--   - `blockKappa`: PDF p.9, Proposition 11: comparison state computed from the SAME blocks and probability law. It is generally not a product of the global marginals.
--   - `inputReferencePurification`: PDF p.16, Eq.(5.1): canonical purification, using the positive square root. For a permutation-invariant rho this purification is invariant under the SAME permutation of input and reference, including degenerate spectra.
--   - `IsPermutationInvariantDensity`: PDF p.16: permutation invariance on a block of n copies.
--   - `symmetricDensities`: PDF p.16, Eq.(5.1): BOTH optimization domains are restricted to symmetric normalized densities; neither is restricted to tensor-product densities.
--   - `converseAlternatives`: PDF p.16, Eq.(5.1): hypothesis-testing alternatives for a fixed input. Register order is output then reference, so the product factors are swapped from the display; the reference marginal is the actual one of the purification.
--   - `converseInputValues`: PDF p.16, Eq.(5.1): max outside min, in a complete extended-real lattice.
-- source:
--   On the Second-Order Asymptotics for Entanglement-Assisted Communication, arXiv:1405.1797v2, https://arxiv.org/abs/1405.1797v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P71
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P80
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P36
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P01

/-!
Datta, Tomamichel and Wilde, arXiv:1405.1797v2. All page numbers are PDF pages.
Only statements are drafted; the eight source-result theorems end in sorry.
New objects below are local to this paper; matching primitives use pinned accepted imports. Registers use arbitrary finite,
nonempty bases; a reference is identified with the input through an isomorphism.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P01

open QAlgorithms Filter MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

-- Reuse pinned accepted definitions; these are not other draft chunks.
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open QAlgorithms.Papers.Independent.Information100.P58 (testingBeta testingD)
open QAlgorithms.Papers.Independent.Information100.P63 (normalCDF normalQuantile)
open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)
open QAlgorithms.Papers.Independent.Information100.P80 (log2)
open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation)
open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)
open QAlgorithms.Papers.Independent.Dependency50.P36 (relativeEntropyFinite)
open QAlgorithms.Papers.Independent.Frontier30.P01 (classicalState)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.7, Eqs.(4.6)–(4.7): extended negative logarithm.
A zero type-II error gives positive infinity, including sigma = 0. -/
def negLog2 (b : ℝ≥0∞) : EReal :=
  if b = 0 then ⊤ else if b = ⊤ then ⊥ else ((-log2 b.toReal : ℝ) : EReal)

/-- PDF pp.4,9: N tensor identity on the second register, on all operators.
In particular, all off-diagonal reference blocks are retained. -/
def tensorIdentity {A B R : Type} (N : Superop A B) : Superop (A × R) (B × R) :=
  fun X i j => N (fun a b => X (a, i.2) (b, j.2)) i.1 j.1

/-- PDF p.4, Eqs.(2.2)–(2.3): arbitrary finite pure entanglement on isomorphic
assistance spaces, local message-dependent CPTP encoders, joint receiver POVM.
The whole code is selected before the uniform message; no feedback is present. -/
structure PureSharedEACode (A B : Type) [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (m : ℕ) where
  messagePositive : 0 < m
  assistance : ℕ
  assistancePositive : 0 < assistance
  shared : EuclideanSpace ℂ (Fin assistance × Fin assistance)
  normalized : ‖shared‖ = 1
  encode : Fin m → Superop (Fin assistance) A
  encodeChannel : ∀ j, IsChannel (encode j)
  measurement : Fin m → Op (B × Fin assistance)
  povm : IsPOVM measurement

/-- PDF p.4, Eq.(2.3): uniform average success probability. -/
def pureSharedCodeSuccess {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (N : Superop A B) {m : ℕ}
    (C : PureSharedEACode A B m) : ℝ :=
  (m : ℝ)⁻¹ * ∑ j, effectProb (C.measurement j)
    (tensorIdentity N (tensorIdentity (C.encode j) (pureDensity C.shared)))

/-- PDF p.4, Definition 1: exact integer-message one-shot boundary, in bits.
For a CPTP N on nonzero finite registers and epsilon in (0,1), the set is
nonempty (m=1) and bounded: m(1-epsilon) ≤ |A|^2. Thus this real supremum
is the logarithm of the attained maximum integer message count, not a
continuous-message relaxation. Assistance dimension is unbounded but finite. -/
def codingBits {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (N : Superop A B) (epsilon : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ (m : ℕ) (C : PureSharedEACode A B m),
    1 - epsilon ≤ pureSharedCodeSuccess N C ∧ r = log2 m}

/-- PDF p.5, Eqs.(2.5)–(2.6): logarithm of a PSD matrix, in bits.
Zero eigenvalues are assigned zero; the trace expressions are used only on
support-included pairs (in particular a state and its product marginals). -/
def operatorLog2 {I : Type} [Fintype I] [DecidableEq I] (rho : Op I) : Op I :=
  cfc log2 rho

/-- PDF p.5, Eq.(2.6): centered relative-information variance in bits squared. -/
def relativeVariance {I : Type} [Fintype I] [DecidableEq I] (rho sigma : Op I) : ℝ :=
  let L := operatorLog2 rho - operatorLog2 sigma - (relativeEntropyFinite rho sigma : ℂ) • 1
  (rho * (L * L)).trace.re

/-- PDF p.5: mutual-information variance; support inclusion is automatic for densities. -/
def mutualVariance {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Op (A × B)) : ℝ :=
  relativeVariance rho (Matrix.kronecker (traceRight rho) (traceLeft rho))

/-- PDF pp.3,5: every pure resource state on two isomorphic input-size registers.
The norm requirement excludes the zero vector. -/
abbrev PureResource (A : Type) [Fintype A] :=
  {psi : EuclideanSpace ℂ (A × A) // ‖psi‖ = 1}

/-- PDF p.5, Eq.(2.8): channel output with the untouched reference second. -/
def resourceOutput {A B : Type} [Fintype A]
    (N : Superop A B) (psi : PureResource A) : Op (B × A) :=
  tensorIdentity N (pureDensity psi.val)

/-- PDF p.5, Eq.(2.8): the independently optimized single-letter EAC capacity.
On the theorem domain, this is the capacity (2.7) by the cited BSST formula.
The unit sphere is nonempty compact and mutual information is continuous,
so the real supremum is a finite attained maximum. It is NOT defined at a
chosen maximally entangled state. -/
def eacSingleLetterCapacity {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (N : Superop A B) : ℝ :=
  sSup (Set.range (fun psi : PureResource A => mutualInformation (resourceOutput N psi)))

/-- PDF p.5, Definition 2: variances over ALL capacity-achieving pure resources.
For finite CPTP channels on nonzero spaces these optimizer sets are nonempty,
and the variance extrema are finite and attained. -/
def optimizerVariances {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (N : Superop A B) : Set ℝ :=
  {v | ∃ psi : PureResource A,
    mutualInformation (resourceOutput N psi) = eacSingleLetterCapacity N ∧
    v = mutualVariance (resourceOutput N psi)}

/-- PDF p.5, Eq.(2.10): minimum optimizer variance, independent of epsilon. -/
def varianceMin {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (N : Superop A B) : ℝ :=
  sInf (optimizerVariances N)

/-- PDF p.5, Eq.(2.10): maximum optimizer variance, independent of epsilon. -/
def varianceMax {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (N : Superop A B) : ℝ :=
  sSup (optimizerVariances N)

/-- PDF p.5, Theorem 3: equality epsilon=1/2 belongs to the maximum branch. -/
def epsilonVariance {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (N : Superop A B) (epsilon : ℝ) : ℝ :=
  if epsilon < 1 / 2 then varianceMin N else varianceMax N

/-- PDF pp.5,12,16: an existential O(log n) remainder, with constants before n.
Finite initial terms are unconstrained; n0≥2 prevents a zero log bound. -/
def IsLogRemainder (K : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, 2 ≤ n0 ∧ ∀ n ≥ n0, |K n| ≤ C * log2 n

/-- PDF p.6, Eq.(3.3): operational epsilon-dispersion, on epsilon≠1/2.
The EReal limsup retains infinity if the squared offset is unbounded. -/
def eaOperationalDispersion {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (N : Superop A B) (epsilon : ℝ) : EReal :=
  Filter.limsup (fun n : ℕ =>
    ((((codingBits (channelPower N n) epsilon - (n : ℝ) * eacSingleLetterCapacity N) /
      normalQuantile epsilon) ^ 2 / (n : ℝ) : ℝ) : EReal)) atTop

/-- PDF p.15: a continuous projective unitary representation.
The multiplication law is modulo unit scalar phases. Continuity is in the
projective sense, expressed by continuity of conjugation on each operator;
no global continuous choice of phases is required. -/
def IsProjectiveRepresentation {G I : Type} [Group G] [TopologicalSpace G]
    [Fintype I] [DecidableEq I] (U : G → Matrix.unitaryGroup I ℂ) : Prop :=
  (∀ g h, ∃ z : ℂ, ‖z‖ = 1 ∧
    (U (g * h) : Op I) = z • ((U g : Op I) * (U h : Op I))) ∧
  ∀ rho : Op I, Continuous (fun g => conjSuperop (U g : Op I) rho)

/-- PDF p.15: irreducibility of ONLY the input representation. -/
def InputActionIrreducible {G A : Type} [Fintype A] [DecidableEq A]
    (U : G → Matrix.unitaryGroup A ℂ) : Prop :=
  ∀ S : Submodule ℂ (A → ℂ),
    (∀ g v, v ∈ S → (U g : Op A).mulVec v ∈ S) → S = ⊥ ∨ S = ⊤

/-- PDF p.15, Eq.(4.72): covariance for every input density matrix. -/
def IsInputOutputCovariant {G A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (N : Superop A B) (U : G → Matrix.unitaryGroup A ℂ)
    (V : G → Matrix.unitaryGroup B ℂ) : Prop :=
  ∀ g rho, IsDensityMatrix rho →
    N (conjSuperop (U g : Op A) rho) = conjSuperop (V g : Op B) (N rho)

/-- PDF pp.9–12, corrected local meaning of (4.16): separate complete local
orthogonal decompositions, with matching dimensions and arbitrary local ON
bases. The full tensor product also contains unmatched block pairs.
The map label and the two bases describe both decompositions without
assuming a false decomposition of the full tensor space. -/
structure BlockResource (A : Type) [Fintype A] [DecidableEq A] where
  blocks : ℕ
  label : A → Fin blocks
  nonemptyBlock : ∀ t, ∃ i, label i = t
  leftBasis : Matrix.unitaryGroup A ℂ
  rightBasis : Matrix.unitaryGroup A ℂ
  weight : Fin blocks → ℝ
  nonnegative : ∀ t, 0 ≤ weight t
  total : ∑ t, weight t = 1

/-- PDF p.9: positive dimension of the t-th matched local block. -/
def blockDimension {A : Type} [Fintype A] [DecidableEq A]
    (R : BlockResource A) (t : Fin R.blocks) : ℕ :=
  (Finset.univ.filter (fun i => R.label i = t)).card

/-- PDF p.9, Eq.(4.17): maximally entangled vector within a matched block.
Schmidt coefficients may differ between blocks after weighting. -/
def blockEntangled {A : Type} [Fintype A] [DecidableEq A]
    (R : BlockResource A) (t : Fin R.blocks) : EuclideanSpace ℂ (A × A) :=
  WithLp.toLp 2 fun p =>
    ((Real.sqrt (blockDimension R t : ℝ))⁻¹ : ℂ) *
      ∑ i ∈ Finset.univ.filter (fun i => R.label i = t),
        (R.leftBasis : Op A) p.1 i * (R.rightBasis : Op A) p.2 i

/-- PDF p.9, Eq.(4.17): the constructed coherent resource superposition. -/
def blockTheta {A : Type} [Fintype A] [DecidableEq A]
    (R : BlockResource A) : Op (A × A) :=
  pureDensity (∑ t, (Real.sqrt (R.weight t) : ℂ) • blockEntangled R t)

/-- PDF p.9: maximally mixed state on a block in the specified local basis. -/
def blockMixed {A : Type} [Fintype A] [DecidableEq A]
    (R : BlockResource A) (basis : Matrix.unitaryGroup A ℂ) (t : Fin R.blocks) : Op A :=
  conjSuperop (basis : Op A) (Matrix.diagonal (fun i =>
    if R.label i = t then ((blockDimension R t : ℂ)⁻¹) else 0))

/-- PDF p.9, Proposition 11: comparison state computed from the SAME blocks
and probability law. It is generally not a product of the global marginals. -/
def blockKappa {A : Type} [Fintype A] [DecidableEq A]
    (R : BlockResource A) : Op (A × A) :=
  ∑ t, (R.weight t : ℂ) • Matrix.kronecker
    (blockMixed R R.leftBasis t) (blockMixed R R.rightBasis t)

/-- PDF p.16, Eq.(5.1): canonical purification, using the positive square root.
For a permutation-invariant rho this purification is invariant under the SAME
permutation of input and reference, including degenerate spectra. -/
def inputReferencePurification {A : Type} [Fintype A] [DecidableEq A]
    (rho : Op A) : Op (A × A) :=
  pureDensity (WithLp.toLp 2 (fun p : A × A => (cfc Real.sqrt rho) p.1 p.2))

/-- PDF p.16: permutation invariance on a block of n copies. -/
def IsPermutationInvariantDensity {A : Type} {n : ℕ} (rho : Op (Fin n → A)) : Prop :=
  ∀ (p : Equiv.Perm (Fin n)) x y, rho (x ∘ p) (y ∘ p) = rho x y

/-- PDF p.16, Eq.(5.1): BOTH optimization domains are restricted to symmetric
normalized densities; neither is restricted to tensor-product densities. -/
def symmetricDensities (A : Type) [Fintype A] (n : ℕ) : Set (Op (Fin n → A)) :=
  {rho | IsDensityMatrix rho ∧ IsPermutationInvariantDensity rho}

/-- PDF p.16, Eq.(5.1): hypothesis-testing alternatives for a fixed input.
Register order is output then reference, so the product factors are swapped
from the display; the reference marginal is the actual one of the purification. -/
def converseAlternatives {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (N : Superop A B) (n : ℕ)
    (epsilon : ℝ) (rho : Op (Fin n → A)) : Set EReal :=
  {v | ∃ sigma ∈ symmetricDensities B n,
    v = testingD epsilon
      (tensorIdentity (channelPower N n) (inputReferencePurification rho))
      (Matrix.kronecker sigma (traceLeft (inputReferencePurification rho)))}

/-- PDF p.16, Eq.(5.1): max outside min, in a complete extended-real lattice. -/
def converseInputValues {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (N : Superop A B) (n : ℕ)
    (epsilon : ℝ) : Set EReal :=
  {v | ∃ rho ∈ symmetricDensities A n, v = sInf (converseAlternatives N n epsilon rho)}

/-! Small definitional sanity checks; no source-result proofs are attempted. -/

example : negLog2 0 = ⊤ := by simp [negLog2]

example {I : Type} [Fintype I] [DecidableEq I] :
    relativeVariance (0 : Op I) 0 = 0 := by
  simp [relativeVariance, relativeEntropyFinite]

example : finiteMaxEntangled (Fin 1) (0, 0) = 1 := by
  simp [finiteMaxEntangled]

example {A R : Type} (X : Op (A × R)) : tensorIdentity (fun Y : Op A => Y) X = X := by
  rfl

example {X B : Type} [DecidableEq X] (p : X → ℝ) (rho : X → Op B)
    (x y : X) (b c : B) (h : x ≠ y) : cqState p rho (x,b) (y,c) = 0 := by
  simp [cqState, h]

example {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (N : Superop A B) : epsilonVariance N (1 / 2) = varianceMax N := by
  simp [epsilonVariance]

/-- The permitted zero alternative has infinite testing entropy, not log(0)=0. -/
example {I : Type} [Fintype I] [DecidableEq I] (rho : Op I)
    (hrho : IsDensityMatrix rho) (epsilon : ℝ) (he : 0 < epsilon) :
    testingD epsilon rho 0 = ⊤ := by
  have hId : IsEffect (1 : Op I) := by
    refine ⟨Matrix.PosSemidef.one, ?_⟩
    simpa using (Matrix.PosSemidef.zero : (0 : Op I).PosSemidef)
  have hp : effectProb (1 : Op I) rho = 1 := by
    simp [effectProb, hrho.2]
  have hz : (0 : ℝ) ∈ {b | ∃ Q : Op I, IsEffect Q ∧
      1 - epsilon ≤ effectProb Q rho ∧ b = effectProb Q 0} := by
    refine ⟨1, hId, ?_, ?_⟩
    · rw [hp]
      linarith
    · simp [effectProb]
  have hbelow : BddBelow {b : ℝ | ∃ Q : Op I, IsEffect Q ∧
      1 - epsilon ≤ effectProb Q rho ∧ b = effectProb Q 0} := by
    refine ⟨0, ?_⟩
    rintro b ⟨Q, _, _, rfl⟩
    simp [effectProb]
  have hb : testingBeta epsilon rho 0 = 0 := by
    apply le_antisymm (csInf_le hbelow hz)
    apply le_csInf ⟨0, hz⟩
    rintro b ⟨Q, _, _, rfl⟩
    simp [effectProb]
  simp [testingD, hb]

/-- Every block used as a denominator is nonzero by construction. -/
example {A : Type} [Fintype A] [DecidableEq A]
    (R : BlockResource A) (t : Fin R.blocks) : blockDimension R t ≠ 0 := by
  obtain ⟨i, hi⟩ := R.nonemptyBlock t
  unfold blockDimension
  exact Finset.card_ne_zero.mpr ⟨i, by simp [hi]⟩

/-- Single-copy symmetry imposes no constraint; it does not force product inputs. -/
example {A : Type} (rho : Op (Fin 1 → A)) : IsPermutationInvariantDensity rho := by
  intro p x y
  have hp : p = 1 := Subsingleton.elim _ _
  subst p
  rfl

/-- The constructed purification is zero at zero; all uses require a density. -/
example {A : Type} [Fintype A] [DecidableEq A] :
    inputReferencePurification (0 : Op A) = 0 := by
  ext i j
  simp [inputReferencePurification, pureDensity, cfc_zero]

end QAlgorithms.Papers.Independent.Bridge50.P01


