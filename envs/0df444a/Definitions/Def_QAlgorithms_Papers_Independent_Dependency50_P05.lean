-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P05
-- name    : QAlgorithms_Papers_Independent_Dependency50_P05
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T07:50:31.847974+00:00
-- url     : https://prove2.me/theorems/6a151a55-97b3-48c9-8e16-3d9f917deb15
-- title:
--   Definitions for Comparison of Quantum Channels by Superchannels
-- statement:
--   The objects the formalized statements of *Comparison of Quantum Channels by Superchannels* (arXiv:1808.02607) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `System`: Gour, arXiv:1808.02607v3, PDF p.2: a finite dynamical system with nonzero input/output.
--   - `In`
--   - `Out`
--   - `ChoiRegister`
--   - `Supermap`
--   - `uniformDensity`: PDF p.7: the uniform density operator; every use has positive register dimension.
--   - `ChannelChoi`: PDF pp.2,4, Eq.(3): input-first Choi description of a CPTP map.
--   - `action`: PDF p.5, Eq.(27): inverse Choi map, defined on all operators.
--   - `amplifySupermap`: PDF pp.3–4: complete extension by the identity on BOTH registers of C.
--   - `IsSuperchannel`: PDF p.4, Definition 1. TPP ranges over ALL trace-preserving complex-linear maps, including those that are not positive. Complete CPP ranges over arbitrary C0 and C1.
--   - `superChoi`: PDF p.3, Eq.(8): unnormalized Choi matrix of the Choi-to-Choi linear map.
--   - `IsDual`: PDF p.4, Eq.(16): Hilbert–Schmidt duality, without identifying transpose with adjoint.
--   - `IsDoublyStochastic`: PDF p.8, Definition 2: both the transformation and its dual are superchannels.
--   - `IsReversible`: PDF p.8: reversibility requires a two-sided inverse that is itself a superchannel.
--   - `UnitaryBetween`: PDF p.8, Eq.(38): unitary maps between fixed-basis copies.
--   - `sandwich`: PDF p.8, Eqs.(38),(40): the pre-unitary acts by TRANSPOSE on the input Choi factor.
--   - `RandomUnitaryData`: PDF p.8, Eq.(39): a finite probability ensemble of unitary pre/post maps. This carries the ensemble, not any consequences about marginals.
--   - `IsRandomUnitary`: PDF p.8, Eq.(39), on every operator in Choi space.
--   - `preUnitaryKet`: PDF p.8, Eq.(42): preUnitaryKet(a0,b0)=(U_pre)^T(b0,a0)=U_pre(a0,b0).
--   - `postUnitaryKet`: PDF p.8, Eq.(42): postUnitaryKet(a1,b1)=U_post(b1,a1).
--   - `ketProjector`: PDF p.8, Eq.(41): ketProjector product, without normalizing maximally entangled vectors.
--   - `jA0B0`: Marginal A0B0 (PDF p.8).
--   - `jA1B1`: Marginal A1B1 (PDF p.8).
--   - `jA1B0`: Marginal A1B0 (PDF p.4, Eq.(19)).
--   - `jA0B1`: Marginal A0B1 (PDF p.8, Eq.(48)).
--   - `jA0B`: Marginal A0B (PDF p.8, Eq.(45)).
--   - `jA1B`: Marginal A1B (PDF p.8, Eq.(43)).
--   - `jAB0`: Marginal AB0 (PDF p.4, Eq.(19)).
--   - `jAB1`: Marginal AB1 (PDF p.11).
--   - `jB`: Marginal B (PDF p.9).
--   - `StandardMarginals`: PDF p.4, Eq.(19), including positivity. A test predicate, not the superchannel definition.
--   - `UniformFactorization`: PDF p.8, Eq.(45), and p.10, Eq.(55).
--   - `UnitalFactorization`: PDF p.11, Theorem 4(2).
--   - `OtherRandomMarginal`: PDF p.8, Eq.(43); tuple order is A1,B0,B1.
--   - `uniformChannel`: PDF p.9, Eq.(54): Choi matrix of the uniformDensity channel.
--   - `PreservesUniformity`: PDF p.9: ordinary preservation of the single uniformDensity channel.
--   - `MarginallyUniform`: PDF pp.9–10: A's output is uniformDensity and independent of all other registers, on ALL input operators, represented here by the corresponding Choi factorization.
--   - `CompletelyUniformityPreserving`: PDF p.10: complete uniformity preservation, with arbitrary auxiliary dynamical system.
--   - `Unital`: PDF p.11: unital means Phi(I)=I, without dimensional rescaling.
--   - `UnitalPreserving`: PDF p.11, ordinary unital-channel preservation.
--   - `CompletelyUnitalPreserving`: PDF p.11: only ancillary systems with matched input/output dimensions occur here, as A0=A1 and B0=B1 in Theorem 4.
--   - `RandomUnitaryChannel`: PDF p.11: a random unitary CHANNEL, distinct from a random unitary superchannel.
--   - `AffineUnitalCriterion`: PDF pp.11–12, corrected ordinary criterion: retain the identity normalization from Eq.(58). Printed: only the affine marginal decomposition in the final iff. Changed: conjoin J^{B1}=d_A0 I. Why: a fixed non-unital output satisfies the decomposition alone.
--   - `applyFirst`: PDF p.4, Eq.(21): apply a map on the first factor, retaining all memory coherences.
--   - `Realizes`: PDF p.4, Eq.(21): equality on all linear maps and all operators, not just channels/states.
--   - `DepolarizingPost`: PDF p.9, Eq.(49): every memory operator, including non-Hermitian operators.
--   - `UniformPre`: PDF p.9, Eq.(50): trace the memory after applying the pre-channel.
--   - `gammaChoi`: PDF pp.5–6, Eqs.(26),(29): reshape the SAME Choi matrix into Gamma's input/output order.
--   - `GammaMarginal`: PDF p.6, Eq.(31): Gamma's ordinary no-signalling marginal, equality on all operators.
--   - `GammaUniformInput`: PDF p.11, Eq.(59): full joint output, with B1 marginal on the right.
--   - `renyiEntropy`: PDF p.12: base-two Renyi entropy. Orders zero and one use rank and von Neumann entropy; the spectral projection onto nonzero eigenvalues has trace equal to rank for a density matrix.
--   - `minimumOutput`: PDF p.12: infimum over exactly the density matrices. The theorem below also states attainment, so no empty-set/unbounded-set default is used for channels.
--   - `StateDivergence`: PDF pp.17–18: a consistent divergence on every finite-dimensional register.
--   - `DivergenceDPI`: PDF p.17: the sole assumption on D is state data processing; no finiteness, positivity, symmetry, or diagonal normalization is imposed.
--   - `stabilizedDivergence`: PDF p.18, Eq.(89): extended-real supremum over all reference dimensions and density operators. Empty references are excluded. The reference is placed first on both outputs.
--   - `BipartiteChannel`: PDF p.2: joint channel Choi matrix, stored in party order A0,A1,B0,B1.
--   - `jointInputNormalizedChoi`: PDF p.13, Definition 4: normalize by INPUT dimensions, never by trace of a CP map.
--   - `EntropyMarginal`: PDF p.13, Eq.(62), the second primal constraint. Gamma lives on A0,A1,B0.
--   - `extendGamma`: PDF p.13: gamma^{AB0} Matrix.kronecker identity^{B1}, in party order.
--   - `EntropyFeasible`: PDF p.13, Definition 4: primal feasibility, NOT a dual or desired entropy identity.
--   - `extendedConditional`: PDF p.13, Definition 4. The real exponent set is embedded BEFORE the EReal supremum. This equals minus log2 of the primal minimum on channels and extends homogeneously to CP maps; at W=0 the value is +infinity. No support-function identity is assumed in this definition.
--   - `stateConditional`: PDF p.7, Eq.(33): state conditional min-entropy H(J|I), by the primal operator inequality.
--   - `extendedMin`: PDF p.12, Definition 3: H_min(A1|A0) of the normalized Choi state.
--   - `entropyPower`: Extended negative exponential: +infinity maps to zero and -infinity to +infinity.
--   - `replacementChoi`: PDF p.14: fixed-output replacement channel, with all off-diagonal input blocks retained as zero. A trace-one output gives a trace-preserving channel.
--   - `productSystem`: Fixed-basis product dynamical system (PDF p.14, Theorem 5(3)).
--   - `splitReg`: The fixed product basis, used consistently for inputs and outputs.
--   - `productChoi`: PDF p.12: Matrix.kronecker product of channels in ordinary input/output Choi order.
--   - `productBipartite`: PDF p.14: Matrix.kronecker product of bipartite maps, regrouped as AA' and BB'.
--   - `localApply`: PDF p.14, Eq.(68): T acts on A, with the identity on the complete dynamical system B.
--   - `discardConditioner`: PDF p.14, Remark 4: insert the SPECIFIED state at C0 and trace C1.
--   - `outputMarginal`: Output-state marginal of the normalized Choi matrix (PDF p.14, upper bound).
--   - `lowerBoundState`: PDF p.14, lower bound: B0 is the conditioning register, and A includes A0 AND A1.
--   - `jointBellOverlap`: PDF p.13, Eq.(66): Bell input/output overlap, with unnormalized Bell projectors.
--   - `ClassicalOutput`: PDF p.15, Eq.(80), and Appendix B: only B1 is classical.
--   - `ClassicalSystem`: PDF pp.15–16: both B0 and B1 are classical.
--   - `classicalBranch`: PDF p.15, Eq.(81): a subnormalized conditional instrument branch; no renormalization.
--   - `GuessStrategy`: PDF p.15, Eq.(82): normalized entangled input and a COMPLETE POVM, with reference A0.
--   - `guessScore`: PDF p.15, Eq.(82): the branch weight remains in the trace, including zero branches.
--   - `guessProbability`: PDF p.16: each known y has its OWN optimization, followed by the UNIFORM average.
--   - `discriminationProbability`: PDF p.16: operational specialization to discrimination of channels with prior p.
--   - `quantumBranch`: Appendix B, Eq.(108): CP instrument on the BOTH quantum inputs; output x is classical.
--   - `QuantumGuessStrategy`: Appendix B, Eq.(112): V may jointly mix the original inputs; this is not a separated-party Bell-agreement instrument. Both positivity AND sum-to-identity of the POVM are retained.
--   - `quantumGuessKet`: Appendix B, Eq.(112): (id Matrix.kronecker V)|phi+>/sqrt(d_B0).
--   - `quantumGuessScore`: Appendix B, Eq.(112): the actual joint input, channel application, and measurement.
--   - `quantumGuessProbability`: Appendix B, Eq.(112): supremum of physical strategies, with attainment in the theorem.
--   - `Tomography`: PDF p.18: the fixed tomographic experiment, with normalized pure input probes and an informationally complete basis POVM. Span and independence are over the REAL Hermitian space.
--   - `extractedBranch`: PDF p.18: prepare probe x at R0 and measure effect y at R1, retaining branch weights.
--   - `InstrumentFamily`: PDF pp.18–19: C_* has one CP instrument for EACH x. This is the star SUBSCRIPT family, with exactly d_R1^2 outcomes y=1,...,d_Y (Fin uses zero-based storage).
--   - `pairedMap`: PDF p.18, Theorem 7: paired CP map; it need not be trace preserving and may be ZERO.
--   - `QuantumMajorizes`: PDF p.17, Eq.(88): one superchannel on A, identity on BOTH R0 and R1. Matrices are stored in party order A,R, a fixed permutation of the source's displayed order R,A.
--   - `familyMixture`: PDF p.20, Corollary 1: the two marginal bipartite channels of the displayed tripartite mixture. The omitted local factor is TP, so fixing any of its input states gives this marginal.
--   - `entropyContraction`: PDF p.20, Remark 6: an increasing entropy contraction; no metric properties are imposed.
--   - `gibbsChoi`: PDF p.21: Gibbs states are supplied as density matrices; the free replacer is trace times G.
--   - `ComparisonFeasible`: PDF p.20, Eqs.(100)–(102), in the proof-equivalent normalization: transpose TEST K. The page image places T on Phi; transposing the ENTIRE LMI (including gamma), then renaming gamma, gives this test-transpose form with unchanged trace objective. Gamma is Hermitian.
--   - `comparisonSDPValue`: PDF p.20, Eq.(99): the proof-derived primal objective, with the d_X^{-2} cq normalization.
--   - `comparisonVariables`: PDF pp.20–21: real scalar variables in the displayed SDP: Hermitian gamma plus each Hermitian test-branch Choi block. This count refers to the variables actually optimized above.
--   - `comparisonEqualities`: PDF pp.20–21: independent real linear equalities in (101),(102).
--   - `comparisonPSDOrder`: PDF p.21: total PSD block order, one block for (100) and one per test branch.
--   - `powerSystem`: PDF p.21, Sec.VI: zero-fold Matrix.kronecker power is the one-dimensional missing system.
--   - `powerBipartite`: PDF p.21: Matrix.kronecker powers as actual products of the supplied channel, not free variables.
--   - `jointChoi`: PDF p.21: ordinary input-first joint Choi order, used only to apply a bipartite channel.
--   - `jointDiamondDistance`: PDF p.21: diamond distance of two channels, with all reference-assisted density inputs. Only channel differences are used. Its supremum is nonempty and lies in [0,2].
--   - `smoothExtended`: PDF p.21: smoothing over CHANNELS in a diamond ball. At channel centers and epsilon>=0 this real supremum is nonempty and bounded; all channel entropies are finite.
--   - `conditionalVonNeumann`: PDF pp.21–22: conditional von Neumann entropy in bits of a trace-one output state.
--   - `ChannelContraction`: PDF p.18: a channel contraction is a family on all finite dynamical systems. No symmetry, positivity, normalization or induced-state-divergence representation is assumed.
--   - `ChannelContractionDPI`: PDF p.18: contraction under every physical superchannel, on every pair of channels.
-- source:
--   Comparison of Quantum Channels by Superchannels, arXiv:1808.02607v3, https://arxiv.org/abs/1808.02607v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_MatrixDistances

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P05

local notation "Mat" I:max => Matrix I I ℂ

/-- Gour, arXiv:1808.02607v3, PDF p.2: a finite dynamical system with nonzero input/output. -/
structure System where
  input : ℕ
  output : ℕ
  input_pos : 0 < input
  output_pos : 0 < output

abbrev In (A : System) := Fin A.input

abbrev Out (A : System) := Fin A.output

abbrev ChoiRegister (A : System) := In A × Out A

abbrev Supermap (A B : System) := Mat (ChoiRegister A) →ₗ[ℂ] Mat (ChoiRegister B)

/-- PDF p.7: the uniform density operator; every use has positive register dimension. -/
def uniformDensity (I : Type) [Fintype I] [DecidableEq I] : Mat I :=
  (Fintype.card I : ℂ)⁻¹ • 1

/-- PDF pp.2,4, Eq.(3): input-first Choi description of a CPTP map. -/
def ChannelChoi {I J : Type} [Fintype I] [Fintype J] [DecidableEq I]
    (X : Mat (I × J)) : Prop :=
  X.PosSemidef ∧ QAlgorithms.traceRight X = 1

/-- PDF p.5, Eq.(27): inverse Choi map, defined on all operators. -/
def action {I J : Type} [Fintype I] (X : Mat (I × J)) (R : Mat I) : Mat J :=
  fun p q => ∑ i, ∑ j, X (i, p) (j, q) * R i j

/-- PDF pp.3–4: complete extension by the identity on BOTH registers of C. -/
def amplifySupermap {A B : System} (T : Supermap A B) (C : System)
    (X : Mat ((In A × In C) × (Out A × Out C))) :
    Mat ((In B × In C) × (Out B × Out C)) :=
  fun p q => QAlgorithms.idTensorSuperop (R := ChoiRegister C) T
    (fun r s => X ((r.2.1, r.1.1), (r.2.2, r.1.2))
      ((s.2.1, s.1.1), (s.2.2, s.1.2)))
    ((p.1.2, p.2.2), (p.1.1, p.2.1))
    ((q.1.2, q.2.2), (q.1.1, q.2.1))

/-- PDF p.4, Definition 1. TPP ranges over ALL trace-preserving complex-linear maps,
including those that are not positive. Complete CPP ranges over arbitrary C0 and C1. -/
def IsSuperchannel {A B : System} (T : Supermap A B) : Prop :=
  (∀ (C : System) (X : Mat ((In A × In C) × (Out A × Out C))),
    X.PosSemidef → (amplifySupermap T C X).PosSemidef) ∧
  ∀ X : Mat (ChoiRegister A), QAlgorithms.traceRight X = 1 → QAlgorithms.traceRight (T X) = 1

/-- PDF p.3, Eq.(8): unnormalized Choi matrix of the Choi-to-Choi linear map. -/
def superChoi {A B : System} (T : Supermap A B) : Mat (ChoiRegister A × ChoiRegister B) :=
  fun p q => T (Matrix.single p.1 q.1 1) p.2 q.2

/-- PDF p.4, Eq.(16): Hilbert–Schmidt duality, without identifying transpose with adjoint. -/
def IsDual {A B : System} (T : Supermap A B) (S : Supermap B A) : Prop :=
  ∀ (X : Mat (ChoiRegister A)) (Y : Mat (ChoiRegister B)),
    ((T X)ᴴ * Y).trace = (Xᴴ * S Y).trace

/-- PDF p.8, Definition 2: both the transformation and its dual are superchannels. -/
def IsDoublyStochastic {A B : System} (T : Supermap A B) : Prop :=
  IsSuperchannel T ∧ ∃ S : Supermap B A, IsDual T S ∧ IsSuperchannel S

/-- PDF p.8: reversibility requires a two-sided inverse that is itself a superchannel. -/
def IsReversible {A B : System} (T : Supermap A B) : Prop :=
  IsSuperchannel T ∧ ∃ S : Supermap B A, IsSuperchannel S ∧
    S.comp T = LinearMap.id ∧ T.comp S = LinearMap.id

/-- PDF p.8, Eq.(38): unitary maps between fixed-basis copies. -/
def UnitaryBetween {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (U : Matrix J I ℂ) : Prop :=
  Uᴴ * U = 1 ∧ U * Uᴴ = 1

/-- PDF p.8, Eqs.(38),(40): the pre-unitary acts by TRANSPOSE on the input Choi factor. -/
def sandwich {A B : System} (P : Matrix (In A) (In B) ℂ)
    (Q : Matrix (Out B) (Out A) ℂ) (X : Mat (ChoiRegister A)) : Mat (ChoiRegister B) :=
  let W : Matrix (ChoiRegister B) (ChoiRegister A) ℂ := fun b a => P a.1 b.1 * Q b.2 a.2
  W * X * Wᴴ

/-- PDF p.8, Eq.(39): a finite probability ensemble of unitary pre/post maps.
This carries the ensemble, not any consequences about marginals. -/
structure RandomUnitaryData (A B : System) where
  m : ℕ
  m_pos : 0 < m
  weight : Fin m → ℝ
  weight_nonneg : ∀ x, 0 ≤ weight x
  weight_sum : ∑ x, weight x = 1
  pre : Fin m → Matrix (In A) (In B) ℂ
  post : Fin m → Matrix (Out B) (Out A) ℂ
  pre_unitary : ∀ x, UnitaryBetween (pre x)
  post_unitary : ∀ x, UnitaryBetween (post x)

/-- PDF p.8, Eq.(39), on every operator in Choi space. -/
def IsRandomUnitary {A B : System} (T : Supermap A B) : Prop :=
  ∃ D : RandomUnitaryData A B, ∀ X,
    T X = ∑ x, (D.weight x : ℂ) • sandwich (D.pre x) (D.post x) X

/-- PDF p.8, Eq.(42): preUnitaryKet(a0,b0)=(U_pre)^T(b0,a0)=U_pre(a0,b0). -/
def preUnitaryKet {A B : System} (P : Matrix (In A) (In B) ℂ) : In A × In B → ℂ :=
  fun p => P p.1 p.2

/-- PDF p.8, Eq.(42): postUnitaryKet(a1,b1)=U_post(b1,a1). -/
def postUnitaryKet {A B : System} (Q : Matrix (Out B) (Out A) ℂ) : Out A × Out B → ℂ :=
  fun p => Q p.2 p.1

/-- PDF p.8, Eq.(41): ketProjector product, without normalizing maximally entangled vectors. -/
def ketProjector {I : Type} (v : I → ℂ) : Mat I :=
  QAlgorithms.pureDensity (WithLp.toLp 2 v)

/-- Marginal A0B0 (PDF p.8). -/
def jA0B0 {A B : System} (T : Supermap A B) : Mat (In A × In B) :=
  fun p q => ∑ a1, ∑ b1, superChoi T ((p.1, a1), (p.2, b1)) ((q.1, a1), (q.2, b1))

/-- Marginal A1B1 (PDF p.8). -/
def jA1B1 {A B : System} (T : Supermap A B) : Mat (Out A × Out B) :=
  fun p q => ∑ a0, ∑ b0, superChoi T ((a0, p.1), (b0, p.2)) ((a0, q.1), (b0, q.2))

/-- Marginal A1B0 (PDF p.4, Eq.(19)). -/
def jA1B0 {A B : System} (T : Supermap A B) : Mat (Out A × In B) :=
  fun p q => ∑ a0, ∑ b1, superChoi T ((a0, p.1), (p.2, b1)) ((a0, q.1), (q.2, b1))

/-- Marginal A0B1 (PDF p.8, Eq.(48)). -/
def jA0B1 {A B : System} (T : Supermap A B) : Mat (In A × Out B) :=
  fun p q => ∑ a1, ∑ b0, superChoi T ((p.1, a1), (b0, p.2)) ((q.1, a1), (b0, q.2))

/-- Marginal A0B (PDF p.8, Eq.(45)). -/
def jA0B {A B : System} (T : Supermap A B) : Mat (In A × ChoiRegister B) :=
  fun p q => ∑ a1, superChoi T ((p.1, a1), p.2) ((q.1, a1), q.2)

/-- Marginal A1B (PDF p.8, Eq.(43)). -/
def jA1B {A B : System} (T : Supermap A B) : Mat (Out A × ChoiRegister B) :=
  fun p q => ∑ a0, superChoi T ((a0, p.1), p.2) ((a0, q.1), q.2)

/-- Marginal AB0 (PDF p.4, Eq.(19)). -/
def jAB0 {A B : System} (T : Supermap A B) : Mat (ChoiRegister A × In B) :=
  fun p q => ∑ b1, superChoi T (p.1, (p.2, b1)) (q.1, (q.2, b1))

/-- Marginal AB1 (PDF p.11). -/
def jAB1 {A B : System} (T : Supermap A B) : Mat (ChoiRegister A × Out B) :=
  fun p q => ∑ b0, superChoi T (p.1, (b0, p.2)) (q.1, (b0, q.2))

/-- Marginal B (PDF p.9). -/
def jB {A B : System} (T : Supermap A B) : Mat (ChoiRegister B) :=
  QAlgorithms.traceLeft (superChoi T)

/-- PDF p.4, Eq.(19), including positivity. A test predicate, not the superchannel definition. -/
def StandardMarginals {A B : System} (T : Supermap A B) : Prop :=
  (superChoi T).PosSemidef ∧ jA1B0 T = 1 ∧
  jAB0 T = (fun p q => jA0B0 T (p.1.1, p.2) (q.1.1, q.2) *
    uniformDensity (Out A) p.1.2 q.1.2)

/-- PDF p.8, Eq.(45), and p.10, Eq.(55). -/
def UniformFactorization {A B : System} (T : Supermap A B) : Prop :=
  jA0B T = (fun p q => jA0B0 T (p.1, p.2.1) (q.1, q.2.1) *
    uniformDensity (Out B) p.2.2 q.2.2)

/-- PDF p.11, Theorem 4(2). -/
def UnitalFactorization {A B : System} (T : Supermap A B) : Prop :=
  jAB1 T = (fun p q => uniformDensity (In A) p.1.1 q.1.1 *
    jA1B1 T (p.1.2, p.2) (q.1.2, q.2))

/-- PDF p.8, Eq.(43); tuple order is A1,B0,B1. -/
def OtherRandomMarginal {A B : System} (T : Supermap A B) : Prop :=
  jA1B T = (fun p q => uniformDensity (In B) p.2.1 q.2.1 *
    jA1B1 T (p.1, p.2.2) (q.1, q.2.2))

/-- PDF p.9, Eq.(54): Choi matrix of the uniformDensity channel. -/
def uniformChannel (A : System) : Mat (ChoiRegister A) := Matrix.kronecker 1 (uniformDensity (Out A))

/-- PDF p.9: ordinary preservation of the single uniformDensity channel. -/
def PreservesUniformity {A B : System} (T : Supermap A B) : Prop :=
  T (uniformChannel A) = uniformChannel B

/-- PDF pp.9–10: A's output is uniformDensity and independent of all other registers,
on ALL input operators, represented here by the corresponding Choi factorization. -/
def MarginallyUniform (A C : System)
    (X : Mat ((In A × In C) × (Out A × Out C))) : Prop :=
  ∀ p q, X p q = uniformDensity (Out A) p.2.1 q.2.1 *
    ∑ a1, X (p.1, (a1, p.2.2)) (q.1, (a1, q.2.2))

/-- PDF p.10: complete uniformity preservation, with arbitrary auxiliary dynamical system. -/
def CompletelyUniformityPreserving {A B : System} (T : Supermap A B) : Prop :=
  ∀ (C : System) (X : Mat ((In A × In C) × (Out A × Out C))),
    ChannelChoi X → MarginallyUniform A C X → MarginallyUniform B C (amplifySupermap T C X)

/-- PDF p.11: unital means Phi(I)=I, without dimensional rescaling. -/
def Unital {I J : Type} [Fintype I] [DecidableEq J] (X : Mat (I × J)) : Prop := QAlgorithms.traceLeft X = 1

/-- PDF p.11, ordinary unital-channel preservation. -/
def UnitalPreserving {A B : System} (T : Supermap A B) : Prop :=
  ∀ X : Mat (ChoiRegister A), ChannelChoi X → Unital X → Unital (T X)

/-- PDF p.11: only ancillary systems with matched input/output dimensions occur here,
as A0=A1 and B0=B1 in Theorem 4. -/
def CompletelyUnitalPreserving {A B : System} (T : Supermap A B) : Prop :=
  ∀ (C : System), C.input = C.output →
    ∀ X : Mat ((In A × In C) × (Out A × Out C)),
      ChannelChoi X → Unital X → Unital (amplifySupermap T C X)

/-- PDF p.11: a random unitary CHANNEL, distinct from a random unitary superchannel. -/
def RandomUnitaryChannel (A : System) (X : Mat (ChoiRegister A)) : Prop :=
  ∃ (m : ℕ) (p : Fin m → ℝ) (U : Fin m → Matrix (Out A) (In A) ℂ),
    0 < m ∧ (∀ x, 0 ≤ p x) ∧ (∑ x, p x = 1) ∧
    (∀ x, UnitaryBetween (U x)) ∧
    X = ∑ x, (p x : ℂ) • ketProjector (fun a => U x a.2 a.1)

/-- PDF pp.11–12, corrected ordinary criterion: retain the identity normalization from
Eq.(58). Printed: only the affine marginal decomposition in the final iff. Changed:
conjoin J^{B1}=d_A0 I. Why: a fixed non-unital output satisfies the decomposition alone. -/
def AffineUnitalCriterion {A B : System} (T : Supermap A B) : Prop :=
  QAlgorithms.traceLeft (jB T) = (A.input : ℂ) • (1 : Mat (Out B)) ∧
  ∃ (a : Mat (Out A × Out B)) (b : Mat (In A × Out B)),
    a.IsHermitian ∧ b.IsHermitian ∧
    jAB1 T = (fun p q => (1 : Mat (In A)) p.1.1 q.1.1 * a (p.1.2, p.2) (q.1.2, q.2) +
      (1 : Mat (Out A)) p.1.2 q.1.2 * b (p.1.1, p.2) (q.1.1, q.2))

/-- PDF p.4, Eq.(21): apply a map on the first factor, retaining all memory coherences. -/
def applyFirst {I J E : Type} [Fintype I] (X : Mat (I × J))
    (R : Mat (I × E)) : Mat (J × E) :=
  fun p q => ∑ i, ∑ j, X (i, p.1) (j, q.1) * R (i, p.2) (j, q.2)

/-- PDF p.4, Eq.(21): equality on all linear maps and all operators, not just channels/states. -/
def Realizes {A B : System} (T : Supermap A B) (e : ℕ)
    (P : Mat (In B × (In A × Fin e))) (Q : Mat ((Out A × Fin e) × Out B)) : Prop :=
  ∀ (X : Mat (ChoiRegister A)) (R : Mat (In B)),
    action (T X) R = action Q (applyFirst X (action P R))

/-- PDF p.9, Eq.(49): every memory operator, including non-Hermitian operators. -/
def DepolarizingPost {A B : System} (e : ℕ)
    (Q : Mat ((Out A × Fin e) × Out B)) : Prop :=
  ∀ R : Mat (Fin e), action Q (Matrix.kronecker (uniformDensity (Out A)) R) = R.trace • uniformDensity (Out B)

/-- PDF p.9, Eq.(50): trace the memory after applying the pre-channel. -/
def UniformPre {A B : System} (e : ℕ) (P : Mat (In B × (In A × Fin e))) : Prop :=
  QAlgorithms.traceRight (action P (uniformDensity (In B))) = uniformDensity (In A)

/-- PDF pp.5–6, Eqs.(26),(29): reshape the SAME Choi matrix into Gamma's input/output order. -/
def gammaChoi {A B : System} (T : Supermap A B) :
    Mat ((Out A × In B) × (In A × Out B)) :=
  fun p q => superChoi T ((p.2.1, p.1.1), (p.1.2, p.2.2))
    ((q.2.1, q.1.1), (q.1.2, q.2.2))

/-- PDF p.6, Eq.(31): Gamma's ordinary no-signalling marginal, equality on all operators. -/
def GammaMarginal {A B : System} (T : Supermap A B) : Prop :=
  ∃ K : Mat (In B × In A), ChannelChoi K ∧
    ∀ R : Mat (Out A × In B),
      QAlgorithms.traceRight (action (gammaChoi T) R) = action K (QAlgorithms.traceLeft R)

/-- PDF p.11, Eq.(59): full joint output, with B1 marginal on the right. -/
def GammaUniformInput {A B : System} (T : Supermap A B) : Prop :=
  ∀ R : Mat (Out A), QAlgorithms.IsDensityMatrix R →
    action (gammaChoi T) (Matrix.kronecker R (uniformDensity (In B))) =
      Matrix.kronecker (uniformDensity (In A)) (QAlgorithms.traceLeft (action (gammaChoi T) (Matrix.kronecker R (uniformDensity (In B)))))

/-- PDF p.12: base-two Renyi entropy. Orders zero and one use rank and von Neumann entropy;
the spectral projection onto nonzero eigenvalues has trace equal to rank for a density matrix. -/
def renyiEntropy {I : Type} [Fintype I] [DecidableEq I] (a : ℝ) (R : Mat I) : ℝ :=
  if a = 0 then Real.logb 2 (cfc (fun x : ℝ => if x = 0 then 0 else 1) R).trace.re
  else if a = 1 then -(cfc (fun x : ℝ => x * Real.logb 2 x) R).trace.re
  else Real.logb 2 (cfc (fun x : ℝ => x ^ a) R).trace.re / (1 - a)

/-- PDF p.12: infimum over exactly the density matrices. The theorem below also states
attainment, so no empty-set/unbounded-set default is used for channels. -/
def minimumOutput (A : System) (a : ℝ) (X : Mat (ChoiRegister A)) : ℝ :=
  sInf {v | ∃ R : Mat (In A), QAlgorithms.IsDensityMatrix R ∧ v = renyiEntropy a (action X R)}

/-- PDF pp.17–18: a consistent divergence on every finite-dimensional register. -/
abbrev StateDivergence := ∀ (I : Type) [Fintype I] [DecidableEq I], Mat I → Mat I → EReal

/-- PDF p.17: the sole assumption on D is state data processing; no finiteness,
positivity, symmetry, or diagonal normalization is imposed. -/
def DivergenceDPI (D : StateDivergence) : Prop :=
  ∀ (I J : Type) [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype J] [DecidableEq J] [Nonempty J]
    (F : QAlgorithms.Superop I J), QAlgorithms.IsChannel F →
    ∀ R S : Mat I, QAlgorithms.IsDensityMatrix R → QAlgorithms.IsDensityMatrix S → D J (F R) (F S) ≤ D I R S

/-- PDF p.18, Eq.(89): extended-real supremum over all reference dimensions and density
operators. Empty references are excluded. The reference is placed first on both outputs. -/
def stabilizedDivergence (D : StateDivergence) (A : System) (X Y : Mat (ChoiRegister A)) : EReal :=
  ⨆ r : ℕ, ⨆ (_hr : 0 < r), ⨆ R : {R : Mat (Fin r × In A) // QAlgorithms.IsDensityMatrix R},
    D (Fin r × Out A) (QAlgorithms.idTensorSuperop (action X) R.val)
      (QAlgorithms.idTensorSuperop (action Y) R.val)

/-- Sanity: ordinary partial trace over a one-dimensional missing system has no scaling. -/
example (X : Mat (Fin 1 × Fin 1)) : QAlgorithms.traceRight X 0 0 = X (0, 0) (0, 0) := by
  simp [QAlgorithms.traceRight]

/-- Sanity: the normalized uniformDensity state on a one-dimensional system is the identity. -/
example : uniformDensity (Fin 1) = (1 : Mat (Fin 1)) := by
  simp [uniformDensity]

/-- Sanity: pre-unitary transposition retains the entry P(a,b), without conjugation. -/
example {A B : System} (P : Matrix (In A) (In B) ℂ) (a : In A) (b : In B) :
    preUnitaryKet P (a, b) = P a b := by
  rfl

/-- Sanity: the zero-order Renyi entropy uses rank rather than the x^0 convention at zero. -/
example {I : Type} [Fintype I] [DecidableEq I] (R : Mat I) :
    renyiEntropy 0 R =
      Real.logb 2 (cfc (fun x : ℝ => if x = 0 then 0 else 1) R).trace.re := by
  simp [renyiEntropy]

/-- PDF p.2: joint channel Choi matrix, stored in party order A0,A1,B0,B1. -/
def BipartiteChannel (A B : System) (W : Mat (ChoiRegister A × ChoiRegister B)) : Prop :=
  W.PosSemidef ∧ ∀ (i j : In A) (k l : In B),
    (∑ a1, ∑ b1, W ((i, a1), (k, b1)) ((j, a1), (l, b1))) =
      (1 : Mat (In A × In B)) (i, k) (j, l)

/-- PDF p.13, Definition 4: normalize by INPUT dimensions, never by trace of a CP map. -/
def jointInputNormalizedChoi (A B : System) (W : Mat (ChoiRegister A × ChoiRegister B)) : Mat (ChoiRegister A × ChoiRegister B) :=
  ((A.input * B.input : ℕ) : ℂ)⁻¹ • W

/-- PDF p.13, Eq.(62), the second primal constraint. Gamma lives on A0,A1,B0. -/
def EntropyMarginal (A B : System) (G : Mat (ChoiRegister A × In B)) : Prop :=
  ∀ (i j : In A) (k l : In B),
    (∑ a1, G ((i, a1), k) ((j, a1), l)) =
      uniformDensity (In A) i j * (∑ a, G (a, k) (a, l))

/-- PDF p.13: gamma^{AB0} Matrix.kronecker identity^{B1}, in party order. -/
def extendGamma {A B : System} (G : Mat (ChoiRegister A × In B)) : Mat (ChoiRegister A × ChoiRegister B) :=
  fun p q => G (p.1, p.2.1) (q.1, q.2.1) * (1 : Mat (Out B)) p.2.2 q.2.2

/-- PDF p.13, Definition 4: primal feasibility, NOT a dual or desired entropy identity. -/
def EntropyFeasible (A B : System) (W : Mat (ChoiRegister A × ChoiRegister B))
    (G : Mat (ChoiRegister A × In B)) : Prop :=
  G.IsHermitian ∧ (extendGamma G - jointInputNormalizedChoi A B W).PosSemidef ∧ EntropyMarginal A B G

/-- PDF p.13, Definition 4. The real exponent set is embedded BEFORE the EReal supremum.
This equals minus log2 of the primal minimum on channels and extends homogeneously to CP maps;
at W=0 the value is +infinity. No support-function identity is assumed in this definition. -/
def extendedConditional (A B : System) (W : Mat (ChoiRegister A × ChoiRegister B)) : EReal :=
  sSup {h : EReal | ∃ l : ℝ, h = (l : EReal) ∧
    ∃ G : Mat (ChoiRegister A × In B), EntropyFeasible A B W G ∧ G.trace.re ≤ Real.rpow 2 (-l)}

/-- PDF p.7, Eq.(33): state conditional min-entropy H(J|I), by the primal operator inequality. -/
def stateConditional {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (R : Mat (I × J)) : EReal :=
  sSup {h : EReal | ∃ l : ℝ, h = (l : EReal) ∧ ∃ G : Mat I,
    G.IsHermitian ∧ (Matrix.kronecker G (1 : Mat J) - R).PosSemidef ∧ G.trace.re ≤ Real.rpow 2 (-l)}

/-- PDF p.12, Definition 3: H_min(A1|A0) of the normalized Choi state. -/
def extendedMin (A : System) (X : Mat (ChoiRegister A)) : EReal :=
  stateConditional ((A.input : ℂ)⁻¹ • X)

/-- Extended negative exponential: +infinity maps to zero and -infinity to +infinity. -/
def entropyPower (h : EReal) : EReal :=
  if h = ⊤ then 0 else if h = ⊥ then ⊤ else (Real.rpow 2 (-h.toReal) : EReal)

/-- PDF p.14: fixed-output replacement channel, with all off-diagonal input blocks retained
as zero. A trace-one output gives a trace-preserving channel. -/
def replacementChoi (A B : System) (R : Mat (Out A × Out B)) : Mat (ChoiRegister A × ChoiRegister B) :=
  fun p q => (1 : Mat (In A)) p.1.1 q.1.1 * (1 : Mat (In B)) p.2.1 q.2.1 *
    R (p.1.2, p.2.2) (q.1.2, q.2.2)

/-- Fixed-basis product dynamical system (PDF p.14, Theorem 5(3)). -/
def productSystem (A B : System) : System :=
  ⟨A.input * B.input, A.output * B.output,
    Nat.mul_pos A.input_pos B.input_pos, Nat.mul_pos A.output_pos B.output_pos⟩

/-- The fixed product basis, used consistently for inputs and outputs. -/
def splitReg (A B : System) (a : ChoiRegister (productSystem A B)) : ChoiRegister A × ChoiRegister B :=
  let i := (finProdFinEquiv (m := A.input) (n := B.input)).symm a.1
  let o := (finProdFinEquiv (m := A.output) (n := B.output)).symm a.2
  ((i.1, o.1), (i.2, o.2))

/-- PDF p.12: Matrix.kronecker product of channels in ordinary input/output Choi order. -/
def productChoi {A B : System} (X : Mat (ChoiRegister A)) (Y : Mat (ChoiRegister B)) :
    Mat (ChoiRegister (productSystem A B)) :=
  fun p q => X (splitReg A B p).1 (splitReg A B q).1 *
    Y (splitReg A B p).2 (splitReg A B q).2

/-- PDF p.14: Matrix.kronecker product of bipartite maps, regrouped as AA' and BB'. -/
def productBipartite {A B C D : System} (W : Mat (ChoiRegister A × ChoiRegister B))
    (Z : Mat (ChoiRegister C × ChoiRegister D)) : Mat (ChoiRegister (productSystem A C) × ChoiRegister (productSystem B D)) :=
  fun p q => W ((splitReg A C p.1).1, (splitReg B D p.2).1)
      ((splitReg A C q.1).1, (splitReg B D q.2).1) *
    Z ((splitReg A C p.1).2, (splitReg B D p.2).2)
      ((splitReg A C q.1).2, (splitReg B D q.2).2)

/-- PDF p.14, Eq.(68): T acts on A, with the identity on the complete dynamical system B. -/
def localApply {A C : System} (T : Supermap A C) (B : System)
    (W : Mat (ChoiRegister A × ChoiRegister B)) : Mat (ChoiRegister C × ChoiRegister B) :=
  fun p q => T (fun a a' => W (a, p.2) (a', q.2)) p.1 q.1

/-- PDF p.14, Remark 4: insert the SPECIFIED state at C0 and trace C1. -/
def discardConditioner {A B C : System}
    (W : Mat (ChoiRegister (productSystem A C) × ChoiRegister B)) (R : Mat (In C)) : Mat (ChoiRegister A × ChoiRegister B) :=
  fun p q => ∑ i, ∑ j, ∑ o,
    W (((finProdFinEquiv (p.1.1, i)), (finProdFinEquiv (p.1.2, o))), p.2)
      (((finProdFinEquiv (q.1.1, j)), (finProdFinEquiv (q.1.2, o))), q.2) * R i j

/-- Output-state marginal of the normalized Choi matrix (PDF p.14, upper bound). -/
def outputMarginal {A B : System} (W : Mat (ChoiRegister A × ChoiRegister B)) : Mat (Out A × Out B) :=
  fun p q => ∑ i, ∑ j, jointInputNormalizedChoi A B W ((i, p.1), (j, p.2)) ((i, q.1), (j, q.2))

/-- PDF p.14, lower bound: B0 is the conditioning register, and A includes A0 AND A1. -/
def lowerBoundState {A B : System} (W : Mat (ChoiRegister A × ChoiRegister B)) : Mat (In B × (ChoiRegister A × Out B)) :=
  fun p q => jointInputNormalizedChoi A B W (p.2.1, (p.1, p.2.2)) (q.2.1, (q.1, q.2.2))

/-- PDF p.13, Eq.(66): Bell input/output overlap, with unnormalized Bell projectors. -/
def jointBellOverlap (B : System) (W : Mat (ChoiRegister B × ChoiRegister B)) : ℝ :=
  (∑ i, ∑ j, ∑ k, ∑ l, W ((i, k), (i, k)) ((j, l), (j, l))).re

/-- PDF p.15, Eq.(80), and Appendix B: only B1 is classical. -/
def ClassicalOutput {A B : System} (W : Mat (ChoiRegister A × ChoiRegister B)) : Prop :=
  ∀ (a a' : ChoiRegister A) (i j : In B) (x y : Out B), x ≠ y → W (a, (i, x)) (a', (j, y)) = 0

/-- PDF pp.15–16: both B0 and B1 are classical. -/
def ClassicalSystem {A B : System} (W : Mat (ChoiRegister A × ChoiRegister B)) : Prop :=
  ClassicalOutput W ∧ ∀ (a a' : ChoiRegister A) (i j : In B) (x y : Out B),
    i ≠ j → W (a, (i, x)) (a', (j, y)) = 0

/-- PDF p.15, Eq.(81): a subnormalized conditional instrument branch; no renormalization. -/
def classicalBranch {A B : System} (W : Mat (ChoiRegister A × ChoiRegister B)) (y : In B) (x : Out B) :
    Mat (ChoiRegister A) := fun a a' => W (a, (y, x)) (a', (y, x))

/-- PDF p.15, Eq.(82): normalized entangled input and a COMPLETE POVM, with reference A0. -/
structure GuessStrategy (A B : System) where
  ket : In A × In A → ℂ
  ket_norm : ∑ i, Complex.normSq (ket i) = 1
  effect : Out B → Mat (In A × Out A)
  effect_positive : ∀ x, (effect x).PosSemidef
  effect_sum : ∑ x, effect x = 1

/-- PDF p.15, Eq.(82): the branch weight remains in the trace, including zero branches. -/
def guessScore {A B : System} (W : Mat (ChoiRegister A × ChoiRegister B)) (y : In B) (s : GuessStrategy A B) : ℝ :=
  ∑ x, (s.effect x * QAlgorithms.idTensorSuperop
    (action (classicalBranch W y x)) (ketProjector s.ket)).trace.re

/-- PDF p.16: each known y has its OWN optimization, followed by the UNIFORM average. -/
def guessProbability {A B : System} (W : Mat (ChoiRegister A × ChoiRegister B)) : EReal :=
  ((1 / (B.input : ℝ) : ℝ) : EReal) *
    ∑ y, ⨆ s : GuessStrategy A B, (guessScore W y s : EReal)

/-- PDF p.16: operational specialization to discrimination of channels with prior p. -/
def discriminationProbability (A B : System) (p : Out B → ℝ)
    (L : In B → Out B → Mat (ChoiRegister A)) : EReal :=
  ((1 / (B.input : ℝ) : ℝ) : EReal) * ∑ y,
    ⨆ s : GuessStrategy A B, ((∑ x, p x *
      (s.effect x * QAlgorithms.idTensorSuperop (action (L y x)) (ketProjector s.ket)).trace.re : ℝ) : EReal)

/-- Appendix B, Eq.(108): CP instrument on the BOTH quantum inputs; output x is classical. -/
def quantumBranch {A B : System} (W : Mat (ChoiRegister A × ChoiRegister B)) (x : Out B) :
    Mat ((In A × In B) × Out A) :=
  fun p q => W ((p.1.1, p.2), (p.1.2, x)) ((q.1.1, q.2), (q.1.2, x))

/-- Appendix B, Eq.(112): V may jointly mix the original inputs; this is not a separated-party
Bell-agreement instrument. Both positivity AND sum-to-identity of the POVM are retained. -/
structure QuantumGuessStrategy (A B : System) where
  isometry : Matrix (In A × (In A × In B)) (In B) ℂ
  isometry_norm : isometryᴴ * isometry = 1
  effect : Out B → Mat ((In A × In B) × Out A)
  effect_positive : ∀ x, (effect x).PosSemidef
  effect_sum : ∑ x, effect x = 1

/-- Appendix B, Eq.(112): (id Matrix.kronecker V)|phi+>/sqrt(d_B0). -/
def quantumGuessKet {A B : System} (s : QuantumGuessStrategy A B) :
    (In A × In B) × (In A × In B) → ℂ :=
  fun p => s.isometry (p.1.1, p.2) p.1.2 / (Real.sqrt (B.input : ℝ) : ℂ)

/-- Appendix B, Eq.(112): the actual joint input, channel application, and measurement. -/
def quantumGuessScore {A B : System} (W : Mat (ChoiRegister A × ChoiRegister B))
    (s : QuantumGuessStrategy A B) : ℝ :=
  ∑ x, (s.effect x * QAlgorithms.idTensorSuperop (action (quantumBranch W x))
    (ketProjector (quantumGuessKet s))).trace.re

/-- Appendix B, Eq.(112): supremum of physical strategies, with attainment in the theorem. -/
def quantumGuessProbability {A B : System} (W : Mat (ChoiRegister A × ChoiRegister B)) : EReal :=
  ⨆ s : QuantumGuessStrategy A B, (quantumGuessScore W s : EReal)

/-- PDF p.18: the fixed tomographic experiment, with normalized pure input probes and an
informationally complete basis POVM. Span and independence are over the REAL Hermitian space. -/
structure Tomography (R : System) where
  probe : Fin (R.input ^ 2) → In R → ℂ
  probe_norm : ∀ x, ∑ i, Complex.normSq (probe x i) = 1
  probe_independent : LinearIndependent ℝ (fun x => ketProjector (probe x))
  probe_span : ∀ H : Mat (In R), H.IsHermitian →
    H ∈ Submodule.span ℝ (Set.range (fun x => ketProjector (probe x)))
  effect : Fin (R.output ^ 2) → Mat (Out R)
  effect_positive : ∀ y, (effect y).PosSemidef
  effect_sum : ∑ y, effect y = 1
  effect_independent : LinearIndependent ℝ effect
  effect_span : ∀ H : Mat (Out R), H.IsHermitian → H ∈ Submodule.span ℝ (Set.range effect)

/-- PDF p.18: prepare probe x at R0 and measure effect y at R1, retaining branch weights. -/
def extractedBranch {A R : System} (W : Mat (ChoiRegister A × ChoiRegister R)) (t : Tomography R)
    (x : Fin (R.input ^ 2)) (y : Fin (R.output ^ 2)) : Mat (ChoiRegister A) :=
  fun a a' => ∑ i, ∑ j, ∑ k, ∑ l,
    W (a, (i, k)) (a', (j, l)) * ketProjector (t.probe x) i j * t.effect y l k

/-- PDF pp.18–19: C_* has one CP instrument for EACH x. This is the star SUBSCRIPT family,
with exactly d_R1^2 outcomes y=1,...,d_Y (Fin uses zero-based storage). -/
def InstrumentFamily (B : System) (x y : ℕ) (K : Fin x → Fin y → Mat (ChoiRegister B)) : Prop :=
  (∀ i j, (K i j).PosSemidef) ∧ ∀ i, QAlgorithms.traceRight (∑ j, K i j) = 1

/-- PDF p.18, Theorem 7: paired CP map; it need not be trace preserving and may be ZERO. -/
def pairedMap {A B : System} {x y : ℕ} (F : Fin x → Fin y → Mat (ChoiRegister A))
    (K : Fin x → Fin y → Mat (ChoiRegister B)) : Mat (ChoiRegister A × ChoiRegister B) :=
  (x : ℂ)⁻¹ • ∑ i, ∑ j, Matrix.kronecker (F i j) (K i j)

/-- PDF p.17, Eq.(88): one superchannel on A, identity on BOTH R0 and R1. Matrices are
stored in party order A,R, a fixed permutation of the source's displayed order R,A. -/
def QuantumMajorizes {A B R : System} (F : Mat (ChoiRegister A × ChoiRegister R))
    (G : Mat (ChoiRegister B × ChoiRegister R)) : Prop :=
  ∃ T : Supermap A B, IsSuperchannel T ∧ localApply T R F = G

/-- PDF p.20, Corollary 1: the two marginal bipartite channels of the displayed tripartite
mixture. The omitted local factor is TP, so fixing any of its input states gives this marginal. -/
def familyMixture {A B : System} {n : ℕ} (X : Fin n → Mat (ChoiRegister A))
    (K : Fin n → Mat (ChoiRegister B)) : Mat (ChoiRegister A × ChoiRegister B) :=
  (n : ℂ)⁻¹ • ∑ j, Matrix.kronecker (X j) (K j)

/-- PDF p.20, Remark 6: an increasing entropy contraction; no metric properties are imposed. -/
def entropyContraction (A B : System) (K L : Mat (ChoiRegister B)) (X Y : Mat (ChoiRegister A)) : EReal :=
  extendedConditional A B ((1 / 2 : ℂ) • (Matrix.kronecker X K + Matrix.kronecker Y L))

/-- PDF p.21: Gibbs states are supplied as density matrices; the free replacer is trace times G. -/
def gibbsChoi (A : System) (G : Mat (Out A)) : Mat (ChoiRegister A) := Matrix.kronecker 1 G

/-- PDF p.20, Eqs.(100)–(102), in the proof-equivalent normalization: transpose TEST K.
The page image places T on Phi; transposing the ENTIRE LMI (including gamma), then renaming
gamma, gives this test-transpose form with unchanged trace objective. Gamma is Hermitian. -/
def ComparisonFeasible {A B : System} {x y : ℕ} (F : Fin x → Fin y → Mat (ChoiRegister A))
    (K : Fin x → Fin y → Mat (ChoiRegister B)) (G : Mat (ChoiRegister A × In B)) : Prop :=
  InstrumentFamily B x y K ∧ G.IsHermitian ∧ EntropyMarginal A B G ∧
  (extendGamma G - (((A.input * x ^ 2 : ℕ) : ℂ)⁻¹ •
    ∑ i, ∑ j, Matrix.kronecker (F i j) (K i j).transpose)).PosSemidef

/-- PDF p.20, Eq.(99): the proof-derived primal objective, with the d_X^{-2} cq normalization. -/
def comparisonSDPValue {A B : System} {x y : ℕ} (F : Fin x → Fin y → Mat (ChoiRegister A))
    (H : Fin x → Fin y → Mat (ChoiRegister B)) : EReal :=
  sInf {v : EReal | ∃ (K : Fin x → Fin y → Mat (ChoiRegister B)) (G : Mat (ChoiRegister A × In B)),
    ComparisonFeasible F K G ∧
    v = ((G.trace.re - (1 / (x : ℝ) ^ 2) * ∑ i, ∑ j, (H i j * K i j).trace.re : ℝ) : EReal)}

/-- PDF pp.20–21: real scalar variables in the displayed SDP: Hermitian gamma plus each
Hermitian test-branch Choi block. This count refers to the variables actually optimized above. -/
def comparisonVariables (A B : System) (x y : ℕ) : ℕ :=
  (A.input * A.output * B.input) ^ 2 + x * y * (B.input * B.output) ^ 2

/-- PDF pp.20–21: independent real linear equalities in (101),(102). -/
def comparisonEqualities (A B : System) (x : ℕ) : ℕ :=
  (A.input ^ 2 - 1) * B.input ^ 2 + x * B.input ^ 2

/-- PDF p.21: total PSD block order, one block for (100) and one per test branch. -/
def comparisonPSDOrder (A B : System) (x y : ℕ) : ℕ :=
  A.input * A.output * B.input * B.output + x * y * B.input * B.output

/-- PDF p.21, Sec.VI: zero-fold Matrix.kronecker power is the one-dimensional missing system. -/
def powerSystem (A : System) : ℕ → System
  | 0 => ⟨1, 1, by decide, by decide⟩
  | n + 1 => productSystem (powerSystem A n) A

/-- PDF p.21: Matrix.kronecker powers as actual products of the supplied channel, not free variables. -/
def powerBipartite {A B : System} (W : Mat (ChoiRegister A × ChoiRegister B)) :
    (n : ℕ) → Mat (ChoiRegister (powerSystem A n) × ChoiRegister (powerSystem B n))
  | 0 => 1
  | n + 1 => productBipartite (powerBipartite W n) W

/-- PDF p.21: ordinary input-first joint Choi order, used only to apply a bipartite channel. -/
def jointChoi {A B : System} (W : Mat (ChoiRegister A × ChoiRegister B)) :
    Mat ((In A × In B) × (Out A × Out B)) :=
  fun p q => W ((p.1.1, p.2.1), (p.1.2, p.2.2)) ((q.1.1, q.2.1), (q.1.2, q.2.2))

/-- PDF p.21: diamond distance of two channels, with all reference-assisted density inputs.
Only channel differences are used. Its supremum is nonempty and lies in [0,2]. -/
def jointDiamondDistance {A B : System} (W Z : Mat (ChoiRegister A × ChoiRegister B)) : ℝ :=
  sSup {v : ℝ | ∃ (r : ℕ) (_hr : 0 < r)
    (R : Mat (Fin r × (In A × In B))), QAlgorithms.IsDensityMatrix R ∧
    v = QAlgorithms.traceNorm (QAlgorithms.idTensorSuperop (action (jointChoi W)) R -
      QAlgorithms.idTensorSuperop (action (jointChoi Z)) R)}

/-- PDF p.21: smoothing over CHANNELS in a diamond ball. At channel centers and epsilon>=0
this real supremum is nonempty and bounded; all channel entropies are finite. -/
def smoothExtended (A B : System) (W : Mat (ChoiRegister A × ChoiRegister B)) (epsilon : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ Z : Mat (ChoiRegister A × ChoiRegister B), BipartiteChannel A B Z ∧
    jointDiamondDistance W Z ≤ epsilon ∧ v = (extendedConditional A B Z).toReal}

/-- PDF pp.21–22: conditional von Neumann entropy in bits of a trace-one output state. -/
def conditionalVonNeumann {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (R : Mat (I × J)) : ℝ :=
  renyiEntropy 1 R - renyiEntropy 1 (QAlgorithms.traceRight R)

/-- Sanity: the zero CP map has zero negative entropy exponential, never a normalized Choi state. -/
example : entropyPower ⊤ = 0 := by simp [entropyPower]

/-- Sanity: product registers use exactly the same fixed basis for input and output. -/
example (A B : System) (i : In A) (j : In B) (k : Out A) (l : Out B) :
    splitReg A B (finProdFinEquiv (i, j), finProdFinEquiv (k, l)) = ((i, k), (j, l)) := by
  simp [splitReg]

/-- Sanity: the initial entanglement factor is 1/sqrt(d_B0), even when the instrument has zero branches. -/
example {A B : System} (s : QuantumGuessStrategy A B)
    (a : In A) (i : In B) (j : In A) (k : In B) :
    quantumGuessKet s ((a, i), (j, k)) = s.isometry (a, (j, k)) i /
      (Real.sqrt (B.input : ℝ) : ℂ) := by rfl

/-- PDF p.18: a channel contraction is a family on all finite dynamical systems.
No symmetry, positivity, normalization or induced-state-divergence representation is assumed. -/
abbrev ChannelContraction := ∀ A : System, Mat (ChoiRegister A) → Mat (ChoiRegister A) → EReal

/-- PDF p.18: contraction under every physical superchannel, on every pair of channels. -/
def ChannelContractionDPI (C : ChannelContraction) : Prop :=
  ∀ (A B : System) (T : Supermap A B), IsSuperchannel T →
    ∀ X Y : Mat (ChoiRegister A), ChannelChoi X → ChannelChoi Y →
      C B (T X) (T Y) ≤ C A X Y

/-- Sanity: the generic contraction hypothesis is satisfiable in every positive dimension. -/
example : ChannelContractionDPI (fun _ _ _ => 0) := by
  intro A B T hT X Y hX hY
  exact le_rfl

end QAlgorithms.Papers.Independent.Dependency50.P05


