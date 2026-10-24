-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P12
-- name    : QAlgorithms_Papers_Independent_Support50_P12
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-23T19:07:51.8876+00:00
-- url     : https://prove2.me/theorems/f9f109b0-b9a5-41ab-a22f-a91af3038efa
-- title:
--   Definitions for Quantum f-divergences and error correction
-- statement:
--   The objects the formalized statements of *Quantum f-divergences and error correction* (arXiv:1008.2529) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Alg`
--   - `supp`: Section 2, p.4: support projection, including support(0)=0.
--   - `AlgebraDensity`: Section 2, p.4: density operators in the stated concrete algebra.
--   - `spec`: Section 2, p.5: distinct spectral values, including zero when it is an eigenvalue.
--   - `cpow`: Section 2, p.5: support-zero complex powers, including z=0.
--   - `modular`: Equation (2.1), p.5: functional calculus of L_A R_(B^-1), acting on X.
--   - `quasi`: Definition 2.1, p.5: the finite Hilbert–Schmidt expression.
--   - `recessionSlope`: Definition 2.1, p.5: recession slope in signed extended reals.
--   - `DivergenceGenerator`: Definition 2.1, p.5: continuity only at strictly positive arguments and existence of the signed extended recession slope. Values at negative arguments are unused.
--   - `div`: Definition 2.1, p.5: supported expression, and one-sided regularization otherwise.
--   - `supportScalarPower`: Example 2.7, pp.6–7: scalar support powers, also at exponent zero.
--   - `petzRenyi`: Example 2.7, pp.6–7: unnormalized Petz Rényi relative entropy.
--   - `AlgebraExtension`: Section 3, p.9: canonical extensions of maps between concrete algebras. The range conditions mean Phi=i_B ◦ phi ◦ E_A; E_A is the trace-orthogonal projection.
--   - `PositiveOnConcreteAlgebra`: Section 3, p.9: positivity only on the stated algebra.
--   - `AlgebraTracePreserving`: Section 3, p.9: trace preservation on the stated algebra.
--   - `AlgebraTraceNonincreasing`: Section 3, p.9: trace non-increase on positive elements.
--   - `SchwarzBound`: Section 3, p.12: Schwarz bound, including positivity at coefficient zero.
--   - `AlgebraSchwarzMap`: Section 3, p.12: finite Schwarz norm means existence of a nonnegative bound.
--   - `snorm`: Section 3, p.12: extended norm, +infinity if there is no Schwarz bound.
--   - `pnorm`: Section 3, p.12: operator norm, using the source equality for positive maps.
--   - `Substochastic`: Section 3, p.12: the adjoint Schwarz condition, not a CP condition.
--   - `AlgebraStochastic`: Section 3, p.12: stochastic = trace preserving and substochastic.
--   - `modularContraction`: Equation (4.1), p.16: the actual Hilbert–Schmidt contraction V.
--   - `CornerTP`: Section 3, p.10: trace preservation on a support corner.
--   - `amp`: Section 3, p.9: n×n block amplification of a map, acting on genuine block entries.
--   - `AlgebraKPositive`: Section 3, p.9: n-positivity on all positive block matrices over the domain algebra.
--   - `AlgebraCompletelyPositive`: Section 3, p.9: complete positivity at every finite amplification size.
--   - `CoBound`: Remark 4.8, p.20: co-Schwarz condition, with reversed product in the argument.
--   - `CoSubstochastic`: Remark 4.8, p.20: co-substochastic maps use the adjoint co-Schwarz contraction.
--   - `CoStochastic`: Remark 4.8, p.20: co-stochastic maps.
--   - `KCoPositive`: Remark 5.7, p.26: n-copositivity is positivity after transposing each input block.
--   - `SemidefiniteOperatorConvex`: Section 4, p.17: all-size operator convexity INCLUDING semidefinite matrices.
--   - `PosReal`: Theorem 8.1, pp.37–38: measures live on the OPEN positive half-line.
--   - `representationKernel`: Equation (8.2), p.37: the combined kernel is integrated as one function.
--   - `HalfLineRepresentation`: Theorem 8.1, p.37: a genuine integral representation, with integrability guards.
--   - `continuousPart`: Equation (5.1), p.21: remove the possible jump at zero before representing f.
--   - `representingMeasure`: Section 5, p.21: the unique representing measure, computed from the continuous part. Only operator convex functions are used in measure-support criteria.
--   - `Rich`: Sections 5 and 7: actual cardinal support, including infinite support.
--   - `resolventGenerator`: Equation (4.9), p.17.
--   - `modularSpec`: Section 5, p.21: spectrum of the relative modular operator on the stated algebra.
--   - `logOverlap`: Definition 6.1, p.27: raw log-overlap, no normalization by trace.
--   - `chernoff`: Definition 6.1, p.27: Chernoff supremum on [0,1).
--   - `hoeffding`: Definition 6.1, p.27: Hoeffding distance as a signed extended supremum.
--   - `psiReal`: Remark 6.2, pp.27–28: finite log-overlap representative, used only on nonorthogonal pairs.
--   - `logOverlapPerspective`: Remark 6.2, p.27: perspective, including +infinity on the negative half-line.
--   - `polar`: Remark 6.2, p.27: Legendre–Fenchel transform in extended reals.
--   - `Reversible`: Sections 6–7: exact recoverability of a positive pair by one stochastic map.
--   - `RepresentsStateDivergence`: Section 6, p.30: representability on the state space of one algebra.
--   - `TwoProjections`: Section 6, p.30: nontrivial algebras admit two nonzero orthogonal projections.
--   - `Noncommutative`: Sections 6–7: noncommutativity is a property of the actual observable algebra.
--   - `signedSchatten`: Proposition A.6, p.46: norm-like functional for ALL nonzero real exponents. The zero-matrix branch is explicitly zero, including at negative q.
--   - `SpectralAlphabet`: Lemma 2.9, p.7: the exact product spectral alphabet.
--   - `law1`: Lemma 2.9, p.7: the first classical distribution a Tr(P_a Q_b).
--   - `law2`: Lemma 2.9, p.7: the second classical distribution b Tr(P_a Q_b).
--   - `isometricConjugation`: Corollary 2.5, p.6: linear isometries, or anti-linear isometries via transpose.
--   - `pairConditions`: Section 5, p.21: ten conditions, computed from the input pair. The Boolean selects Remark 5.7's co-variant, changing precisely (i),(ii),(vi)–(viii).
--   - `PairChain`: Theorem 5.1, pp.21–25: asymmetric implication chain, never a blanket equivalence.
--   - `RecoveryRefinement`: Sections 5 and 7: preserve the positivity level when a stochastic recovery exists.
--   - `hull`: Section 7, p.33: CLOSED convex hull in the finite-dimensional matrix topology.
--   - `Covers`: Section 7, p.33: maximal support without choosing an unrelated projection.
--   - `CodeSupportEquals`: Section 7, p.33: equality of a reference support with the join of code supports.
--   - `RecoveryBlocks`: Section 7, p.34: shared direct-sum/tensor data. Algebraic action and cone equality are deliberately NOT fields; they are conclusions in the theorems below.
--   - `inputBlock`: Shared block embedding on the input side, equation (3.8), p.15.
--   - `outputBlock`: Shared block action on the output side, equation (3.8), p.15.
--   - `BlockSupports`: Section 7, p.34: support joins are exactly the direct sum of all the shared blocks.
--   - `BlockState`: Section 7, p.34: a code state has variable left states and probabilities, while the noise states, embeddings, and unitaries are shared across the whole code.
--   - `bayesianTestingDistance`: Equation (6.8), p.29: optimal Bayesian error normalized by min(p,1-p).
--   - `codeConditions`: Theorem 7.1, pp.33–34: its ten uniform criteria.
--   - `MonotoneRepresentation`: Section 6, p.30: monotone functions are strictly increasing on the ATTAINED extended divergence range, rather than on an arbitrary real domain.
--   - `transposeNoise`: Example 3.6, p.12: transpose mixed with complete depolarization.
--   - `identityNoise`: Example 3.6, pp.12–13: identity mixed with complete depolarization.
--   - `transposeMix`: Example 3.6, p.13: transpose mixed with identity.
--   - `transposeDefect`: Example 3.6, p.12: the full six-term Schwarz defect expansion.
--   - `MonotoneMap`: Remark 4.8, pp.20–21: maps monotone for a specified f.
--   - `renyiOne`: Remark 6.2, p.28: limiting order-one entropy, before identifying it on states.
--   - `exampleRho`: Example 6.6, p.31: the stated diagonal state.
--   - `exampleSigma`: Example 6.6, p.31: the stated reference state.
--   - `merge`: Example 6.6, p.31: canonical extension of the diagonal block-merging map.
--   - `diagonalAlgebra`: Section 6, p.31: the concrete diagonal observable algebra.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, https://arxiv.org/abs/1008.2529v6

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Learning
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04
import Definitions.Def_QAlgorithms_Defs_SpectralFilter
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P30
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P28
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P17
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P23
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P03
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_QuantumOutputMetrics
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P71

/-! Hiai–Mosonyi–Petz–Beny, arXiv:1008.2529v6.
Accepted primitives supply matrices, linear maps, trace, Hilbert–Schmidt product,
spectral calculus, support inclusion, adjoints, Petz recovery and tensor-state powers.
Remaining paper-specific definitions use actual representation traces and support-zero powers.
An intrinsic algebra map is represented by its canonical full-matrix extension:
inclusion after the map after the trace-orthogonal projection onto its domain.
`AlgebraExtension` characterizes exactly these extensions by the ranges of the map and
its computed Hilbert–Schmidt adjoint. It adds no positivity or trace assumption.
Compilation is pending the authorized batch handoff. -/

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P12

open Filter MeasureTheory Set
open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)
open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)
open QAlgorithms.Papers.Independent.Dependency50.P28 (tr LE logNonnegativeExtended pinch)
open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint spectralFunction petz relativeEntropy)
open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)
open QAlgorithms.Papers.Independent.Next46.P23 (Supports)
open QAlgorithms.Papers.Independent.Support21.P03 (ExtendedConvex)
open QAlgorithms (spectralProjector)
open QAlgorithms.Learning (IsDistribution)
open QAlgorithms.Papers.Independent.Information100.P04 (absOp)
open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Topology Kronecker

attribute [local instance] Classical.propDecidable Classical.decEq

abbrev Alg (I : Type) [Fintype I] [DecidableEq I] := StarSubalgebra ℂ (Mat I)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

variable {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K]

/-- Section 2, p.4: support projection, including support(0)=0. -/
def supp (X : Mat I) : Mat I := supportPower X 0

/-- Section 2, p.4: density operators in the stated concrete algebra. -/
def AlgebraDensity (A : Alg I) (rho : Mat I) : Prop := rho ∈ A ∧ rho.PosSemidef ∧ tr rho = 1

/-- Section 2, p.5: distinct spectral values, including zero when it is an eigenvalue. -/
def spec (X : Mat I) : Finset ℝ :=
  if h : X.IsHermitian then Finset.univ.image h.eigenvalues else ∅

/-- Section 2, p.5: support-zero complex powers, including z=0. -/
def cpow (X : Mat I) (z : ℂ) : Mat I :=
  spectralFunction (fun a => if a = 0 then 0 else Complex.exp (z * (Real.log a : ℂ))) X

/-- Equation (2.1), p.5: functional calculus of L_A R_(B^-1), acting on X. -/
def modular (f : ℝ → ℝ) (A B X : Mat I) : Mat I :=
  ∑ a ∈ spec A, ∑ b ∈ spec B, (f (a / b) : ℂ) • (spectralProjector A a * X * spectralProjector B b)

/-- Definition 2.1, p.5: the finite Hilbert–Schmidt expression. -/
def quasi (f : ℝ → ℝ) (A B : Mat I) : ℝ :=
  (hs (supportPower B (1 / 2)) (modular f A B (supportPower B (1 / 2)))).re

/-- Definition 2.1, p.5: recession slope in signed extended reals. -/
def recessionSlope (f : ℝ → ℝ) : EReal := limUnder atTop (fun x : ℝ => ((f x / x : ℝ) : EReal))

/-- Definition 2.1, p.5: continuity only at strictly positive arguments and existence
of the signed extended recession slope. Values at negative arguments are unused. -/
def DivergenceGenerator (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Ioi 0) ∧ Tendsto (fun x : ℝ => ((f x / x : ℝ) : EReal)) atTop (𝓝 (recessionSlope f))

/-- Definition 2.1, p.5: supported expression, and one-sided regularization otherwise. -/
def div (f : ℝ → ℝ) (A B : Mat I) : EReal :=
  if Supports A B then (quasi f A B : EReal) else
    limUnder (𝓝[>] (0 : ℝ)) (fun e => (quasi f A (B + (e : ℂ) • 1) : EReal))

/-- Example 2.7, pp.6–7: scalar support powers, also at exponent zero. -/
def supportScalarPower (a x : ℝ) : ℝ := if x = 0 then 0 else Real.rpow x a

/-- Example 2.7, pp.6–7: unnormalized Petz Rényi relative entropy. -/
def petzRenyi (a : ℝ) (A B : Mat I) : EReal :=
  if Supports A B ∨ a < 1 then
    (((a - 1)⁻¹ : ℝ) : EReal) * logNonnegativeExtended (tr (supportPower A a * supportPower B (1 - a)))
  else ⊤

/-- Section 3, p.9: canonical extensions of maps between concrete algebras.
The range conditions mean Phi=i_B ◦ phi ◦ E_A; E_A is the trace-orthogonal projection. -/
def AlgebraExtension (A : Alg I) (B : Alg J) (Phi : MatrixMap I J) : Prop :=
  (∀ X, Phi X ∈ B) ∧ (∀ Y, channelAdjoint Phi Y ∈ A)

/-- Section 3, p.9: positivity only on the stated algebra. -/
def PositiveOnConcreteAlgebra (A : Alg I) (Phi : Mat I → Mat J) : Prop :=
  ∀ X ∈ A, X.PosSemidef → (Phi X).PosSemidef

/-- Section 3, p.9: trace preservation on the stated algebra. -/
def AlgebraTracePreserving (A : Alg I) (Phi : Mat I → Mat J) : Prop := ∀ X ∈ A, (Phi X).trace = X.trace

/-- Section 3, p.9: trace non-increase on positive elements. -/
def AlgebraTraceNonincreasing (A : Alg I) (Phi : Mat I → Mat J) : Prop :=
  ∀ X ∈ A, X.PosSemidef → tr (Phi X) ≤ tr X

/-- Section 3, p.12: Schwarz bound, including positivity at coefficient zero. -/
def SchwarzBound (A : Alg I) (Phi : Mat I → Mat J) (c : ℝ) : Prop :=
  0 ≤ c ∧ PositiveOnConcreteAlgebra A Phi ∧ ∀ X ∈ A, LE ((Phi X)ᴴ * Phi X) ((c : ℂ) • Phi (Xᴴ * X))

/-- Section 3, p.12: finite Schwarz norm means existence of a nonnegative bound. -/
def AlgebraSchwarzMap (A : Alg I) (Phi : Mat I → Mat J) : Prop := ∃ c, SchwarzBound A Phi c

/-- Section 3, p.12: extended norm, +infinity if there is no Schwarz bound. -/
def snorm (A : Alg I) (Phi : Mat I → Mat J) : ℝ≥0∞ :=
  sInf {c | ∃ r : ℝ, SchwarzBound A Phi r ∧ c = ENNReal.ofReal r}

/-- Section 3, p.12: operator norm, using the source equality for positive maps. -/
def pnorm (Phi : Mat I → Mat J) : ℝ :=
  Real.sqrt (sSup {x : ℝ | ∃ v : J → ℂ, ∑ j, ‖v j‖ ^ 2 = 1 ∧
    x = (∑ j, conj (v j) * (((Phi 1)ᴴ * Phi 1) *ᵥ v) j).re})

/-- Section 3, p.12: the adjoint Schwarz condition, not a CP condition. -/
def Substochastic (A : Alg I) (B : Alg J) (Phi : MatrixMap I J) : Prop :=
  AlgebraExtension A B Phi ∧ SchwarzBound B (channelAdjoint Phi) 1

/-- Section 3, p.12: stochastic = trace preserving and substochastic. -/
def AlgebraStochastic (A : Alg I) (B : Alg J) (Phi : MatrixMap I J) : Prop :=
  Substochastic A B Phi ∧ AlgebraTracePreserving A Phi

/-- Equation (4.1), p.16: the actual Hilbert–Schmidt contraction V. -/
def modularContraction (Phi : MatrixMap I J) (B : Mat I) (X : Mat J) : Mat I :=
  channelAdjoint Phi (X * supportPower (Phi B) (-(1 / 2))) * supportPower B (1 / 2)

/-- Section 3, p.10: trace preservation on a support corner. -/
def CornerTP (A : Alg I) (Phi : Mat I → Mat J) (P : Mat I) : Prop :=
  ∀ X ∈ A, (Phi (P * X * P)).trace = (P * X * P).trace

/-- Section 3, p.9: n×n block amplification of a map, acting on genuine block entries. -/
def amp (Phi : Mat I → Mat J) (n : ℕ) (X : Mat (Fin n × I)) : Mat (Fin n × J) :=
  fun u v => Phi (fun i j => X (u.1, i) (v.1, j)) u.2 v.2

/-- Section 3, p.9: n-positivity on all positive block matrices over the domain algebra. -/
def AlgebraKPositive (A : Alg I) (Phi : Mat I → Mat J) (n : ℕ) : Prop :=
  ∀ X : Mat (Fin n × I), (∀ a b, (fun i j => X (a, i) (b, j)) ∈ A) →
    X.PosSemidef → (amp Phi n X).PosSemidef

/-- Section 3, p.9: complete positivity at every finite amplification size. -/
def AlgebraCompletelyPositive (A : Alg I) (Phi : Mat I → Mat J) : Prop := ∀ n, AlgebraKPositive A Phi n

/-- Remark 4.8, p.20: co-Schwarz condition, with reversed product in the argument. -/
def CoBound (A : Alg I) (Phi : Mat I → Mat J) (c : ℝ) : Prop :=
  0 ≤ c ∧ PositiveOnConcreteAlgebra A Phi ∧ ∀ X ∈ A, LE ((Phi X)ᴴ * Phi X) ((c : ℂ) • Phi (X * Xᴴ))

/-- Remark 4.8, p.20: co-substochastic maps use the adjoint co-Schwarz contraction. -/
def CoSubstochastic (A : Alg I) (B : Alg J) (Phi : MatrixMap I J) : Prop :=
  AlgebraExtension A B Phi ∧ CoBound B (channelAdjoint Phi) 1

/-- Remark 4.8, p.20: co-stochastic maps. -/
def CoStochastic (A : Alg I) (B : Alg J) (Phi : MatrixMap I J) : Prop :=
  CoSubstochastic A B Phi ∧ AlgebraTracePreserving A Phi

/-- Remark 5.7, p.26: n-copositivity is positivity after transposing each input block. -/
def KCoPositive (A : Alg I) (Phi : Mat I → Mat J) (n : ℕ) : Prop :=
  ∀ X : Mat (Fin n × I), (∀ a b, (fun i j => X (a, j) (b, i)) ∈ A) →
    X.PosSemidef → (amp (fun Y => Phi (Yᵀ)) n X).PosSemidef

/-- Section 4, p.17: all-size operator convexity INCLUDING semidefinite matrices. -/
def SemidefiniteOperatorConvex (f : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (A B : Mat (Fin n)), A.PosSemidef → B.PosSemidef →
    ∀ t ∈ Icc (0 : ℝ) 1,
      LE (cfc f ((t : ℂ) • A + ((1 - t : ℝ) : ℂ) • B))
        ((t : ℂ) • cfc f A + ((1 - t : ℝ) : ℂ) • cfc f B)

/-- Theorem 8.1, pp.37–38: measures live on the OPEN positive half-line. -/
abbrev PosReal := {t : ℝ // 0 < t}

/-- Equation (8.2), p.37: the combined kernel is integrated as one function. -/
def representationKernel (x : ℝ) (t : PosReal) : ℝ := x / (1 + t.1) - x / (x + t.1)

/-- Theorem 8.1, p.37: a genuine integral representation, with integrability guards. -/
def HalfLineRepresentation (f : ℝ → ℝ) (a b : ℝ) (mu : Measure PosReal) : Prop :=
  0 ≤ b ∧ Integrable (fun t : PosReal => (1 + t.1)⁻¹ ^ 2) mu ∧
  ∀ x ≥ 0, Integrable (representationKernel x) mu ∧
    f x = f 0 + a * x + b * x ^ 2 + ∫ t, representationKernel x t ∂mu

/-- Equation (5.1), p.21: remove the possible jump at zero before representing f. -/
def continuousPart (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x = 0 then limUnder (𝓝[>] (0 : ℝ)) f else f x

/-- Section 5, p.21: the unique representing measure, computed from the continuous part.
Only operator convex functions are used in measure-support criteria. -/
def representingMeasure (f : ℝ → ℝ) : Measure PosReal :=
  Classical.epsilon (fun mu => ∃ a b, HalfLineRepresentation (continuousPart f) a b mu)

/-- Sections 5 and 7: actual cardinal support, including infinite support. -/
def Rich (f : ℝ → ℝ) (n : ℕ) : Prop :=
  (n : Cardinal) ≤ Cardinal.mk (representingMeasure f).support

/-- Equation (4.9), p.17. -/
def resolventGenerator (t x : ℝ) : ℝ := -x / (x + t)

/-- Section 5, p.21: spectrum of the relative modular operator on the stated algebra. -/
def modularSpec (A : Alg I) (X Y : Mat I) : Finset ℝ :=
  ((spec X).product (spec Y)).image (fun p => p.1 / p.2) |>.filter
    (fun a => ∃ Z ∈ A, Z ≠ 0 ∧ X * Z * supportPower Y (-1) = (a : ℂ) • Z)

/-- Definition 6.1, p.27: raw log-overlap, no normalization by trace. -/
def logOverlap (A B : Mat I) (a : ℝ) : EReal :=
  logNonnegativeExtended (tr (supportPower A a * supportPower B (1 - a)))

/-- Definition 6.1, p.27: Chernoff supremum on [0,1). -/
def chernoff (A B : Mat I) : EReal :=
  sSup {v | ∃ a : ℝ, 0 ≤ a ∧ a < 1 ∧ v = -logOverlap A B a}

/-- Definition 6.1, p.27: Hoeffding distance as a signed extended supremum. -/
def hoeffding (A B : Mat I) (r : ℝ) : EReal :=
  sSup {v | ∃ a : ℝ, 0 ≤ a ∧ a < 1 ∧
    v = (((1 - a)⁻¹ : ℝ) : EReal) * ((-a * r : ℝ) - logOverlap A B a)}

/-- Remark 6.2, pp.27–28: finite log-overlap representative, used only on nonorthogonal pairs. -/
def psiReal (A B : Mat I) (a : ℝ) : ℝ := (logOverlap A B a).toReal

/-- Remark 6.2, p.27: perspective, including +infinity on the negative half-line. -/
def logOverlapPerspective (A B : Mat I) (s : ℝ) : EReal :=
  if 0 ≤ s then ((1 + s : ℝ) : EReal) * logOverlap A B (s / (1 + s)) else ⊤

/-- Remark 6.2, p.27: Legendre–Fenchel transform in extended reals. -/
def polar (f : ℝ → EReal) (r : ℝ) : EReal :=
  sSup {v | ∃ s : ℝ, v = ((s * r : ℝ) : EReal) - f s}

/-- Sections 6–7: exact recoverability of a positive pair by one stochastic map. -/
def Reversible (A : Alg I) (B : Alg J) (Phi : MatrixMap I J) (X Y : Mat I) : Prop :=
  ∃ Psi : MatrixMap J I, AlgebraStochastic B A Psi ∧ Psi (Phi X) = X ∧ Psi (Phi Y) = Y

/-- Section 6, p.30: representability on the state space of one algebra. -/
def RepresentsStateDivergence (A : Alg I) (D : Mat I → Mat I → EReal) (f : ℝ → ℝ) : Prop :=
  DivergenceGenerator f ∧ ∀ rho sigma, AlgebraDensity A rho → AlgebraDensity A sigma → D rho sigma = div f rho sigma

/-- Section 6, p.30: nontrivial algebras admit two nonzero orthogonal projections. -/
def TwoProjections (A : Alg I) : Prop :=
  ∃ P Q : Mat I, P ∈ A ∧ Q ∈ A ∧ P.IsHermitian ∧ Q.IsHermitian ∧
    P * P = P ∧ Q * Q = Q ∧ P ≠ 0 ∧ Q ≠ 0 ∧ P * Q = 0

/-- Sections 6–7: noncommutativity is a property of the actual observable algebra. -/
def Noncommutative (A : Alg I) : Prop := ∃ X ∈ A, ∃ Y ∈ A, X * Y ≠ Y * X

/-- Proposition A.6, p.46: norm-like functional for ALL nonzero real exponents.
The zero-matrix branch is explicitly zero, including at negative q. -/
def signedSchatten (p : ℝ) (X : Mat I) : ℝ :=
  if X = 0 then 0 else Real.rpow (tr (supportPower (absOp X) p)) (1 / p)

/-- Section 2 convention at the zero eigenvalue and zero exponent. -/
example : supportScalarPower 0 0 = 0 := by simp [supportScalarPower]

/-- Section 2 convention for the zero overlap. -/
example : logNonnegativeExtended 0 = ⊥ := by simp [logNonnegativeExtended]

/-- The zero-map adjoint is zero, independently of the algebra representation. -/
example (Y : Mat J) : channelAdjoint (0 : MatrixMap I J) Y = 0 := by ext i j; simp [channelAdjoint]

/-- The Appendix's negative-exponent zero branch. -/
example (p : ℝ) : signedSchatten p (0 : Mat I) = 0 := by simp [signedSchatten]

/-- Lemma 2.9, p.7: the exact product spectral alphabet. -/
abbrev SpectralAlphabet (X Y : Mat I) := ↥(spec X) × ↥(spec Y)

/-- Lemma 2.9, p.7: the first classical distribution a Tr(P_a Q_b). -/
def law1 (X Y : Mat I) : SpectralAlphabet X Y → ℝ :=
  fun p => p.1.1 * tr (spectralProjector X p.1.1 * spectralProjector Y p.2.1)

/-- Lemma 2.9, p.7: the second classical distribution b Tr(P_a Q_b). -/
def law2 (X Y : Mat I) : SpectralAlphabet X Y → ℝ :=
  fun p => p.2.1 * tr (spectralProjector X p.1.1 * spectralProjector Y p.2.1)

/-- Corollary 2.5, p.6: linear isometries, or anti-linear isometries via transpose. -/
def isometricConjugation (anti : Bool) (W : Matrix J I ℂ) (X : Mat I) : Mat J :=
  W * (if anti then Xᵀ else X) * Wᴴ

/-- Section 5, p.21: ten conditions, computed from the input pair. The Boolean
selects Remark 5.7's co-variant, changing precisely (i),(ii),(vi)–(viii). -/
def pairConditions (co : Bool) (A : Alg I) (B : Alg J) (Phi : MatrixMap I J)
    (X Y : Mat I) : Fin 10 → Prop :=
  let stochastic := if co then CoStochastic else AlgebraStochastic
  let substochastic := if co then CoSubstochastic else Substochastic
  let cocycle := fun z : ℂ =>
    supp Y * channelAdjoint Phi (if co then cpow (Phi X) z * cpow (Phi Y) (-z)
      else cpow (Phi Y) (-z) * cpow (Phi X) z) = cpow Y (-z) * cpow X z
  ![∃ Psi : MatrixMap J I, stochastic B A Psi ∧ Psi (Phi X) = X ∧ Psi (Phi Y) = Y,
    ∃ Psi : MatrixMap J I, substochastic B A Psi ∧ Psi (Phi X) = X ∧ Psi (Phi Y) = Y,
    ∀ f, DivergenceGenerator f → SemidefiniteOperatorConvex f → div f (Phi X) (Phi Y) = div f X Y,
    ∃ f, DivergenceGenerator f ∧ SemidefiniteOperatorConvex f ∧
      Rich f ((modularSpec A X Y ∪ modularSpec B (Phi X) (Phi Y)).card) ∧
      div f (Phi X) (Phi Y) = div f X Y,
    ∃ T : Set ℝ, T ⊆ Ioi 0 ∧
      (((modularSpec A X Y ∪ modularSpec B (Phi X) (Phi Y)).card : ℕ) : Cardinal) ≤
        Cardinal.mk T ∧ ∀ t ∈ T, div (resolventGenerator t) (Phi X) (Phi Y) = div (resolventGenerator t) X Y,
    ∀ z : ℂ, cocycle z,
    ∃ a : ℝ, 0 < a ∧ a < 2 ∧ a ≠ 1 ∧ cocycle (a : ℂ),
    ∀ t : ℝ, cocycle (Complex.I * (t : ℂ)),
    supp Y * channelAdjoint Phi (cfc Real.log (Phi X) - cfc Real.log (Phi Y) * supp (Phi X)) =
      cfc Real.log X - cfc Real.log Y * supp X,
    petz Y Phi (Phi X) = X]

/-- Theorem 5.1, pp.21–25: asymmetric implication chain, never a blanket equivalence. -/
def PairChain (c : Fin 10 → Prop) : Prop :=
  (c 0 → c 1) ∧ (c 1 → c 2) ∧ (c 2 → c 3) ∧ (c 3 ↔ c 4) ∧
  (c 4 ↔ c 5) ∧ (c 5 ↔ c 6) ∧ (c 6 ↔ c 7) ∧ (c 7 ↔ c 8) ∧ (c 8 → c 9)

/-- Sections 5 and 7: preserve the positivity level when a stochastic recovery exists. -/
def RecoveryRefinement (A : Alg I) (B : Alg J) (Phi : MatrixMap I J) (C : Set (Mat I)) : Prop :=
  (∀ n, AlgebraKPositive A Phi n → ∃ Psi : MatrixMap J I,
    AlgebraStochastic B A Psi ∧ AlgebraKPositive B Psi n ∧ ∀ rho ∈ C, Psi (Phi rho) = rho) ∧
  (AlgebraCompletelyPositive A Phi → ∃ Psi : MatrixMap J I,
    AlgebraStochastic B A Psi ∧ AlgebraCompletelyPositive B Psi ∧ ∀ rho ∈ C, Psi (Phi rho) = rho)

/-- Section 7, p.33: CLOSED convex hull in the finite-dimensional matrix topology. -/
def hull (C : Set (Mat I)) : Set (Mat I) := closure (convexHull ℝ C)

/-- Section 7, p.33: maximal support without choosing an unrelated projection. -/
def Covers (C : Set (Mat I)) (sigma : Mat I) : Prop := ∀ rho ∈ C, Supports rho sigma

/-- Section 7, p.33: equality of a reference support with the join of code supports. -/
def CodeSupportEquals (C : Set (Mat I)) (sigma : Mat I) : Prop :=
  ∀ v : I → ℂ, sigma *ᵥ v = 0 ↔ ∀ rho ∈ C, rho *ᵥ v = 0

/-- Section 7, p.34: shared direct-sum/tensor data. Algebraic action and cone equality
are deliberately NOT fields; they are conclusions in the theorems below. -/
structure RecoveryBlocks (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] where
  count : ℕ
  left1 : Fin count → ℕ
  right1 : Fin count → ℕ
  left2 : Fin count → ℕ
  right2 : Fin count → ℕ
  left1_pos : ∀ k, 0 < left1 k
  right1_pos : ∀ k, 0 < right1 k
  left2_pos : ∀ k, 0 < left2 k
  right2_pos : ∀ k, 0 < right2 k
  embed1 : ∀ k, Matrix I (Fin (left1 k) × Fin (right1 k)) ℂ
  embed2 : ∀ k, Matrix J (Fin (left2 k) × Fin (right2 k)) ℂ
  isometry1 : ∀ k, (embed1 k)ᴴ * embed1 k = 1
  isometry2 : ∀ k, (embed2 k)ᴴ * embed2 k = 1
  orthogonal1 : ∀ k l, k ≠ l → (embed1 k)ᴴ * embed1 l = 0
  orthogonal2 : ∀ k l, k ≠ l → (embed2 k)ᴴ * embed2 l = 0
  noise1 : ∀ k, Mat (Fin (right1 k))
  noise2 : ∀ k, Mat (Fin (right2 k))
  noise1_pos : ∀ k, (noise1 k).PosDef
  noise2_pos : ∀ k, (noise2 k).PosDef
  noise1_trace : ∀ k, tr (noise1 k) = 1
  noise2_trace : ∀ k, tr (noise2 k) = 1
  unitary : ∀ k, Matrix (Fin (left2 k)) (Fin (left1 k)) ℂ
  unitary_left : ∀ k, (unitary k)ᴴ * unitary k = 1
  unitary_right : ∀ k, unitary k * (unitary k)ᴴ = 1

/-- Shared block embedding on the input side, equation (3.8), p.15. -/
def inputBlock (D : RecoveryBlocks I J) (k : Fin D.count) (X : Mat (Fin (D.left1 k))) : Mat I :=
  D.embed1 k * Matrix.kronecker X (D.noise1 k) * (D.embed1 k)ᴴ

/-- Shared block action on the output side, equation (3.8), p.15. -/
def outputBlock (D : RecoveryBlocks I J) (k : Fin D.count) (X : Mat (Fin (D.left1 k))) : Mat J :=
  D.embed2 k * Matrix.kronecker (D.unitary k * X * (D.unitary k)ᴴ) (D.noise2 k) * (D.embed2 k)ᴴ

/-- Section 7, p.34: support joins are exactly the direct sum of all the shared blocks. -/
def BlockSupports (D : RecoveryBlocks I J) (C : Set (Mat I)) (E : Set (Mat J)) : Prop :=
  CodeSupportEquals C (∑ k, D.embed1 k * (D.embed1 k)ᴴ) ∧
  CodeSupportEquals E (∑ k, D.embed2 k * (D.embed2 k)ᴴ)

/-- Section 7, p.34: a code state has variable left states and probabilities,
while the noise states, embeddings, and unitaries are shared across the whole code. -/
def BlockState (D : RecoveryBlocks I J) (rho : Mat I) : Prop :=
  ∃ (p : Fin D.count → ℝ) (X : ∀ k, Mat (Fin (D.left1 k))),
    IsDistribution p ∧ (∀ k, (X k).PosSemidef ∧ tr (X k) = 1) ∧
    rho = ∑ k, (p k : ℂ) • inputBlock D k (X k)

/-- Equation (6.8), p.29: optimal Bayesian error normalized by min(p,1-p). -/
def bayesianTestingDistance (p : ℝ) (rho sigma : Mat I) : EReal :=
  -logNonnegativeExtended ((1 - QAlgorithms.traceNorm ((p : ℂ) • rho - ((1 - p : ℝ) : ℂ) • sigma)) /
    (2 * min p (1 - p)))

/-- Theorem 7.1, pp.33–34: its ten uniform criteria. -/
def codeConditions (A : Alg I) (B : Alg J) (Phi : MatrixMap I J) (C : Set (Mat I)) : Fin 10 → Prop :=
  let d := Fintype.card I ^ 2 + Fintype.card J ^ 2
  ![∃ Psi : MatrixMap J I, AlgebraStochastic B A Psi ∧ ∀ rho ∈ hull C, Psi (Phi rho) = rho,
    ∀ f, DivergenceGenerator f → SemidefiniteOperatorConvex f → ∀ rho ∈ hull C, ∀ sigma ∈ hull C,
      div f (Phi rho) (Phi sigma) = div f rho sigma,
    ∃ sigma f, AlgebraDensity A sigma ∧ Covers C sigma ∧ DivergenceGenerator f ∧ SemidefiniteOperatorConvex f ∧ Rich f d ∧
      ∀ rho ∈ C, div f (Phi rho) (Phi sigma) = div f rho sigma,
    ∃ sigma, AlgebraDensity A sigma ∧ Covers C sigma ∧ ∃ T : Set ℝ, T ⊆ Ioi 0 ∧
      (d : Cardinal) ≤ Cardinal.mk T ∧ ∀ rho ∈ C, ∀ t ∈ T,
        div (resolventGenerator t) (Phi rho) (Phi sigma) = div (resolventGenerator t) rho sigma,
    ∀ rho ∈ hull C, ∀ sigma ∈ hull C, ∀ r : ℝ,
      hoeffding (Phi rho) (Phi sigma) r = hoeffding rho sigma r,
    ∃ sigma, AlgebraDensity A sigma ∧ Covers C sigma ∧ ∃ delta : ℝ, 0 < delta ∧
      ∀ rho ∈ C, ∀ r ∈ Ioo 0 delta, hoeffding (Phi rho) (Phi sigma) r = hoeffding rho sigma r,
    ∀ rho ∈ hull C, ∀ sigma ∈ hull C, CodeSupportEquals C sigma → petz sigma Phi (Phi rho) = rho,
    ∃ sigma, AlgebraDensity A sigma ∧ ∀ rho ∈ C, petz sigma Phi (Phi rho) = rho,
    ∃ D : RecoveryBlocks I J, BlockSupports D C (Phi '' C) ∧ (∀ rho ∈ C, BlockState D rho) ∧
      ∀ k X, inputBlock D k X ∈ A ∧ Phi (inputBlock D k X) = outputBlock D k X,
    ∃ sigma, AlgebraDensity A sigma ∧ Covers C sigma ∧ ∀ rho ∈ C, ∀ p ∈ Ioo (0 : ℝ) 1, ∀ n : ℕ,
      bayesianTestingDistance p ((QAlgorithms.piSuperop (fun _ : Fin n => (Phi : Mat I → Mat J))) (copies n rho)) ((QAlgorithms.piSuperop (fun _ : Fin n => (Phi : Mat I → Mat J))) (copies n sigma)) =
        bayesianTestingDistance p (copies n rho) (copies n sigma)]

/-- Section 6, p.30: monotone functions are strictly increasing on the ATTAINED
extended divergence range, rather than on an arbitrary real domain. -/
def MonotoneRepresentation (A : Alg I) (D : Mat I → Mat I → EReal) (f : ℝ → ℝ) : Prop :=
  let R := {v : EReal | ∃ rho sigma, AlgebraDensity A rho ∧ AlgebraDensity A sigma ∧ v = div f rho sigma}
  ∃ g : R → EReal, StrictMono g ∧ ∀ rho sigma (hr : AlgebraDensity A rho) (hs : AlgebraDensity A sigma),
    D rho sigma = g ⟨div f rho sigma, ⟨rho, sigma, hr, hs, rfl⟩⟩

/-- The zero-copy product is the scalar identity. -/
example (X : Mat I) (a b : Fin 0 → I) : copies 0 X a b = 1 := by simp [copies]

/-- Resolvent kernels do not divide by zero on their intended parameter domain. -/
example (t : PosReal) : representationKernel 0 t = 0 := by simp [representationKernel]

/-- Example 3.6, p.12: transpose mixed with complete depolarization. -/
def transposeNoise (e : ℝ) (X : Mat I) : Mat I :=
  ((1 - e : ℝ) : ℂ) • Xᵀ + ((e : ℂ) * X.trace / (Fintype.card I : ℂ)) • 1

/-- Example 3.6, pp.12–13: identity mixed with complete depolarization. -/
def identityNoise (e : ℝ) (X : Mat I) : Mat I :=
  ((1 - e : ℝ) : ℂ) • X + ((e : ℂ) * X.trace / (Fintype.card I : ℂ)) • 1

/-- Example 3.6, p.13: transpose mixed with identity. -/
def transposeMix (e : ℝ) (X : Mat I) : Mat I :=
  ((1 - e : ℝ) : ℂ) • Xᵀ + (e : ℂ) • X

/-- The source's identity endpoint. -/
example (X : Mat I) : transposeMix 1 X = X := by simp [transposeMix]

/-- Example 3.6, p.12: the full six-term Schwarz defect expansion. -/
def transposeDefect (e c : ℝ) (X : Mat I) : Mat I :=
  ((c * (1 - e) : ℝ) : ℂ) • (Xᴴ * X)ᵀ +
  (((c * e : ℝ) : ℂ) * (Xᴴ * X).trace / (Fintype.card I : ℂ)) • 1 -
  (((1 - e) ^ 2 : ℝ) : ℂ) • ((Xᴴ)ᵀ * Xᵀ) -
  (((e * (1 - e) : ℝ) : ℂ) * X.trace / (Fintype.card I : ℂ)) • (Xᴴ)ᵀ -
  (((e * (1 - e) : ℝ) : ℂ) * (Xᴴ).trace / (Fintype.card I : ℂ)) • Xᵀ -
  (((e ^ 2 : ℝ) : ℂ) * (Complex.normSq X.trace : ℂ) / (Fintype.card I : ℂ) ^ 2) • 1

/-- Remark 4.8, pp.20–21: maps monotone for a specified f. -/
def MonotoneMap (A : Alg I) (f : ℝ → ℝ) (Phi : Mat I → Mat J) : Prop :=
  PositiveOnConcreteAlgebra A Phi ∧ ∀ X ∈ A, ∀ Y ∈ A, X.PosSemidef → Y.PosSemidef →
    div f (Phi X) (Phi Y) ≤ div f X Y

/-- Remark 6.2, p.28: limiting order-one entropy, before identifying it on states. -/
def renyiOne (X Y : Mat I) : EReal := limUnder (𝓝[<] (1 : ℝ)) (fun a => petzRenyi a X Y)

/-- Example 6.6, p.31: the stated diagonal state. -/
def exampleRho : Mat (Fin 3) := Matrix.diagonal ![(2 / 3 : ℂ), 1 / 3, 0]

/-- Example 6.6, p.31: the stated reference state. -/
def exampleSigma : Mat (Fin 3) := Matrix.diagonal ![(1 / 6 : ℂ), 1 / 3, 1 / 2]

/-- Example 6.6, p.31: canonical extension of the diagonal block-merging map. -/
def merge : MatrixMap (Fin 3) (Fin 3) where
  toFun X := Matrix.diagonal (fun i => if i = 0 then X 0 0 + X 1 1 else if i = 2 then X 2 2 else 0)
  map_add' X Y := by
    ext i j
    simp only [Matrix.diagonal_apply, Matrix.add_apply]
    split_ifs <;> simp_all <;> ring
  map_smul' c X := by
    ext i j
    simp only [Matrix.diagonal_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp_all <;> ring

/-- Section 6, p.31: the concrete diagonal observable algebra. -/
def diagonalAlgebra (I : Type) [Fintype I] [DecidableEq I] : Alg I where
  carrier := {X | ∀ i j, i ≠ j → X i j = 0}
  zero_mem' := by simp
  one_mem' := by intro i j h; simp [Matrix.one_apply, h]
  add_mem' := by intro X Y hX hY i j h; simp [hX i j h, hY i j h]
  mul_mem' := by
    intro X Y hX hY i j h
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hik : i = k
    · subst k; simp [hY i j h]
    · simp [hX i k hik]
  algebraMap_mem' := by intro c i j h; simp [Algebra.algebraMap_eq_smul_one, Matrix.one_apply, h]
  star_mem' := by intro X hX i j h; simpa using congrArg conj (hX j i (Ne.symm h))

/-- The merge map preserves the last basis projection exactly. -/
example : merge (Matrix.single 2 2 1) = (Matrix.single 2 2 1 : Mat (Fin 3)) := by
  change Matrix.diagonal (fun k : Fin 3 =>
    if k = 0 then
      (Matrix.single 2 2 (1 : ℂ) : Mat (Fin 3)) 0 0 +
        (Matrix.single 2 2 (1 : ℂ) : Mat (Fin 3)) 1 1
    else if k = 2 then (Matrix.single 2 2 (1 : ℂ) : Mat (Fin 3)) 2 2 else 0) =
      (Matrix.single 2 2 1 : Mat (Fin 3))
  ext i j
  by_cases hi : i = 2
  · subst i
    simp only [Matrix.diagonal_apply, Matrix.single_apply,
      show (2 : Fin 3) ≠ 0 from by decide, if_false, and_self,
      true_and, eq_self_iff_true, if_true]
  · by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply, Matrix.single_apply,
        show (2 : Fin 3) ≠ 0 from by decide,
        show (2 : Fin 3) ≠ 1 from by decide,
        hi, Ne.symm hi, eq_self_iff_true, and_self,
        if_false, if_true, zero_add, ite_self]
    · have hsingle : ¬ (2 = i ∧ 2 = j) := by
        intro h
        exact hij (h.1.symm.trans h.2)
      simp only [Matrix.diagonal_apply, Matrix.single_apply, hij, hsingle, if_false]

/-- Support inclusion includes the zero and reflexive edge cases. -/
example (X : Mat I) : Supports X X := by intro v hv; exact hv

/-- The support-zero convention applies to the zero matrix even at exponent zero. -/
example : supp (0 : Mat I) = 0 := by simp [supp, supportPower, cfc_zero]

/-- The source identity channel has no hidden trace normalization. -/
example : AlgebraTracePreserving (⊤ : Alg I) (LinearMap.id : MatrixMap I I) := by intro X hX; rfl

/-- The actual amplification of identity acts on every block entry. -/
example (n : ℕ) (X : Mat (Fin n × I)) : amp (fun Y : Mat I => Y) n X = X := rfl

/-- The combined representing kernel vanishes at x=1, pinning a=f(1)-f(0)-b. -/
example (t : PosReal) : representationKernel 1 t = 0 := by simp [representationKernel]

end QAlgorithms.Papers.Independent.Support50.P12


