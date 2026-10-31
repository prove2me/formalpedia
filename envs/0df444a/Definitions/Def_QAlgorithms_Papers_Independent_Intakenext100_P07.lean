-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P07
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P07
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T03:57:18.681258+00:00
-- url     : https://prove2.me/theorems/a994eab1-955e-41d1-b6d3-7b3a66ae1776
-- title:
--   Definitions for Quantum Information Processing with Finite Resources -- Mathematical Foundations
-- statement:
--   The objects the formalized statements of *Quantum Information Processing with Finite Resources -- Mathematical Foundations* (arXiv:1504.00233) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `paperMat`
--   - `paperBelow`: PDF p.22: Loewner order.
--   - `paperSupported`: PDF p.22: support inclusion is reverse kernel inclusion.
--   - `paperSubnormalized`: PDF pp.26-28: subnormalized PSD states, including zero.
--   - `paperPure`: PDF p.27: pure means rank one.
--   - `paperLogE`: PDF pp.19-20: binary logarithm with log(0)=-infinity.
--   - `expE`: PDF pp.19-20: binary exponential at finite and infinite arguments.
--   - `paperPower`: PDF p.32: support powers, with zero on the kernel even at exponent zero.
--   - `matrixLog`: PDF p.32: logarithm on the support, zero on the kernel.
--   - `paperSchatten`: PDF p.40: Schatten functional at positive real orders.
--   - `positiveNorm`: PDF p.42, (3.17): norm on all complex operators, with trace modulus.
--   - `paperDelta`: PDF p.43: generalized trace distance for all operators.
--   - `paperFidelity`: PDF p.44: squared algebraic fidelity, distinct from generalized fidelity.
--   - `paperGeneralizedFidelity`: PDF p.46: squared generalized fidelity.
--   - `purified`: PDF p.47: purified distance, using generalized fidelity once.
--   - `paperBall`: PDF p.98: full subnormalized ball, without a support restriction.
--   - `Radius`: PDF p.98: standing trace-dependent smoothing-radius restriction.
--   - `paperTraceMiddle`: PDF p.30: trace out B in (AB)C.
--   - `paperRegroup`: PDF p.30: actual regrouping (AB)C to A(BC).
--   - `paperMarginalBC`: PDF p.30: computed marginal BC.
--   - `paperHmin`: PDF p.92: extended supremum of domination exponents and reference states.
--   - `hmax`: PDF p.94: extended max-entropy from squared algebraic fidelity; Hmax(0)=-infinity.
--   - `paperSmoothMin`: PDF p.98: smooth min-entropy over the full subnormalized ball.
--   - `paperSmoothMax`: PDF p.98: smooth max-entropy is an infimum over the same ball.
--   - `conditionalVN`: PDF p.76: conditional von Neumann entropy in bits.
--   - `paperJointPower`: PDF pp.109-111: iid matrix product, regrouped as A^n B^n.
--   - `paperTensorPower`: PDF p.109: single-system matrix tensor power, with tensor unit at n=0.
--   - `minRate`: PDF p.110: regularization in EReal; the n=0 default is irrelevant to the limit.
--   - `maxRate`: PDF p.110: regularized smooth max-entropy.
--   - `paperLocalEmbedding`: PDF p.100: arbitrary rectangular local isometric embedding.
--   - `CPTNI`: PDF p.26: CPTNI, on every PSD input.
--   - `paperCPTP`: PDF p.26: CPTP, with trace preservation on every operator.
--   - `paperTensorAction`: PDF p.104: tensor action on the actual matrix-unit expansion.
--   - `paperMix`: PDF p.32: binary convex combination of matrices.
--   - `ClassicalLeft`: PDF p.32: classical on the first register.
--   - `ClassicalXY`: PDF p.100: classical X and Y in register order (AX)(BY).
--   - `classicalProcess`: PDF p.105: pushforward of the classical register; quantum registers retained.
--   - `paperPenalty`: PDF p.103: smoothing penalty, used only at 0<e<1.
--   - `maxD`: PDF p.106: max-divergence, including -infinity for a zero numerator.
--   - `smoothMaxD`: PDF p.106: relative smoothing over subnormalized states, also at large radii.
--   - `paperPositivePart`: PDF p.107: actual positive spectral part.
--   - `excessRadius`: PDF p.107: radius computed from the positive excess, not a free witness.
--   - `paperRelativeD`: PDF pp.61,65: normalized-trace Umegaki entropy with support-failure value +infinity.
--   - `paperVariance`: PDF pp.72,109: centered relative-entropy variance on the support domain.
--   - `MinPrimal`: PDF p.93: min-entropy primal feasibility.
--   - `MinDual`: PDF p.93: min-entropy dual feasibility.
--   - `SmoothPrimal`: PDF p.99: smooth min-entropy SDP, with overlap threshold 1-e^2.
--   - `conditionalBlocks`: PDF p.96: classical blocks in the BY register without renormalization.
--   - `guessObjective`: PDF p.97: guessing success probability.
--   - `paperMeasuredJoint`: PDF p.97: classical joint distribution produced by a measurement.
--   - `paperCqState`: PDF p.97: actual CQ assembly.
--   - `hartleyConditional`: PDF p.95: optimized support entropy with the extended zero value.
--   - `paperRenyiQ`: PDF pp.62,69: unnormalized sandwiched or Petz trace functional.
--   - `renyiFinite`: PDF pp.61,69: finite positive-order divergence, normalized by Tr r. The a=1 value is the Umegaki limit, and support/orthogonality guards preserve infinity.
--   - `paperRenyi`: PDF pp.61,69,78: endpoint orders are limits of the increasing finite-order family. For the sandwiched family infinity is the max-divergence.
--   - `conditionalDown`: PDF p.77, Definition 5.2: fixed-reference conditional Renyi entropy.
--   - `conditionalUp`: PDF p.77, Definition 5.2: optimize over actual normalized reference states.
--   - `paperConditional`: PDF p.81: select fixed-reference or optimized entropy without changing the divergence family.
--   - `DPIOrder`: PDF pp.81,86: orders for which this family has data processing, including limiting endpoints.
--   - `transformedOrder`: PDF pp.84-85: real order 2-1/a including a=infinity, with reciprocal endpoint limits.
--   - `paperIndependentProduct`: PDF p.84: regrouped independent product AB,CD to AC,BD.
--   - `spectralValues`: PDF p.36: distinct spectral values; zero is included when present.
--   - `paperSpectralProjector`: PDF p.36: actual spectral projection at l.
--   - `paperPinch`: PDF p.36: spectral pinching of an operator.
--   - `SpectralRep`: PDF p.70: spectral data is tied to the input matrix by reconstruction.
--   - `paperNsP`: PDF p.70: Nussbaum-Szkola probability law from the actual two spectral bases.
--   - `paperNsQ`: PDF p.70: Nussbaum-Szkola reference law.
--   - `paperProbability`: PDF p.12: a finite normalized classical probability distribution.
--   - `paperSeparable`: PDF p.76: finite separable states, with actual normalized product components.
--   - `basisLaw`: PDF p.116: Born law for the orthonormal basis in the columns of U.
--   - `paperBasisMeasurement`: PDF p.117: local basis measurement on A, retaining the side information B.
--   - `basisOverlap`: PDF p.116: maximum SQUARED overlap of the two actual bases.
--   - `paperTypeI`: PDF p.114: type-I error when T accepts rho.
--   - `paperTypeII`: PDF p.114: type-II error when T accepts rho.
--   - `alphaStar`: PDF p.114, (7.6). Printed: minimize alpha(T;sigma) subject to beta(T;rho). Changed: minimize alpha(T;rho) subject to beta(T;sigma). Why: (7.1)-(7.2), the sentence before (7.6), and the Stein threshold all fix these roles.
--   - `paperBetaStar`: PDF p.115: minimum type-II error at prescribed type-I tolerance.
--   - `paperSymmetricError`: PDF p.114: optimal average error with equal priors.
--   - `paperRenyiReal`: PDF p.72: Renyi divergences as real-valued functions only on supported pairs.
--   - `petzExtendedQ`: PDF p.69: extended Petz Q on support failure above one.
--   - `paperSourceCode`: PDF p.12: fixed-cardinality deterministic source code.
--   - `paperCodeError`: PDF p.12: actual probability of decoding failure.
--   - `paperClassicalRenyi`: PDF p.13: classical Renyi entropy at finite positive order other than one.
--   - `paperShannon`: PDF p.13: Shannon entropy, with zero contributions from zero probabilities.
--   - `variation`: PDF p.14: introductory variation distance (different from purified distance).
--   - `introSmoothMax`: PDF p.14: smoothing only over normalized classical probability laws.
--   - `iidLaw`: PDF p.13: iid classical product law.
--   - `codeCardinality`: PDF p.13: integer memory cardinality rounded upward from 2^(nR).
--   - `Resolution`: PDF p.36: finite orthogonal resolution of identity.
--   - `resolutionPinch`: PDF p.36: pinching from a finite resolution.
--   - `UnitaryInvariantNorm`: PDF p.40: all unitarily invariant complex norms, rather than a particular matrix norm.
--   - `hatState`: PDF p.46: normalized hat-state with a single vacuum flag.
--   - `paperChoi`: PDF p.37: Choi matrix from the UNNORMALIZED entangled vector.
--   - `inverseChoi`: PDF p.37, (2.69): inverse in register order A-prime,B; the input transpose is implicit in the pairing.
--   - `paperEntangled`: PDF p.93: normalized maximally entangled density matrix on two copies of the same basis.
--   - `preparedEntangled`: PDF p.94, (6.11): a B-prime-to-A channel applied to the second half of psi_BBprime, then regrouped as AB.
--   - `paperAdjointAction`: PDF pp.91-92: the actual Hilbert-Schmidt adjoint, computed from matrix units.
--   - `sdpPrimal`: PDF p.92: extended primal infimum; infeasibility is +infinity.
--   - `sdpDual`: PDF p.92: extended dual supremum; infeasibility is -infinity.
--   - `productState`: PDF p.109: heterogeneous product states, retaining every factor.
--   - `paperQuadratic`: PDF pp.31,42: the actual quadratic form, with conjugation in the first argument.
--   - `measureOutput`: PDF pp.35,68: actual classical probability matrix of a POVM output.
--   - `optimalCardinality`: PDF p.14: minimum code alphabet cardinality. On probability sources the feasible set is nonempty (lossless coding).
--   - `paperDivergenceFamily`: PDF pp.52-58: a divergence is one family across all finite systems, so classical outputs, tensor powers, direct sums and rectangular channels have the same value rule.
--   - `paperClassicalAgreement`: PDF pp.56,58,61: agreement with the classical divergence on diagonal positive pairs.
--   - `AdditiveDivergence`: PDF p.52, (V): tensor additivity, on arbitrary nonzero positive numerators.
--   - `paperDataProcessing`: PDF p.53, (VIII): every CPTP map, including maps between different dimensions.
--   - `paperMaxFamily`: PDF pp.60-61: the concrete max-divergence family.
--   - `measuredRenyi`: PDF p.66, (4.73): optimization over actual finite-outcome POVMs, in EReal.
--   - `MeasuredRepresentation`: PDF p.66, (4.73): the measured representation for every positive input pair, including attainment of each finite-copy maximum. This predicate does not assume DPI.
--   - `AxiomDomain`: PDF p.52: finite real domain of the six axioms.
--   - `RealDivergenceFamily`: PDF p.52: real-valued divergence across every finite system, before adjoining infinities.
--   - `paperDirectSum`: PDF p.52: direct sum in the disjoint-union basis.
--   - `paperSixAxioms`: PDF p.52, (I)-(VI): the actual unbounded positive cone and the full trace-weighted mean. The accepted Dependency50.P35.SixAxioms restricts the mean to total traces at most one; this book states the mean for arbitrary positive inputs, so it has a distinct local predicate.
--   - `MeanCurvature`: PDF pp.53,57: joint convexity or concavity of g(D) on normalized pairs.
--   - `RealDataProcessing`: PDF pp.53,57: data processing on the finite domain where the axiomatic D is real.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, https://arxiv.org/abs/1504.00233v5

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_Ensemble

/-! Tomamichel, arXiv:1504.00233v5. PDF pages; binary logarithms.
New definitions are local to this paper. Compilation and independent moderation pending. -/
noncomputable section
open Filter
open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology
namespace QAlgorithms.Papers.Independent.Intakenext100.P07
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev paperMat (I : Type*) := Matrix I I ℂ

variable {I J A B C D X Y Z : Type*}
variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
variable [Fintype Z] [DecidableEq Z]

/-- PDF p.22: Loewner order. -/
def paperBelow (M N : paperMat I) : Prop := (N-M).PosSemidef

/-- PDF p.22: support inclusion is reverse kernel inclusion. -/
def paperSupported (M N : paperMat I) : Prop := LinearMap.ker N.mulVecLin ≤ LinearMap.ker M.mulVecLin

/-- PDF pp.26-28: subnormalized PSD states, including zero. -/
def paperSubnormalized (r : paperMat I) : Prop := r.PosSemidef ∧ r.trace.re ≤ 1

/-- PDF p.27: pure means rank one. -/
def paperPure (r : paperMat I) : Prop := r.PosSemidef ∧ r.rank = 1

/-- PDF pp.19-20: binary logarithm with log(0)=-infinity. -/
def paperLogE (x : ℝ) : EReal := if x = 0 then ⊥ else (Real.logb 2 x : EReal)

/-- PDF pp.19-20: binary exponential at finite and infinite arguments. -/
def expE (x : EReal) : ENNReal :=
  if x = ⊤ then ⊤ else if x = ⊥ then 0 else ENNReal.ofReal ((2:ℝ)^x.toReal)

/-- PDF p.32: support powers, with zero on the kernel even at exponent zero. -/
def paperPower (M : paperMat I) (p : ℝ) : paperMat I := cfc (fun x : ℝ => if x = 0 then 0 else x^p) M

/-- PDF p.32: logarithm on the support, zero on the kernel. -/
def matrixLog (M : paperMat I) : paperMat I := cfc (fun x : ℝ => Real.logb 2 x) M

/-- PDF p.40: Schatten functional at positive real orders. -/
def paperSchatten (M : paperMat I) (p : ℝ) : ℝ :=
  (paperPower (cfc Real.sqrt (Mᴴ*M)) p).trace.re ^ (1/p)

/-- PDF p.42, (3.17): norm on all complex operators, with trace modulus. -/
def positiveNorm (M : paperMat I) : ℝ :=
  sSup {r : ℝ | ∃ E : paperMat I, IsEffect E ∧ r = ‖(M*E).trace‖}

/-- PDF p.43: generalized trace distance for all operators. -/
def paperDelta (M N : paperMat I) : ℝ := positiveNorm (M-N)

/-- PDF p.44: squared algebraic fidelity, distinct from generalized fidelity. -/
def paperFidelity (r s : paperMat I) : ℝ := rootFidelity r s ^ 2

/-- PDF p.46: squared generalized fidelity. -/
def paperGeneralizedFidelity (r s : paperMat I) : ℝ :=
  (rootFidelity r s + Real.sqrt ((1-r.trace.re)*(1-s.trace.re)))^2

/-- PDF p.47: purified distance, using generalized fidelity once. -/
def purified (r s : paperMat I) : ℝ := Real.sqrt (1-paperGeneralizedFidelity r s)

/-- PDF p.98: full subnormalized ball, without a support restriction. -/
def paperBall (r : paperMat I) (e : ℝ) : Set (paperMat I) := {s | paperSubnormalized s ∧ purified s r ≤ e}

/-- PDF p.98: standing trace-dependent smoothing-radius restriction. -/
def Radius (r : paperMat I) (e : ℝ) : Prop := 0 ≤ e ∧ e < Real.sqrt r.trace.re

/-- PDF p.30: trace out B in (AB)C. -/
def paperTraceMiddle (r : paperMat ((A × B) × C)) : paperMat (A × C) :=
  fun x y => ∑ b, r ((x.1,b),x.2) ((y.1,b),y.2)

/-- PDF p.30: actual regrouping (AB)C to A(BC). -/
def paperRegroup (r : paperMat ((A × B) × C)) : paperMat (A × (B × C)) :=
  fun x y => r ((x.1,x.2.1),x.2.2) ((y.1,y.2.1),y.2.2)

/-- PDF p.30: computed marginal BC. -/
def paperMarginalBC (r : paperMat ((A × B) × C)) : paperMat (B × C) := traceLeft (paperRegroup r)

/-- PDF p.92: extended supremum of domination exponents and reference states. -/
def paperHmin (r : paperMat (A × B)) : EReal :=
  sSup {h : EReal | ∃ l : ℝ, h = (l:EReal) ∧ ∃ s : paperMat B, paperSubnormalized s ∧
    paperBelow r ((((2:ℝ)^(-l) : ℝ) : ℂ) • Matrix.kronecker (1:paperMat A) s)}

/-- PDF p.94: extended max-entropy from squared algebraic fidelity; Hmax(0)=-infinity. -/
def hmax (r : paperMat (A × B)) : EReal :=
  sSup {h : EReal | ∃ s : paperMat B, paperSubnormalized s ∧ h = paperLogE (paperFidelity r (Matrix.kronecker (1:paperMat A) s))}

/-- PDF p.98: smooth min-entropy over the full subnormalized ball. -/
def paperSmoothMin (r : paperMat (A × B)) (e : ℝ) : EReal :=
  sSup {h : EReal | ∃ s ∈ paperBall r e, h = paperHmin s}

/-- PDF p.98: smooth max-entropy is an infimum over the same ball. -/
def paperSmoothMax (r : paperMat (A × B)) (e : ℝ) : EReal :=
  sInf {h : EReal | ∃ s ∈ paperBall r e, h = hmax s}

/-- PDF p.76: conditional von Neumann entropy in bits. -/
def conditionalVN (r : paperMat (A × B)) : ℝ := vnEntropy r-vnEntropy (traceLeft r)

/-- PDF pp.109-111: iid matrix product, regrouped as A^n B^n. -/
def paperJointPower (r : paperMat (A × B)) (n : ℕ) : paperMat ((Fin n → A) × (Fin n → B)) :=
  fun x y => ∏ i, r (x.1 i,x.2 i) (y.1 i,y.2 i)

/-- PDF p.109: single-system matrix tensor power, with tensor unit at n=0. -/
def paperTensorPower (r : paperMat I) (n : ℕ) : paperMat (Fin n → I) := fun x y => ∏ i, r (x i) (y i)

/-- PDF p.110: regularization in EReal; the n=0 default is irrelevant to the limit. -/
def minRate (r : paperMat (A × B)) (e : ℝ) (n : ℕ) : EReal :=
  ((1/(n:ℝ) : ℝ) : EReal)*paperSmoothMin (paperJointPower r n) e

/-- PDF p.110: regularized smooth max-entropy. -/
def maxRate (r : paperMat (A × B)) (e : ℝ) (n : ℕ) : EReal :=
  ((1/(n:ℝ) : ℝ) : EReal)*paperSmoothMax (paperJointPower r n) e

/-- PDF p.100: arbitrary rectangular local isometric embedding. -/
def paperLocalEmbedding (U : Matrix C A ℂ) (V : Matrix D B ℂ) (r : paperMat (A × B)) : paperMat (C × D) :=
  Matrix.kronecker U V*r*(Matrix.kronecker U V)ᴴ

/-- PDF p.26: CPTNI, on every PSD input. -/
def CPTNI (E : paperMat I →ₗ[ℂ] paperMat J) : Prop :=
  QAlgorithms.Entanglement.IsCompletelyPositive E ∧ ∀ r, r.PosSemidef → (E r).trace.re ≤ r.trace.re

/-- PDF p.26: CPTP, with trace preservation on every operator. -/
def paperCPTP (E : paperMat I →ₗ[ℂ] paperMat J) : Prop :=
  QAlgorithms.Entanglement.IsCompletelyPositive E ∧ ∀ M, (E M).trace = M.trace

/-- PDF p.104: tensor action on the actual matrix-unit expansion. -/
def paperTensorAction (E : paperMat A →ₗ[ℂ] paperMat C) (F : paperMat B →ₗ[ℂ] paperMat D) (r : paperMat (A × B)) : paperMat (C × D) :=
  fun x y => ∑ a, ∑ a', ∑ b, ∑ b', r (a,b) (a',b') * E (Matrix.single a a' 1) x.1 y.1 *
    F (Matrix.single b b' 1) x.2 y.2

/-- PDF p.32: binary convex combination of matrices. -/
def paperMix (t : ℝ) (M N : paperMat I) : paperMat I := (t:ℂ) • M + ((1-t:ℝ):ℂ) • N

/-- PDF p.32: classical on the first register. -/
def ClassicalLeft (r : paperMat (X × A)) : Prop := ∀ x y a b, x ≠ y → r (x,a) (y,b) = 0

/-- PDF p.100: classical X and Y in register order (AX)(BY). -/
def ClassicalXY (r : paperMat ((A × X) × (B × Y))) : Prop :=
  ∀ a x b y a' x' b' y', x ≠ x' ∨ y ≠ y' → r ((a,x),(b,y)) ((a',x'),(b',y')) = 0

/-- PDF p.105: pushforward of the classical register; quantum registers retained. -/
def classicalProcess (f : X → Z) (r : paperMat ((X × A) × B)) : paperMat ((Z × A) × B) :=
  fun z w => if z.1.1 = w.1.1 then ∑ x, if f x = z.1.1 then
    r ((x,z.1.2),z.2) ((x,w.1.2),w.2) else 0 else 0

/-- PDF p.103: smoothing penalty, used only at 0<e<1. -/
def paperPenalty (e : ℝ) : ℝ := -Real.logb 2 (1-Real.sqrt (1-e^2))

/-- PDF p.106: max-divergence, including -infinity for a zero numerator. -/
def maxD (r s : paperMat I) : EReal :=
  sInf {d : EReal | ∃ l : ℝ, d = (l:EReal) ∧ paperBelow r (((2:ℝ)^l : ℂ) • s)}

/-- PDF p.106: relative smoothing over subnormalized states, also at large radii. -/
def smoothMaxD (r s : paperMat I) (e : ℝ) : EReal :=
  sInf {d : EReal | ∃ t ∈ paperBall r e, d = maxD t s}

/-- PDF p.107: actual positive spectral part. -/
def paperPositivePart (M : paperMat I) : paperMat I := cfc (fun x : ℝ => max x 0) M

/-- PDF p.107: radius computed from the positive excess, not a free witness. -/
def excessRadius (r s : paperMat I) (l : ℝ) : ℝ :=
  let t := (paperPositivePart (r-(((2:ℝ)^l : ℂ) • s))).trace.re
  Real.sqrt (2*t-t^2)

/-- PDF pp.61,65: normalized-trace Umegaki entropy with support-failure value +infinity. -/
def paperRelativeD (r s : paperMat I) : EReal := if paperSupported r s then
  (((r*(matrixLog r-matrixLog s)).trace.re/r.trace.re : ℝ):EReal) else ⊤

/-- PDF pp.72,109: centered relative-entropy variance on the support domain. -/
def paperVariance (r s : paperMat I) : ℝ :=
  (r*(matrixLog r-matrixLog s-((paperRelativeD r s).toReal:ℂ) • (1:paperMat I))^2).trace.re

/-- PDF p.93: min-entropy primal feasibility. -/
def MinPrimal (r : paperMat (A × B)) (s : paperMat B) : Prop := s.PosSemidef ∧ paperBelow r (Matrix.kronecker (1:paperMat A) s)

/-- PDF p.93: min-entropy dual feasibility. -/
def MinDual (W : paperMat (A × B)) : Prop := W.PosSemidef ∧ paperBelow (traceLeft W) 1

/-- PDF p.99: smooth min-entropy SDP, with overlap threshold 1-e^2. -/
def SmoothPrimal (r : paperMat ((A × B) × C)) (e : ℝ) (t : paperMat ((A × B) × C)) (s : paperMat B) : Prop :=
  paperSubnormalized t ∧ s.PosSemidef ∧ 1-e^2 ≤ (t*r).trace.re ∧
    paperBelow (traceRight t) (Matrix.kronecker (1:paperMat A) s)

/-- PDF p.96: classical blocks in the BY register without renormalization. -/
def conditionalBlocks (r : Y → paperMat (A × B)) : paperMat (A × (B × Y)) :=
  fun x z => if x.2.2 = z.2.2 then r x.2.2 (x.1,x.2.1) (z.1,z.2.1) else 0

/-- PDF p.97: guessing success probability. -/
def guessObjective (r : X → paperMat B) (M : X → paperMat B) : ℝ := ∑ x, (M x*r x).trace.re

/-- PDF p.97: classical joint distribution produced by a measurement. -/
def paperMeasuredJoint (r : X → paperMat B) (M : X → paperMat B) : paperMat (X × X) :=
  Matrix.diagonal (fun xy => ((M xy.2*r xy.1).trace.re:ℂ))

/-- PDF p.97: actual CQ assembly. -/
def paperCqState (r : X → paperMat B) : paperMat (X × B) := fun x y => if x.1 = y.1 then r x.1 x.2 y.2 else 0

/-- PDF p.95: optimized support entropy with the extended zero value. -/
def hartleyConditional (r : paperMat (A × B)) : EReal :=
  sSup {h : EReal | ∃ s : paperMat B, paperSubnormalized s ∧
    h = paperLogE ((paperPower r 0*Matrix.kronecker (1:paperMat A) s).trace.re)}

example (M : paperMat I) : paperMix 0 M M = M := by simp [paperMix]

example : paperLogE 0 = ⊥ := by simp [paperLogE]

example : paperSubnormalized (0:paperMat I) := ⟨Matrix.PosSemidef.zero, by simp⟩

example (r : paperMat I) (x y : Fin 0 → I) : paperTensorPower r 0 x y = 1 := by simp [paperTensorPower]

example (r : paperMat I) (e : ℝ) (s : paperMat I) : s ∈ paperBall r e ↔ paperSubnormalized s ∧ purified s r ≤ e := Iff.rfl

example (r : paperMat ((A × B) × C)) (a a' : A) (b b' : B) (c c' : C) :
    paperRegroup r (a,(b,c)) (a',(b',c')) = r ((a,b),c) ((a',b'),c') := rfl

example (r : Y → paperMat (A × B)) (a a' : A) (b b' : B) (y : Y) :
    conditionalBlocks r (a,(b,y)) (a',(b',y)) = r y (a,b) (a',b') := by simp [conditionalBlocks]

/-- PDF pp.62,69: unnormalized sandwiched or Petz trace functional. -/
def paperRenyiQ (sand : Bool) (r s : paperMat I) (a : ℝ) : ℝ :=
  if sand then (paperPower (paperPower s ((1-a)/(2*a))*r*paperPower s ((1-a)/(2*a))) a).trace.re
  else (paperPower r a*paperPower s (1-a)).trace.re

/-- PDF pp.61,69: finite positive-order divergence, normalized by Tr r.
The a=1 value is the Umegaki limit, and support/orthogonality guards preserve infinity. -/
def renyiFinite (sand : Bool) (r s : paperMat I) (a : ℝ) : EReal :=
  if a = 1 then paperRelativeD r s
  else if (a < 1 ∧ 0 < paperRenyiQ sand r s a) ∨ paperSupported r s then
    ((1/(a-1):ℝ):EReal)*paperLogE (paperRenyiQ sand r s a/r.trace.re)
  else ⊤

/-- PDF pp.61,69,78: endpoint orders are limits of the increasing finite-order family.
For the sandwiched family infinity is the max-divergence. -/
def paperRenyi (sand : Bool) (r s : paperMat I) (a : ENNReal) : EReal :=
  if a = 0 then sInf {d : EReal | ∃ t : ℝ, 0 < t ∧ d = renyiFinite sand r s t}
  else if a = ⊤ then
    if sand then maxD r s else sSup {d : EReal | ∃ t : ℝ, 0 < t ∧ d = renyiFinite sand r s t}
  else renyiFinite sand r s a.toReal

/-- PDF p.77, Definition 5.2: fixed-reference conditional Renyi entropy. -/
def conditionalDown (sand : Bool) (a : ENNReal) (r : paperMat (A × B)) : EReal :=
  -paperRenyi sand r (Matrix.kronecker (1:paperMat A) (traceLeft r)) a

/-- PDF p.77, Definition 5.2: optimize over actual normalized reference states. -/
def conditionalUp (sand : Bool) (a : ENNReal) (r : paperMat (A × B)) : EReal :=
  sSup {h : EReal | ∃ s : paperMat B, IsDensityMatrix s ∧ h = -paperRenyi sand r (Matrix.kronecker (1:paperMat A) s) a}

/-- PDF p.81: select fixed-reference or optimized entropy without changing the divergence family. -/
def paperConditional (sand up : Bool) (a : ENNReal) (r : paperMat (A × B)) : EReal :=
  if up then conditionalUp sand a r else conditionalDown sand a r

/-- PDF pp.81,86: orders for which this family has data processing, including limiting endpoints. -/
def DPIOrder (sand : Bool) (a : ENNReal) : Prop :=
  if sand then (1/2:ENNReal) ≤ a else a ≤ 2

/-- PDF pp.84-85: real order 2-1/a including a=infinity, with reciprocal endpoint limits. -/
def transformedOrder (a : ENNReal) : ENNReal :=
  if a = ⊤ then 2 else ENNReal.ofReal (2-1/a.toReal)

/-- PDF p.84: regrouped independent product AB,CD to AC,BD. -/
def paperIndependentProduct (r : paperMat (A × B)) (s : paperMat (C × D)) : paperMat ((A × C) × (B × D)) :=
  fun x y => r (x.1.1,x.2.1) (y.1.1,y.2.1)*s (x.1.2,x.2.2) (y.1.2,y.2.2)

/-- PDF p.36: distinct spectral values; zero is included when present. -/
def spectralValues (H : paperMat I) : Finset ℝ := Finset.univ.image (ascEigenvalues H)

/-- PDF p.36: actual spectral projection at l. -/
def paperSpectralProjector (H : paperMat I) (l : ℝ) : paperMat I :=
  cfc (fun x : ℝ => if x = l then (1:ℝ) else 0) H

/-- PDF p.36: spectral pinching of an operator. -/
def paperPinch (H L : paperMat I) : paperMat I :=
  ∑ l ∈ spectralValues H, paperSpectralProjector H l*L*paperSpectralProjector H l

/-- PDF p.70: spectral data is tied to the input matrix by reconstruction. -/
def SpectralRep (r : paperMat I) (v : I → ℝ) (U : paperMat I) : Prop :=
  (∀ i, 0 ≤ v i) ∧ Uᴴ*U = 1 ∧ U*Uᴴ = 1 ∧ r = U*Matrix.diagonal (fun i => (v i:ℂ))*Uᴴ

/-- PDF p.70: Nussbaum-Szkola probability law from the actual two spectral bases. -/
def paperNsP (v : I → ℝ) (U V : paperMat I) : I × I → ℝ :=
  fun xy => v xy.1*‖(Uᴴ*V) xy.1 xy.2‖^2

/-- PDF p.70: Nussbaum-Szkola reference law. -/
def paperNsQ (v : I → ℝ) (U V : paperMat I) : I × I → ℝ :=
  fun xy => v xy.2*‖(Uᴴ*V) xy.1 xy.2‖^2

/-- PDF p.12: a finite normalized classical probability distribution. -/
def paperProbability (p : X → ℝ) : Prop := (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1

/-- PDF p.76: finite separable states, with actual normalized product components. -/
def paperSeparable (r : paperMat (A × B)) : Prop :=
  ∃ n : ℕ, ∃ w : Fin n → ℝ, ∃ s : Fin n → paperMat A, ∃ t : Fin n → paperMat B,
    paperProbability w ∧ (∀ i, IsDensityMatrix (s i) ∧ IsDensityMatrix (t i)) ∧
      r = ∑ i, (w i:ℂ) • Matrix.kronecker (s i) (t i)

/-- PDF p.116: Born law for the orthonormal basis in the columns of U. -/
def basisLaw (U r : paperMat I) : paperMat I := Matrix.diagonal (fun i => (Uᴴ*r*U) i i)

/-- PDF p.117: local basis measurement on A, retaining the side information B. -/
def paperBasisMeasurement (U : paperMat A) (r : paperMat (A × B)) : paperMat (A × B) :=
  let W := Matrix.kronecker U (1:paperMat B)
  fun x y => if x.1 = y.1 then (Wᴴ*r*W) x y else 0

/-- PDF p.116: maximum SQUARED overlap of the two actual bases. -/
def basisOverlap (U V : paperMat I) : ℝ := sSup {c : ℝ | ∃ i j, c = ‖(Uᴴ*V) i j‖^2}

/-- PDF p.114: type-I error when T accepts rho. -/
def paperTypeI (r T : paperMat I) : ℝ := ((1-T)*r).trace.re

/-- PDF p.114: type-II error when T accepts rho. -/
def paperTypeII (s T : paperMat I) : ℝ := (T*s).trace.re

/-- PDF p.114, (7.6). Printed: minimize alpha(T;sigma) subject to beta(T;rho).
Changed: minimize alpha(T;rho) subject to beta(T;sigma).
Why: (7.1)-(7.2), the sentence before (7.6), and the Stein threshold all fix these roles. -/
def alphaStar (r s : paperMat I) (e : ℝ) : ℝ :=
  sInf {v : ℝ | ∃ T : paperMat I, IsEffect T ∧ paperTypeII s T ≤ e ∧ v = paperTypeI r T}

/-- PDF p.115: minimum type-II error at prescribed type-I tolerance. -/
def paperBetaStar (r s : paperMat I) (e : ℝ) : ℝ :=
  sInf {v : ℝ | ∃ T : paperMat I, IsEffect T ∧ paperTypeI r T ≤ e ∧ v = paperTypeII s T}

/-- PDF p.114: optimal average error with equal priors. -/
def paperSymmetricError (r s : paperMat I) : ℝ :=
  sInf {v : ℝ | ∃ T : paperMat I, IsEffect T ∧ v = (paperTypeI r T+paperTypeII s T)/2}

/-- PDF p.72: Renyi divergences as real-valued functions only on supported pairs. -/
def paperRenyiReal (sand : Bool) (r s : paperMat I) (a : ℝ) : ℝ := (renyiFinite sand r s a).toReal

example (r : paperMat I) (a : ENNReal) :
    conditionalDown true a (fun x y : I × Unit => r x.1 y.1) = 
      -paperRenyi true (fun x y : I × Unit => r x.1 y.1)
        (Matrix.kronecker (1:paperMat I) (traceLeft (fun x y : I × Unit => r x.1 y.1))) a := rfl

example (r s : paperMat I) : renyiFinite false r s 1 = paperRelativeD r s := by simp [renyiFinite]

example (r : paperMat I) (v : I → ℝ) (U : paperMat I) : paperNsP v U U = (fun xy => v xy.1*‖(Uᴴ*U) xy.1 xy.2‖^2) := rfl

example (r : paperMat I) : paperTypeI r 1 = 0 := by simp [paperTypeI]

example (s : paperMat I) : paperTypeII s 0 = 0 := by simp [paperTypeII]

/-- PDF p.69: extended Petz Q on support failure above one. -/
def petzExtendedQ (r s : paperMat I) (a : ℝ) : EReal :=
  if 1 < a ∧ ¬paperSupported r s then ⊤ else (paperRenyiQ false r s a:EReal)

/-- PDF p.12: fixed-cardinality deterministic source code. -/
structure paperSourceCode (X : Type*) (m : ℕ) where
  encode : X → Fin m
  decode : Fin m → X

/-- PDF p.12: actual probability of decoding failure. -/
def paperCodeError (p : X → ℝ) {m : ℕ} (c : paperSourceCode X m) : ℝ :=
  ∑ x, if c.decode (c.encode x) = x then 0 else p x

/-- PDF p.13: classical Renyi entropy at finite positive order other than one. -/
def paperClassicalRenyi (p : X → ℝ) (a : ℝ) : ℝ := Real.logb 2 (∑ x, p x^a)/(1-a)

/-- PDF p.13: Shannon entropy, with zero contributions from zero probabilities. -/
def paperShannon (p : X → ℝ) : ℝ := -∑ x, p x*Real.logb 2 (p x)

/-- PDF p.14: introductory variation distance (different from purified distance). -/
def variation (p q : X → ℝ) : ℝ := (∑ x, |p x-q x|)/2

/-- PDF p.14: smoothing only over normalized classical probability laws. -/
def introSmoothMax (p : X → ℝ) (e : ℝ) : ℝ :=
  sInf {h : ℝ | ∃ q : X → ℝ, paperProbability q ∧ variation p q ≤ e ∧ h = paperClassicalRenyi q (1/2)}

/-- PDF p.13: iid classical product law. -/
def iidLaw (p : X → ℝ) (n : ℕ) : (Fin n → X) → ℝ := fun x => ∏ i, p (x i)

/-- PDF p.13: integer memory cardinality rounded upward from 2^(nR). -/
def codeCardinality (n : ℕ) (R : ℝ) : ℕ := Nat.ceil ((2:ℝ)^((n:ℝ)*R))

/-- PDF p.36: finite orthogonal resolution of identity. -/
def Resolution {m : ℕ} (P : Fin m → paperMat I) : Prop :=
  (∀ i, (P i)ᴴ = P i ∧ P i*P i = P i) ∧ (∀ i j, i ≠ j → P i*P j = 0) ∧ ∑ i, P i = 1

/-- PDF p.36: pinching from a finite resolution. -/
def resolutionPinch {m : ℕ} (P : Fin m → paperMat I) (M : paperMat I) : paperMat I := ∑ i, P i*M*P i

/-- PDF p.40: all unitarily invariant complex norms, rather than a particular matrix norm. -/
def UnitaryInvariantNorm (v : paperMat I → ℝ) : Prop :=
  (∀ M, 0 ≤ v M ∧ (v M = 0 ↔ M = 0)) ∧
  (∀ (z : ℂ) M, v (z • M) = ‖z‖*v M) ∧ (∀ M N, v (M+N) ≤ v M+v N) ∧
  ∀ U V M : paperMat I, Uᴴ*U = 1 → Vᴴ*V = 1 → v (U*M*V) = v M

/-- PDF p.46: normalized hat-state with a single vacuum flag. -/
def hatState (r : paperMat I) : paperMat (Sum I Unit) :=
  fun x y => match x,y with
    | .inl i,.inl j => r i j
    | .inr _,.inr _ => (1-r.trace.re:ℂ)
    | _,_ => 0

/-- PDF p.37: Choi matrix from the UNNORMALIZED entangled vector. -/
def paperChoi (E : paperMat I →ₗ[ℂ] paperMat J) : paperMat (I × J) :=
  fun x y => E (Matrix.single x.1 y.1 1) x.2 y.2

/-- PDF p.37, (2.69): inverse in register order A-prime,B; the input transpose is implicit in the pairing. -/
def inverseChoi (G : paperMat (I × J)) (r : paperMat I) : paperMat J :=
  fun b b' => ∑ i, ∑ j, r i j*G (i,b) (j,b')

/-- PDF p.93: normalized maximally entangled density matrix on two copies of the same basis. -/
def paperEntangled (I : Type*) [Fintype I] [DecidableEq I] : paperMat (I × I) :=
  fun x y => if x.1 = x.2 ∧ y.1 = y.2 then (Fintype.card I:ℂ)⁻¹ else 0

/-- PDF p.94, (6.11): a B-prime-to-A channel applied to the second half of psi_BBprime, then regrouped as AB. -/
def preparedEntangled (E : paperMat B →ₗ[ℂ] paperMat A) : paperMat (A × B) :=
  fun x y => idTensorSuperop E (paperEntangled B) (x.2,x.1) (y.2,y.1)

/-- PDF pp.91-92: the actual Hilbert-Schmidt adjoint, computed from matrix units. -/
def paperAdjointAction (E : paperMat I →ₗ[ℂ] paperMat J) (Y : paperMat J) : paperMat I :=
  fun i j => ∑ a, ∑ b, conj (E (Matrix.single i j 1) a b)*Y a b

/-- PDF p.92: extended primal infimum; infeasibility is +infinity. -/
def sdpPrimal (E : paperMat I →ₗ[ℂ] paperMat J) (K : paperMat I) (L : paperMat J) : EReal :=
  sInf {v : EReal | ∃ X : paperMat I, X.PosSemidef ∧ paperBelow L (E X) ∧ v = ((K*X).trace.re:EReal)}

/-- PDF p.92: extended dual supremum; infeasibility is -infinity. -/
def sdpDual (E : paperMat I →ₗ[ℂ] paperMat J) (K : paperMat I) (L : paperMat J) : EReal :=
  sSup {v : EReal | ∃ Y : paperMat J, Y.PosSemidef ∧ paperBelow (paperAdjointAction E Y) K ∧ v = ((L*Y).trace.re:EReal)}

/-- PDF p.109: heterogeneous product states, retaining every factor. -/
def productState {n : ℕ} (r : Fin n → paperMat I) : paperMat (Fin n → I) :=
  fun x y => ∏ i, r i (x i) (y i)

/-- PDF pp.31,42: the actual quadratic form, with conjugation in the first argument. -/
def paperQuadratic (r : paperMat I) (v : I → ℂ) : ℂ := ∑ i, ∑ j, conj (v i)*r i j*v j

example (r : paperMat I) (i j : I) : hatState r (.inl i) (.inl j) = r i j := rfl

example (E : paperMat I →ₗ[ℂ] paperMat J) (i j : I) (b c : J) :
    paperChoi E (i,b) (j,c) = E (Matrix.single i j 1) b c := rfl

example (p : X → ℝ) (x : Fin 0 → X) : iidLaw p 0 x = 1 := by simp [iidLaw]

example (p : X → ℝ) : variation p p = 0 := by simp [variation]

example (K : paperMat I) (L : paperMat J) :
    paperAdjointAction (0 : paperMat I →ₗ[ℂ] paperMat J) L = 0 := by ext i j; simp [paperAdjointAction]

/-- PDF pp.35,68: actual classical probability matrix of a POVM output. -/
def measureOutput {m : ℕ} (M : Fin m → paperMat I) (r : paperMat I) : paperMat (Fin m) :=
  Matrix.diagonal (fun x => (M x*r).trace)

/-- PDF p.14: minimum code alphabet cardinality. On probability sources the feasible set is nonempty (lossless coding). -/
def optimalCardinality (p : X → ℝ) (e : ℝ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ ∃ c : paperSourceCode X m, paperCodeError p c ≤ e}

/-- PDF pp.52-58: a divergence is one family across all finite systems,
so classical outputs, tensor powers, direct sums and rectangular channels have the same value rule. -/
structure paperDivergenceFamily where
  value : (I : Type) → [Fintype I] → [DecidableEq I] → paperMat I → paperMat I → EReal

/-- PDF pp.56,58,61: agreement with the classical divergence on diagonal positive pairs. -/
def paperClassicalAgreement (D : paperDivergenceFamily) (a : ENNReal) : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I], ∀ p q : I → ℝ,
    (∀ i, 0 ≤ p i) → (∀ i, 0 ≤ q i) → p ≠ 0 →
    D.value I (Matrix.diagonal (fun i => (p i:ℂ))) (Matrix.diagonal (fun i => (q i:ℂ))) = 
      paperRenyi false (Matrix.diagonal (fun i => (p i:ℂ))) (Matrix.diagonal (fun i => (q i:ℂ))) a

/-- PDF p.52, (V): tensor additivity, on arbitrary nonzero positive numerators. -/
def AdditiveDivergence (D : paperDivergenceFamily) : Prop :=
  ∀ (I J : Type) [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype J] [DecidableEq J] [Nonempty J], ∀ r s : paperMat I, ∀ t u : paperMat J,
    r.PosSemidef → s.PosSemidef → t.PosSemidef → u.PosSemidef → r ≠ 0 → t ≠ 0 →
    D.value (I × J) (Matrix.kronecker r t) (Matrix.kronecker s u) = D.value I r s+D.value J t u

/-- PDF p.53, (VIII): every CPTP map, including maps between different dimensions. -/
def paperDataProcessing (D : paperDivergenceFamily) : Prop :=
  ∀ (I J : Type) [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype J] [DecidableEq J] [Nonempty J], ∀ E : paperMat I →ₗ[ℂ] paperMat J,
    paperCPTP E → ∀ r s : paperMat I, r.PosSemidef → s.PosSemidef → r ≠ 0 →
      D.value J (E r) (E s) ≤ D.value I r s

/-- PDF pp.60-61: the concrete max-divergence family. -/
def paperMaxFamily : paperDivergenceFamily := ⟨fun _ _ _ r s => maxD r s⟩

/-- PDF p.66, (4.73): optimization over actual finite-outcome POVMs, in EReal. -/
def measuredRenyi (r s : paperMat I) (a : ENNReal) : EReal :=
  sSup {d : EReal | ∃ m : ℕ, 0 < m ∧ ∃ M : Fin m → paperMat I, IsPOVM M ∧
    d = paperRenyi false (measureOutput M r) (measureOutput M s) a}

/-- PDF p.66, (4.73): the measured representation for every positive input pair,
including attainment of each finite-copy maximum. This predicate does not assume DPI. -/
def MeasuredRepresentation (D : paperDivergenceFamily) (a : ENNReal) : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I], ∀ r s : paperMat I,
    r.PosSemidef → s.PosSemidef → r ≠ 0 →
    Tendsto (fun n : ℕ => ((1/(n:ℝ):ℝ):EReal)*measuredRenyi (paperTensorPower r n) (paperTensorPower s n) a)
      atTop (nhds (D.value I r s)) ∧
    ∀ n : ℕ, 0 < n → ∃ m : ℕ, 0 < m ∧ ∃ M : Fin m → paperMat (Fin n → I), IsPOVM M ∧
      measuredRenyi (paperTensorPower r n) (paperTensorPower s n) a = 
        paperRenyi false (measureOutput M (paperTensorPower r n)) (measureOutput M (paperTensorPower s n)) a

example {K : Type} [Fintype K] [DecidableEq K] (r s : paperMat K) :
    paperMaxFamily.value K r s = maxD r s := rfl

example (E : paperMat A →ₗ[ℂ] paperMat C) (F : paperMat B →ₗ[ℂ] paperMat D) :
    paperTensorAction E F (0:paperMat (A × B)) = 0 := by ext x y; simp [paperTensorAction]

/-- PDF p.52: finite real domain of the six axioms. -/
def AxiomDomain (r s : paperMat I) : Prop := r.PosSemidef ∧ s.PosSemidef ∧ r ≠ 0 ∧ paperSupported r s

/-- PDF p.52: real-valued divergence across every finite system, before adjoining infinities. -/
abbrev RealDivergenceFamily := (I : Type) → [Fintype I] → [DecidableEq I] → paperMat I → paperMat I → ℝ

/-- PDF p.52: direct sum in the disjoint-union basis. -/
def paperDirectSum (r : paperMat I) (s : paperMat J) : paperMat (I ⊕ J) :=
  fun x y => match x,y with
    | .inl i,.inl j => r i j
    | .inr i,.inr j => s i j
    | _,_ => 0

/-- PDF p.52, (I)-(VI): the actual unbounded positive cone and the full trace-weighted mean.
The accepted Dependency50.P35.SixAxioms restricts the mean to total traces at most one;
this book states the mean for arbitrary positive inputs, so it has a distinct local predicate. -/
def paperSixAxioms (D : RealDivergenceFamily) (g : ℝ → ℝ) : Prop :=
  Continuous g ∧ (StrictMono g ∨ StrictAnti g) ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I],
    ContinuousOn (fun x : paperMat I × paperMat I => D I x.1 x.2) {x | AxiomDomain x.1 x.2}) ∧
  (∀ (I J : Type) [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype J] [DecidableEq J] [Nonempty J], ∀ r s : paperMat I, ∀ U : Matrix J I ℂ,
    AxiomDomain r s → Uᴴ*U = 1 → U*Uᴴ = 1 → D I r s = D J (U*r*Uᴴ) (U*s*Uᴴ)) ∧
  D (Fin 1) 1 ((1/2:ℂ) • (1:paperMat (Fin 1))) = Real.logb 2 2 ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I], ∀ r s : paperMat I,
    AxiomDomain r s → (paperBelow s r → 0 ≤ D I r s) ∧ (paperBelow r s → D I r s ≤ 0)) ∧
  (∀ (I J : Type) [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype J] [DecidableEq J] [Nonempty J], ∀ r s : paperMat I, ∀ t u : paperMat J,
    AxiomDomain r s → AxiomDomain t u →
    D (I × J) (Matrix.kronecker r t) (Matrix.kronecker s u) = D I r s+D J t u) ∧
  (∀ (I J : Type) [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype J] [DecidableEq J] [Nonempty J], ∀ r s : paperMat I, ∀ t u : paperMat J,
    AxiomDomain r s → AxiomDomain t u →
    g (D (I ⊕ J) (paperDirectSum r t) (paperDirectSum s u)) = 
      r.trace.re/(r.trace.re+t.trace.re)*g (D I r s)+t.trace.re/(r.trace.re+t.trace.re)*g (D J t u))

/-- PDF pp.53,57: joint convexity or concavity of g(D) on normalized pairs. -/
def MeanCurvature (D : RealDivergenceFamily) (g : ℝ → ℝ) : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I], ∀ r s t u : paperMat I,
    AxiomDomain r s → AxiomDomain t u →
    IsDensityMatrix r → IsDensityMatrix s → IsDensityMatrix t → IsDensityMatrix u →
    ∀ l : ℝ, l ∈ Set.Icc 0 1 →
      (StrictMono g → g (D I (paperMix l r t) (paperMix l s u)) ≤ l*g (D I r s)+(1-l)*g (D I t u)) ∧
      (StrictAnti g → l*g (D I r s)+(1-l)*g (D I t u) ≤ g (D I (paperMix l r t) (paperMix l s u)))

/-- PDF pp.53,57: data processing on the finite domain where the axiomatic D is real. -/
def RealDataProcessing (D : RealDivergenceFamily) : Prop :=
  ∀ (I J : Type) [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype J] [DecidableEq J] [Nonempty J], ∀ E : paperMat I →ₗ[ℂ] paperMat J,
    paperCPTP E → ∀ r s : paperMat I, AxiomDomain r s → D J (E r) (E s) ≤ D I r s

example (r : paperMat I) (s : paperMat J) (i j : I) : paperDirectSum r s (.inl i) (.inl j) = r i j := rfl

example (r : paperMat I) (h : AxiomDomain r r) : r ≠ 0 := h.2.2.1

/-- Definition sanity: the exponential has the extended endpoint values. -/
example : expE ⊥ = 0 ∧ expE ⊤ = ⊤ := by simp [expE]

/-- Definition sanity: the zero matrix remains zero at support exponent zero. -/
example : paperPower (0:paperMat I) 0 = 0 := by simp [paperPower, cfc_zero]

/-- Definition sanity: zero radius around the zero center is outside the strict chapter domain. -/
example : ¬Radius (0:paperMat I) 0 := by simp [Radius]

/-- Definition sanity: the order transformation maps infinity to collision order two. -/
example : transformedOrder ⊤ = 2 := by simp [transformedOrder]

/-- Definition sanity: two zero subnormalized states have generalized fidelity one. -/
example : paperGeneralizedFidelity (0:paperMat I) 0 = 1 := by
  simp [paperGeneralizedFidelity, rootFidelity, cfc_zero]

/-- Definition sanity: algebraic fidelity at zero gives extended max-entropy minus infinity. -/
example : hmax (0:paperMat (A × B)) = ⊥ := by
  apply le_antisymm
  · apply sSup_le
    rintro h ⟨s, hs, rfl⟩
    simp [paperLogE, paperFidelity, rootFidelity, cfc_zero]
  · exact bot_le

/-- Definition sanity: a one-symbol source is decoded exactly by a one-symbol code. -/
example : paperCodeError (fun _ : Unit => (1:ℝ))
    (⟨fun _ => 0, fun _ => ()⟩ : paperSourceCode Unit 1) = 0 := by
  simp [paperCodeError]

end QAlgorithms.Papers.Independent.Intakenext100.P07


