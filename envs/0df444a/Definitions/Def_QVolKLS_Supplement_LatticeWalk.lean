-- Prove2me | Definitions.Def_QVolKLS_Supplement_LatticeWalk
-- name    : QVolKLS_Supplement_LatticeWalk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:33:15.426206+00:00
-- url     : https://prove2.me/theorems/ab96eb80-b616-4504-854b-9e88bc2528a8
-- title:
--   Fixed-lattice preconditioned Metropolis walk and its conductance data
-- statement:
--   Fix a convex body $K\subseteq\mathbb R^D$, a dyadic cubic lattice $\Lambda=h\mathbb Z^D$, a tilt $b$, and a rational positive-definite preconditioner $A$. The **lattice Metropolis walk** is the finite Algorithm 2 chain on $\Omega_\Lambda=K\cap\Lambda$: it mixes a holding branch, a symmetric finite-seed local proposal selected from $J$ radii, and a positive connector proposal, followed by the Metropolis acceptance probability for the log-affine lattice law $\pi_{b,\Lambda}$. Its local sampler records its total-variation error from an ideal symmetric proposal.
--
--   The module also defines the rational inverse pair $W_A,T_A$, the exact rounded-uniform-ball law (83), its independent-sign finite-seed approximation (84), the geometric radius schedule (85), the exact signed uniform connector box, the transformed cell-radius and exceptional-mass bounds (79) and (82), the zero-extended discriminant block-encoding requirement, empirical covariance event, $s$-conductance cut inequality, arbitrary-$M$ warm-start mixing, and the mesh conditions (66), (88), and (93).
--
--   These definitions are shared by Theorem 5.2 and Theorem B.7.
--
--   **Formalization Note** Conductance is stated directly as the cut inequality for every admissible set, and mixing asserts an actual bounded natural time. This avoids default values of real infima over empty or unbounded families. Lattice points use the published two's-complement dyadic decoder. The sampler error compares against the fixed pushforward of uniform ball measure, so it cannot be discharged by choosing an unrelated comparison kernel.
-- source:
--   R. Zhang, Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation, arXiv:2610.04987 (held version, sha256 eee7a45e7117af08035a8d75fd6f145fa82ddade51ad87a6507911b6a0aa4f80), Algorithm 2 and Theorem 5.2, pp.37-40; Appendix B, pp.61-78

import Definitions.Def_QVolKLS_MixTime2Le
import Definitions.Def_QVolKLS_logAffineZ
import Definitions.Def_QVolKLS_memOracle
import Definitions.Def_SongZhangKLS_cheegerPsi
import Mathlib.Analysis.Matrix.Order

set_option autoImplicit false

namespace QVolKLS.Supplement

open QAlgorithms MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace MatrixOrder

/-!
# The fixed-lattice Metropolis walk, conductance, and covariance sampling

R. Zhang, *Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation*,
arXiv:2610.04987 (held version, sha256 eee7a45e…), §5.1, pp.37–40 (Algorithm 2 and
Theorem 5.2) and Appendix B, pp.61–78 (especially (66), (88), (93), Theorem B.7, and (103)).

**Formalization Note.** The finite sample register represents the cubic lattice by the published
two's-complement `decodePoint`. `CommonWalkParams` is selected once for the whole finite tilt list
and contains the mesh, radius list, seed length and arithmetic precision bound. `IsAlgorithm2Walk`
spells out the holding/local/connector mixture and Metropolis acceptance. Its local proposal is the
independent-sign symmetrization of a common finite-seed sampler and is compared in total variation
with the exact rounded pushforward of the uniform ball law (83)–(84). The radius weights are the
published reduction-modulo-`J` probabilities, the radii obey the geometric schedule (85), and the
connector is exactly uniform on the signed integer box from Algorithm 2. Thus the sampler error
cannot be made artificially zero by choosing an unrelated comparison kernel.

Conductance is encoded by `ConductanceAtLeast`, the defining cut inequality itself, rather than a
real `sInf`; this avoids a junk value on an empty cut family. Mixing predicates assert the existence
of an actual time bounded by the displayed expression, rather than using a default infimum.
-/

/-- Parameters chosen once for all tilts and all allowed preconditioners in Theorem 5.2. -/
structure CommonWalkParams (D : ℕ) where
  /-- Dyadic mesh `h = 2⁻ᵖ`. -/
  p : ℕ
  /-- Bits per coordinate in the finite lattice register. -/
  b : ℕ
  /-- Number of dyadic local radii. -/
  J : ℕ
  J_pos : 0 < J
  /-- Number of unbiased bits used to select a radius by reduction modulo `J`. -/
  radiusSeedBits : ℕ
  radius_seed_range : J ≤ 2 ^ radiusSeedBits ∧ 2 ^ radiusSeedBits < 2 * J
  /-- Local radii `δ_j`. -/
  radius : Fin J → ℝ
  radius_pos : ∀ j, 0 < radius j
  /-- Common upper bound used for `r_mesh` in (79). -/
  rMesh : ℝ
  rMesh_pos : 0 < rMesh
  rMesh_dyadic : ∃ k p : ℕ, rMesh = (k : ℝ) / (2 : ℝ) ^ p
  /-- Common upper bound for the transformed outer radius. -/
  transformedOuterRadius : ℝ
  transformedOuterRadius_pos : 0 < transformedOuterRadius
  transformedOuterRadius_dyadic :
    ∃ k p : ℕ, transformedOuterRadius = (k : ℝ) / (2 : ℝ) ^ p
  /-- The dyadic radius list (85), beginning at `4 r_mesh`. -/
  radius_schedule : ∀ j, radius j = 2 ^ (j : ℕ) * (4 * rMesh)
  /-- The list reaches the transformed outer-radius scale required in (85). -/
  radius_covers : ∃ j, Real.sqrt D * transformedOuterRadius ≤ radius j
  /-- Number of random seed bits. -/
  seedBits : ℕ
  /-- Common finite arithmetic precision bound. -/
  precisionBits : ℕ
  /-- Half-width `M_out = 2^connectorBits` of the connector's integer box. -/
  connectorBits : ℕ

/-- The point represented by a lattice-register label under common parameters. -/
noncomputable def walkPoint {D : ℕ} (q : CommonWalkParams D) (z : Qubits (D * q.b)) : Euc D :=
  decodePoint D q.b q.p z

/-- Feasible register labels for the body `K`. -/
noncomputable def walkOmega {D : ℕ} (q : CommonWalkParams D) (K : Set (Euc D)) :
    Finset (Qubits (D * q.b)) := by
  classical
  exact Finset.univ.filter fun z ↦ walkPoint q z ∈ K

/-- The lattice law on the finite register, zero off the body. -/
noncomputable def walkLaw {D : ℕ} (q : CommonWalkParams D) (K : Set (Euc D))
    (tilt : Euc D) : Qubits (D * q.b) → ℝ :=
  regWeight D q.b q.p K (latticeLaw K ((2 : ℝ)⁻¹ ^ q.p) tilt)

/-- Euclidean norm after applying the rational affine preconditioner `W_A`. -/
noncomputable def transformedNorm {D : ℕ} (WA : Matrix (Fin D) (Fin D) ℚ) (u : Euc D) : ℝ :=
  Real.sqrt (∑ i, (∑ j, ((WA i j : ℚ) : ℝ) * u j) ^ 2)

/-- The quadratic form `uᵀ W_A A W_Aᵀ u`. -/
noncomputable def preconditionedCovForm {D : ℕ} (A WA : Matrix (Fin D) (Fin D) ℚ)
    (u : Euc D) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l,
    u i * ((WA i j : ℚ) : ℝ) * ((A j k : ℚ) : ℝ) * ((WA l k : ℚ) : ℝ) * u l

/-- A rational matrix coerced entrywise to a complex matrix. -/
def ratMatrixComplex {D : ℕ} (A : Matrix (Fin D) (Fin D) ℚ) : Matrix (Fin D) (Fin D) ℂ :=
  fun i j => (((A i j : ℚ) : ℝ) : ℂ)

/-- Operator norm of a finite complex matrix. -/
noncomputable def matrixOpNorm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)‖

/-- Proposition B.3's rational approximation `W_A A W_Aᵀ ≈ I`. -/
def IsAffinePreconditioner {D : ℕ} (A WA : Matrix (Fin D) (Fin D) ℚ) : Prop :=
  matrixOpNorm (ratMatrixComplex WA * CFC.sqrt (ratMatrixComplex A) - 1) ≤ 1 / 10 ∧
    ∀ u : Euc D,
      (9 / 10 : ℝ) ^ 2 * ‖u‖ ^ 2 ≤ preconditionedCovForm A WA u ∧
        preconditionedCovForm A WA u ≤ (11 / 10 : ℝ) ^ 2 * ‖u‖ ^ 2

/-- A rational matrix acting on a Euclidean vector. -/
noncomputable def ratMatrixVec {D : ℕ} (M : Matrix (Fin D) (Fin D) ℚ) (u : Euc D) : Euc D :=
  WithLp.toLp 2 fun i => ∑ j, ((M i j : ℚ) : ℝ) * u j

/-- Coordinatewise rounding `R_h(u) = h ⌊h⁻¹u + 1/2⌋` for `h = 2⁻ᵖ`. -/
noncomputable def roundDyadic {D : ℕ} (p : ℕ) (u : Euc D) : Euc D :=
  WithLp.toLp 2 fun i =>
    ((Int.floor (u i * (2 : ℝ) ^ p + 1 / 2) : ℤ) : ℝ) / (2 : ℝ) ^ p

/-- A vector whose coordinates use at most the stated dyadic precision. -/
def IsDyadicVector {D : ℕ} (precisionBits : ℕ) (u : Euc D) : Prop :=
  ∃ k : Fin D → ℤ, ∀ i, u i = (k i : ℝ) / (2 : ℝ) ^ precisionBits

/-- The exact radius-selection probability obtained from unbiased bits and reduction modulo `J`. -/
noncomputable def radiusWeight {D : ℕ} (q : CommonWalkParams D) (j : Fin q.J) : ℝ := by
  classical
  exact ((Finset.univ.filter fun s : Qubits q.radiusSeedBits =>
      bitsToNat s % q.J = j).card : ℝ) / (2 : ℝ) ^ q.radiusSeedBits

/-- The symmetrized probability of a displacement produced from a uniform finite seed. -/
noncomputable def finiteSeedSymProb {D n : ℕ} (sample : Qubits n → Euc D) (v : Euc D) : ℝ := by
  classical
  exact (((Finset.univ.filter fun s => sample s = v).card : ℝ) +
      ((Finset.univ.filter fun s => -sample s = v).card : ℝ)) /
    (2 * (2 : ℝ) ^ n)

/-- The ideal rounded displacement probability (83), obtained from a uniform point in a ball. -/
noncomputable def idealRoundedBallProb {D : ℕ} (p : ℕ)
    (TA : Matrix (Fin D) (Fin D) ℚ) (delta : ℝ) (v : Euc D) : ℝ :=
  (volume (Metric.ball (0 : Euc D) delta ∩
      {u | roundDyadic p (ratMatrixVec TA u) = v})).toReal /
    (volume (Metric.ball (0 : Euc D) delta)).toReal

/-- The displacement corresponding to a coefficient vector in
`{-M_out, …, M_out-1}^D`, where `M_out = 2^connectorBits`. -/
noncomputable def connectorDisplacement {D : ℕ} (q : CommonWalkParams D)
    (k : Fin D → Fin (2 * (2 ^ q.connectorBits))) : Euc D :=
  latticePt ((2 : ℝ)⁻¹ ^ q.p) fun i =>
    ((k i : ℕ) : ℤ) - ((2 ^ q.connectorBits : ℕ) : ℤ)

/-- The exact connector proposal probability from the uniform integer box and independent sign. -/
noncomputable def connectorProposalProb {D : ℕ} (q : CommonWalkParams D) (v : Euc D) : ℝ := by
  classical
  let disp := connectorDisplacement q
  let box := Finset.univ.filter fun k : Fin D → Fin (2 * (2 ^ q.connectorBits)) => disp k = v
  let negBox := Finset.univ.filter fun k : Fin D → Fin (2 * (2 ^ q.connectorBits)) => -disp k = v
  exact ((box.card : ℝ) + (negBox.card : ℝ)) /
    (2 * (2 * (2 : ℝ) ^ q.connectorBits) ^ D)

/-- The connector box contains every difference between points in the supplied outer ball. -/
def ConnectorCovers {D : ℕ} (q : CommonWalkParams D) (R0 : ℝ) : Prop :=
  2 * R0 * (2 : ℝ) ^ q.p < (2 : ℝ) ^ q.connectorBits

/-- `rhoA` bounds the radius of the transformed lattice cell `W_A Q_Λ`. -/
def TransformedCellRadiusBound {D : ℕ} (q : CommonWalkParams D)
    (WA : Matrix (Fin D) (Fin D) ℚ) (rhoA : ℝ) : Prop :=
  0 ≤ rhoA ∧ ∀ e : Euc D, e ∈ cellQ D ((2 : ℝ)⁻¹ ^ q.p) → transformedNorm WA e ≤ rhoA

/-- The common transformed outer-radius bound contains `W_A(K-x_c)`. -/
def TransformedOuterRadiusBound {D : ℕ} (q : CommonWalkParams D) (K : Set (Euc D))
    (xc : Euc D) (WA : Matrix (Fin D) (Fin D) ℚ) : Prop :=
  ∀ x ∈ K, transformedNorm WA (x - xc) ≤ q.transformedOuterRadius

/-- Exact high-level semantics of Algorithm 2 for one tilt and preconditioner. -/
def IsAlgorithm2Walk {D : ℕ} (q : CommonWalkParams D) (K : Set (Euc D))
    (tilt : Euc D) (TA : Matrix (Fin D) (Fin D) ℚ)
    (epsDir : ℝ) (P : Qubits (D * q.b) → Qubits (D * q.b) → ℝ) : Prop :=
  ∃ sampleU : Fin q.J → Qubits q.seedBits → Euc D,
    (∀ j seed, IsDyadicVector q.precisionBits (sampleU j seed) ∧
      sampleU j seed ∈ Metric.ball 0 (q.radius j)) ∧
    (∀ j x,
      finTV
        (fun y => finiteSeedSymProb
          (fun seed => roundDyadic q.p (ratMatrixVec TA (sampleU j seed)))
          (walkPoint q y - walkPoint q x))
        (fun y => idealRoundedBallProb q.p TA (q.radius j)
          (walkPoint q y - walkPoint q x)) ≤ epsDir) ∧
    (∀ x ∈ walkOmega q K, ∀ y ∈ walkOmega q K, x ≠ y →
      P x y = (1 / 2 : ℝ) *
        ((3 / 4 : ℝ) * (∑ j, radiusWeight q j *
          finiteSeedSymProb
            (fun seed => roundDyadic q.p (ratMatrixVec TA (sampleU j seed)))
            (walkPoint q y - walkPoint q x)) +
          (1 / 4 : ℝ) * connectorProposalProb q (walkPoint q y - walkPoint q x)) *
        min 1 (Real.exp (-inner ℝ tilt (walkPoint q y - walkPoint q x)))) ∧
    (∀ x ∈ walkOmega q K,
      P x x = 1 - ∑ y ∈ (walkOmega q K).erase x, P x y)

/-- The finite Algorithm 2 walk together with the structural properties established in clause (i)
of Theorem 5.2. -/
structure LatticeWalk {D : ℕ} (q : CommonWalkParams D) (K : Set (Euc D))
    (tilt : Euc D) (A : Matrix (Fin D) (Fin D) ℚ) where
  WA : Matrix (Fin D) (Fin D) ℚ
  TA : Matrix (Fin D) (Fin D) ℚ
  inverse_left : WA * TA = 1
  inverse_right : TA * WA = 1
  preconditions : IsAffinePreconditioner A WA
  P : Qubits (D * q.b) → Qubits (D * q.b) → ℝ
  /-- Total-variation error of each finite local direction sampler. -/
  epsDir : ℝ
  algorithm2 : IsAlgorithm2Walk q K tilt TA epsDir P
  reversible : IsReversibleChainOn (walkOmega q K) P (walkLaw q K tilt)
  lazy : ∀ x ∈ walkOmega q K, 1 / 2 ≤ P x x
  positive : IsPositiveChain (walkOmega q K) P (walkLaw q K tilt)
  irreducible : ∀ x ∈ walkOmega q K, ∀ y ∈ walkOmega q K, 0 < P x y

/-- Clause (iii): an exact block-encoding and arbitrarily accurate finite implementation using a
constant number of coherent membership queries. -/
def HasConstantQueryBlockEncoding {D : ℕ} (q : CommonWalkParams D) (K : Set (Euc D))
    (tilt : Euc D) (A : Matrix (Fin D) (Fin D) ℚ) (W : LatticeWalk q K tilt A)
    (Cq : ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 2 →
    ∃ (a : ℕ) (U : Matrix (Qubits (a + D * q.b)) (Qubits (a + D * q.b)) ℂ)
      (impl : OracleCircuit unitaryGateSet (fun _ : Fin 1 ↦ D * q.b + 1) (a + D * q.b)),
      IsZeroExtBlockEncoding U (discriminantExt (walkOmega q K) (walkLaw q K tilt) W.P) ∧
      matrixOpNorm (impl.unitary (fun _ ↦ memOracle K q.b q.p) - U) ≤ eps ∧
      (impl.queryCount 0 : ℝ) ≤ Cq

/-- Empirical mean of `L` represented lattice samples. -/
noncomputable def empiricalMean {D L : ℕ} {q : CommonWalkParams D}
    (z : Fin L → Qubits (D * q.b)) : Euc D :=
  (L : ℝ)⁻¹ • ∑ ell, walkPoint q (z ell)

/-- Empirical covariance quadratic form of represented lattice samples. -/
noncomputable def empiricalDirVariance {D L : ℕ} {q : CommonWalkParams D}
    (z : Fin L → Qubits (D * q.b)) (u : Euc D) : ℝ :=
  (L : ℝ)⁻¹ * ∑ ell, inner ℝ u (walkPoint q (z ell) - empiricalMean z) ^ 2

/-- Clause (v): probability that `L` independent lattice samples have empirical covariance between
`1/4` and `4` times the continuous covariance. -/
noncomputable def covarianceGoodProbability {D L : ℕ} (q : CommonWalkParams D)
    (K : Set (Euc D)) (tilt : Euc D) : ℝ := by
  classical
  exact ∑ z : Fin L → Qubits (D * q.b),
    if ∀ u : Euc D,
        (1 / 4 : ℝ) * dirVariance (logAffineMeasure K tilt) u ≤ empiricalDirVariance z u ∧
          empiricalDirVariance z u ≤ 4 * dirVariance (logAffineMeasure K tilt) u then
      ∏ ell, walkLaw q K tilt (z ell)
    else 0

/-- Stationary flow across a cut of a finite walk. -/
noncomputable def cutFlow {ι : Type*} [Fintype ι] [DecidableEq ι] (Ω S : Finset ι)
    (pi : ι → ℝ) (P : ι → ι → ℝ) : ℝ :=
  ∑ x ∈ S, ∑ y ∈ Ω \ S, pi x * P x y

/-- `Φ_s(P) ≥ gamma`, stated directly for every admissible cut. -/
def ConductanceAtLeast {ι : Type*} [Fintype ι] [DecidableEq ι] (Ω : Finset ι)
    (pi : ι → ℝ) (P : ι → ι → ℝ) (s gamma : ℝ) : Prop :=
  ∀ S : Finset ι, S ⊆ Ω → s < ∑ x ∈ S, pi x → ∑ x ∈ S, pi x ≤ 1 / 2 →
    gamma * ((∑ x ∈ S, pi x) - s) ≤ cutFlow Ω S pi P

/-- Mixing from every `M`-warm start by some time at most `T`. -/
def MixTimeWarmLe {ι : Type*} [Fintype ι] [DecidableEq ι] (Ω : Finset ι)
    (M eta : ℝ) (pi : ι → ℝ) (P : ι → ι → ℝ) (T : ℕ) : Prop :=
  ∀ nu : ι → ℝ, (∀ x, 0 ≤ nu x) → ∑ x, nu x = 1 → (∀ x, nu x ≤ M * pi x) →
    ∃ j ≤ T, finTV (distAfter Ω P nu j) pi ≤ eta

/-- Appendix B condition (66). -/
def Satisfies66 (Cquad D : ℝ) (r0 R0 bnorm rho epsQuad : ℝ) : Prop :=
  rho ≤ r0 / 4 ∧
    epsQuad = Cquad * (((D + bnorm * R0) * rho / r0) + bnorm * rho) ∧ epsQuad ≤ 1

/-- Appendix B condition (88). -/
def Satisfies88 (bnorm rho : ℝ) : Prop :=
  bnorm * rho ≤ (1 / 2 : ℝ) * Real.log (4 / 3)

/-- Appendix B condition (93). -/
def Satisfies93 (cMesh D psi s epsMesh : ℝ) : Prop :=
  epsMesh ≤ cMesh * min s (s * psi / (D * (1 + Real.log (4 / s))))

/-- Equations (79) and (82): the exceptional-mass error is derived from the transformed cell
radius and the quadrature error. -/
def SatisfiesMeshError (Cradius Cerror D rhoA epsQuad rMesh epsMesh : ℝ) : Prop :=
  rMesh = Cradius * D ^ 3 * rhoA ∧
    epsMesh = Cerror * (Real.sqrt D * rMesh + epsQuad)

end QVolKLS.Supplement


