-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60
-- name    : QAlgorithms_Papers_Independent_Information100_P60
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T12:30:36.851065+00:00
-- url     : https://prove2.me/theorems/41289457-52d5-44eb-8b42-930b0d65deea
-- title:
--   Definitions for Quantum hypothesis testing of non-mixed-unitarity: A multifaceted hierarchy of quantum channel discrimination
-- statement:
--   The objects the formalized statements of *Quantum hypothesis testing of non-mixed-unitarity: A multifaceted hierarchy of quantum channel discrimination* (arXiv:2609.40355) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Mat`
--   - `Maps`: Paper p.5: finite-dimensional linear-map space, with its norm topology.
--   - `Setting`: Paper pp.10–11: positive dimensions, nonempty closed convex CPTP null set, CPTP alternative outside it.
--   - `relativeBits`: Paper pp.5–6: accepted support-aware Umegaki entropy converted from nats to bits. The explicit off-domain value is zero; all uses below have density inputs.
--   - `testingBits`: Paper p.8 Eqs.(16),(18): optimize effects accepting the null, with a uniform Type-I constraint.
--   - `Reg`: Paper pp.9–11: r=1 is no memory; r=a supplies reference dimension a^k.
--   - `output`: Paper p.11: the SAME channel in every use, identity on the reference.
--   - `copies`: Paper p.11: m identical independent copies of a block state.
--   - `productProbe`: Paper p.14 Eq.(38), regrouping reference/input indices.
--   - `Correlation`: Paper p.14: the three intra-block correlation restrictions.
--   - `admissible`: Paper p.14 Eqs.(37)–(38): separability is across uses, not across reference/input.
--   - `blockRate`: Paper p.11 Eq.(25): optimize the probe before the unknown channel, repeating the block m+1 times.
--   - `arbitraryRate`: Paper p.11 Eq.(24): arbitrary parallel probes, defined independently of regularization.
--   - `HasSteinValue`: Paper p.6 Definition 2: BOTH outer limits, no inner ordinary limit assumed.
--   - `operational`: Paper p.8 Eq.(19): the operational lower exponent; main formulas also assert both limiting values.
--   - `blockExponent`: Paper p.11: block exponent from tests, not from relative entropy.
--   - `arbitraryExponent`: Paper p.11: arbitrary-probe exponent from independent operational tests.
--   - `finiteValue`: Paper pp.11–14: finite-letter minimax with null output first.
--   - `MinimumAttained`: Paper p.12: the inner infimum is attained, also if its value is infinite.
--   - `FiniteLetter`: Paper pp.11–14: operational equality, both outer limits, and the minimum-attainment clause.
--   - `productValue`: Paper p.14 Eqs.(39)–(40): a single null channel minimizes OUTSIDE the sum.
--   - `MU`: Paper p.1: finite convex mixtures of unitary conjugations, within CPTP maps.
--   - `MUConvertible`: Paper p.17 Definition 3: independent MU preprocessing and postprocessing.
--   - `UnitaryEquivalent`: Paper p.17 Definition 3: independent input/output unitaries.
--   - `wernerHolevo`: Paper p.20: Werner–Holevo channel, used only with d≥3.
--   - `OrthogonalCovariant`: Paper p.20 Eq.(64): covariance under all real orthogonal matrices.
--   - `JointUET`: Paper p.21: the same unitary implements transpose for both matrices.
--   - `chi`: Paper p.22: complex degree-six invariant, retaining the noncommutative order.
--   - `TransposeCancellation`: Paper p.20 Eq.(67): two-unitary cancellation for both matrices.
--   - `TwoProbeConjecture`: Paper p.24: full Conjecture-1 predicate, never asserted as a theorem or axiom. Equal-weight two-term representation permits coincident unitaries.
--   - `CommonEigenvector`: Paper p.23: common eigenvector is nonzero.
--   - `RepeatedEigenvalue`: Paper p.23: repeated eigenvalue means eigenspace dimension at least two.
--   - `Pure`: Paper p.24: normalized pure-state predicate.
--   - `SpecialPair`: Paper p.24 Proposition 1: all listed sufficient disjuncts and pure-state consequence.
--   - `plainProduct`: Paper p.24: specified memoryless product probe with a trivial reference.
--   - `fixedExponent`: Paper p.24: operational exponent of a fixed probe; singleton removes probe optimization.
--   - `K1`: Paper p.24 Eq.(73).
--   - `K2`: Paper p.24 Eq.(73).
--   - `phaseP`: Paper p.24: phase diagonal, alongside the accepted positive-sign QFT.
--   - `counterU`: Paper p.24: first explicit cancelling unitary.
--   - `counterV`: Paper p.24: second explicit cancelling unitary.
--   - `MESProbe`: Paper p.29 Eqs.(111)–(112): all maximally entangled memoryless two-use probes.
--   - `omega`: Paper p.32 Eq.(130): the maximally entangled vector, normalized for d>0.
--   - `isotropic`: Paper p.32 Eq.(130): isotropic reference/input state.
--   - `singleValue`: Paper p.32 Eq.(131): fixed single-use reference-assisted relative-entropy value.
--   - `SingleMinimumAttained`: Paper p.32: the fixed single-use infimum is attained.
--   - `diamondDistance`: Paper p.31 Eq.(126): full diamond distance, no extra factor 1/2. The nonempty MU distance set is bounded below by zero when d>0.
-- source:
--   Quantum hypothesis testing of non-mixed-unitarity: A multifaceted hierarchy of quantum channel discrimination, arXiv:2609.40355v1, https://arxiv.org/abs/2609.40355v1

import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Defs_ChannelDiamondNorm
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Defs_Fourier

noncomputable section

open scoped Matrix ComplexConjugate ENNReal
open Filter Topology

namespace QAlgorithms.Papers.Independent.Information100.P60

attribute [local instance] Classical.propDecidable Classical.decEq

abbrev Mat (I : Type*) := Matrix I I ℂ

/-- Paper p.5: finite-dimensional linear-map space, with its norm topology. -/
abbrev Maps (a b : ℕ) := Mat (Fin a) →L[ℂ] Mat (Fin b)

/-- Paper pp.10–11: positive dimensions, nonempty closed convex CPTP null set, CPTP alternative outside it. -/
def Setting {a b : ℕ} (R : Set (Maps a b)) (N : Maps a b) : Prop :=
  0 < a ∧ 0 < b ∧ R.Nonempty ∧ IsClosed R ∧ Convex ℝ R ∧
    (∀ Phi ∈ R, IsChannel Phi) ∧ IsChannel N ∧ N ∉ R

/-- Paper pp.5–6: accepted support-aware Umegaki entropy converted from nats to bits.
The explicit off-domain value is zero; all uses below have density inputs. -/
def relativeBits {I : Type*} [Fintype I] [DecidableEq I] (rho sigma : Mat I) : ℝ≥0∞ :=
  if h : IsDensityMatrix rho ∧ IsDensityMatrix sigma then
    QuantumLoss.umegakiEntropy rho sigma h.1 h.2 / ENNReal.ofReal (Real.log 2)
  else 0

/-- Paper p.8 Eqs.(16),(18): optimize effects accepting the null, with a uniform Type-I constraint. -/
def testingBits {I : Type*} [Fintype I] [DecidableEq I]
    (R : Set (Mat I)) (sigma : Mat I) (eps : ℝ) : ℝ≥0∞ :=
  ⨆ T : {T : Mat I // IsEffect T ∧ ∀ rho ∈ R, effectProb (1 - T) rho ≤ eps},
    if effectProb T.1 sigma = 0 then ⊤
    else ENNReal.ofReal (-Real.logb 2 (effectProb T.1 sigma))

/-- Paper pp.9–11: r=1 is no memory; r=a supplies reference dimension a^k. -/
abbrev Reg (r a k : ℕ) := (Fin k → Fin r) × (Fin k → Fin a)

/-- Paper p.11: the SAME channel in every use, identity on the reference. -/
def output {a b : ℕ} (r k : ℕ) (Phi : Maps a b) : Superop (Reg r a k) (Reg r b k) :=
  idTensorSuperop (R := Fin k → Fin r)
    (piSuperop (fun _ : Fin k => (Phi : Superop (Fin a) (Fin b))))

/-- Paper p.11: m identical independent copies of a block state. -/
def copies {I : Type*} (m : ℕ) (X : Mat I) : Mat (Fin m → I) :=
  Matrix.of fun x y => ∏ i, X (x i) (y i)

/-- Paper p.14 Eq.(38), regrouping reference/input indices. -/
def productProbe {r a k : ℕ} (tau : Fin k → Mat (Fin r × Fin a)) : Mat (Reg r a k) :=
  Matrix.of fun x y => ∏ i, tau i (x.1 i, x.2 i) (y.1 i, y.2 i)

/-- Paper p.14: the three intra-block correlation restrictions. -/
inductive Correlation where
  | unrestricted
  | separable
  | product
  deriving DecidableEq

/-- Paper p.14 Eqs.(37)–(38): separability is across uses, not across reference/input. -/
def admissible (r a k : ℕ) (c : Correlation) : Set (Mat (Reg r a k)) :=
  {X | IsDensityMatrix X ∧ match c with
    | .unrestricted => True
    | .product => ∃ tau : Fin k → Mat (Fin r × Fin a),
        (∀ i, IsDensityMatrix (tau i)) ∧ X = productProbe tau
    | .separable => ∃ q : ℕ, ∃ w : Fin q → ℝ,
        ∃ tau : Fin q → Fin k → Mat (Fin r × Fin a),
        (∀ j, 0 ≤ w j) ∧ (∑ j, w j) = 1 ∧
        (∀ j i, IsDensityMatrix (tau j i)) ∧ X = ∑ j, (w j : ℂ) • productProbe (tau j)}

/-- Paper p.11 Eq.(25): optimize the probe before the unknown channel, repeating the block m+1 times. -/
def blockRate {a b : ℕ} (r : ℕ) (R : Set (Maps a b)) (N : Maps a b)
    (k : ℕ) (P : Set (Mat (Reg r a k))) (m : ℕ) (eps : ℝ) : ℝ≥0∞ :=
  (⨆ X : P, testingBits
    {Y | ∃ Phi ∈ R, Y = copies (m + 1) (output r k Phi X.1)}
    (copies (m + 1) (output r k N X.1)) eps) / (k * (m + 1) : ℕ)

/-- Paper p.11 Eq.(24): arbitrary parallel probes, defined independently of regularization. -/
def arbitraryRate {a b : ℕ} (r : ℕ) (R : Set (Maps a b)) (N : Maps a b)
    (c : Correlation) (n : ℕ) (eps : ℝ) : ℝ≥0∞ :=
  (⨆ X : admissible r a (n + 1) c, testingBits
    {Y | ∃ Phi ∈ R, Y = output r (n + 1) Phi X.1}
    (output r (n + 1) N X.1) eps) / (n + 1 : ℕ)

/-- Paper p.6 Definition 2: BOTH outer limits, no inner ordinary limit assumed. -/
def HasSteinValue (g : ℕ → ℝ → ℝ≥0∞) (e : ℝ≥0∞) : Prop :=
  Tendsto (fun eps => liminf (fun n => g n eps) atTop)
    (nhdsWithin 0 (Set.Ioo 0 1)) (𝓝 e) ∧
  Tendsto (fun eps => limsup (fun n => g n eps) atTop)
    (nhdsWithin 0 (Set.Ioo 0 1)) (𝓝 e)

/-- Paper p.8 Eq.(19): the operational lower exponent; main formulas also assert both limiting values. -/
def operational (g : ℕ → ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  liminf (fun eps => liminf (fun n => g n eps) atTop) (nhdsWithin 0 (Set.Ioo 0 1))

/-- Paper p.11: block exponent from tests, not from relative entropy. -/
def blockExponent {a b : ℕ} (r : ℕ) (R : Set (Maps a b)) (N : Maps a b)
    (k : ℕ) (c : Correlation) : ℝ≥0∞ :=
  operational (blockRate r R N k (admissible r a k c))

/-- Paper p.11: arbitrary-probe exponent from independent operational tests. -/
def arbitraryExponent {a b : ℕ} (r : ℕ) (R : Set (Maps a b)) (N : Maps a b)
    (c : Correlation) : ℝ≥0∞ := operational (arbitraryRate r R N c)

/-- Paper pp.11–14: finite-letter minimax with null output first. -/
def finiteValue {a b : ℕ} (r : ℕ) (R : Set (Maps a b)) (N : Maps a b)
    (k : ℕ) (c : Correlation) : ℝ≥0∞ :=
  ⨆ X : admissible r a k c,
    (⨅ Phi : R, relativeBits (output r k Phi.1 X.1) (output r k N X.1)) / (k : ℕ)

/-- Paper p.12: the inner infimum is attained, also if its value is infinite. -/
def MinimumAttained {a b : ℕ} (r : ℕ) (R : Set (Maps a b)) (N : Maps a b)
    (k : ℕ) (c : Correlation) : Prop :=
  ∀ X ∈ admissible r a k c, ∃ Phi ∈ R, ∀ Psi ∈ R,
    relativeBits (output r k Phi X) (output r k N X) ≤
    relativeBits (output r k Psi X) (output r k N X)

/-- Paper pp.11–14: operational equality, both outer limits, and the minimum-attainment clause. -/
def FiniteLetter {a b : ℕ} (r : ℕ) (R : Set (Maps a b)) (N : Maps a b)
    (k : ℕ) (c : Correlation) : Prop :=
  HasSteinValue (blockRate r R N k (admissible r a k c)) (finiteValue r R N k c) ∧
  blockExponent r R N k c = finiteValue r R N k c ∧ MinimumAttained r R N k c

/-- Paper p.14 Eqs.(39)–(40): a single null channel minimizes OUTSIDE the sum. -/
def productValue {a b : ℕ} (r : ℕ) (R : Set (Maps a b)) (N : Maps a b) (k : ℕ) : ℝ≥0∞ :=
  ⨆ tau : {tau : Fin k → Mat (Fin r × Fin a) // ∀ i, IsDensityMatrix (tau i)},
    (⨅ Phi : R, ∑ i, relativeBits (idTensorSuperop Phi.1 (tau.1 i))
      (idTensorSuperop N (tau.1 i))) / (k : ℕ)

/-- Paper p.1: finite convex mixtures of unitary conjugations, within CPTP maps. -/
def MU (d : ℕ) : Set (Maps d d) :=
  {Phi | IsChannel Phi ∧ ∃ q : ℕ, ∃ w : Fin q → ℝ,
    ∃ U : Fin q → Matrix.unitaryGroup (Fin d) ℂ,
    (∀ j, 0 ≤ w j) ∧ (∑ j, w j) = 1 ∧
    ∀ X, Phi X = ∑ j, (w j : ℂ) • ((U j : Mat (Fin d)) * X * (U j : Mat (Fin d))ᴴ)}

/-- Paper p.17 Definition 3: independent MU preprocessing and postprocessing. -/
def MUConvertible {d : ℕ} (N M : Maps d d) : Prop :=
  ∃ P ∈ MU d, ∃ Q ∈ MU d, ∀ X, M X = Q (N (P X))

/-- Paper p.17 Definition 3: independent input/output unitaries. -/
def UnitaryEquivalent {d : ℕ} (N M : Superop (Fin d) (Fin d)) : Prop :=
  ∃ U V : Matrix.unitaryGroup (Fin d) ℂ, ∀ X,
    M X = (V : Mat (Fin d)) * N ((U : Mat (Fin d)) * X * (U : Mat (Fin d))ᴴ) * (V : Mat (Fin d))ᴴ

/-- Paper p.20: Werner–Holevo channel, used only with d≥3. -/
def wernerHolevo (d : ℕ) : Superop (Fin d) (Fin d) :=
  fun X => ((d : ℂ) - 1)⁻¹ • (X.trace • 1 - X.transpose)

/-- Paper p.20 Eq.(64): covariance under all real orthogonal matrices. -/
def OrthogonalCovariant {d : ℕ} (N : Maps d d) : Prop :=
  ∀ O : Matrix (Fin d) (Fin d) ℝ, O.transpose * O = 1 → O * O.transpose = 1 →
    let C : Mat (Fin d) := O.map (fun x => (x : ℂ))
    ∀ X, N (C * X * C.transpose) = C * N X * C.transpose

/-- Paper p.21: the same unitary implements transpose for both matrices. -/
def JointUET (A B : Mat (Fin 3)) : Prop :=
  ∃ S : Matrix.unitaryGroup (Fin 3) ℂ,
    (S : Mat (Fin 3)) * A * (S : Mat (Fin 3))ᴴ = A.transpose ∧
    (S : Mat (Fin 3)) * B * (S : Mat (Fin 3))ᴴ = B.transpose

/-- Paper p.22: complex degree-six invariant, retaining the noncommutative order. -/
def chi (A B : Mat (Fin 3)) : ℂ :=
  (A ^ 2 * B ^ 2 * A * B - B ^ 2 * A ^ 2 * B * A).trace

/-- Paper p.20 Eq.(67): two-unitary cancellation for both matrices. -/
def TransposeCancellation (A B : Mat (Fin 3)) : Prop :=
  ∃ U V : Matrix.unitaryGroup (Fin 3) ℂ, ∀ M ∈ ({A, B} : Set (Mat (Fin 3))),
    M.transpose + (U : Mat (Fin 3)) * M * (U : Mat (Fin 3))ᴴ +
      (V : Mat (Fin 3)) * M * (V : Mat (Fin 3))ᴴ = 0

/-- Paper p.24: full Conjecture-1 predicate, never asserted as a theorem or axiom.
Equal-weight two-term representation permits coincident unitaries. -/
def TwoProbeConjecture : Prop :=
  ∀ rho sigma : Mat (Fin 3), IsDensityMatrix rho → IsDensityMatrix sigma →
    ∃ U V : Matrix.unitaryGroup (Fin 3) ℂ, ∀ X ∈ ({rho, sigma} : Set (Mat (Fin 3))),
      (1 / 2 : ℂ) • ((U : Mat (Fin 3)) * X * (U : Mat (Fin 3))ᴴ +
        (V : Mat (Fin 3)) * X * (V : Mat (Fin 3))ᴴ) = wernerHolevo 3 X

/-- Paper p.23: common eigenvector is nonzero. -/
def CommonEigenvector (A B : Mat (Fin 3)) : Prop :=
  ∃ v : Fin 3 → ℂ, v ≠ 0 ∧ ∃ x y : ℂ, A.mulVec v = x • v ∧ B.mulVec v = y • v

/-- Paper p.23: repeated eigenvalue means eigenspace dimension at least two. -/
def RepeatedEigenvalue (A : Mat (Fin 3)) : Prop :=
  ∃ x : ℂ, 2 ≤ Module.finrank ℂ (LinearMap.ker (A - x • 1).mulVecLin)

/-- Paper p.24: normalized pure-state predicate. -/
def Pure (A : Mat (Fin 3)) : Prop :=
  ∃ psi : EuclideanSpace ℂ (Fin 3), ‖psi‖ = 1 ∧ A = pureDensity psi

/-- Paper p.24 Proposition 1: all listed sufficient disjuncts and pure-state consequence. -/
def SpecialPair (A B : Mat (Fin 3)) : Prop :=
  ((∀ i j, (A i j).im = 0) ∧ (∀ i j, (B i j).im = 0)) ∨
  A * B = B * A ∨ CommonEigenvector A B ∨ RepeatedEigenvalue A ∨ RepeatedEigenvalue B ∨ Pure A ∨ Pure B

/-- Paper p.24: specified memoryless product probe with a trivial reference. -/
def plainProduct {a k : ℕ} (tau : Fin k → Mat (Fin a)) : Mat (Reg 1 a k) :=
  Matrix.of fun x y => ∏ i, tau i (x.2 i) (y.2 i)

/-- Paper p.24: operational exponent of a fixed probe; singleton removes probe optimization. -/
def fixedExponent {a b : ℕ} (r : ℕ) (R : Set (Maps a b)) (N : Maps a b)
    (k : ℕ) (X : Mat (Reg r a k)) : ℝ≥0∞ := operational (blockRate r R N k {X})

/-- Paper p.24 Eq.(73). -/
def K1 : Mat (Fin 3) :=
  !![0, 0, 1/2 + (Real.sqrt 3 / 2 : ℝ) * Complex.I;
     0, 1, 1;
     1/2 - (Real.sqrt 3 / 2 : ℝ) * Complex.I, 1, -1]

/-- Paper p.24 Eq.(73). -/
def K2 : Mat (Fin 3) :=
  !![0, 0, (Real.sqrt 3 / 2 : ℝ) - 1/2 * Complex.I;
     0, -(Real.sqrt 3 : ℝ), Complex.I;
     (Real.sqrt 3 / 2 : ℝ) + 1/2 * Complex.I, -Complex.I, (Real.sqrt 3 : ℝ)]

/-- Paper p.24: phase diagonal, alongside the accepted positive-sign QFT. -/
def phaseP : Mat (Fin 3) := Matrix.diagonal ![1, 1, Complex.exp (2 * Real.pi * Complex.I / 3)]

/-- Paper p.24: first explicit cancelling unitary. -/
def counterU : Mat (Fin 3) := phaseP * qftMatrix 3

/-- Paper p.24: second explicit cancelling unitary. -/
def counterV : Mat (Fin 3) := phaseP ^ 2 * qftMatrix 3 * phaseP * qftMatrix 3

/-- Paper p.29 Eqs.(111)–(112): all maximally entangled memoryless two-use probes. -/
def MESProbe (d : ℕ) : Set (Mat (Reg 1 d 2)) :=
  {X | ∃ V : Matrix.unitaryGroup (Fin d) ℂ, X = Matrix.of (fun x y =>
    ((Real.sqrt d : ℂ)⁻¹ * (V : Mat (Fin d)) (x.2 1) (x.2 0)) *
      conj ((Real.sqrt d : ℂ)⁻¹ * (V : Mat (Fin d)) (y.2 1) (y.2 0)))}

/-- Paper p.32 Eq.(130): the maximally entangled vector, normalized for d>0. -/
def omega (d : ℕ) : EuclideanSpace ℂ (Fin d × Fin d) :=
  WithLp.toLp 2 fun x => if x.1 = x.2 then (Real.sqrt d : ℂ)⁻¹ else 0

/-- Paper p.32 Eq.(130): isotropic reference/input state. -/
def isotropic (d : ℕ) (p : ℝ) : Mat (Fin d × Fin d) :=
  (p : ℂ) • pureDensity (omega d) + ((1 - p) / (d : ℝ)^2 : ℝ) • (1 : Mat (Fin d × Fin d))

/-- Paper p.32 Eq.(131): fixed single-use reference-assisted relative-entropy value. -/
def singleValue {d : ℕ} (N : Maps d d) (rho : Mat (Fin d × Fin d)) : ℝ≥0∞ :=
  ⨅ Phi : MU d, relativeBits (idTensorSuperop Phi.1 rho) (idTensorSuperop N rho)

/-- Paper p.32: the fixed single-use infimum is attained. -/
def SingleMinimumAttained {d : ℕ} (N : Maps d d) (rho : Mat (Fin d × Fin d)) : Prop :=
  ∃ Phi ∈ MU d, ∀ Psi ∈ MU d,
    relativeBits (idTensorSuperop Phi rho) (idTensorSuperop N rho) ≤
      relativeBits (idTensorSuperop Psi rho) (idTensorSuperop N rho)

/-- Paper p.31 Eq.(126): full diamond distance, no extra factor 1/2.
The nonempty MU distance set is bounded below by zero when d>0. -/
def diamondDistance (d : ℕ) (hd : 0 < d) (N : Maps d d) : ℝ :=
  sInf {v | ∃ Phi ∈ MU d,
    v = IntrinsicLearning.diamondNorm d hd (Phi.toLinearMap - N.toLinearMap)}

/-- Sanity: zero copies is a scalar identity, not a zero state. -/
example {I : Type*} (X : Mat I) (x y : Fin 0 → I) : copies 0 X x y = 1 := by simp [copies]

/-- Sanity: a one-factor product keeps both reference and input indices. -/
example {r a : ℕ} (tau : Fin 1 → Mat (Fin r × Fin a)) (x y : Reg r a 1) :
    productProbe tau x y = tau 0 (x.1 0, x.2 0) (y.1 0, y.2 0) := by simp [productProbe]

/-- Sanity: commuting zero matrices have zero invariant. -/
example : chi 0 0 = 0 := by simp [chi]

/-- Sanity: p=1 removes the white-noise term. -/
example (d : ℕ) : isotropic d 1 = pureDensity (omega d) := by simp [isotropic]

end QAlgorithms.Papers.Independent.Information100.P60


