-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56
-- name    : QAlgorithms_Papers_Independent_Information100_P56
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T12:11:56.825925+00:00
-- url     : https://prove2.me/theorems/dab1cdb6-7c48-4853-8eb6-8876827ed941
-- title:
--   Definitions for From Symmetry to Secrecy: Covariant Classical--Quantum Wiretap Channels
-- statement:
--   The objects the formalized statements of *From Symmetry to Secrecy: Covariant Classical--Quantum Wiretap Channels* (arXiv:2610.03580) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsLaw`: Probability vectors on a finite alphabet (paper p.3).
--   - `IsWiretap`: Finite cq wiretap outputs, each positive semidefinite and of trace one (p.3).
--   - `entropy`: Natural von Neumann entropy: the continuous spectral function `-x log x`, including its value zero at a zero eigenvalue (p.3).
--   - `average`: Average output of a cq channel (p.5, Eq.(8)).
--   - `holevo`: The Holevo information of a finite ensemble (pp.3,7).
--   - `delta`: The entropy difference of the two average outputs (p.5, Eq.(9)).
--   - `Encoder`: A finite auxiliary distribution and a stochastic input encoder. Zero-weight auxiliaries are allowed, and their conditional laws can be chosen arbitrarily (p.5, Eq.(12)).
--   - `encoderValue`: Private information of the actual cq ensembles produced by a finite encoder (p.5).
--   - `privateInfo`: Supremum over every finite auxiliary and every stochastic encoder (p.5, Eq.(12)). For nonempty finite alphabets and density outputs the value set is nonempty and bounded: constant auxiliaries attain zero and Holevo information is at most log output dimension.
--   - `productOutput`: Physical product outputs, with arbitrary correlations still allowed in the input law (p.5).
--   - `blockPrivate`: The n-use private information, unnormalized by n (p.5, Eq.(12)).
--   - `translate`: Left translation, with exactly the order in Eq.(6), p.4.
--   - `convolution`: Ordered convolution of the independent outer variable and noise (p.5, Eq.(7)).
--   - `uniform`: Uniform law, used only on a nonempty finite alphabet (p.3).
--   - `ProjectiveRep`: Possibly projective unitary representations. The phases have modulus one and cancel under conjugation; no irreducibility or commutativity is required (pp.3–4).
--   - `orbit`: Seed orbit channel (p.4, Eq.(5)).
--   - `translatedValue`: Private information of the specified translated-noise joint law `P(v,x)=P3(v)P1(v⁻¹x)` (pp.6–7, Eqs.(15)–(16)).
--   - `IntervalDecomposition`: Finite convex decompositions with the source's mean constraint (p.6).
--   - `convexEnvelope`: The lower convex envelope, computed from all finite convex decompositions (p.6). For continuous f on [0,1] and x in that interval, this is a nonempty bounded infimum.
--   - `bernoulli`: Bernoulli law: x is the probability of symbol 1 (p.6).
--   - `binaryDelta`: Binary-input entropy difference as a function of the prior (p.6).
--   - `hybridBob`: The binary symmetric channel, as diagonal quantum states (p.14, Eqs.(49)–(50)).
--   - `hybridEve`: Eve's pure binary outputs. The first basis coordinate is sqrt(q') (p.14).
--   - `binaryConvolution`: Binary convolution x star q (p.14).
--   - `hybridFormula`: Formula (52), p.15, in nats, with the factor 16 intact.
--   - `diagonalDelta`: The source's diagonal-line change of variable (p.23, Eqs.(78)–(79)).
--   - `inverseTanh`: Real inverse hyperbolic tangent on (-1,1); explicit logarithmic formula (p.23).
--   - `physicalNoise`: Independent physical Bernoulli flips on n bits (p.17).
--   - `prefixedNoise`: Independent logical flip followed by independent physical flips (p.17, Eq.(62)).
--   - `repetitionOuter`: Uniform law on the two repetition words, used with n>=1 (p.17).
--   - `xorConvolution`: XOR convolution for bit strings, with no Fourier normalization factor (pp.16–17).
--   - `hybridBlockDelta`: The hybrid n-use entropy difference (p.15, Eq.(55)).
--   - `repetitionRate`: Prefixed repetition rate per physical channel use (p.17, Eq.(63)).
--   - `walsh`: Unnormalized Walsh coefficients of a probability distribution (p.16, Eq.(58)).
--   - `eveWeight`: Product pure-state basis weights, including zero weights at the endpoints (p.16).
--   - `repetitionOutput`: Physical repetition-preprocessed channel, with arbitrary logical prior later allowed (p.18).
--   - `repetitionZero`: The uniform logical benchmark (p.17, Eq.(66)).
--   - `repetitionLogical`: The benchmark allowing a symmetric logical flip (p.18, Eq.(69)).
--   - `repetitionFull`: Full private information after repetition; the auxiliary is unrestricted (p.18, Eq.(71)).
--   - `fourWeight`: Exact decimal weight profile of Eq.(75), p.20.
--   - `factorialMoment`: Normalized factorial moments E[choose(K,j)]/choose(4,j), p.20.
--   - `binomialFour`: Binomial distribution on the four-use Hamming weight (p.20).
--   - `witnessNoise`: Witness noise P1 in binary-integer order (p.22, Eq.(76)).
--   - `witnessOuter`: Witness outer law on the coset {01,10}, not the repetition subgroup (p.22).
--   - `witnessRate`: Certified witness rate per physical use (p.22, Eq.(77)).
--   - `normalizedChoi`: Normalized Choi matrix in the preferred basis, reference first (p.26, Eq.(A1)).
--   - `ensembleLeakage`: Uniform-message full trace-norm leakage, equivalently the sum of the cq diagonal blocks' trace norms (p.8). The Eve marginal is recomputed from the supplied prior.
--   - `PrivateCode`: General randomized private code, selected before the secret message (pp.8–11).
--   - `privateError`: Uniform-message average decoding error of a private code (p.8).
--   - `privateLeakage`: Strong-secrecy leakage of a private code for a uniform message (p.8).
--   - `AchievableRate`: Operational achievable rate in nats per physical use, with uniform messages, vanishing average error and full trace-norm leakage (pp.10–11).
--   - `BalancedHash`: Balanced universal2 public hashing, including positive message, fiber and seed sizes. Every hash has exactly L elements in each fiber and seed averaging is uniform (p.8).
--   - `hashedOutput`: Eve's conditional hashed-message output. The draw in the fiber is uniform and the product induced outputs implement independent P1-randomization at every position (pp.8–9).
--   - `hashLeakage`: Full trace-norm leakage for a fixed public seed (pp.8–9).
--   - `expectedLeakage`: Leakage averaged over an independent uniform public seed (p.10, Eq.(30)).
--   - `HasType`: Empirical type of every codeword, with N>=1 in all uses (p.8).
--   - `induced`: Sender-randomized output channel (p.8, Eq.(21)).
--   - `sandwichedTrace`: Support-aware sandwiched trace objective (p.9, Eq.(26)). A kernel inclusion failure gives infinity before any negative power is evaluated.
--   - `renyiLog`: Extended logarithm of the sandwiched trace objective for alpha>1 (p.9).
--   - `renyiDivergence`: Sandwiched Renyi divergence, with infinity on support violations (p.9).
--   - `renyiInfo`: cq sandwiched Renyi mutual information: optimize over every density comparison state, including singular states with the support convention (p.9, Eq.(28)).
--   - `renyiJ`: J_alpha(Q) with the FIXED P3-average comparison state; the sum runs only over supp(P3), so every divergence is finite (p.10, Eq.(31)).
--   - `actionRelation`: The relation whose classes are exactly the left stabilizer cosets (p.4).
--   - `pushJoint`: Push a finite auxiliary/input law through a relabeling, summing over its fibers (p.4).
--   - `cqBlock`: Subnormalized output block of a cq auxiliary/output state (pp.4–5).
--   - `IsIrreducible`: Nontrivial finite-dimensional irreducibility, expressed using invariant complex subspaces of the defining representation (p.12, Eq.(40)).
--   - `Inequivalent`: Inequivalence of two irreducible blocks: there is no nonzero intertwiner (p.12).
--   - `IsIsotypic`: Orthogonal isotypic decomposition, supplied by the source as an assumption (pp.12–13). The embeddings retain arbitrary bases and finite multiplicity spaces; they are not restricted to coordinate subspaces.
--   - `invariantBlocks`: Invariant block form directSum_j (I_dj/dj) tensor A_j (p.13, Remark V.7).
--   - `invariantWeights`: Multiplicity-free invariant states, with scalar probability weights (p.12).
--   - `reverseSandwichedTrace`: Equivalent trace objective written in the order of Eq.(41), with a support guard. Taking kernel powers as zero alone would give a false zero minimum (pp.9,12).
--   - `invariantMinimum`: Minimum of Eq.(41) over probability weights; this infimum is attained (p.12).
--   - `uniformExponent`: Eq.(43), with t=0 assigned its continuous extension 2. The outer exponent is N/(1+t), not N and not 1/(1+t) (p.13).
--   - `cyclicOptimizer`: Positive-support cyclic optimizing weights, Eq.(46), pp.13–14.
--   - `cyclicOutput`: Cyclic diagonal pure-state channel, including the point-mass P1 specialization of Section VI A, pp.13–14.
--   - `cyclicExponent`: Explicit cyclic leakage exponent including the continuous endpoint (p.14, Eq.(47)).
--   - `retained`: The messages retained by the two square-root cutoffs (p.11, Remark V.4).
-- source:
--   From Symmetry to Secrecy: Covariant Classical--Quantum Wiretap Channels, arXiv:2610.03580v1, https://arxiv.org/abs/2610.03580v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_MatrixDistances

/-!
Statements from Hayashi and Salek, arXiv:2610.03580v1.
All information quantities below use natural logarithms. All paper-local definitions have
complete bodies; theorem proofs are deliberately omitted. See the unit's GAPS.json for
nodes deferred because their full interfaces have not been supplied.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P56

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- Probability vectors on a finite alphabet (paper p.3). -/
def IsLaw {X : Type*} [Fintype X] (P : X → ℝ) : Prop :=
  (∀ x, 0 ≤ P x) ∧ ∑ x, P x = 1

/-- Finite cq wiretap outputs, each positive semidefinite and of trace one (p.3). -/
def IsWiretap {X B E : Type*} [Fintype B] [Fintype E]
    (WB : X → Matrix B B ℂ) (WE : X → Matrix E E ℂ) : Prop :=
  (∀ x, QAlgorithms.IsDensityMatrix (WB x)) ∧
    (∀ x, QAlgorithms.IsDensityMatrix (WE x))

/-- Natural von Neumann entropy: the continuous spectral function `-x log x`,
including its value zero at a zero eigenvalue (p.3). -/
def entropy {B : Type*} [Fintype B] [DecidableEq B] (rho : Matrix B B ℂ) : ℝ :=
  -(cfc (fun x : ℝ => x * Real.log x) rho).trace.re

/-- Average output of a cq channel (p.5, Eq.(8)). -/
def average {X B : Type*} [Fintype X] (W : X → Matrix B B ℂ) (P : X → ℝ) :
    Matrix B B ℂ :=
  ∑ x, (P x : ℂ) • W x

/-- The Holevo information of a finite ensemble (pp.3,7). -/
def holevo {X B : Type*} [Fintype X] [Fintype B] [DecidableEq B]
    (P : X → ℝ) (W : X → Matrix B B ℂ) : ℝ :=
  entropy (average W P) - ∑ x, P x * entropy (W x)

/-- The entropy difference of the two average outputs (p.5, Eq.(9)). -/
def delta {X B E : Type*} [Fintype X] [Fintype B] [Fintype E]
    [DecidableEq B] [DecidableEq E]
    (WB : X → Matrix B B ℂ) (WE : X → Matrix E E ℂ) (P : X → ℝ) : ℝ :=
  entropy (average WB P) - entropy (average WE P)

/-- A finite auxiliary distribution and a stochastic input encoder. Zero-weight auxiliaries
are allowed, and their conditional laws can be chosen arbitrarily (p.5, Eq.(12)). -/
structure Encoder (X : Type*) [Fintype X] where
  size : ℕ
  positive : 0 < size
  outer : Fin size → ℝ
  outer_law : IsLaw outer
  conditional : Fin size → X → ℝ
  conditional_law : ∀ v, IsLaw (conditional v)

/-- Private information of the actual cq ensembles produced by a finite encoder (p.5). -/
def encoderValue {X B E : Type*} [Fintype X] [Fintype B] [Fintype E]
    [DecidableEq B] [DecidableEq E]
    (WB : X → Matrix B B ℂ) (WE : X → Matrix E E ℂ) (A : Encoder X) : ℝ :=
  holevo A.outer (fun v => average WB (A.conditional v)) -
    holevo A.outer (fun v => average WE (A.conditional v))

/-- Supremum over every finite auxiliary and every stochastic encoder (p.5, Eq.(12)).
For nonempty finite alphabets and density outputs the value set is nonempty and bounded:
constant auxiliaries attain zero and Holevo information is at most log output dimension. -/
def privateInfo {X B E : Type*} [Fintype X] [Fintype B] [Fintype E]
    [DecidableEq B] [DecidableEq E]
    (WB : X → Matrix B B ℂ) (WE : X → Matrix E E ℂ) : ℝ :=
  sSup (Set.range (encoderValue WB WE))

/-- Physical product outputs, with arbitrary correlations still allowed in the input law (p.5). -/
def productOutput {X B : Type*} (n : ℕ) (W : X → Matrix B B ℂ)
    (x : Fin n → X) : Matrix (Fin n → B) (Fin n → B) ℂ :=
  fun j k => ∏ i, W (x i) (j i) (k i)

/-- The n-use private information, unnormalized by n (p.5, Eq.(12)). -/
def blockPrivate {X B E : Type*} [Fintype X] [Fintype B] [Fintype E]
    [DecidableEq B] [DecidableEq E] (n : ℕ)
    (WB : X → Matrix B B ℂ) (WE : X → Matrix E E ℂ) : ℝ :=
  privateInfo (productOutput n WB) (productOutput n WE)

/-- Left translation, with exactly the order in Eq.(6), p.4. -/
def translate {G : Type*} [Group G] (v : G) (P : G → ℝ) : G → ℝ :=
  fun x => P (v⁻¹ * x)

/-- Ordered convolution of the independent outer variable and noise (p.5, Eq.(7)). -/
def convolution {G : Type*} [Group G] [Fintype G] (P3 P1 : G → ℝ) : G → ℝ :=
  fun x => ∑ v, P3 v * P1 (v⁻¹ * x)

/-- Uniform law, used only on a nonempty finite alphabet (p.3). -/
def uniform {X : Type*} [Fintype X] : X → ℝ :=
  fun _ => (Fintype.card X : ℝ)⁻¹

/-- Possibly projective unitary representations. The phases have modulus one and cancel
under conjugation; no irreducibility or commutativity is required (pp.3–4). -/
structure ProjectiveRep (G B : Type*) [Group G] [Fintype B] [DecidableEq B] where
  unitary : G → Matrix.unitaryGroup B ℂ
  phase : G → G → ℂ
  phase_norm : ∀ g h, ‖phase g h‖ = 1
  mul_phase : ∀ g h,
    (unitary (g * h) : Matrix B B ℂ) =
      phase g h • ((unitary g : Matrix B B ℂ) * (unitary h : Matrix B B ℂ))

/-- Seed orbit channel (p.4, Eq.(5)). -/
def orbit {G B : Type*} [Group G] [Fintype B] [DecidableEq B]
    (U : ProjectiveRep G B) (rho : Matrix B B ℂ) (g : G) : Matrix B B ℂ :=
  (U.unitary g : Matrix B B ℂ) * rho * (U.unitary g : Matrix B B ℂ)ᴴ

/-- Private information of the specified translated-noise joint law
`P(v,x)=P3(v)P1(v⁻¹x)` (pp.6–7, Eqs.(15)–(16)). -/
def translatedValue {G B E : Type*} [Group G] [Fintype G]
    [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]
    (WB : G → Matrix B B ℂ) (WE : G → Matrix E E ℂ) (P1 P3 : G → ℝ) : ℝ :=
  holevo P3 (fun v => average WB (translate v P1)) -
    holevo P3 (fun v => average WE (translate v P1))

/-- Finite convex decompositions with the source's mean constraint (p.6). -/
structure IntervalDecomposition (x : ℝ) where
  size : ℕ
  positive : 0 < size
  weight : Fin size → ℝ
  weight_law : IsLaw weight
  point : Fin size → ℝ
  point_mem : ∀ v, point v ∈ Set.Icc (0 : ℝ) 1
  mean : ∑ v, weight v * point v = x

/-- The lower convex envelope, computed from all finite convex decompositions (p.6).
For continuous f on [0,1] and x in that interval, this is a nonempty bounded infimum. -/
def convexEnvelope (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  sInf (Set.range (fun D : IntervalDecomposition x => ∑ v, D.weight v * f (D.point v)))

/-- Bernoulli law: x is the probability of symbol 1 (p.6). -/
def bernoulli (x : ℝ) : Bool → ℝ :=
  fun b => if b then x else 1 - x

/-- Binary-input entropy difference as a function of the prior (p.6). -/
def binaryDelta {B E : Type*} [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]
    (WB : Bool → Matrix B B ℂ) (WE : Bool → Matrix E E ℂ) (x : ℝ) : ℝ :=
  delta WB WE (bernoulli x)

/-- The binary symmetric channel, as diagonal quantum states (p.14, Eqs.(49)–(50)). -/
def hybridBob (q : ℝ) (x : Bool) : Matrix Bool Bool ℂ :=
  Matrix.diagonal (fun y => ((if y = x then 1 - q else q : ℝ) : ℂ))

/-- Eve's pure binary outputs. The first basis coordinate is sqrt(q') (p.14). -/
def hybridEve (qprime : ℝ) (x : Bool) : Matrix Bool Bool ℂ :=
  let psi : Bool → ℂ := fun j =>
    if j then (if x then -1 else 1) * (Real.sqrt (1 - qprime) : ℂ)
    else (Real.sqrt qprime : ℂ)
  fun j k => psi j * conj (psi k)

/-- Binary convolution x star q (p.14). -/
def binaryConvolution (x q : ℝ) : ℝ := x * (1 - q) + (1 - x) * q

/-- Formula (52), p.15, in nats, with the factor 16 intact. -/
def hybridFormula (q qprime x : ℝ) : ℝ :=
  Real.binEntropy (binaryConvolution x q) -
    Real.binEntropy ((1 - Real.sqrt (1 - 16 * qprime * (1 - qprime) * x * (1 - x))) / 2)

/-- The source's diagonal-line change of variable (p.23, Eqs.(78)–(79)). -/
def diagonalDelta (p z : ℝ) : ℝ :=
  let a := 1 - 2 * p
  let u := a ^ 2
  let k := 1 - u
  Real.binEntropy ((1 + a * z) / 2) -
    Real.binEntropy ((1 + Real.sqrt (u + k * z ^ 2)) / 2)

/-- Real inverse hyperbolic tangent on (-1,1); explicit logarithmic formula (p.23). -/
def inverseTanh (r : ℝ) : ℝ := (Real.log (1 + r) - Real.log (1 - r)) / 2

/-- Independent physical Bernoulli flips on n bits (p.17). -/
def physicalNoise (n : ℕ) (lambda : ℝ) : QAlgorithms.Qubits n → ℝ :=
  fun z => ∏ i, bernoulli lambda (z i)

/-- Independent logical flip followed by independent physical flips (p.17, Eq.(62)). -/
def prefixedNoise (n : ℕ) (lambda mu : ℝ) : QAlgorithms.Qubits n → ℝ :=
  fun z => (1 - mu) * physicalNoise n lambda z + mu * physicalNoise n (1 - lambda) z

/-- Uniform law on the two repetition words, used with n>=1 (p.17). -/
def repetitionOuter (n : ℕ) : QAlgorithms.Qubits n → ℝ :=
  fun z => if z = (fun _ => false) ∨ z = (fun _ => true) then 1 / 2 else 0

/-- XOR convolution for bit strings, with no Fourier normalization factor (pp.16–17). -/
def xorConvolution {n : ℕ} (P Q : QAlgorithms.Qubits n → ℝ) : QAlgorithms.Qubits n → ℝ :=
  fun x => ∑ v, P v * Q (fun i => Bool.xor (v i) (x i))

/-- The hybrid n-use entropy difference (p.15, Eq.(55)). -/
def hybridBlockDelta (n : ℕ) (q qprime : ℝ) (P : QAlgorithms.Qubits n → ℝ) : ℝ :=
  delta (productOutput n (hybridBob q)) (productOutput n (hybridEve qprime)) P

/-- Prefixed repetition rate per physical channel use (p.17, Eq.(63)). -/
def repetitionRate (n : ℕ) (q qprime lambda mu : ℝ) : ℝ :=
  (hybridBlockDelta n q qprime
    (xorConvolution (repetitionOuter n) (prefixedNoise n lambda mu)) -
      hybridBlockDelta n q qprime (prefixedNoise n lambda mu)) / n

/-- Unnormalized Walsh coefficients of a probability distribution (p.16, Eq.(58)). -/
def walsh {n : ℕ} (P : QAlgorithms.Qubits n → ℝ) (d : QAlgorithms.Qubits n) : ℝ :=
  ∑ g, P g * (if QAlgorithms.dotBits g d then -1 else 1)

/-- Product pure-state basis weights, including zero weights at the endpoints (p.16). -/
def eveWeight (n : ℕ) (qprime : ℝ) (j : QAlgorithms.Qubits n) : ℝ :=
  qprime ^ (n - QAlgorithms.hammingWeight j) * (1 - qprime) ^ QAlgorithms.hammingWeight j

/-- Physical repetition-preprocessed channel, with arbitrary logical prior later allowed (p.18). -/
def repetitionOutput {B : Type*} [Fintype B] (n : ℕ)
    (W : Bool → Matrix B B ℂ) (lambda : ℝ) (u : Bool) :
    Matrix (Fin n → B) (Fin n → B) ℂ :=
  average (productOutput n W) (fun z => physicalNoise n lambda (fun i => Bool.xor u (z i)))

/-- The uniform logical benchmark (p.17, Eq.(66)). -/
def repetitionZero (n : ℕ) (p : ℝ) : ℝ :=
  sSup ((fun lambda => repetitionRate n p p lambda 0) '' Set.Icc (0 : ℝ) (1 / 2))

/-- The benchmark allowing a symmetric logical flip (p.18, Eq.(69)). -/
def repetitionLogical (n : ℕ) (p : ℝ) : ℝ :=
  sSup {r | ∃ lambda ∈ Set.Icc (0 : ℝ) (1 / 2), ∃ mu ∈ Set.Icc (0 : ℝ) (1 / 2),
    r = repetitionRate n p p lambda mu}

/-- Full private information after repetition; the auxiliary is unrestricted (p.18, Eq.(71)). -/
def repetitionFull (n : ℕ) (p : ℝ) : ℝ :=
  sSup ((fun lambda => privateInfo
    (repetitionOutput n (hybridBob p) lambda)
    (repetitionOutput n (hybridEve p) lambda) / n) '' Set.Icc (0 : ℝ) (1 / 2))

/-- Exact decimal weight profile of Eq.(75), p.20. -/
def fourWeight (j : Fin 5) : ℝ :=
  (![23089, 33839, 27248, 11757, 4067] j : ℝ) / 100000

/-- Normalized factorial moments E[choose(K,j)]/choose(4,j), p.20. -/
def factorialMoment (j : ℕ) : ℝ :=
  (∑ k : Fin 5, fourWeight k * (Nat.choose k.val j : ℝ)) / (Nat.choose 4 j : ℝ)

/-- Binomial distribution on the four-use Hamming weight (p.20). -/
def binomialFour (theta : ℝ) (k : Fin 5) : ℝ :=
  (Nat.choose 4 k.val : ℝ) * theta ^ k.val * (1 - theta) ^ (4 - k.val)

/-- Witness noise P1 in binary-integer order (p.22, Eq.(76)). -/
def witnessNoise (z : QAlgorithms.Qubits 2) : ℝ :=
  (![364, 217, 217, 202] (QAlgorithms.bitsEquivFin 2 z) : ℝ) / 1000

/-- Witness outer law on the coset {01,10}, not the repetition subgroup (p.22). -/
def witnessOuter (z : QAlgorithms.Qubits 2) : ℝ :=
  (![0, 1, 1, 0] (QAlgorithms.bitsEquivFin 2 z) : ℝ) / 2

/-- Certified witness rate per physical use (p.22, Eq.(77)). -/
def witnessRate : ℝ :=
  (hybridBlockDelta 2 (621 / 5000) (621 / 5000) (xorConvolution witnessOuter witnessNoise) -
    hybridBlockDelta 2 (621 / 5000) (621 / 5000) witnessNoise) / 2

/-- Normalized Choi matrix in the preferred basis, reference first (p.26, Eq.(A1)). -/
def normalizedChoi {A B : Type*} [Fintype A] [DecidableEq A]
    (N : QAlgorithms.Superop A B) : Matrix (A × B) (A × B) ℂ :=
  fun ab cd => N (Matrix.single ab.1 cd.1 1) ab.2 cd.2 / (Fintype.card A : ℂ)

/-! Sanity examples pin normalization, ordering and boundary behavior without theorem proofs. -/

example : bernoulli 0 false = 1 ∧ bernoulli 0 true = 0 := by
  norm_num [bernoulli]

example : hybridBob 0 false false false = 1 := by
  norm_num [hybridBob]

example : hybridEve 0 false false false = 0 := by
  simp [hybridEve]

example : physicalNoise 0 (1 / 3) (fun i => Fin.elim0 i) = 1 := by
  simp [physicalNoise]

example : fourWeight 0 = (23089 : ℝ) / 100000 := rfl

example {G : Type*} [Group G] (P : G → ℝ) : translate 1 P = P := by
  funext x
  simp [translate]

example {X B : Type*} [Fintype X] (W : X → Matrix B B ℂ) :
    average W (fun _ => 0) = 0 := by
  simp [average]

/-- Uniform-message full trace-norm leakage, equivalently the sum of the cq diagonal
blocks' trace norms (p.8). The Eve marginal is recomputed from the supplied prior. -/
def ensembleLeakage {M E : Type*} [Fintype M] [Fintype E] [DecidableEq E]
    (P : M → ℝ) (W : M → Matrix E E ℂ) : ℝ :=
  ∑ m, P m * QAlgorithms.traceNorm (W m - average W P)

/-- General randomized private code, selected before the secret message (pp.8–11). -/
structure PrivateCode (X B : Type*) [Fintype X] [Fintype B] [DecidableEq B] (n : ℕ) where
  messages : ℕ
  positive : 0 < messages
  input : Fin messages → (Fin n → X) → ℝ
  input_law : ∀ m, IsLaw (input m)
  decoder : Fin messages → Matrix (Fin n → B) (Fin n → B) ℂ
  decoder_povm : QAlgorithms.IsPOVM decoder

/-- Uniform-message average decoding error of a private code (p.8). -/
def privateError {X B : Type*} [Fintype X] [Fintype B] [DecidableEq B] {n : ℕ}
    (WB : X → Matrix B B ℂ) (C : PrivateCode X B n) : ℝ :=
  1 - ∑ m, (C.messages : ℝ)⁻¹ *
    QAlgorithms.effectProb (C.decoder m) (average (productOutput n WB) (C.input m))

/-- Strong-secrecy leakage of a private code for a uniform message (p.8). -/
def privateLeakage {X B E : Type*} [Fintype X] [Fintype B] [DecidableEq B]
    [Fintype E] [DecidableEq E] {n : ℕ}
    (WE : X → Matrix E E ℂ) (C : PrivateCode X B n) : ℝ :=
  ensembleLeakage uniform (fun m => average (productOutput n WE) (C.input m))

/-- Operational achievable rate in nats per physical use, with uniform messages,
vanishing average error and full trace-norm leakage (pp.10–11). -/
def AchievableRate {X B E : Type*} [Fintype X] [Fintype B] [DecidableEq B]
    [Fintype E] [DecidableEq E]
    (WB : X → Matrix B B ℂ) (WE : X → Matrix E E ℂ) (R : ℝ) : Prop :=
  ∃ C : (n : ℕ) → PrivateCode X B n,
    (∀ eps : ℝ, 0 < eps → ∀ᶠ n in Filter.atTop,
      R - eps ≤ Real.log ((C n).messages : ℝ) / n) ∧
    Filter.Tendsto (fun n => privateError WB (C n)) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun n => privateLeakage WE (C n)) Filter.atTop (nhds 0)

/-- Balanced universal2 public hashing, including positive message, fiber and seed sizes.
Every hash has exactly L elements in each fiber and seed averaging is uniform (p.8). -/
structure BalancedHash (K M L : ℕ) where
  index_positive : 0 < K
  message_positive : 0 < M
  fiber_positive : 0 < L
  factorization : K = M * L
  seeds : ℕ
  seeds_positive : 0 < seeds
  hash : Fin seeds → Fin K → Fin M
  balanced : ∀ s m, (Finset.univ.filter (fun k => hash s k = m)).card = L
  universal : ∀ k l, k ≠ l →
    ((Finset.univ.filter (fun s => hash s k = hash s l)).card : ℝ) / seeds ≤ (M : ℝ)⁻¹

/-- Eve's conditional hashed-message output. The draw in the fiber is uniform and the
product induced outputs implement independent P1-randomization at every position (pp.8–9). -/
def hashedOutput {G E : Type*} [Fintype E] [DecidableEq E]
    {N K M L : ℕ} (H : BalancedHash K M L)
    (phi : Fin K → Fin N → G) (omega : G → Matrix E E ℂ)
    (s : Fin H.seeds) (m : Fin M) : Matrix (Fin N → E) (Fin N → E) ℂ :=
  (L : ℂ)⁻¹ • ∑ k, if H.hash s k = m then productOutput N omega (phi k) else 0

/-- Full trace-norm leakage for a fixed public seed (pp.8–9). -/
def hashLeakage {G E : Type*} [Fintype E] [DecidableEq E]
    {N K M L : ℕ} (H : BalancedHash K M L)
    (phi : Fin K → Fin N → G) (omega : G → Matrix E E ℂ) (s : Fin H.seeds) : ℝ :=
  ensembleLeakage uniform (hashedOutput H phi omega s)

/-- Leakage averaged over an independent uniform public seed (p.10, Eq.(30)). -/
def expectedLeakage {G E : Type*} [Fintype E] [DecidableEq E]
    {N K M L : ℕ} (H : BalancedHash K M L)
    (phi : Fin K → Fin N → G) (omega : G → Matrix E E ℂ) : ℝ :=
  ∑ s, (H.seeds : ℝ)⁻¹ * hashLeakage H phi omega s

/-- Empirical type of every codeword, with N>=1 in all uses (p.8). -/
def HasType {G : Type*} [DecidableEq G] {N K : ℕ}
    (phi : Fin K → Fin N → G) (Q : G → ℝ) : Prop :=
  ∀ m v, ((Finset.univ.filter (fun j => phi m j = v)).card : ℝ) / N = Q v

/-- Sender-randomized output channel (p.8, Eq.(21)). -/
def induced {G B : Type*} [Group G] [Fintype G]
    (W : G → Matrix B B ℂ) (P1 : G → ℝ) (v : G) : Matrix B B ℂ :=
  average W (translate v P1)

/-- Support-aware sandwiched trace objective (p.9, Eq.(26)).
A kernel inclusion failure gives infinity before any negative power is evaluated. -/
def sandwichedTrace {E : Type*} [Fintype E] [DecidableEq E]
    (alpha : ℝ) (rho sigma : Matrix E E ℂ) : ENNReal :=
  if LinearMap.ker sigma.mulVecLin ≤ LinearMap.ker rho.mulVecLin then
    let S := cfc (fun x : ℝ => if x = 0 then 0 else Real.rpow x ((1 - alpha) / (2 * alpha))) sigma
    ENNReal.ofReal ((cfc (fun x : ℝ => Real.rpow x alpha) (S * rho * S)).trace.re)
  else ⊤

/-- Extended logarithm of the sandwiched trace objective for alpha>1 (p.9). -/
def renyiLog (alpha : ℝ) (q : ENNReal) : ENNReal :=
  if q = ⊤ then ⊤ else ENNReal.ofReal (Real.log q.toReal / (alpha - 1))

/-- Sandwiched Renyi divergence, with infinity on support violations (p.9). -/
def renyiDivergence {E : Type*} [Fintype E] [DecidableEq E]
    (alpha : ℝ) (rho sigma : Matrix E E ℂ) : ENNReal :=
  renyiLog alpha (sandwichedTrace alpha rho sigma)

/-- cq sandwiched Renyi mutual information: optimize over every density comparison
state, including singular states with the support convention (p.9, Eq.(28)). -/
def renyiInfo {X E : Type*} [Fintype X] [Fintype E] [DecidableEq E]
    (alpha : ℝ) (P : X → ℝ) (W : X → Matrix E E ℂ) : ENNReal :=
  renyiLog alpha (sInf {q | ∃ sigma : Matrix E E ℂ, QAlgorithms.IsDensityMatrix sigma ∧
    q = ∑ x, if P x = 0 then 0 else ENNReal.ofReal (P x) * sandwichedTrace alpha (W x) sigma})

/-- J_alpha(Q) with the FIXED P3-average comparison state; the sum runs only over
supp(P3), so every divergence is finite (p.10, Eq.(31)). -/
def renyiJ {G E : Type*} [Fintype G] [Fintype E] [DecidableEq E]
    (alpha : ℝ) (P3 Q : G → ℝ) (omega : G → Matrix E E ℂ) : ℝ :=
  ∑ v ∈ Finset.univ.filter (fun v => 0 < P3 v),
    Q v * (renyiDivergence alpha (omega v) (average omega P3)).toReal

/-- The relation whose classes are exactly the left stabilizer cosets (p.4). -/
def actionRelation {G X : Type*} [Group G] [MulAction G X] (x0 : X) : Setoid G where
  r g h := g • x0 = h • x0
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩

/-- Push a finite auxiliary/input law through a relabeling, summing over its fibers (p.4). -/
def pushJoint {V X Y : Type*} [Fintype X] [DecidableEq Y]
    (f : X → Y) (J : V × X → ℝ) : V × Y → ℝ :=
  fun vy => ∑ x, if f x = vy.2 then J (vy.1, x) else 0

/-- Subnormalized output block of a cq auxiliary/output state (pp.4–5). -/
def cqBlock {V X B : Type*} [Fintype X]
    (W : X → Matrix B B ℂ) (J : V × X → ℝ) (v : V) : Matrix B B ℂ :=
  ∑ x, (J (v, x) : ℂ) • W x

example {E : Type*} [Fintype E] [DecidableEq E]
    (alpha : ℝ) (rho sigma : Matrix E E ℂ)
    (h : ¬ LinearMap.ker sigma.mulVecLin ≤ LinearMap.ker rho.mulVecLin) :
    sandwichedTrace alpha rho sigma = ⊤ := by
  simp [sandwichedTrace, h]

example {G X : Type*} [Group G] [MulAction G X] (x0 : X) (g : G) :
    (actionRelation x0).r g g := rfl

example {B : Type*} [Fintype B] [DecidableEq B] :
    QAlgorithms.traceNorm (0 : Matrix B B ℂ) = 0 := by
  simp [QAlgorithms.traceNorm, cfc_zero]

/-- Nontrivial finite-dimensional irreducibility, expressed using invariant complex
subspaces of the defining representation (p.12, Eq.(40)). -/
def IsIrreducible {G : Type*} [Group G] {d : ℕ} (U : ProjectiveRep G (Fin d)) : Prop :=
  0 < d ∧ ∀ S : Submodule ℂ (Fin d → ℂ),
    (∀ g v, v ∈ S → Matrix.mulVec (U.unitary g : Matrix (Fin d) (Fin d) ℂ) v ∈ S) →
      S = ⊥ ∨ S = ⊤

/-- Inequivalence of two irreducible blocks: there is no nonzero intertwiner (p.12). -/
def Inequivalent {G : Type*} [Group G] {d e : ℕ}
    (U : ProjectiveRep G (Fin d)) (V : ProjectiveRep G (Fin e)) : Prop :=
  ∀ A : Matrix (Fin d) (Fin e) ℂ,
    (∀ g, (U.unitary g : Matrix (Fin d) (Fin d) ℂ) * A =
      A * (V.unitary g : Matrix (Fin e) (Fin e) ℂ)) → A = 0

/-- Orthogonal isotypic decomposition, supplied by the source as an assumption (pp.12–13).
The embeddings retain arbitrary bases and finite multiplicity spaces; they are not
restricted to coordinate subspaces. -/
def IsIsotypic {G E J : Type*} [Group G] [Fintype E] [DecidableEq E] [Fintype J]
    (U : ProjectiveRep G E) (d m : J → ℕ)
    (R : (j : J) → ProjectiveRep G (Fin (d j)))
    (T : (j : J) → Matrix E (Fin (d j) × Fin (m j)) ℂ) : Prop :=
  (∀ j, 0 < m j ∧ IsIrreducible (R j)) ∧
  (∀ j k, j ≠ k → Inequivalent (R j) (R k)) ∧
  (∀ j, (T j)ᴴ * T j = 1) ∧
  (∀ j k, j ≠ k → (T j)ᴴ * T k = 0) ∧
  (∑ j, T j * (T j)ᴴ = 1) ∧
  (∀ g j, (U.unitary g : Matrix E E ℂ) * T j =
    T j * Matrix.kronecker ((R j).unitary g : Matrix (Fin (d j)) (Fin (d j)) ℂ)
      (1 : Matrix (Fin (m j)) (Fin (m j)) ℂ))

/-- Invariant block form directSum_j (I_dj/dj) tensor A_j (p.13, Remark V.7). -/
def invariantBlocks {E J : Type*} [Fintype E] [Fintype J]
    (d m : J → ℕ) (T : (j : J) → Matrix E (Fin (d j) × Fin (m j)) ℂ)
    (A : (j : J) → Matrix (Fin (m j)) (Fin (m j)) ℂ) : Matrix E E ℂ :=
  ∑ j, T j * Matrix.kronecker
    ((d j : ℂ)⁻¹ • (1 : Matrix (Fin (d j)) (Fin (d j)) ℂ)) (A j) * (T j)ᴴ

/-- Multiplicity-free invariant states, with scalar probability weights (p.12). -/
def invariantWeights {E J : Type*} [Fintype E] [Fintype J]
    (d : J → ℕ) (T : (j : J) → Matrix E (Fin (d j) × Fin 1) ℂ)
    (P : J → ℝ) : Matrix E E ℂ :=
  ∑ j, ((P j : ℂ) / (d j : ℂ)) • (T j * (T j)ᴴ)

/-- Equivalent trace objective written in the order of Eq.(41), with a support guard.
Taking kernel powers as zero alone would give a false zero minimum (pp.9,12). -/
def reverseSandwichedTrace {E : Type*} [Fintype E] [DecidableEq E]
    (alpha : ℝ) (rho sigma : Matrix E E ℂ) : ENNReal :=
  if LinearMap.ker sigma.mulVecLin ≤ LinearMap.ker rho.mulVecLin then
    let A := cfc Real.sqrt rho
    let S := cfc (fun x : ℝ => if x = 0 then 0 else Real.rpow x ((1 - alpha) / alpha)) sigma
    ENNReal.ofReal ((cfc (fun x : ℝ => Real.rpow x alpha) (A * S * A)).trace.re)
  else ⊤

/-- Minimum of Eq.(41) over probability weights; this infimum is attained (p.12). -/
def invariantMinimum {E J : Type*} [Fintype E] [DecidableEq E] [Fintype J]
    (d : J → ℕ) (T : (j : J) → Matrix E (Fin (d j) × Fin 1) ℂ)
    (alpha : ℝ) (tau : Matrix E E ℂ) : ENNReal :=
  sInf {q | ∃ P : J → ℝ, IsLaw P ∧
    q = reverseSandwichedTrace alpha tau (invariantWeights d T P)}

/-- Eq.(43), with t=0 assigned its continuous extension 2. The outer exponent is
N/(1+t), not N and not 1/(1+t) (p.13). -/
def uniformExponent {E J : Type*} [Fintype E] [DecidableEq E] [Fintype J]
    (d : J → ℕ) (T : (j : J) → Matrix E (Fin (d j) × Fin 1) ℂ)
    (tau : Matrix E E ℂ) (N L : ℕ) (t : ℝ) : ℝ :=
  if t = 0 then 2 else
    Real.rpow 2 ((1 - t) / (1 + t)) * Real.exp (-t * Real.log L / (1 + t)) *
      Real.rpow (invariantMinimum d T (1 + t) tau).toReal ((N : ℝ) / (1 + t))

/-- Positive-support cyclic optimizing weights, Eq.(46), pp.13–14. -/
def cyclicOptimizer {d : ℕ} (q : Fin d → ℝ) (t : ℝ) : Fin d → ℝ :=
  fun j => Real.rpow (q j) ((1 + t) / (1 + 2 * t)) /
    ∑ k, Real.rpow (q k) ((1 + t) / (1 + 2 * t))

/-- Cyclic diagonal pure-state channel, including the point-mass P1 specialization
of Section VI A, pp.13–14. -/
def cyclicOutput {d : ℕ} (q : Fin d → ℝ) (x : ZMod d) : Matrix (Fin d) (Fin d) ℂ :=
  fun j k => (Real.sqrt (q j) : ℂ) * (Real.sqrt (q k) : ℂ) *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((j.val : ℂ) - (k.val : ℂ)) *
      (x.val : ℂ) / (d : ℂ))

/-- Explicit cyclic leakage exponent including the continuous endpoint (p.14, Eq.(47)). -/
def cyclicExponent {d : ℕ} (q : Fin d → ℝ) (N L : ℕ) (t : ℝ) : ℝ :=
  if t = 0 then 2 else Real.rpow 2 ((1 - t) / (1 + t)) *
    Real.exp (-t * Real.log L / (1 + t)) *
    Real.rpow (∑ j, Real.rpow (q j) ((1 + t) / (1 + 2 * t)))
      ((N : ℝ) * (1 + 2 * t) / (1 + t))

/-- The messages retained by the two square-root cutoffs (p.11, Remark V.4). -/
def retained {M E : Type*} [Fintype M] [Fintype E] [DecidableEq E]
    (err : M → ℝ) (W : M → Matrix E E ℂ) : Finset M :=
  Finset.univ.filter (fun m =>
    err m ≤ Real.sqrt (∑ k, uniform k * err k) ∧
    QAlgorithms.traceNorm (W m - average W uniform) ≤ Real.sqrt (ensembleLeakage uniform W))

example {d : ℕ} (q : Fin d → ℝ) (N L : ℕ) : cyclicExponent q N L 0 = 2 := by
  simp [cyclicExponent]

example {E : Type*} [Fintype E] [DecidableEq E]
    (alpha : ℝ) (rho sigma : Matrix E E ℂ)
    (h : ¬ LinearMap.ker sigma.mulVecLin ≤ LinearMap.ker rho.mulVecLin) :
    reverseSandwichedTrace alpha rho sigma = ⊤ := by
  simp [reverseSandwichedTrace, h]

/-- Small normalization checks for the paper-local families. -/
example {B : Type*} [Fintype B] [DecidableEq B] : entropy (1 : Matrix B B ℂ) = 0 := by
  simp [entropy, cfc_one]

example {X B : Type*} [Fintype X] [Fintype B] [DecidableEq B]
    (W : X → Matrix B B ℂ) (P : X → ℝ) : delta W W P = 0 := by
  simp [delta]

example {X B : Type*} [Fintype X] [Fintype B] [DecidableEq B]
    (W : X → Matrix B B ℂ) (A : Encoder X) : encoderValue W W A = 0 := by
  simp [encoderValue]

example {X B : Type*} (W : X → Matrix B B ℂ) (x : Fin 1 → X)
    (j k : Fin 1 → B) : productOutput 1 W x j k = W (x 0) (j 0) (k 0) := by
  simp [productOutput]

example : (uniform : Fin 1 → ℝ) 0 = 1 := by
  norm_num [uniform]

example (n : ℕ) (lambda : ℝ) : prefixedNoise n lambda 0 = physicalNoise n lambda := by
  funext z
  simp [prefixedNoise]

example : inverseTanh 0 = 0 := by
  simp [inverseTanh]

example (q qprime : ℝ) : hybridFormula q qprime 0 = Real.binEntropy q := by
  simp [hybridFormula, binaryConvolution]

example {E J : Type*} [Fintype E] [Fintype J]
    (d : J → ℕ) (T : (j : J) → Matrix E (Fin (d j) × Fin 1) ℂ) :
    invariantWeights d T (fun _ => 0) = 0 := by
  simp [invariantWeights]

end QAlgorithms.Papers.Independent.Information100.P56


