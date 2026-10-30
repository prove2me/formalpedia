-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P27
-- name    : QAlgorithms_Papers_Independent_Extend50_P27
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T20:33:36.653585+00:00
-- url     : https://prove2.me/theorems/0285f9dc-c685-4947-a02b-885b203e91ee
-- title:
--   Definitions for Optimal Port-based Teleportation
-- statement:
--   The objects the formalized statements of *Optimal Port-based Teleportation* (arXiv:1707.08456) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Predecessor`: One-box inclusion, on actual cells (PDF pp.3,5).
--   - `BoxMove`: Moving one box between distinct shapes (PDF pp.5,7).
--   - `removableCount`: Removable corners, counted independently of any height cutoff (PDF p.7).
--   - `teleportEntry`: Definition 3, evaluated on diagrams, independently of any incidence Gram matrix (PDF p.7).
--   - `teleportMatrix`: Definition 10: all shapes of height at most d, with the original diagonal (PDF p.11).
--   - `fullMatrix`: Full matrix, containing all size-N shapes (PDF pp.7,10).
--   - `incidence`: Rectangular physical branching incidence, Definition 18 (PDF p.13).
--   - `columnGram`: Column Gram matrix, Definition 21 (PDF p.14).
--   - `rowGram`: Row Gram matrix, Definition 21 (PDF p.14).
--   - `heightCorrection`: Shape-restricted diagonal correction. The printed height=d in Eq.(54) must be height<d, as Lemma 27 and Eq.(55) require (PDF p.15).
--   - `topValue`: Largest real spectral value. Every use below is on a nonempty finite symmetric matrix; PSD and attainment are conclusions, not fields of this definition (PDF pp.19,27).
--   - `spectralFidelity`: Entanglement-fidelity value singled out by Eq.(78), with one eigenvalue, not its square.
--   - `maxRowSum`: Explicit maximum absolute row sum, the source's norm in Eq.(43) (PDF p.12).
--   - `includePermutation`: Last-letter-fixing embedding S_K into S_(K+1) (PDF pp.5–6).
--   - `irrepDim`: Actual Specht dimension, not an arbitrary shape weight (PDF pp.3–5).
--   - `pbtIntertwinerSpace`: Intertwiners between two actual finite actions. No branching counts are supplied as data; multiplicity is the dimension of this subspace (PDF pp.5,8–9).
--   - `tensorMultiplicity`: Tensor-space multiplicity m_mu, computed by actual intertwiners (PDF pp.3–4).
--   - `restrictedAction`: Restriction of a concrete Specht action to the subgroup fixing the last letter (PDF p.5).
--   - `inducedAction`: Induction in the explicit coset basis of Eqs.(20)–(21); N copies of the actual alpha Specht module, not an array of assumed branching multiplicities (PDF p.6).
--   - `restrictionMultiplicity`: Multiplicity in the restricted Specht module, defined through intertwiners (PDF p.5).
--   - `inductionMultiplicity`: Multiplicity in the explicit induced module, defined through intertwiners (PDF pp.5–6).
--   - `fixedCount`: Number of fixed points, including zero, as in the proof of Lemma 2 (PDF pp.6–7).
--   - `characterTable`: Definition 6 uses literal, unweighted Specht characters (PDF p.9).
--   - `cycleClassCount`: Count of cycle types with exactly k fixed points. Each xi_l is bounded by N; the equation is written without truncated N-k (PDF p.10).
--   - `AliceIndex`: Alice's N local registers.
--   - `SignalIndex`: Alice plus the input register C, with N=K+1.
--   - `liftAlice`: Extend an Alice operator by identity on C (PDF pp.4,16).
--   - `pbtSignal`: Normalized signals sigma_a = d^(-N) V^{t_C}(a,C), Eq.(4) (PDF p.3). The equalities couple a with C on each side; other Alice coordinates are unchanged.
--   - `effectFidelity`: Entanglement fidelity of effective effects, Eq.(57) (PDF p.16).
--   - `PBTPrimalFeasible`: All primal variables; positivity includes Hermiticity. The inequality is a positive-semidefinite difference, not entrywise order (PDF pp.4,16).
--   - `primalValues`: Attainable primal values; no spectral ansatz restricts the variables (PDF p.16).
--   - `pbtOptimalFidelity`: Optimal value of the actual primal program; its greatest element is asserted below, so the real supremum is not used as a substitute for attainment (PDF pp.16–19).
--   - `PBTDualFeasible`: Full dual feasible set, Eq.(80), without the proof's block ansatz (PDF pp.19–20).
--   - `pbtDualObjective`: The Euclidean operator norm in Eq.(79), on a Hermitian positive partial trace. Using the largest real eigenvalue avoids the unrelated maximum row-sum norm.
--   - `pbtDualValues`: Actual dual objective values, Eq.(79) (PDF p.19).
--   - `projectorSeed`: Concrete unnormalized P_alpha tensor tilde P+ seed (PDF p.31, Eq.(145)).
--   - `etaBlock`: Eta(alpha), the explicit sum of transported seeds in Eq.(145) (PDF pp.4,31).
--   - `pbtGammaValue`: Nonzero physical eigenvalue gamma_mu(alpha), Eq.(8) (PDF p.4).
--   - `lambdaValue`: Lambda_mu(alpha)=gamma_mu(alpha)/d^N, Eq.(10) (PDF p.4).
--   - `physicalProjector`: Concrete physical F_mu(alpha), Eq.(145); no projector or spectral identities are assumed as structure fields (PDF p.31). Used only for one-box-compatible labels.
--   - `blockPower`: Spectral power of the physical alpha block, extended by zero off its nonzero support, even at exponent zero or a negative exponent (PDF pp.24,29).
--   - `blockSignal`: Alpha-resolved sigma_a. This is constructed from the seed, not postulated as an eigenspace decomposition (PDF pp.24–25).
--   - `coefficientFilter`: Spectral filter with actual block coefficients p_mu(alpha), Eq.(61) (PDF p.17).
--   - `filterEffects`: Effective effects Pi sigma_a Pi, Eq.(60) (PDF p.17).
--   - `powerEffects`: The general block power-filter effects, Eq.(110). Feasibility is never inferred for arbitrary z,y (PDF pp.24–25).
--   - `contractionConstant`: The scalar contraction coefficient, Eqs.(113),(139) (PDF pp.24,29).
--   - `eprFormula`: Formula (120), with physical labels and actual dimensions (PDF p.26).
--   - `coefficientFidelity`: The scalar expression before maximization in Eq.(68) (PDF p.18).
--   - `IsOptimalVector`: Source-normalized positive Perron vector, with Euclidean unit norm, Eq.(76).
--   - `optimalFilter`: The explicit optimal filter, Eq.(97), with sqrt(m_alpha/d_alpha) times v_mu/m_mu (PDF p.22). Both v_mu and m_mu are outside the radical, also confirmed by Eq.(74).
--   - `optimalResourceOperator`: Positive optimal Alice filter O_A, Eq.(99), with sqrt(d^N) (PDF p.22).
--   - `resourceState`: Actual resource amplitudes (O_A tensor I)|Phi+>^tensor N, Eq.(98) (PDF pp.4,22).
--   - `absorbedEffects`: Absorb the resource filter into physical identity-summing Alice effects (PDF pp.4,16). Bob's operation is solely to retain the named port.
--   - `positiveInverse`: Moore–Penrose inverse of a positive optimizer, zero on its kernel (PDF pp.16–18).
--   - `completedMeasurement`: Deterministic physical POVM obtained by inverse filtering and uniformly completing the residual positive effect (PDF pp.3–4,16–18).
--   - `pbtBellEmbedding`: Normalized Bell embedding on the last two factors, identity on the first K (PDF p.29, Fact 39).
--   - `powerIterate`: Sum-normalized power iteration, Eq.(124), with the source's initial vector and no unspecified normalization convention (PDF p.27).
--   - `powerOutput`: The v_(m+1) in Eq.(124), avoiding an undefined v_0 (PDF pp.27–28).
--   - `OptimalConstruction`: Operational content of Eqs.(96)–(99): explicit filter and resource, the unrestricted optimal value, and support completion to a deterministic physical POVM (PDF pp.21–22).
--   - `squareRootEffects`: Global support inverse square root of rho, Eq.(1), for the fixed EPR resource (PDF pp.3,26). Its value on the zero eigenvalue is zero.
-- source:
--   Optimal Port-based Teleportation, arXiv:1707.08456v1, https://arxiv.org/abs/1707.08456v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SchurWeylDecomposition
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26
import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P01
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P28

/-!
Statements from Mozrzymas–Studzinski–Strelchuk–Horodecki,
Optimal Port-based Teleportation, arXiv:1707.08456v1.
All paper-local objects below have complete bodies. Theorems are statement targets.
N = K+1 is used in physical-register formulas to include N=1 without an invalid last index.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder
open Filter Topology
open QAlgorithms.Schur

namespace QAlgorithms.Papers.Independent.Extend50.P27

-- Exact accepted interfaces; unrelated short-name homonyms remain paper-specific.
open QAlgorithms.Papers.Independent.Renew46.P26 (deleteLast)
open QAlgorithms.Papers.Independent.Gap20.P01 (spechtMatrix)
open QAlgorithms.Papers.Independent.Claimed50.P28 (traceInput)

attribute [local instance] Classical.propDecidable

/-- One-box inclusion, on actual cells (PDF pp.3,5). -/
def Predecessor (alpha mu : YoungDiagram) : Prop :=
  alpha.cells ⊆ mu.cells ∧ (mu.cells \ alpha.cells).card = 1

/-- Moving one box between distinct shapes (PDF pp.5,7). -/
def BoxMove (mu nu : YoungDiagram) : Prop :=
  mu ≠ nu ∧ (mu.cells \ nu.cells).card = 1 ∧ (nu.cells \ mu.cells).card = 1

/-- Removable corners, counted independently of any height cutoff (PDF p.7). -/
def removableCount (mu : YoungDiagram) : ℕ :=
  ((Finset.range mu.card).filter fun i => mu.rowLen (i+1) < mu.rowLen i).card

/-- Definition 3, evaluated on diagrams, independently of any incidence Gram matrix (PDF p.7). -/
def teleportEntry (mu nu : YoungDiagram) : ℝ :=
  if mu = nu then removableCount mu else if BoxMove mu nu then 1 else 0

/-- Definition 10: all shapes of height at most d, with the original diagonal (PDF p.11). -/
def teleportMatrix (d N : ℕ) : Matrix (Partition d N) (Partition d N) ℝ :=
  fun mu nu => teleportEntry mu.val nu.val

/-- Full matrix, containing all size-N shapes (PDF pp.7,10). -/
def fullMatrix (N : ℕ) : Matrix (Partition N N) (Partition N N) ℝ :=
  teleportMatrix N N

/-- Rectangular physical branching incidence, Definition 18 (PDF p.13). -/
def incidence (d N : ℕ) : Matrix (Partition d (N-1)) (Partition d N) ℝ :=
  fun alpha mu => if Predecessor alpha.val mu.val then 1 else 0

/-- Column Gram matrix, Definition 21 (PDF p.14). -/
def columnGram (d N : ℕ) := (incidence d N).transpose * incidence d N

/-- Row Gram matrix, Definition 21 (PDF p.14). -/
def rowGram (d N : ℕ) := incidence d N * (incidence d N).transpose

/-- Shape-restricted diagonal correction. The printed height=d in Eq.(54) must be
height<d, as Lemma 27 and Eq.(55) require (PDF p.15). -/
def heightCorrection (d N : ℕ) : Matrix (Partition d (N-1)) (Partition d (N-1)) ℝ :=
  Matrix.diagonal fun alpha => if alpha.val.colLen 0 < d then 1 else 0

/-- Largest real spectral value. Every use below is on a nonempty finite symmetric
matrix; PSD and attainment are conclusions, not fields of this definition (PDF pp.19,27). -/
def topValue {I : Type*} [Fintype I] [DecidableEq I] (A : Matrix I I ℝ) : ℝ :=
  sSup (spectrum ℝ A)

/-- Entanglement-fidelity value singled out by Eq.(78), with one eigenvalue, not its square. -/
def spectralFidelity (d N : ℕ) : ℝ := topValue (teleportMatrix d N) / (d : ℝ)^2

/-- Explicit maximum absolute row sum, the source's norm in Eq.(43) (PDF p.12). -/
def maxRowSum {I : Type*} [Fintype I] (A : Matrix I I ℝ) : ℝ :=
  sSup (Set.range (fun i => ∑ j, |A i j|))

/-- Last-letter-fixing embedding S_K into S_(K+1) (PDF pp.5–6). -/
def includePermutation {K : ℕ} (pi : Equiv.Perm (Fin K)) : Equiv.Perm (Fin (K+1)) :=
  finSuccEquivLast.trans ((Equiv.optionCongr pi).trans finSuccEquivLast.symm)

/-- Actual Specht dimension, not an arbitrary shape weight (PDF pp.3–5). -/
def irrepDim {d N : ℕ} (mu : Partition d N) : ℕ := Module.finrank ℂ (spechtSpace mu)

/-- Intertwiners between two actual finite actions. No branching counts are supplied
as data; multiplicity is the dimension of this subspace (PDF pp.5,8–9). -/
def pbtIntertwinerSpace {G I J : Type*} [Fintype I] [Fintype J]
    (A : G → Matrix I I ℂ) (B : G → Matrix J J ℂ) : Submodule ℂ (Matrix J I ℂ) where
  carrier := {T | ∀ g, B g * T = T * A g}
  zero_mem' := by intro g; simp
  add_mem' := by
    intro T S hT hS g
    simp only [Matrix.mul_add, Matrix.add_mul, hT g, hS g]
  smul_mem' := by
    intro c T hT g
    simp only [Matrix.mul_smul, Matrix.smul_mul, hT g]

/-- Tensor-space multiplicity m_mu, computed by actual intertwiners (PDF pp.3–4). -/
def tensorMultiplicity {d N : ℕ} (mu : Partition d N) : ℕ :=
  Module.finrank ℂ (pbtIntertwinerSpace (spechtMatrix mu) (tensorPermutation d N))

/-- Restriction of a concrete Specht action to the subgroup fixing the last letter (PDF p.5). -/
def restrictedAction {d K : ℕ} (mu : Partition d (K+1)) (pi : Equiv.Perm (Fin K)) :=
  spechtMatrix mu (includePermutation pi)

/-- Induction in the explicit coset basis of Eqs.(20)–(21); N copies of the
actual alpha Specht module, not an array of assumed branching multiplicities (PDF p.6). -/
def inducedAction {d K : ℕ} (alpha : Partition d K) (pi : Equiv.Perm (Fin (K+1))) :
    Matrix (Fin (K+1) × Fin (irrepDim alpha)) (Fin (K+1) × Fin (irrepDim alpha)) ℂ :=
  fun a b =>
    let tau := Equiv.swap a.1 (Fin.last K) * pi * Equiv.swap b.1 (Fin.last K)
    if tau (Fin.last K) = Fin.last K then
      spechtMatrix alpha (deleteLast K tau) a.2 b.2 else 0

/-- Multiplicity in the restricted Specht module, defined through intertwiners (PDF p.5). -/
def restrictionMultiplicity {d K : ℕ} (alpha : Partition d K) (mu : Partition d (K+1)) : ℕ :=
  Module.finrank ℂ (pbtIntertwinerSpace (spechtMatrix alpha) (restrictedAction mu))

/-- Multiplicity in the explicit induced module, defined through intertwiners (PDF pp.5–6). -/
def inductionMultiplicity {d K : ℕ} (mu : Partition d (K+1)) (alpha : Partition d K) : ℕ :=
  Module.finrank ℂ (pbtIntertwinerSpace (spechtMatrix mu) (inducedAction alpha))

/-- Number of fixed points, including zero, as in the proof of Lemma 2 (PDF pp.6–7). -/
def fixedCount {N : ℕ} (pi : Equiv.Perm (Fin N)) : ℕ :=
  (Finset.univ.filter fun i => pi i = i).card

/-- Definition 6 uses literal, unweighted Specht characters (PDF p.9). -/
def characterTable (N : ℕ) :
    Matrix (Partition N N) (ConjClasses (Equiv.Perm (Fin N))) ℂ :=
  fun mu C => spechtCharacter mu (Quotient.out C)

/-- Count of cycle types with exactly k fixed points. Each xi_l is bounded by N;
the equation is written without truncated N-k (PDF p.10). -/
def cycleClassCount (N k : ℕ) : ℕ :=
  (Finset.univ.filter fun xi : Fin (N+1) → Fin (N+1) =>
    xi 0 = 0 ∧ xi 1 = 0 ∧ k + ∑ l : Fin (N+1), l.val * (xi l).val = N).card

/-- Alice's N local registers. -/
abbrev AliceIndex (d N : ℕ) := Fin N → Fin d

/-- Alice plus the input register C, with N=K+1. -/
abbrev SignalIndex (d K : ℕ) := AliceIndex d (K+1) × Fin d

/-- Extend an Alice operator by identity on C (PDF pp.4,16). -/
def liftAlice {d K : ℕ} (A : Matrix (AliceIndex d (K+1)) (AliceIndex d (K+1)) ℂ) :
    Matrix (SignalIndex d K) (SignalIndex d K) ℂ :=
  fun x y => if x.2 = y.2 then A x.1 y.1 else 0

/-- Normalized signals sigma_a = d^(-N) V^{t_C}(a,C), Eq.(4) (PDF p.3).
The equalities couple a with C on each side; other Alice coordinates are unchanged. -/
def pbtSignal (d K : ℕ) (a : Fin (K+1)) : Matrix (SignalIndex d K) (SignalIndex d K) ℂ :=
  fun x y => if x.1 a = x.2 ∧ y.1 a = y.2 ∧ (∀ i, i ≠ a → x.1 i = y.1 i)
    then ((d : ℂ)^(K+1))⁻¹ else 0

/-- Entanglement fidelity of effective effects, Eq.(57) (PDF p.16). -/
def effectFidelity {d K : ℕ}
    (E : Fin (K+1) → Matrix (SignalIndex d K) (SignalIndex d K) ℂ) : ℝ :=
  (∑ a, (Matrix.trace (E a * pbtSignal d K a)).re) / (d : ℝ)^2

/-- All primal variables; positivity includes Hermiticity. The inequality is a
positive-semidefinite difference, not entrywise order (PDF pp.4,16). -/
def PBTPrimalFeasible {d K : ℕ}
    (X : Matrix (AliceIndex d (K+1)) (AliceIndex d (K+1)) ℂ)
    (E : Fin (K+1) → Matrix (SignalIndex d K) (SignalIndex d K) ℂ) : Prop :=
  X.PosSemidef ∧ X.trace = (d : ℂ)^(K+1) ∧
    (∀ a, (E a).PosSemidef) ∧ (liftAlice X - ∑ a, E a).PosSemidef

/-- Attainable primal values; no spectral ansatz restricts the variables (PDF p.16). -/
def primalValues (d K : ℕ) : Set ℝ :=
  {f | ∃ (X : Matrix (AliceIndex d (K+1)) (AliceIndex d (K+1)) ℂ)
      (E : Fin (K+1) → Matrix (SignalIndex d K) (SignalIndex d K) ℂ),
    PBTPrimalFeasible (d := d) (K := K) X E ∧ f = effectFidelity (d := d) (K := K) E}

/-- Optimal value of the actual primal program; its greatest element is asserted
below, so the real supremum is not used as a substitute for attainment (PDF pp.16–19). -/
def pbtOptimalFidelity (d N : ℕ) : ℝ := sSup (primalValues d (N-1))

/-- Full dual feasible set, Eq.(80), without the proof's block ansatz (PDF pp.19–20). -/
def PBTDualFeasible {d K : ℕ} (Omega : Matrix (SignalIndex d K) (SignalIndex d K) ℂ) : Prop :=
  Omega.IsHermitian ∧ ∀ a, (Omega - pbtSignal d K a).PosSemidef

/-- The Euclidean operator norm in Eq.(79), on a Hermitian positive partial trace.
Using the largest real eigenvalue avoids the unrelated maximum row-sum norm. -/
def pbtDualObjective {d K : ℕ} (Omega : Matrix (SignalIndex d K) (SignalIndex d K) ℂ) : ℝ :=
  (d : ℝ)^(K+1) / (d : ℝ)^2 * sSup (spectrum ℝ (traceInput Omega))

/-- Actual dual objective values, Eq.(79) (PDF p.19). -/
def pbtDualValues (d K : ℕ) : Set ℝ :=
  {f | ∃ Omega : Matrix (SignalIndex d K) (SignalIndex d K) ℂ,
    PBTDualFeasible (d := d) (K := K) Omega ∧
      f = pbtDualObjective (d := d) (K := K) Omega}

/-- Concrete unnormalized P_alpha tensor tilde P+ seed (PDF p.31, Eq.(145)). -/
def projectorSeed {d K : ℕ} (alpha : Partition d K) :
    Matrix (SignalIndex d K) (SignalIndex d K) ℂ :=
  fun x y => if x.1 (Fin.last K) = x.2 ∧ y.1 (Fin.last K) = y.2 then
    isotypicProjector alpha (fun i => x.1 i.castSucc) (fun i => y.1 i.castSucc) else 0

/-- Eta(alpha), the explicit sum of transported seeds in Eq.(145) (PDF pp.4,31). -/
def etaBlock {d K : ℕ} (alpha : Partition d K) :
    Matrix (SignalIndex d K) (SignalIndex d K) ℂ :=
  ∑ a : Fin (K+1),
    let V := liftAlice (tensorPermutation d (K+1) (Equiv.swap a (Fin.last K)))
    V * projectorSeed alpha * Vᴴ

/-- Nonzero physical eigenvalue gamma_mu(alpha), Eq.(8) (PDF p.4). -/
def pbtGammaValue {d K : ℕ} (alpha : Partition d K) (mu : Partition d (K+1)) : ℝ :=
  (K+1 : ℝ) * tensorMultiplicity mu * irrepDim alpha /
    ((tensorMultiplicity alpha : ℝ) * irrepDim mu)

/-- Lambda_mu(alpha)=gamma_mu(alpha)/d^N, Eq.(10) (PDF p.4). -/
def lambdaValue {d K : ℕ} (alpha : Partition d K) (mu : Partition d (K+1)) : ℝ :=
  pbtGammaValue alpha mu / (d : ℝ)^(K+1)

/-- Concrete physical F_mu(alpha), Eq.(145); no projector or spectral identities
are assumed as structure fields (PDF p.31). Used only for one-box-compatible labels. -/
def physicalProjector {d K : ℕ} (alpha : Partition d K) (mu : Partition d (K+1)) :
    Matrix (SignalIndex d K) (SignalIndex d K) ℂ :=
  ((pbtGammaValue alpha mu : ℂ)⁻¹) •
    (liftAlice (isotypicProjector mu) * etaBlock alpha * liftAlice (isotypicProjector mu))

/-- Spectral power of the physical alpha block, extended by zero off its nonzero
support, even at exponent zero or a negative exponent (PDF pp.24,29). -/
def blockPower {d K : ℕ} (alpha : Partition d K) (t : ℝ) :
    Matrix (SignalIndex d K) (SignalIndex d K) ℂ :=
  ∑ mu : Partition d (K+1), if Predecessor alpha.val mu.val then
    ((Real.rpow (lambdaValue alpha mu) t : ℝ) : ℂ) • physicalProjector alpha mu else 0

/-- Alpha-resolved sigma_a. This is constructed from the seed, not postulated as
an eigenspace decomposition (PDF pp.24–25). -/
def blockSignal {d K : ℕ} (alpha : Partition d K) (a : Fin (K+1)) :
    Matrix (SignalIndex d K) (SignalIndex d K) ℂ :=
  let V := liftAlice (tensorPermutation d (K+1) (Equiv.swap a (Fin.last K)))
  ((d : ℂ)^(K+1))⁻¹ • (V * projectorSeed alpha * Vᴴ)

/-- Spectral filter with actual block coefficients p_mu(alpha), Eq.(61) (PDF p.17). -/
def coefficientFilter {d K : ℕ} (p : Partition d K → Partition d (K+1) → ℝ) :
    Matrix (SignalIndex d K) (SignalIndex d K) ℂ :=
  ∑ alpha : Partition d K, ∑ mu : Partition d (K+1),
    if Predecessor alpha.val mu.val then (p alpha mu : ℂ) • physicalProjector alpha mu else 0

/-- Effective effects Pi sigma_a Pi, Eq.(60) (PDF p.17). -/
def filterEffects {d K : ℕ} (P : Matrix (SignalIndex d K) (SignalIndex d K) ℂ)
    (a : Fin (K+1)) := P * pbtSignal d K a * P

/-- The general block power-filter effects, Eq.(110). Feasibility is never inferred
for arbitrary z,y (PDF pp.24–25). -/
def powerEffects {d K : ℕ} (z y : Partition d K → ℝ) (a : Fin (K+1)) :
    Matrix (SignalIndex d K) (SignalIndex d K) ℂ :=
  ∑ alpha : Partition d K, (z alpha : ℂ) •
    (blockPower alpha (-(y alpha)⁻¹) * blockSignal alpha a * blockPower alpha (-(y alpha)⁻¹))

/-- The scalar contraction coefficient, Eqs.(113),(139) (PDF pp.24,29). -/
def contractionConstant {d K : ℕ} (alpha : Partition d K) (y : ℝ) : ℝ :=
  (∑ mu : Partition d (K+1), if Predecessor alpha.val mu.val then
    Real.rpow (lambdaValue alpha mu) (-y⁻¹) * tensorMultiplicity mu /
      (tensorMultiplicity alpha : ℝ) else 0) / d

/-- Formula (120), with physical labels and actual dimensions (PDF p.26). -/
def eprFormula (d K : ℕ) : ℝ :=
  (∑ alpha : Partition d K,
    (∑ mu : Partition d (K+1), if Predecessor alpha.val mu.val then
      Real.sqrt ((irrepDim mu : ℝ) * tensorMultiplicity mu) else 0)^2) / (d : ℝ)^(K+3)

/-- The scalar expression before maximization in Eq.(68) (PDF p.18). -/
def coefficientFidelity {d K : ℕ} (p : Partition d K → Partition d (K+1) → ℝ) : ℝ :=
  (K+1 : ℝ) / (d : ℝ)^(2*(K+1)+2) *
    ∑ alpha : Partition d K, (irrepDim alpha : ℝ) / tensorMultiplicity alpha *
      (∑ mu : Partition d (K+1), if Predecessor alpha.val mu.val then
        p alpha mu * tensorMultiplicity mu else 0)^2

/-- Source-normalized positive Perron vector, with Euclidean unit norm, Eq.(76). -/
def IsOptimalVector {d N : ℕ} (v : Partition d N → ℝ) : Prop :=
  (∀ mu, 0 < v mu) ∧ (∑ mu, (v mu)^2) = 1 ∧
    (teleportMatrix d N) *ᵥ v = topValue (teleportMatrix d N) • v

/-- The explicit optimal filter, Eq.(97), with sqrt(m_alpha/d_alpha) times v_mu/m_mu
(PDF p.22). Both v_mu and m_mu are outside the radical, also confirmed by Eq.(74). -/
def optimalFilter {d K : ℕ} (v : Partition d (K+1) → ℝ) :=
  coefficientFilter (fun alpha mu =>
    (d : ℝ)^(K+1) / Real.sqrt (K+1) *
      Real.sqrt ((tensorMultiplicity alpha : ℝ) / irrepDim alpha) * v mu / tensorMultiplicity mu)

/-- Positive optimal Alice filter O_A, Eq.(99), with sqrt(d^N) (PDF p.22). -/
def optimalResourceOperator {d N : ℕ} (v : Partition d N → ℝ) :
    Matrix (AliceIndex d N) (AliceIndex d N) ℂ :=
  ∑ mu : Partition d N,
    ((Real.sqrt ((d : ℝ)^N) * v mu /
      Real.sqrt ((irrepDim mu : ℝ) * tensorMultiplicity mu) : ℝ) : ℂ) • isotypicProjector mu

/-- Actual resource amplitudes (O_A tensor I)|Phi+>^tensor N, Eq.(98) (PDF pp.4,22). -/
def resourceState {d N : ℕ} (O : Matrix (AliceIndex d N) (AliceIndex d N) ℂ) :
    EuclideanSpace ℂ (AliceIndex d N × AliceIndex d N) :=
  WithLp.toLp 2 (fun xy => O xy.1 xy.2 / (Real.sqrt ((d : ℝ)^N) : ℂ))

/-- Absorb the resource filter into physical identity-summing Alice effects
(PDF pp.4,16). Bob's operation is solely to retain the named port. -/
def absorbedEffects {d K : ℕ}
    (O : Matrix (AliceIndex d (K+1)) (AliceIndex d (K+1)) ℂ)
    (M : Fin (K+1) → Matrix (SignalIndex d K) (SignalIndex d K) ℂ) (a : Fin (K+1)) :=
  (liftAlice O)ᴴ * M a * liftAlice O

/-- Moore–Penrose inverse of a positive optimizer, zero on its kernel (PDF pp.16–18). -/
def positiveInverse {I : Type*} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) : Matrix I I ℂ :=
  cfc (fun t : ℝ => if t = 0 then 0 else t⁻¹) A

/-- Deterministic physical POVM obtained by inverse filtering and uniformly
completing the residual positive effect (PDF pp.3–4,16–18). -/
def completedMeasurement {d K : ℕ}
    (O : Matrix (AliceIndex d (K+1)) (AliceIndex d (K+1)) ℂ)
    (E : Fin (K+1) → Matrix (SignalIndex d K) (SignalIndex d K) ℂ) (a : Fin (K+1)) :
    Matrix (SignalIndex d K) (SignalIndex d K) ℂ :=
  let Q := liftAlice (positiveInverse O)
  Q * E a * Q + ((K+1 : ℂ)⁻¹) • (1 - ∑ b, Q * E b * Q)

/-- Normalized Bell embedding on the last two factors, identity on the first K
(PDF p.29, Fact 39). -/
def pbtBellEmbedding (d K : ℕ) : Matrix (SignalIndex d K) (AliceIndex d K) ℂ :=
  fun x y => if (fun i => x.1 i.castSucc) = y ∧ x.1 (Fin.last K) = x.2
    then ((Real.sqrt d)⁻¹ : ℂ) else 0

/-- Sum-normalized power iteration, Eq.(124), with the source's initial vector
and no unspecified normalization convention (PDF p.27). -/
def powerIterate {I : Type*} [Fintype I] (A : Matrix I I ℝ) (w0 : I → ℝ) : ℕ → I → ℝ
  | 0 => w0
  | m+1 => let v := A *ᵥ powerIterate A w0 m; fun i => v i / ∑ j, v j

/-- The v_(m+1) in Eq.(124), avoiding an undefined v_0 (PDF pp.27–28). -/
def powerOutput {I : Type*} [Fintype I] (A : Matrix I I ℝ) (w0 : I → ℝ) (m : ℕ) :=
  A *ᵥ powerIterate A w0 m

example (mu : YoungDiagram) : ¬ BoxMove mu mu := by simp [BoxMove]

example (mu : YoungDiagram) : teleportEntry mu mu = removableCount mu := by
  simp [teleportEntry]

example {d K : ℕ} (alpha : Partition d K) (mu : Partition d (K+1))
    (h : Predecessor alpha.val mu.val) : incidence d (K+1) alpha mu = 1 := by
  simp [incidence, h]

example {K : ℕ} (pi : Equiv.Perm (Fin K)) :
    includePermutation pi (Fin.last K) = Fin.last K := by simp [includePermutation]

example {I : Type*} [Fintype I] (A : Matrix I I ℝ) (w : I → ℝ) :
    powerIterate A w 0 = w := rfl

example {d K : ℕ} : liftAlice (0 : Matrix (AliceIndex d (K+1)) (AliceIndex d (K+1)) ℂ) = 0 := by
  ext x y
  simp [liftAlice]

example {d K : ℕ} (alpha : Partition d K) (mu : Partition d (K+1)) :
    lambdaValue alpha mu = pbtGammaValue alpha mu / (d : ℝ)^(K+1) := rfl

example {d K : ℕ} (O : Matrix (AliceIndex d (K+1)) (AliceIndex d (K+1)) ℂ)
    (M : Fin (K+1) → Matrix (SignalIndex d K) (SignalIndex d K) ℂ) :
    absorbedEffects O M = fun a => (liftAlice O)ᴴ * M a * liftAlice O := rfl

/-- Operational content of Eqs.(96)–(99): explicit filter and resource, the unrestricted
optimal value, and support completion to a deterministic physical POVM (PDF pp.21–22). -/
def OptimalConstruction {d K : ℕ} (v : Partition d (K+1) → ℝ) : Prop :=
  let O := optimalResourceOperator v
  let E := filterEffects (optimalFilter v)
  let M := completedMeasurement O E
  O.PosSemidef ∧ (Oᴴ * O).trace = (d : ℂ)^(K+1) ∧
    ‖resourceState O‖ = 1 ∧ PBTPrimalFeasible (Oᴴ * O) E ∧
    effectFidelity E = spectralFidelity d (K+1) ∧
    IsGreatest (primalValues d K) (spectralFidelity d (K+1)) ∧
    QAlgorithms.IsPOVM M ∧
    effectFidelity (absorbedEffects O M) = spectralFidelity d (K+1) ∧
    (∀ (Oother : Matrix (AliceIndex d (K+1)) (AliceIndex d (K+1)) ℂ)
      (Mother : Fin (K+1) → Matrix (SignalIndex d K) (SignalIndex d K) ℂ),
      (Ootherᴴ * Oother).trace = (d : ℂ)^(K+1) → QAlgorithms.IsPOVM Mother →
      effectFidelity (absorbedEffects Oother Mother) ≤ spectralFidelity d (K+1))

/-- Global support inverse square root of rho, Eq.(1), for the fixed EPR resource
(PDF pp.3,26). Its value on the zero eigenvalue is zero. -/
def squareRootEffects (d K : ℕ) (a : Fin (K+1)) :
    Matrix (SignalIndex d K) (SignalIndex d K) ℂ :=
  let P := cfc (fun t : ℝ => if t = 0 then 0 else (Real.sqrt t)⁻¹) (∑ b, pbtSignal d K b)
  P * pbtSignal d K a * P

end QAlgorithms.Papers.Independent.Extend50.P27


