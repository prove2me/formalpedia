-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P23
-- name    : QAlgorithms_Papers_Independent_Support50_P23
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-23T20:54:58.532306+00:00
-- url     : https://prove2.me/theorems/890d188f-4892-4d71-8d84-5a822b4d1f01
-- title:
--   Definitions for A Fully Quantum Asymptotic Equipartition Property
-- statement:
--   The objects the formalized statements of *A Fully Quantum Asymptotic Equipartition Property* (arXiv:0811.1221) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `supportedBy`: PDF p.3: support inclusion is reverse kernel inclusion.
--   - `identityTensorReference`: PDF p.3: identity on A tensored with the fixed reference sigma_B.
--   - `fidelityDistance`: PDF p.3, (12): sine distance using ROOT fidelity.
--   - `inBall`: PDF p.3, (12): closed subnormalized ball, also extended to epsilon=0.
--   - `log2Extended`: Binary logarithm of a nonnegative real, with log(0)=-infinity.
--   - `exp2Extended`: Binary exponential preserving the infinite endpoints.
--   - `fixedVonNeumann`: PDF p.3: fixed-reference von Neumann entropy. The kernel guard implements the singular-reference regularization, equal to -infinity on support failure.
--   - `conditionalEntropyBitsAB`: PDF p.3: conditional von Neumann entropy in bits, with the actual B marginal.
--   - `minEntropy`: PDF p.3, (9): optimize over normalized reference states.
--   - `dualMaxEntropy`: PDF pp.3-4, Definition 2 and (17): purification-dual max entropy, represented by the equivalent root-fidelity formula, extended homogeneously to subnormalized inputs.
--   - `sineSmoothFixedMin`: PDF p.3: fixed-reference smooth min entropy; sigma remains fixed.
--   - `sineSmoothMin`: PDF p.3: optimized smooth min entropy.
--   - `sineSmoothMax`: PDF p.3, (13): smooth max entropy is an INFIMUM over the same ball.
--   - `finiteAlpha`: PDF p.4, (16): finite positive-order Petz entropy, with the von Neumann value at one. Below one, zero reference eigenvalues contribute zero. Above one, support failure gives -infinity; otherwise inverse powers are taken on support.
--   - `alphaEntropy`: PDF p.4: all nonnegative orders, including infinity. The decreasing finite-order family's endpoint limits are its extended supremum and infimum. No totalized limit operator is used; finite orders below are always positive.
--   - `entropyConvergenceParameter`: PDF p.5, (24): computed convergence parameter, possibly +infinity.
--   - `aepBlockError`: PDF p.6, (30): real error constant, used only for finite eta and 0<epsilon<1.
--   - `jointPower`: PDF pp.2,4,6: i.i.d. AB tensor power regrouped in the order A^n,B^n.
--   - `independentProduct`: PDF p.4: binary product regrouped from AB,CD into AC,BD.
--   - `traceMiddleABC`: PDF p.4, Lemma 6: trace out B from a state ordered (AB)C.
--   - `thresholdRadius`: PDF p.8, (C1): epsilon is COMPUTED from lambda and the positive part.
--   - `trivialJoint`: PDF p.6 footnote 9: a single system viewed with trivial A.
--   - `smoothMaxRelative`: PDF p.6 footnote 9: negative fixed-reference smooth min entropy, hence an INFIMUM over the smoothing ball.
--   - `relativeUpsilon`: PDF p.6 footnote 9: the displayed parameter equals Upsilon with trivial A.
--   - `NonnegativeSpectralDecomposition`: PDF p.4: nonnegative eigenvalues and an orthonormal eigenbasis.
--   - `NonnegativeSpectralDecomposition.operator`: PDF p.4: reconstruct the operator from its spectral decomposition.
--   - `spectralLog`: PDF p.4: the overlap restriction is essential. For xi>0 and normalized rho, the contributing set is finite and nonempty and its maximum is positive.
-- source:
--   A Fully Quantum Asymptotic Equipartition Property, arXiv:0811.1221v3, https://arxiv.org/abs/0811.1221v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P03
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P36
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69

/-! Statements from Tomamichel, Colbeck and Renner, arXiv:0811.1221v3.
All logarithms are binary. Bases are arbitrary finite nonempty types.
Paper-specific entropy definitions use this paper's subnormalized root-fidelity smoothing. -/

noncomputable section

open Filter
open scoped ENNReal ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Support50.P23

attribute [local instance] Classical.propDecidable

-- Exact accepted bodies. Other similarly named catalogue entries use different
-- smoothing, conditioning order, logarithm base, or channel-level objects.
open QAlgorithms.Papers.Independent.Gap20.P03 (fixedMin)
open QAlgorithms.Papers.Independent.Dependency50.P36 (relativeEntropy)
open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized)
open QAlgorithms.Papers.Independent.Information100.P69 (matrixPower)

variable {A B C D I : Type*}
variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype I]
variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D] [DecidableEq I]

/-- PDF p.3: support inclusion is reverse kernel inclusion. -/
def supportedBy (rho sigma : Matrix I I ℂ) : Prop :=
  LinearMap.ker sigma.mulVecLin ≤ LinearMap.ker rho.mulVecLin

/-- PDF p.3: identity on A tensored with the fixed reference sigma_B. -/
def identityTensorReference (sigma : Matrix B B ℂ) : Matrix (A × B) (A × B) ℂ :=
  Matrix.kronecker (1 : Matrix A A ℂ) sigma

/-- PDF p.3, (12): sine distance using ROOT fidelity. -/
def fidelityDistance (rho tau : Matrix I I ℂ) : ℝ :=
  Real.sqrt (1 - rootFidelity rho tau ^ 2)

/-- PDF p.3, (12): closed subnormalized ball, also extended to epsilon=0. -/
def inBall (rho tau : Matrix I I ℂ) (epsilon : ℝ) : Prop :=
  IsSubnormalized tau ∧ fidelityDistance rho tau ≤ epsilon

/-- Binary logarithm of a nonnegative real, with log(0)=-infinity. -/
def log2Extended (x : ℝ) : EReal :=
  if x = 0 then ⊥ else (Real.logb 2 x : EReal)

/-- Binary exponential preserving the infinite endpoints. -/
def exp2Extended (x : EReal) : ℝ≥0∞ :=
  if x = ⊤ then ⊤ else if x = ⊥ then 0 else ENNReal.ofReal ((2 : ℝ) ^ x.toReal)

/-- PDF p.3: fixed-reference von Neumann entropy. The kernel guard implements the
singular-reference regularization, equal to -infinity on support failure. -/
def fixedVonNeumann (rho : Matrix (A × B) (A × B) ℂ)
    (sigma : Matrix B B ℂ) : EReal :=
  if supportedBy rho (identityTensorReference (A := A) sigma) then
    (((rho * cfc (fun x : ℝ => Real.logb 2 x) (identityTensorReference (A := A) sigma)).trace.re +
      vnEntropy rho : ℝ) : EReal)
  else ⊥

/-- PDF p.3: conditional von Neumann entropy in bits, with the actual B marginal. -/
def conditionalEntropyBitsAB (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  vnEntropy rho - vnEntropy (traceLeft rho)

/-- PDF p.3, (9): optimize over normalized reference states. -/
def minEntropy (rho : Matrix (A × B) (A × B) ℂ) : EReal :=
  sSup {h : EReal | ∃ sigma : Matrix B B ℂ,
    IsDensityMatrix sigma ∧ h = fixedMin rho sigma}

/-- PDF pp.3-4, Definition 2 and (17): purification-dual max entropy, represented
by the equivalent root-fidelity formula, extended homogeneously to subnormalized inputs. -/
def dualMaxEntropy (rho : Matrix (A × B) (A × B) ℂ) : EReal :=
  sSup {h : EReal | ∃ sigma : Matrix B B ℂ,
    IsDensityMatrix sigma ∧ h = log2Extended (rootFidelity rho (identityTensorReference (A := A) sigma) ^ 2)}

/-- PDF p.3: fixed-reference smooth min entropy; sigma remains fixed. -/
def sineSmoothFixedMin (rho : Matrix (A × B) (A × B) ℂ)
    (sigma : Matrix B B ℂ) (epsilon : ℝ) : EReal :=
  sSup {h : EReal | ∃ tau : Matrix (A × B) (A × B) ℂ,
    inBall rho tau epsilon ∧ h = fixedMin tau sigma}

/-- PDF p.3: optimized smooth min entropy. -/
def sineSmoothMin (rho : Matrix (A × B) (A × B) ℂ) (epsilon : ℝ) : EReal :=
  sSup {h : EReal | ∃ tau : Matrix (A × B) (A × B) ℂ,
    inBall rho tau epsilon ∧ h = minEntropy tau}

/-- PDF p.3, (13): smooth max entropy is an INFIMUM over the same ball. -/
def sineSmoothMax (rho : Matrix (A × B) (A × B) ℂ) (epsilon : ℝ) : EReal :=
  sInf {h : EReal | ∃ tau : Matrix (A × B) (A × B) ℂ,
    inBall rho tau epsilon ∧ h = dualMaxEntropy tau}

/-- PDF p.4, (16): finite positive-order Petz entropy, with the von Neumann value at
one. Below one, zero reference eigenvalues contribute zero. Above one, support
failure gives -infinity; otherwise inverse powers are taken on support. -/
def finiteAlpha (rho : Matrix (A × B) (A × B) ℂ)
    (sigma : Matrix B B ℂ) (alpha : ℝ) : EReal :=
  if alpha = 1 then fixedVonNeumann rho sigma
  else if 1 < alpha ∧ ¬ supportedBy rho (identityTensorReference (A := A) sigma) then ⊥
  else ((1 / (1 - alpha) : ℝ) : EReal) *
    log2Extended ((cfc (fun x : ℝ => x ^ alpha) rho *
      cfc (fun x : ℝ => if x = 0 then 0 else x ^ (1 - alpha))
        (identityTensorReference (A := A) sigma)).trace.re)

/-- PDF p.4: all nonnegative orders, including infinity. The decreasing finite-order
family's endpoint limits are its extended supremum and infimum. No totalized limit
operator is used; finite orders below are always positive. -/
def alphaEntropy (rho : Matrix (A × B) (A × B) ℂ)
    (sigma : Matrix B B ℂ) (alpha : ℝ≥0∞) : EReal :=
  if alpha = 0 then
    sSup {h : EReal | ∃ t : ℝ, 0 < t ∧ h = finiteAlpha rho sigma t}
  else if alpha = ⊤ then
    sInf {h : EReal | ∃ t : ℝ, 0 < t ∧ h = finiteAlpha rho sigma t}
  else finiteAlpha rho sigma alpha.toReal

/-- PDF p.5, (24): computed convergence parameter, possibly +infinity. -/
def entropyConvergenceParameter (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ) : ℝ≥0∞ :=
  exp2Extended (-(finiteAlpha rho sigma (3 / 2)) * ((1 / 2 : ℝ) : EReal)) +
    exp2Extended (finiteAlpha rho sigma (1 / 2) * ((1 / 2 : ℝ) : EReal)) + 1

/-- PDF p.6, (30): real error constant, used only for finite eta and 0<epsilon<1. -/
def aepBlockError (epsilon : ℝ) (eta : ℝ≥0∞) : ℝ :=
  4 * Real.logb 2 eta.toReal * Real.sqrt (Real.logb 2 (2 / epsilon ^ 2))

/-- PDF pp.2,4,6: i.i.d. AB tensor power regrouped in the order A^n,B^n. -/
def jointPower (rho : Matrix (A × B) (A × B) ℂ) (n : ℕ) :
    Matrix ((Fin n → A) × (Fin n → B)) ((Fin n → A) × (Fin n → B)) ℂ :=
  fun x y => ∏ i, rho (x.1 i, x.2 i) (y.1 i, y.2 i)

/-- PDF p.4: binary product regrouped from AB,CD into AC,BD. -/
def independentProduct (rho : Matrix (A × B) (A × B) ℂ)
    (tau : Matrix (C × D) (C × D) ℂ) :
    Matrix ((A × C) × (B × D)) ((A × C) × (B × D)) ℂ :=
  fun x y => rho (x.1.1, x.2.1) (y.1.1, y.2.1) * tau (x.1.2, x.2.2) (y.1.2, y.2.2)

/-- PDF p.4, Lemma 6: trace out B from a state ordered (AB)C. -/
def traceMiddleABC (rho : Matrix ((A × B) × C) ((A × B) × C) ℂ) :
    Matrix (A × C) (A × C) ℂ :=
  fun x y => ∑ b, rho ((x.1, b), x.2) ((y.1, b), y.2)

/-- PDF p.8, (C1): epsilon is COMPUTED from lambda and the positive part. -/
def thresholdRadius (rho : Matrix (A × B) (A × B) ℂ)
    (sigma : Matrix B B ℂ) (lambda : ℝ) : ℝ :=
  Real.sqrt (2 * (cfc (fun x : ℝ => max x 0)
    (rho - (lambda : ℂ) • identityTensorReference (A := A) sigma)).trace.re)

/-- PDF p.6 footnote 9: a single system viewed with trivial A. -/
def trivialJoint (rho : Matrix I I ℂ) : Matrix (Unit × I) (Unit × I) ℂ :=
  fun x y => rho x.2 y.2

/-- PDF p.6 footnote 9: negative fixed-reference smooth min entropy, hence an
INFIMUM over the smoothing ball. -/
def smoothMaxRelative (rho sigma : Matrix I I ℂ) (epsilon : ℝ) : EReal :=
  -sineSmoothFixedMin (trivialJoint rho) sigma epsilon

/-- PDF p.6 footnote 9: the displayed parameter equals Upsilon with trivial A. -/
def relativeUpsilon (rho sigma : Matrix I I ℂ) : ℝ≥0∞ :=
  entropyConvergenceParameter (trivialJoint rho) sigma

/-- PDF p.4: nonnegative eigenvalues and an orthonormal eigenbasis. -/
structure NonnegativeSpectralDecomposition (I : Type*) [Fintype I] where
  values : I → ℝ
  nonnegative : ∀ i, 0 ≤ values i
  basis : OrthonormalBasis I ℂ (EuclideanSpace ℂ I)

/-- PDF p.4: reconstruct the operator from its spectral decomposition. -/
def NonnegativeSpectralDecomposition.operator (s : NonnegativeSpectralDecomposition I) : Matrix I I ℂ :=
  ∑ i, (s.values i : ℂ) • pureDensity (s.basis i)

/-- PDF p.4: the overlap restriction is essential. For xi>0 and normalized rho,
the contributing set is finite and nonempty and its maximum is positive. -/
def spectralLog (s t : NonnegativeSpectralDecomposition I) (xi : ℝ) : EReal :=
  -log2Extended (sSup {r : ℝ | ∃ i j,
    inner ℂ (s.basis i) (t.basis j) ≠ 0 ∧ r = s.values i / (t.values j + xi)})

/-! Sanity checks for local bodies; no result from the paper is proved here. -/

example : log2Extended 0 = ⊥ := by simp [log2Extended]

example : exp2Extended ⊥ = 0 := by simp [exp2Extended]

example : exp2Extended ⊤ = ⊤ := by simp [exp2Extended]

example (rho tau : Matrix I I ℂ) (epsilon : ℝ) :
    inBall rho tau epsilon ↔ IsSubnormalized tau ∧
      Real.sqrt (1 - rootFidelity rho tau ^ 2) ≤ epsilon := Iff.rfl

example : IsSubnormalized (0 : Matrix I I ℂ) := by
  exact ⟨(Matrix.PosSemidef.zero : (0 : Matrix I I ℂ).PosSemidef), by simp⟩

example (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (h : ¬ supportedBy rho (identityTensorReference (A := A) sigma)) :
    fixedVonNeumann rho sigma = ⊥ := by simp [fixedVonNeumann, h]

example (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (h : ¬ supportedBy rho (identityTensorReference (A := A) sigma)) :
    finiteAlpha rho sigma 2 = ⊥ := by simp [finiteAlpha, h]

example (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ) :
    finiteAlpha rho sigma 1 = fixedVonNeumann rho sigma := by simp [finiteAlpha]

example (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ) :
    alphaEntropy rho sigma ⊤ =
      sInf {h : EReal | ∃ t : ℝ, 0 < t ∧ h = finiteAlpha rho sigma t} := by
  simp [alphaEntropy]

example (sigma : Matrix B B ℂ) (x y : Fin 0 → B) : matrixPower sigma 0 x y = 1 := by
  simp [matrixPower]

example (rho : Matrix (A × B) (A × B) ℂ)
    (x y : (Fin 1 → A) × (Fin 1 → B)) :
    jointPower rho 1 x y = rho (x.1 0, x.2 0) (y.1 0, y.2 0) := by
  simp [jointPower]

example (rho sigma : Matrix I I ℂ) (epsilon : ℝ) :
    smoothMaxRelative rho sigma epsilon = -sineSmoothFixedMin (trivialJoint rho) sigma epsilon := rfl

/-- A scalar identity on the first system leaves the reference entries unchanged. -/
example (sigma : Matrix B B ℂ) (b bprime : B) :
    identityTensorReference (A := Unit) sigma ((), b) ((), bprime) = sigma b bprime := by
  simp [identityTensorReference, Matrix.kronecker, Matrix.one_apply]

/-- Zero fidelity has maximal sine distance, rather than distance zero. -/
example : fidelityDistance (0 : Matrix I I ℂ) 0 = 1 := by
  simp [fidelityDistance, rootFidelity]

/-- One scalar probability has zero binary log entropy. -/
example : log2Extended 1 = 0 := by simp [log2Extended]

end QAlgorithms.Papers.Independent.Support50.P23


