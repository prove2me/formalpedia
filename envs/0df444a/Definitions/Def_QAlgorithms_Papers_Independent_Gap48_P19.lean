-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P19
-- name    : QAlgorithms_Papers_Independent_Gap48_P19
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-22T04:06:09.843079+00:00
-- url     : https://prove2.me/theorems/e95130b2-2a0c-47e6-8952-e1fe692c6184
-- title:
--   Definitions for Entanglement of Distillation and Conditional Mutual Information
-- statement:
--   The objects the formalized statements of *Entanglement of Distillation and Conditional Mutual Information* (arXiv:quant-ph/0202144) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsKernel`: PDF pp.3,5,8: conditional law normalized at every parent value.
--   - `lawMap`: PDF p.2: the computed marginal law of a coordinate map.
--   - `shannonNats`: PDF pp.2,8: Shannon entropy in nats, with zero contribution at zero mass.
--   - `extensionClassicalCMI`: PDF pp.2,9, (2),(42)-(43): corrected nonnegative CMI in nats.
--   - `commonCause`: PDF p.3, (5): the specified common-cause joint law.
--   - `ClassicalExtension`: PDF pp.3-4, (6): raw extensions of arbitrary finite auxiliary cardinality.
--   - `ValidClassical`: PDF pp.3-4, (6): normalized extensions of the fixed AB marginal, positive flag size.
--   - `classicalScores`: PDF pp.3-4, (6): attainable CMI values; IsLeast retains minimum attainment.
--   - `fairPair`: PDF p.4, fixed-size caveat: a=b is a fair bit.
--   - `marginalAL`: PDF p.3: AL marginal of a state ordered as (A x B) x L.
--   - `marginalBL`: PDF p.3: BL marginal of a state ordered as (A x B) x L.
--   - `extensionQuantumCMI`: PDF pp.3-4, (4),(7)-(9): corrected CMI S(AL)+S(BL)-S(L)-S(ABL). The printed (4) has the opposite sign; see module preamble.
--   - `orthonormalFlagMixture`: PDF p.4, (7),(9): classical flags in any orthonormal basis, the columns of F.
--   - `flaggedProduct`: PDF p.4, (7): the actual flagged product-state construction.
--   - `QuantumExtension`: PDF p.4, (8): raw quantum extensions with arbitrary finite auxiliary size.
--   - `ValidQuantum`: PDF p.4, K0: genuine density matrices with the prescribed AB partial trace.
--   - `quantumScores`: PDF p.4, (8): CMI values of K0, with no minimum-attainment assumption.
--   - `k2Scores`: PDF p.4, (9): K2 consists of flags of normalized pure AB ensemble members. The accepted ensemble allows zero weights.
--   - `ClassicalProtocol`: PDF pp.5-6, (11) without communication: local stochastic maps on AA' and BB'.
--   - `localSelectionBranch`: PDF p.5, (11),(13): independent inputs, local maps, and the selected branch.
--   - `localSelectionProbability`: PDF p.5, (13): computed probability of a'=a0,b'=b0.
--   - `classicalOutput`: PDF p.5, (13): postselected law, used only at positive success probability.
--   - `classicalDistillationScores`: PDF pp.5-6, (14): attained inner minima, restricted to defined postselection. Outer IsGreatest in the theorem supplies maximization and its witness.
--   - `inputCopies`: PDF pp.6-7, (25),(28)-(29): rho_X tensor rho_X', regrouped as AA' x BB'.
--   - `aliceProject`: PDF p.7, (24): rank-one projection on a, identity on the other three registers.
--   - `quantumBranchFull`: PDF p.7, (25): both projectors, with genuinely a-dependent Bob unitary.
--   - `quantumNumerator`: PDF p.7, numerator of (25): sum over measured a, then select a'=a0,b'=b0.
--   - `quantumSuccess`: PDF p.7: normalization probability is the actual unnormalized trace.
--   - `measuredSelectionOutput`: PDF p.7, (25): normalized output; the theorem requires positive computed success.
--   - `quantumBlock`: PDF p.7, (26)-(31): eight-index contraction (two grouped summation indices). Right factors are conjugates in the printed adjoint order V*, then U*.
--   - `fig3Law`: PDF pp.8-9, (39): Fig.3 law including x,y conditional independence given L.
-- source:
--   Entanglement of Distillation and Conditional Mutual Information, arXiv:quant-ph/0202144v2, https://arxiv.org/abs/quant-ph/0202144v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P75

/-!
Tucci, arXiv:quant-ph/0202144v2. Entropies are in nats.
SOURCE CORRECTION: the second line of (2), PDF p.2, and (4), p.3, print
H(L)-H(AL)-H(BL)+H(ABL). We use H(AL)+H(BL)-H(L)-H(ABL),
as required by the first line of (2) and the nonnegative KL forms (42)-(43).
Independent moderation of this correction is pending. Equation (32) is deferred;
no operational distillable-entanglement characterization is asserted.
-/

namespace QAlgorithms.Papers.Independent.Gap48.P19

open scoped ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Information100.P75 (Mat)
open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.3,5,8: conditional law normalized at every parent value. -/
def IsKernel {I J : Type} [Fintype J] (k : I → J → ℝ) : Prop :=
  ∀ i, IsLaw (k i)

/-- PDF p.2: the computed marginal law of a coordinate map. -/
def lawMap {I J : Type} [Fintype I] (p : I → ℝ) (f : I → J) : J → ℝ :=
  fun j => ∑ i, if f i = j then p i else 0

/-- PDF pp.2,8: Shannon entropy in nats, with zero contribution at zero mass. -/
def shannonNats {I : Type} [Fintype I] (p : I → ℝ) : ℝ :=
  -∑ i, p i * Real.log (p i)

/-- PDF pp.2,9, (2),(42)-(43): corrected nonnegative CMI in nats. -/
def extensionClassicalCMI {A B L : Type} [Fintype A] [Fintype B] [Fintype L]
    (p : (A × B) × L → ℝ) : ℝ :=
  shannonNats (lawMap p (fun z => (z.1.1, z.2))) +
  shannonNats (lawMap p (fun z => (z.1.2, z.2))) -
  shannonNats (lawMap p Prod.snd) - shannonNats p

/-- PDF p.3, (5): the specified common-cause joint law. -/
def commonCause {A B L : Type} (w : L → ℝ) (ka : L → A → ℝ)
    (kb : L → B → ℝ) : (A × B) × L → ℝ :=
  fun z => ka z.2 z.1.1 * kb z.2 z.1.2 * w z.2

/-- PDF pp.3-4, (6): raw extensions of arbitrary finite auxiliary cardinality. -/
abbrev ClassicalExtension (A B : Type) := Σ n : ℕ, (((A × B) × Fin n) → ℝ)

/-- PDF pp.3-4, (6): normalized extensions of the fixed AB marginal, positive flag size. -/
def ValidClassical {A B : Type} [Fintype A] [Fintype B]
    (p : A × B → ℝ) (e : ClassicalExtension A B) : Prop :=
  0 < e.1 ∧ IsLaw e.2 ∧ lawMap e.2 Prod.fst = p

/-- PDF pp.3-4, (6): attainable CMI values; IsLeast retains minimum attainment. -/
def classicalScores {A B : Type} [Fintype A] [Fintype B]
    (p : A × B → ℝ) : Set ℝ :=
  {r | ∃ e : ClassicalExtension A B, ValidClassical p e ∧ extensionClassicalCMI e.2 = r}

/-- PDF p.4, fixed-size caveat: a=b is a fair bit. -/
def fairPair : Bool × Bool → ℝ := fun z => if z.1 = z.2 then 1 / 2 else 0

/-- PDF p.3: AL marginal of a state ordered as (A x B) x L. -/
def marginalAL {A B L : Type} [Fintype B] (rho : Mat ((A × B) × L)) : Mat (A × L) :=
  fun i j => ∑ b, rho ((i.1, b), i.2) ((j.1, b), j.2)

/-- PDF p.3: BL marginal of a state ordered as (A x B) x L. -/
def marginalBL {A B L : Type} [Fintype A] (rho : Mat ((A × B) × L)) : Mat (B × L) :=
  fun i j => ∑ a, rho ((a, i.1), i.2) ((a, j.1), j.2)

/-- PDF pp.3-4, (4),(7)-(9): corrected CMI S(AL)+S(BL)-S(L)-S(ABL).
The printed (4) has the opposite sign; see module preamble. -/
def extensionQuantumCMI {A B L : Type} [Fintype A] [Fintype B] [Fintype L]
    [DecidableEq A] [DecidableEq B] [DecidableEq L] (rho : Mat ((A × B) × L)) : ℝ :=
  QAlgorithms.Papers.Independent.Information100.P56.entropy (marginalAL rho) +
  QAlgorithms.Papers.Independent.Information100.P56.entropy (marginalBL rho) -
  QAlgorithms.Papers.Independent.Information100.P56.entropy (traceLeft rho) -
  QAlgorithms.Papers.Independent.Information100.P56.entropy rho

/-- PDF p.4, (7),(9): classical flags in any orthonormal basis, the columns of F. -/
def orthonormalFlagMixture {I L : Type} [Fintype L] [DecidableEq L] (w : L → ℝ)
    (tau : L → Mat I) (F : Matrix.unitaryGroup L ℂ) : Mat (I × L) :=
  fun i j => ∑ l, (w l : ℂ) * tau l i.1 j.1 *
    (F : Mat L) i.2 l * conj ((F : Mat L) j.2 l)

/-- PDF p.4, (7): the actual flagged product-state construction. -/
def flaggedProduct {A B L : Type} [Fintype L] [DecidableEq L]
    (w : L → ℝ) (ra : L → Mat A) (rb : L → Mat B)
    (F : Matrix.unitaryGroup L ℂ) : Mat ((A × B) × L) :=
  orthonormalFlagMixture w (fun l => Matrix.kronecker (ra l) (rb l)) F

/-- PDF p.4, (8): raw quantum extensions with arbitrary finite auxiliary size. -/
abbrev QuantumExtension (A B : Type) := Σ n : ℕ, Mat ((A × B) × Fin n)

/-- PDF p.4, K0: genuine density matrices with the prescribed AB partial trace. -/
def ValidQuantum {A B : Type} [Fintype A] [Fintype B]
    (rho : Mat (A × B)) (e : QuantumExtension A B) : Prop :=
  0 < e.1 ∧ IsDensityMatrix e.2 ∧ traceRight e.2 = rho

/-- PDF p.4, (8): CMI values of K0, with no minimum-attainment assumption. -/
def quantumScores {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Mat (A × B)) : Set ℝ :=
  {r | ∃ e : QuantumExtension A B, ValidQuantum rho e ∧ extensionQuantumCMI e.2 = r}

/-- PDF p.4, (9): K2 consists of flags of normalized pure AB ensemble members.
The accepted ensemble allows zero weights. -/
def k2Scores {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Mat (A × B)) : Set ℝ :=
  {r | ∃ e : QAlgorithms.Papers.Independent.Information100.P08.PureEnsemble (A × B),
    QAlgorithms.Papers.Independent.Information100.P08.pureAverage e = rho ∧
    ∃ F : Matrix.unitaryGroup (Fin e.size) ℂ,
      extensionQuantumCMI (orthonormalFlagMixture e.prob (fun l => pureDensity (e.vector l)) F) = r}

/-- PDF pp.5-6, (11) without communication: local stochastic maps on AA' and BB'. -/
structure ClassicalProtocol (A B : Type) [Fintype A] [Fintype B] where
  alice : (A × A) → (A × A) → ℝ
  bob : (B × B) → (B × B) → ℝ
  alice_kernel : IsKernel alice
  bob_kernel : IsKernel bob

/-- PDF p.5, (11),(13): independent inputs, local maps, and the selected branch. -/
def localSelectionBranch {A B : Type} [Fintype A] [Fintype B]
    (p q : A × B → ℝ) (k : ClassicalProtocol A B) (a0 : A) (b0 : B) : A × B → ℝ :=
  fun z => ∑ x, ∑ y, k.alice (x.1, y.1) (z.1, a0) *
    k.bob (x.2, y.2) (z.2, b0) * p x * q y

/-- PDF p.5, (13): computed probability of a'=a0,b'=b0. -/
def localSelectionProbability {A B : Type} [Fintype A] [Fintype B]
    (p q : A × B → ℝ) (k : ClassicalProtocol A B) (a0 : A) (b0 : B) : ℝ :=
  ∑ z, localSelectionBranch p q k a0 b0 z

/-- PDF p.5, (13): postselected law, used only at positive success probability. -/
def classicalOutput {A B : Type} [Fintype A] [Fintype B]
    (p q : A × B → ℝ) (k : ClassicalProtocol A B) (a0 : A) (b0 : B) : A × B → ℝ :=
  fun z => localSelectionBranch p q k a0 b0 z / localSelectionProbability p q k a0 b0

/-- PDF pp.5-6, (14): attained inner minima, restricted to defined postselection.
Outer IsGreatest in the theorem supplies maximization and its witness. -/
def classicalDistillationScores {A B : Type} [Fintype A] [Fintype B]
    (p q : A × B → ℝ) (a0 : A) (b0 : B) : Set ℝ :=
  {r | ∃ k : ClassicalProtocol A B, 0 < localSelectionProbability p q k a0 b0 ∧
    IsLeast (classicalScores (classicalOutput p q k a0 b0)) r}

/-- PDF pp.6-7, (25),(28)-(29): rho_X tensor rho_X', regrouped as AA' x BB'. -/
def inputCopies {A B : Type} (rho sigma : Mat (A × B)) : Mat ((A × A) × (B × B)) :=
  fun i j => rho (i.1.1, i.2.1) (j.1.1, j.2.1) *
    sigma (i.1.2, i.2.2) (j.1.2, j.2.2)

/-- PDF p.7, (24): rank-one projection on a, identity on the other three registers. -/
def aliceProject {A B : Type} [DecidableEq A] (a : A) : Mat ((A × A) × (B × B)) :=
  Matrix.diagonal (fun i => if i.1.1 = a then 1 else 0)

/-- PDF p.7, (25): both projectors, with genuinely a-dependent Bob unitary. -/
def quantumBranchFull {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho sigma : Mat (A × B)) (U : Matrix.unitaryGroup (A × A) ℂ)
    (V : A → Matrix.unitaryGroup (B × B) ℂ) (a : A) : Mat ((A × A) × (B × B)) :=
  let W := Matrix.kronecker (U : Mat (A × A)) (V a : Mat (B × B))
  aliceProject a * W * inputCopies rho sigma * W.conjTranspose * aliceProject a

/-- PDF p.7, numerator of (25): sum over measured a, then select a'=a0,b'=b0. -/
def quantumNumerator {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho sigma : Mat (A × B)) (U : Matrix.unitaryGroup (A × A) ℂ)
    (V : A → Matrix.unitaryGroup (B × B) ℂ) (a0 : A) (b0 : B) : Mat (A × B) :=
  fun i j => ∑ a, quantumBranchFull rho sigma U V a
    ((i.1, a0), (i.2, b0)) ((j.1, a0), (j.2, b0))

/-- PDF p.7: normalization probability is the actual unnormalized trace. -/
def quantumSuccess {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho sigma : Mat (A × B)) (U : Matrix.unitaryGroup (A × A) ℂ)
    (V : A → Matrix.unitaryGroup (B × B) ℂ) (a0 : A) (b0 : B) : ℝ :=
  (quantumNumerator rho sigma U V a0 b0).trace.re

/-- PDF p.7, (25): normalized output; the theorem requires positive computed success. -/
def measuredSelectionOutput {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho sigma : Mat (A × B)) (U : Matrix.unitaryGroup (A × A) ℂ)
    (V : A → Matrix.unitaryGroup (B × B) ℂ) (a0 : A) (b0 : B) : Mat (A × B) :=
  ((quantumSuccess rho sigma U V a0 b0)⁻¹ : ℂ) • quantumNumerator rho sigma U V a0 b0

/-- PDF p.7, (26)-(31): eight-index contraction (two grouped summation indices).
Right factors are conjugates in the printed adjoint order V*, then U*. -/
def quantumBlock {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho sigma : Mat (A × B)) (U : Matrix.unitaryGroup (A × A) ℂ)
    (V : A → Matrix.unitaryGroup (B × B) ℂ) (a0 : A) (b0 : B)
    (a : A) (b1 b2 : B) : ℂ :=
  ((quantumSuccess rho sigma U V a0 b0)⁻¹ : ℂ) *
    ∑ i : (A × A) × (B × B), ∑ j : (A × A) × (B × B),
      (U : Mat (A × A)) (a, a0) i.1 * (V a : Mat (B × B)) (b1, b0) i.2 *
      rho (i.1.1, i.2.1) (j.1.1, j.2.1) * sigma (i.1.2, i.2.2) (j.1.2, j.2.2) *
      conj ((V a : Mat (B × B)) (b2, b0) j.2) * conj ((U : Mat (A × A)) (a, a0) j.1)

/-- PDF pp.8-9, (39): Fig.3 law including x,y conditional independence given L. -/
def fig3Law {A B X Y L : Type} (w : L → ℝ) (kx : L → X → ℝ)
    (ky : L → Y → ℝ) (ka : X → A → ℝ) (kb : Y → B → ℝ) :
    ((A × B) × (X × Y)) × L → ℝ :=
  fun z => ka z.1.2.1 z.1.1.1 * kb z.1.2.2 z.1.1.2 *
    kx z.2 z.1.2.1 * ky z.2 z.1.2.2 * w z.2

/-- Sanity: the one-point law is normalized. -/
example : IsLaw (fun _ : Unit => (1 : ℝ)) := by
  constructor
  · intro i; norm_num
  · simp

/-- Sanity: entropy of a certain outcome is zero. -/
example : shannonNats (fun _ : Unit => (1 : ℝ)) = 0 := by simp [shannonNats]

/-- Sanity: singleton-flag common cause is the product law. -/
example {A B : Type} (ka : A → ℝ) (kb : B → ℝ) (a : A) (b : B) :
    commonCause (fun _ : Unit => (1 : ℝ)) (fun _ => ka) (fun _ => kb) ((a,b), ()) =
      ka a * kb b := by simp [commonCause]

/-- Sanity: zero weights give zero flagged contribution. -/
example {I L : Type} [Fintype L] [DecidableEq L] (tau : L → Mat I)
    (F : Matrix.unitaryGroup L ℂ) : orthonormalFlagMixture (fun _ => 0) tau F = 0 := by
  ext i j
  simp [orthonormalFlagMixture]

/-- Sanity: the imported quantum entropy is the natural-log spectral expression. -/
example {I : Type} [Fintype I] [DecidableEq I] (rho : Mat I) :
    QAlgorithms.Papers.Independent.Information100.P56.entropy rho =
      -(cfc (fun x : ℝ => x * Real.log x) rho).trace.re := rfl

/-- Sanity: independent input copies occur in their actual regrouped coordinates. -/
example {A B : Type} (rho sigma : Mat (A × B)) (a ap c cp : A) (b bp d dp : B) :
    inputCopies rho sigma ((a,ap),(b,bp)) ((c,cp),(d,dp)) =
      rho (a,b) (c,d) * sigma (ap,bp) (cp,dp) := rfl

end

end QAlgorithms.Papers.Independent.Gap48.P19


