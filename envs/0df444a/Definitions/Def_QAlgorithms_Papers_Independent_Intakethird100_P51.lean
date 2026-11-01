-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P51
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P51
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T05:42:30.494803+00:00
-- url     : https://prove2.me/theorems/ff417fe6-3981-4fbf-a07b-66ac82b163c0
-- title:
--   Definitions for Inequalities for Quantum Entropy: A Review with Conditions for Equality
-- statement:
--   The objects the formalized statements of *Inequalities for Quantum Entropy: A Review with Conditions for Equality* (arXiv:quant-ph/0205064) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `logMatrix`: Natural Hermitian logarithm (PDF pp.4–5). At a zero eigenvalue the value is zero; this is used only inside x log x, or as zero extension of a common-support logarithm difference. It does not assert that a singular matrix has a finite logarithm.
--   - `SupportedBy`: Support inclusion supp X ⊆ supp Y, PDF p.4.
--   - `FaithfulDensity`: Default strictly positive normalized density convention, PDF pp.3,5.
--   - `liftAB`: AB operator lifted by the unnormalized identity on C (PDF p.4).
--   - `liftBC`: BC operator lifted by the identity on A (PDF p.4).
--   - `liftB`: B operator lifted by identities on A and C (PDF p.4).
--   - `ssaGap`: Right minus left side of SSA (3), PDF p.3, with actual marginals.
--   - `SSAlogCondition`: The literal lifted logarithm equality (4), PDF p.4.
--   - `imaginaryExp`: exp(itL), with the natural-log imaginary-power convention, PDF p.7.
--   - `splitProduct`: Regrouping of rho_(1,2a) tensor rho_(2b,3), PDF p.7.
--   - `marginalABC`: ABC marginal of the four-register purification, PDF p.9.
--   - `marginalABD`: ABD marginal of the same four-register purification, PDF p.9.
--   - `WeakMonotonicity`: Inequality (22) on the actual 124 marginal (PDF pp.9,15).
--   - `krausV`: The computed rectangular Kraus isometry in (26), PDF pp.10–11.
--   - `coordinatePVM`: Coordinate projections I tensor |b><b| in Section 3.5, PDF p.11.
--   - `basisPVM`: Common-basis rank-one spectral measurement, PDF p.17.
--   - `inverseRoot`: Inverse square root for the faithful ensemble–POVM duality, PDF p.21.
--   - `dualEffects`: Dual POVM, PDF p.21. Its uses require a faithful reference and positive weights.
--   - `dualUnnormalized`: Unnormalized dual ensemble component sqrt(rho) E_b sqrt(rho), PDF p.21.
--   - `dualStates`: Dual normalized state at an active outcome tau_b>0, PDF p.21. Its zero-mass value is zero and is never treated as a density matrix or placed inside a log.
--   - `hallBound`: Hall's right side (59), PDF p.21, explicitly omitting zero-mass outcomes.
--   - `hallRelative`: Equation (60), PDF p.21, retaining the factor tau_b.
--   - `UEP`: The optimizing expression (61), PDF p.21. Only the definition is retained; no strict comparison between global optima is inferred from one maximizing pair.
--   - `MONO`: MONO as a global finite PSD/support principle (PDF pp.14–15). Unnormalized positive matrices are included, so embedded references used in the reductions are covered.
--   - `MPT`: MPT as a global principle, with genuine partial traces, PDF pp.13–15.
--   - `SSA`: SSA as a global normalized PSD inequality, including block and pure states, PDF p.15.
--   - `JC`: JC as a global finite PSD/support principle, PDF pp.14–15.
--   - `UpperLogContour`: Admissible positively oriented circle for the principal analytic matrix logarithm, equation (63), PDF p.24. Its closed disk is in the scalar upper half-plane and its open disk contains the entire spectrum, ensuring winding number one and no resolvent pole.
--   - `principalLog`: Principal holomorphic matrix logarithm on upper-half-plane spectrum, using exactly the contour-resolvent calculus (63), PDF p.24. Different admissible circles give the same value by holomorphic functional calculus. Outside this domain the zero value is a totalization only, never used by the Pick theorem.
--   - `epsteinTrace`: Epstein's nonnormal matrix pencil trace function (62), PDF p.24.
-- source:
--   Inequalities for Quantum Entropy: A Review with Conditions for Equality, arXiv:quant-ph/0205064v2, https://arxiv.org/abs/quant-ph/0205064v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P27
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P19
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P33

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator
open MeasureTheory

namespace QAlgorithms.Papers.Independent.Intakethird100.P51

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact interfaces from the frozen accepted library; no local redeclarations.
open QAlgorithms.Papers.Independent.Information100.P63 (Mat)
open QAlgorithms.Papers.Independent.Information100.P56 (entropy holevo IsLaw)
open QAlgorithms.Papers.Independent.Information100.P27 (average)
open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy marginalAB channelAdjoint)
open QAlgorithms.Papers.Independent.Dependency50.P35 (marginalAC)
open QAlgorithms.Papers.Independent.Gap48.P19 (shannonNats)
open QAlgorithms.Papers.Independent.Gap48.P33 (measurementInformation)

/- The accepted relativeEntropy is EReal-valued in nats. Every use below is finite
by positive definiteness, explicit support inclusion, common channel-output support,
or the active ensemble construction, so .toReal is its finite real value.
The accepted measurementInformation uses bits; multiplying by Real.log 2 gives
exactly the natural-logarithm entropy difference (47). -/

/-- Natural Hermitian logarithm (PDF pp.4–5). At a zero eigenvalue the value is
zero; this is used only inside x log x, or as zero extension of a common-support
logarithm difference. It does not assert that a singular matrix has a finite logarithm. -/
def logMatrix {A : Type} [Fintype A] [DecidableEq A] (X : Mat A) : Mat A :=
  cfc Real.log X

/-- Support inclusion supp X ⊆ supp Y, PDF p.4. -/
def SupportedBy {A : Type} [Fintype A] [DecidableEq A] (X Y : Mat A) : Prop :=
  LinearMap.ker Y.mulVecLin ≤ LinearMap.ker X.mulVecLin

/-- Default strictly positive normalized density convention, PDF pp.3,5. -/
def FaithfulDensity {A : Type} [Fintype A] (X : Mat A) : Prop :=
  X.PosDef ∧ X.trace = 1

/-- AB operator lifted by the unnormalized identity on C (PDF p.4). -/
def liftAB {A B C : Type} [DecidableEq C] (X : Mat (A × B)) : Mat (A × (B × C)) :=
  fun p q => if p.2.2 = q.2.2 then X (p.1, p.2.1) (q.1, q.2.1) else 0

/-- BC operator lifted by the identity on A (PDF p.4). -/
def liftBC {A B C : Type} [DecidableEq A] (X : Mat (B × C)) : Mat (A × (B × C)) :=
  fun p q => if p.1 = q.1 then X p.2 q.2 else 0

/-- B operator lifted by identities on A and C (PDF p.4). -/
def liftB {A B C : Type} [DecidableEq A] [DecidableEq C] (X : Mat B) : Mat (A × (B × C)) :=
  fun p q => if p.1 = q.1 ∧ p.2.2 = q.2.2 then X p.2.1 q.2.1 else 0

/-- Right minus left side of SSA (3), PDF p.3, with actual marginals. -/
def ssaGap {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] (X : Mat (A × (B × C))) : ℝ :=
  entropy (marginalAB X) + entropy (traceLeft X) - entropy X -
    entropy (traceRight (traceLeft X))

/-- The literal lifted logarithm equality (4), PDF p.4. -/
def SSAlogCondition {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] (X : Mat (A × (B × C))) : Prop :=
  logMatrix X - liftAB (logMatrix (marginalAB X)) =
    liftBC (logMatrix (traceLeft X)) - liftB (logMatrix (traceRight (traceLeft X)))

/-- exp(itL), with the natural-log imaginary-power convention, PDF p.7. -/
def imaginaryExp {A : Type} [Fintype A] [DecidableEq A] (t : ℝ) (L : Mat A) : Mat A :=
  NormedSpace.exp (((t : ℂ) * Complex.I) • L)

/-- Regrouping of rho_(1,2a) tensor rho_(2b,3), PDF p.7. -/
def splitProduct {A B D C : Type} (X : Mat (A × B)) (Y : Mat (D × C)) :
    Mat (A × ((B × D) × C)) :=
  fun p q => X (p.1, p.2.1.1) (q.1, q.2.1.1) * Y (p.2.1.2, p.2.2) (q.2.1.2, q.2.2)

/-- ABC marginal of the four-register purification, PDF p.9. -/
def marginalABC {A B C D : Type} [Fintype D] (X : Mat (A × (B × (C × D)))) :
    Mat (A × (B × C)) :=
  fun p q => ∑ d, X (p.1, (p.2.1, (p.2.2, d))) (q.1, (q.2.1, (q.2.2, d)))

/-- ABD marginal of the same four-register purification, PDF p.9. -/
def marginalABD {A B C D : Type} [Fintype C] (X : Mat (A × (B × (C × D)))) :
    Mat (A × (B × D)) :=
  fun p q => ∑ c, X (p.1, (p.2.1, (c, p.2.2))) (q.1, (q.2.1, (c, q.2.2)))

/-- Inequality (22) on the actual 124 marginal (PDF pp.9,15). -/
def WeakMonotonicity {A B D : Type} [Fintype A] [Fintype B] [Fintype D]
    [DecidableEq A] [DecidableEq B] [DecidableEq D] (X : Mat (A × (B × D))) : Prop :=
  entropy (traceLeft (traceLeft X)) + entropy (traceRight (traceLeft X)) ≤
    entropy (marginalAB X) + entropy (marginalAC X)

/-- The computed rectangular Kraus isometry in (26), PDF pp.10–11. -/
def krausV {A B K : Type} (F : K → Matrix B A ℂ) : Matrix (B × K) A ℂ :=
  fun bk a => F bk.2 bk.1 a

/-- Coordinate projections I tensor |b><b| in Section 3.5, PDF p.11. -/
def coordinatePVM {A O : Type} [DecidableEq A] [DecidableEq O] (b : O) : Mat (A × O) :=
  Matrix.kronecker (1 : Mat A) (Matrix.single b b 1)

/-- Common-basis rank-one spectral measurement, PDF p.17. -/
def basisPVM {A : Type} (U : Mat A) (a : A) : Mat A :=
  fun i j => U i a * conj (U j a)

/-- Inverse square root for the faithful ensemble–POVM duality, PDF p.21. -/
def inverseRoot {A : Type} [Fintype A] [DecidableEq A] (rho : Mat A) : Mat A :=
  cfc (fun x : ℝ => (Real.sqrt x)⁻¹) rho

/-- Dual POVM, PDF p.21. Its uses require a faithful reference and positive weights. -/
def dualEffects {J A : Type} [Fintype A] [DecidableEq A]
    (rho : Mat A) (w : J → ℝ) (sigma : J → Mat A) : J → Mat A :=
  fun j => (w j : ℂ) • (inverseRoot rho * sigma j * inverseRoot rho)

/-- Unnormalized dual ensemble component sqrt(rho) E_b sqrt(rho), PDF p.21. -/
def dualUnnormalized {O A : Type} [Fintype A] [DecidableEq A]
    (rho : Mat A) (E : O → Mat A) (b : O) : Mat A :=
  cfc Real.sqrt rho * E b * cfc Real.sqrt rho

/-- Dual normalized state at an active outcome tau_b>0, PDF p.21. Its zero-mass
value is zero and is never treated as a density matrix or placed inside a log. -/
def dualStates {O A : Type} [Fintype A] [DecidableEq A]
    (rho : Mat A) (E : O → Mat A) (b : O) : Mat A :=
  ((effectProb (E b) rho : ℂ)⁻¹) • dualUnnormalized rho E b

/-- Hall's right side (59), PDF p.21, explicitly omitting zero-mass outcomes. -/
def hallBound {O A : Type} [Fintype O] [Fintype A] [DecidableEq A]
    (rho : Mat A) (E : O → Mat A) : ℝ :=
  entropy rho - ∑ b, if 0 < effectProb (E b) rho then
    effectProb (E b) rho * entropy (dualStates rho E b) else 0

/-- Equation (60), PDF p.21, retaining the factor tau_b. -/
def hallRelative {O A : Type} [Fintype O] [Fintype A] [DecidableEq A]
    (rho : Mat A) (E : O → Mat A) : ℝ :=
  ∑ b, if 0 < effectProb (E b) rho then
    effectProb (E b) rho * (relativeEntropy (dualStates rho E b) rho).toReal else 0

/-- The optimizing expression (61), PDF p.21. Only the definition is retained;
no strict comparison between global optima is inferred from one maximizing pair. -/
def UEP {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (Phi : Superop A B) (_hPhi : IsChannel Phi) [Nonempty A] [Nonempty B] : ℝ :=
  sSup {v : ℝ | ∃ rho : Mat A, IsDensityMatrix rho ∧
    ∃ m : ℕ, 0 < m ∧ ∃ E : Fin m → Mat B, IsPOVM E ∧
      v = hallBound rho (fun b => channelAdjoint Phi (E b))}

/-- MONO as a global finite PSD/support principle (PDF pp.14–15). Unnormalized
positive matrices are included, so embedded references used in the reductions are covered. -/
def MONO : Prop :=
  ∀ n m : ℕ, ∀ Phi : Superop (Fin (n + 1)) (Fin (m + 1)), IsChannel Phi →
    ∀ X Y : Mat (Fin (n + 1)), X.PosSemidef → Y.PosSemidef → SupportedBy X Y →
      SupportedBy (Phi X) (Phi Y) ∧ (relativeEntropy (Phi X) (Phi Y)).toReal ≤ (relativeEntropy X Y).toReal

/-- MPT as a global principle, with genuine partial traces, PDF pp.13–15. -/
def MPT : Prop :=
  ∀ n m : ℕ, ∀ X Y : Mat (Fin (n + 1) × Fin (m + 1)),
    X.PosSemidef → Y.PosSemidef → SupportedBy X Y →
      SupportedBy (traceLeft X) (traceLeft Y) ∧
      (relativeEntropy (traceLeft X) (traceLeft Y)).toReal ≤ (relativeEntropy X Y).toReal

/-- SSA as a global normalized PSD inequality, including block and pure states, PDF p.15. -/
def SSA : Prop :=
  ∀ n m k : ℕ, ∀ X : Mat (Fin (n + 1) × (Fin (m + 1) × Fin (k + 1))),
    IsDensityMatrix X → 0 ≤ ssaGap X

/-- JC as a global finite PSD/support principle, PDF pp.14–15. -/
def JC : Prop :=
  ∀ n k : ℕ, ∀ w : Fin (k + 1) → ℝ, IsLaw w →
    ∀ X Y : Fin (k + 1) → Mat (Fin (n + 1)),
      (∀ j, (X j).PosSemidef ∧ (Y j).PosSemidef ∧ SupportedBy (X j) (Y j)) →
      SupportedBy (average w X) (average w Y) ∧
      (relativeEntropy (average w X) (average w Y)).toReal ≤ ∑ j, w j * (relativeEntropy (X j) (Y j)).toReal

/-- Admissible positively oriented circle for the principal analytic matrix logarithm,
equation (63), PDF p.24. Its closed disk is in the scalar upper half-plane and
its open disk contains the entire spectrum, ensuring winding number one and no resolvent pole. -/
def UpperLogContour {A : Type} [Fintype A] [DecidableEq A]
    (M : Mat A) (c : ℂ) (r : ℝ) : Prop :=
  0 < r ∧ r < c.im ∧ spectrum ℂ M ⊆ Metric.ball c r

/-- Principal holomorphic matrix logarithm on upper-half-plane spectrum, using
exactly the contour-resolvent calculus (63), PDF p.24. Different admissible circles
give the same value by holomorphic functional calculus. Outside this domain the
zero value is a totalization only, never used by the Pick theorem. -/
def principalLog {A : Type} [Fintype A] [DecidableEq A] (M : Mat A) : Mat A :=
  if h : ∃ cr : ℂ × ℝ, UpperLogContour M cr.1 cr.2 then
    let cr := Classical.choose h
    ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) •
      circleIntegral (fun z => Complex.log z • (z • (1 : Mat A) - M)⁻¹) cr.1 cr.2
  else 0

/-- Epstein's nonnormal matrix pencil trace function (62), PDF p.24. -/
def epsteinTrace {A : Type} [Fintype A] [DecidableEq A]
    (K R B : Mat A) (z : ℂ) : ℂ :=
  (NormedSpace.exp (K + principalLog (z • R + B))).trace

/-! Sanity checks pinning the local definitions, without proving the paper's theorems. -/

example {A : Type} [Fintype A] [DecidableEq A] : entropy (1 : Mat A) = 0 := by
  simp [entropy, cfc_one]

example {A : Type} [Fintype A] [DecidableEq A] : logMatrix (1 : Mat A) = 0 := by
  simp [logMatrix, cfc_one]

example : shannonNats (fun _ : Unit => (1 : ℝ)) = 0 := by
  simp [shannonNats]

example {A B K : Type} (F : K → Matrix B A ℂ) (b : B) (k : K) (a : A) :
    krausV F (b, k) a = F k b a := rfl

example {A B C : Type} [Fintype C] (X : Mat (A × (B × C))) (a a2 : A) (b b2 : B) :
    marginalAB X (a, b) (a2, b2) = ∑ c, X (a, (b, c)) (a2, (b2, c)) := rfl

example {A : Type} [Fintype A] [DecidableEq A] (X : Mat A)
    (h : ¬ ∃ cr : ℂ × ℝ, UpperLogContour X cr.1 cr.2) : principalLog X = 0 := by
  simp [principalLog, h]

example {A : Type} [Fintype A] [DecidableEq A] : (relativeEntropy (1 : Mat A) 1).toReal = 0 := by
  simp [relativeEntropy, QAlgorithms.Papers.Independent.Dependency50.P21.IsSupported, cfc_one]

example {A : Type} [Fintype A] [DecidableEq A] (X : Mat A) : SupportedBy X X := le_refl _

example : FaithfulDensity (1 : Mat (Fin 1)) := by
  exact ⟨Matrix.PosDef.one, by simp [Matrix.trace]⟩

example : IsLaw (fun _ : Unit => (1 : ℝ)) := by
  exact ⟨fun _ => by norm_num, by simp⟩

example {A : Type} (X : Mat A) : average (fun _ : Unit => (1 : ℝ)) (fun _ => X) = X := by
  simp [QAlgorithms.Papers.Independent.Information100.P27.average]

example {A B C : Type} [DecidableEq C] (X : Mat (A × B)) (a a2 : A) (b b2 : B) (c : C) :
    liftAB X (a, (b, c)) (a2, (b2, c)) = X (a, b) (a2, b2) := by
  simp [liftAB]

example {A B C : Type} [DecidableEq A] (X : Mat (B × C)) (a : A) (b b2 : B) (c c2 : C) :
    liftBC X (a, (b, c)) (a, (b2, c2)) = X (b, c) (b2, c2) := by
  simp [liftBC]

example {A B C : Type} [DecidableEq A] [DecidableEq C] (X : Mat B) (a : A) (b b2 : B) (c : C) :
    liftB X (a, (b, c)) (a, (b2, c)) = X b b2 := by
  simp [liftB]

example {A : Type} [Fintype A] [DecidableEq A] (L : Mat A) : imaginaryExp 0 L = 1 := by
  simp [imaginaryExp]

example {A B D C : Type} (X : Mat (A × B)) (Y : Mat (D × C))
    (a a2 : A) (b b2 : B) (d d2 : D) (c c2 : C) :
    splitProduct X Y (a, ((b, d), c)) (a2, ((b2, d2), c2)) =
      X (a, b) (a2, b2) * Y (d, c) (d2, c2) := rfl

example {A : Type} [Fintype A] [DecidableEq A] (X : Mat A) :
    holevo (fun _ : Unit => (1 : ℝ)) (fun _ => X) = 0 := by
  simp [holevo, QAlgorithms.Papers.Independent.Information100.P56.average]

example {A : Type} [Fintype A] [DecidableEq A] : inverseRoot (1 : Mat A) = 1 := by
  simp [inverseRoot, cfc_one]

example {O A : Type} [Fintype A] [DecidableEq A] (E : O → Mat A) (b : O) :
    dualUnnormalized (1 : Mat A) E b = E b := by
  simp [dualUnnormalized, cfc_one]

example {A : Type} [DecidableEq A] (a : A) : basisPVM (1 : Mat A) a a a = 1 := by
  simp [basisPVM]

section Statements

variable {A B C D J K O : Type}
variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype J] [Fintype K] [Fintype O]
variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
variable [DecidableEq J] [DecidableEq K] [DecidableEq O]

end Statements

end QAlgorithms.Papers.Independent.Intakethird100.P51


