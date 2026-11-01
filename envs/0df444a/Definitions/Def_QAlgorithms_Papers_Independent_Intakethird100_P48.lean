-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P48
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P48
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T05:30:12.043745+00:00
-- url     : https://prove2.me/theorems/455eff3f-9a4c-4874-8bdd-ea4b03a9a4f2
-- title:
--   Definitions for Distilling Non-Locality
-- statement:
--   The objects the formalized statements of *Distilling Non-Locality* (arXiv:0809.3173) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Behavior`: PDF pp.1–2: a binary-input, binary-output conditional probability table. Arguments are ordered x,y,a,b. Validity is supplied by IsBinaryNS.
--   - `IsBinaryNS`: PDF pp.1–2: positivity, normalization at every input, and both no-signaling marginal equalities, including input pairs assigned zero probability by an input law.
--   - `binaryCorrelator`: PDF p.2: the correlator X_xy=P(00|xy)+P(11|xy)-P(01|xy)-P(10|xy).
--   - `chshAt`: PDF p.2, Definition 1: absolute three-plus/one-minus CHSH expression.
--   - `nonlocality`: PDF p.2, Definition 1: the maximum over exactly the four CHSH input pairs. Nested binary maxima avoid any empty-set or unbounded real-supremum convention.
--   - `ParallelProtocol`: PDF pp.2–3: deterministic parallel local operations on n resource copies. Neither party's input/output functions access any remote data or the resource table. This is the class containing the exhibited NDP; it is not a model of every adaptive wiring.
--   - `parityProtocol`: PDF pp.2–3 and Fig.1: all copies receive the same local input and each party outputs its own XOR using frozen dotBits against the all-true history. The wiring is fixed independently of the resource behavior.
--   - `parallelOutputLaw`: PDF p.3, proof of Theorem 1: actual simulated output distribution. The product is the joint law of independent identical resource instances.
--   - `StrictlyDistills`: PDF p.2, Definition 2, specialized to an explicitly local parallel wiring: valid input/output boxes, a non-local resource, and strictly increased CHSH non-locality.
--   - `parameterBox`: PDF p.3: the full two-parameter probability table, with r=epsilon at xy=11 and r=delta otherwise. Positivity domain is 0<=epsilon,delta<=1.
--   - `epsilonBox`: PDF pp.2–3: P_epsilon is the delta=0 resource, not its protocol output.
--   - `HilbertSystem`: Hilbert spaces used by the source's quantum-state/local-observable model, PDF pp.2–3. No finite-dimensional or separability hypothesis is imposed.
--   - `JointSpace`: PDF pp.2–3: completed spatial tensor product for a bipartite pure state.
--   - `IsBinaryPOVM`: PDF pp.2–3: a genuine binary local POVM, using Mathlib positivity (self-adjoint positive operators), not just a correlator test.
--   - `IsQuantum`: PDF pp.2–3: exact quantum realization of the whole probability table by a normalized spatial bipartite state and input-dependent local binary measurements. An enlarged local Hilbert space accommodates purification and shared randomness. Mathlib Completion.map of TensorProduct.mapL supplies the completed local action.
--   - `quantumDistilledValues`: PDF p.4: all actually distilled values from quantum members of the full positivity square, with copy number varied. No scalar-sector shortcut or real sSup.
--   - `optimalDelta`: PDF p.4: exact delta corresponding to the displayed rounded optimizer 0.03806.
--   - `optimalEpsilon`: PDF p.4: exact epsilon corresponding to the displayed rounded optimizer 0.30866.
-- source:
--   Distilling Non-Locality, arXiv:0809.3173v4, https://arxiv.org/abs/0809.3173v4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

/-!
# Distilling Non-Locality (arXiv:0809.3173v4)

Paper-local definitions and six statement targets. False/true label bits 0/1.
The protocol acts on independent identical resource copies. All no-signaling
constraints hold at every input, independently of any input distribution.
Quantum realizability uses normalized states on completed spatial tensor products
and genuine local POVMs, with unrestricted Hilbert spaces. Mixed states can be
purified into an enlarged local space. No arcsine criterion is a definition.
Compilation is pending the separate mechanical handoff.
-/

namespace QAlgorithms.Papers.Independent.Intakethird100.P48

open scoped BigOperators TensorProduct

noncomputable section

/-- PDF pp.1–2: a binary-input, binary-output conditional probability table.
Arguments are ordered x,y,a,b. Validity is supplied by IsBinaryNS. -/
abbrev Behavior := Bool → Bool → Bool → Bool → ℝ

/-- PDF pp.1–2: positivity, normalization at every input, and both no-signaling
marginal equalities, including input pairs assigned zero probability by an input law. -/
def IsBinaryNS (P : Behavior) : Prop :=
  (∀ x y a b, 0 ≤ P x y a b) ∧
  (∀ x y, ∑ a : Bool, ∑ b : Bool, P x y a b = 1) ∧
  (∀ x y z a, ∑ b : Bool, P x y a b = ∑ b : Bool, P x z a b) ∧
  (∀ x z y b, ∑ a : Bool, P x y a b = ∑ a : Bool, P z y a b)

/-- PDF p.2: the correlator X_xy=P(00|xy)+P(11|xy)-P(01|xy)-P(10|xy). -/
def binaryCorrelator (P : Behavior) (x y : Bool) : ℝ :=
  P x y false false + P x y true true - P x y false true - P x y true false

/-- PDF p.2, Definition 1: absolute three-plus/one-minus CHSH expression. -/
def chshAt (P : Behavior) (x y : Bool) : ℝ :=
  |binaryCorrelator P x y + binaryCorrelator P x (!y) + binaryCorrelator P (!x) y -
    binaryCorrelator P (!x) (!y)|

/-- PDF p.2, Definition 1: the maximum over exactly the four CHSH input pairs.
Nested binary maxima avoid any empty-set or unbounded real-supremum convention. -/
def nonlocality (P : Behavior) : ℝ :=
  max (max (chshAt P false false) (chshAt P false true))
    (max (chshAt P true false) (chshAt P true true))

/-- PDF pp.2–3: deterministic parallel local operations on n resource copies.
Neither party's input/output functions access any remote data or the resource table.
This is the class containing the exhibited NDP; it is not a model of every adaptive wiring. -/
structure ParallelProtocol (n : ℕ) where
  aliceInput : Bool → Fin n → Bool
  bobInput : Bool → Fin n → Bool
  aliceOutput : Bool → Qubits n → Bool
  bobOutput : Bool → Qubits n → Bool

/-- PDF pp.2–3 and Fig.1: all copies receive the same local input and each party
outputs its own XOR using frozen dotBits against the all-true history.
The wiring is fixed independently of the resource behavior. -/
def parityProtocol (n : ℕ) : ParallelProtocol n where
  aliceInput := fun x _ => x
  bobInput := fun y _ => y
  aliceOutput := fun _ a => dotBits a (fun _ => true)
  bobOutput := fun _ b => dotBits b (fun _ => true)

/-- PDF p.3, proof of Theorem 1: actual simulated output distribution.
The product is the joint law of independent identical resource instances. -/
def parallelOutputLaw {n : ℕ} (W : ParallelProtocol n) (P : Behavior) : Behavior :=
  fun x y a b => ∑ u : Qubits n, ∑ v : Qubits n,
    if W.aliceOutput x u = a ∧ W.bobOutput y v = b then
      ∏ i : Fin n, P (W.aliceInput x i) (W.bobInput y i) (u i) (v i)
    else 0

/-- PDF p.2, Definition 2, specialized to an explicitly local parallel wiring:
valid input/output boxes, a non-local resource, and strictly increased CHSH non-locality. -/
def StrictlyDistills {n : ℕ} (W : ParallelProtocol n) (P : Behavior) : Prop :=
  IsBinaryNS P ∧ IsBinaryNS (parallelOutputLaw W P) ∧
    2 < nonlocality P ∧ nonlocality P < nonlocality (parallelOutputLaw W P)

/-- PDF p.3: the full two-parameter probability table, with r=epsilon at xy=11
and r=delta otherwise. Positivity domain is 0<=epsilon,delta<=1. -/
def parameterBox (epsilon delta : ℝ) : Behavior :=
  fun x y a b =>
    let r := if x && y then epsilon else delta
    if a = b then (1 - r) / 2 else r / 2

/-- PDF pp.2–3: P_epsilon is the delta=0 resource, not its protocol output. -/
def epsilonBox (epsilon : ℝ) : Behavior := parameterBox epsilon 0

/-- Hilbert spaces used by the source's quantum-state/local-observable model,
PDF pp.2–3. No finite-dimensional or separability hypothesis is imposed. -/
structure HilbertSystem where
  carrier : Type
  [normed : NormedAddCommGroup carrier]
  [innerSpace : InnerProductSpace ℂ carrier]
  [complete : CompleteSpace carrier]

attribute [instance] HilbertSystem.normed HilbertSystem.innerSpace HilbertSystem.complete

/-- PDF pp.2–3: completed spatial tensor product for a bipartite pure state. -/
abbrev JointSpace (A B : HilbertSystem) :=
  UniformSpace.Completion (TensorProduct ℂ A.carrier B.carrier)

/-- PDF pp.2–3: a genuine binary local POVM, using Mathlib positivity
(self-adjoint positive operators), not just a correlator test. -/
def IsBinaryPOVM {A : HilbertSystem} (M : Bool → A.carrier →L[ℂ] A.carrier) : Prop :=
  (∀ a, (M a).IsPositive) ∧ ∑ a : Bool, M a = 1

/-- PDF pp.2–3: exact quantum realization of the whole probability table by a
normalized spatial bipartite state and input-dependent local binary measurements.
An enlarged local Hilbert space accommodates purification and shared randomness.
Mathlib Completion.map of TensorProduct.mapL supplies the completed local action. -/
def IsQuantum (P : Behavior) : Prop :=
  ∃ (A B : HilbertSystem) (psi : JointSpace A B)
    (M : Bool → Bool → A.carrier →L[ℂ] A.carrier)
    (N : Bool → Bool → B.carrier →L[ℂ] B.carrier),
    ‖psi‖ = 1 ∧ (∀ x, IsBinaryPOVM (A := A) (M x)) ∧ (∀ y, IsBinaryPOVM (A := B) (N y)) ∧
      ∀ x y a b, P x y a b = (inner ℂ psi (UniformSpace.Completion.map (TensorProduct.mapL (M x a) (N y b)) psi)).re

/-- PDF p.4: all actually distilled values from quantum members of the full
positivity square, with copy number varied. No scalar-sector shortcut or real sSup. -/
def quantumDistilledValues : Set ℝ :=
  {z | ∃ (epsilon delta : ℝ) (n : ℕ),
    0 ≤ epsilon ∧ epsilon ≤ 1 ∧ 0 ≤ delta ∧ delta ≤ 1 ∧ 1 < n ∧
    IsQuantum (parameterBox epsilon delta) ∧
    StrictlyDistills (parityProtocol n) (parameterBox epsilon delta) ∧
    z = nonlocality (parallelOutputLaw (parityProtocol n) (parameterBox epsilon delta))}

/-- PDF p.4: exact delta corresponding to the displayed rounded optimizer 0.03806. -/
def optimalDelta : ℝ := (1 - Real.cos (Real.pi / 8)) / 2

/-- PDF p.4: exact epsilon corresponding to the displayed rounded optimizer 0.30866. -/
def optimalEpsilon : ℝ := (1 - Real.cos (3 * Real.pi / 8)) / 2

/-! Definition sanity checks; these are not additional paper-result targets. -/

example (a : Qubits 0) : dotBits a (fun _ => true) = false := by
  simp [dotBits, Bool.zero_eq_false]

example (a : Qubits 1) : dotBits a (fun _ => true) = a 0 := by simp [dotBits]

example (n : ℕ) (x : Bool) (i : Fin n) : (parityProtocol n).aliceInput x i = x := rfl

example (epsilon delta : ℝ) : parameterBox epsilon delta true true false true = epsilon / 2 := by
  simp [parameterBox]

example (epsilon delta : ℝ) : parameterBox epsilon delta false true false false = (1 - delta) / 2 := by
  simp [parameterBox]

example (epsilon : ℝ) : epsilonBox epsilon = parameterBox epsilon 0 := rfl

example (P : Behavior) : binaryCorrelator P false false =
    P false false false false + P false false true true -
      P false false false true - P false false true false := rfl

example (A B : HilbertSystem) : ¬ ‖(0 : JointSpace A B)‖ = 1 := by simp

example (A : HilbertSystem) : (0 : A.carrier →L[ℂ] A.carrier).IsPositive :=
  ContinuousLinearMap.isPositive_zero

example {A B : HilbertSystem} (M : A.carrier →L[ℂ] A.carrier)
    (N : B.carrier →L[ℂ] B.carrier) (t : TensorProduct ℂ A.carrier B.carrier) :
    UniformSpace.Completion.map (TensorProduct.mapL M N) (t : JointSpace A B) =
      ((TensorProduct.mapL M N t) : JointSpace A B) :=
  UniformSpace.Completion.map_coe (TensorProduct.mapL M N).uniformContinuous t

/-- At the excluded local endpoint, the resource has exactly the Bell-bound value. -/
example : nonlocality (epsilonBox 0) = 2 := by
  norm_num [nonlocality, chshAt, binaryCorrelator, epsilonBox, parameterBox]

/-- Zero resource copies produce the deterministic output pair 00 independently of P. -/
example (P : Behavior) (x y a b : Bool) :
    parallelOutputLaw (parityProtocol 0) P x y a b =
      if a = false ∧ b = false then 1 else 0 := by
  simp [parallelOutputLaw, parityProtocol, dotBits, Qubits, Bool.zero_eq_false, eq_comm]

end

end QAlgorithms.Papers.Independent.Intakethird100.P48


