-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Information100_P48
-- name    : QAlgorithms_Papers_Independent_Information100_P48
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T11:38:54.917975+00:00
-- url     : https://prove2.me/theorems/a9487d7a-131b-4312-a4cf-4dae6195d1d2
-- title:
--   Definitions for Coherent Control of Channel Dilations Activate Temporal Bell Nonclassicality
-- statement:
--   The objects the formalized statements of *Coherent Control of Channel Dilations Activate Temporal Bell Nonclassicality* (arXiv:2607.05643) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `QOp`: Qubit operators, with the frozen library's Bool computational basis.
--   - `QQOp`: Two-qubit operators in first-register, second-register order.
--   - `outcomeSign`: PDF p.3, Eq.(6): the sign of a dichotomic outcome; false is +.
--   - `pairIndex`: Computational ordering 00,01,10,11 used on PDF p.3.
--   - `pairMatrix`: Reindex a displayed four-by-four matrix in the source's tensor order.
--   - `k0`: PDF p.3, Eq.(7): positive no-jump ADC Kraus operator.
--   - `k1`: PDF p.3, Eq.(8): positive jump ADC Kraus operator.
--   - `adc`: PDF p.3, Eq.(13): ADC on every input operator.
--   - `principalAngle`: PDF p.3: principal angle, needed for the positive Kraus convention.
--   - `adcDilationGenerator`: PDF p.3, Eq.(10): dimensionless Hermitian ADC generator.
--   - `adcUnitary`: PDF p.3, Eq.(12): the displayed system/environment unitary.
--   - `dilation`: Principal-angle physical ADC dilation, PDF p.3.
--   - `traceEnv`: Partial trace over the second register, as used in Eqs.(9),(22),(42).
--   - `cleanInput`: Initially uncorrelated input with the environment in a pure basis state.
--   - `cross`: PDF p.7, Eqs.(38),(39): diagonal reductions and off-diagonal cross maps.
--   - `interference`: PDF p.4, Eq.(19): clean-input/clean-output interference block.
--   - `embed0`: PDF p.4: embed a dilation on S,E0, leaving E1 inactive.
--   - `embed1`: PDF p.4: embed a dilation on S,E1, leaving E0 inactive.
--   - `selectedOperator`: PDF pp.4,7, Eqs.(21),(41): Hadamard-selected joint operator, initial control +.
--   - `branch`: Operational CP outcome map, retaining the environment until after selection.
--   - `controlledPair`: PDF pp.4,6, Eqs.(14),(32): actual controlled system/environment unitary.
--   - `jointCS`: PDF pp.4,7: evolve an uncorrelated control/system/environment input and discard E.
--   - `hadamardProjector`: Hadamard-basis control state/projector, PDF p.4.
--   - `selectControl`: Projectively measure the control and trace it out; no success normalization.
--   - `controlBlocks`: Explicit control block matrix in Eqs.(18),(40).
--   - `IsCP`: Finite-dimensional CP maps, without the trace-preserving Kraus condition.
--   - `normalize`: Normalize an operator by its real trace; statements guard strict positivity.
--   - `independentADC`: PDF pp.5–6: independent-environment ADC coherent outcome maps.
--   - `sharedADC`: PDF p.8: shared-environment forward/inverse coherent outcome maps.
--   - `incoherentIndependent`: PDF pp.5,8: selected outcome for incoherent independent-environment control.
--   - `incoherentShared`: PDF p.8: selected outcome for incoherent forward/inverse control.
--   - `mixedQubit`: PDF p.3, Eq.(6): normalized initial system state I/2.
--   - `projector`: PDF p.3, Eq.(5): rank-one projector for a unit Bloch observable.
--   - `rawJoint`: PDF pp.6,8, Eqs.(31),(52): joint probability before conditioning.
--   - `success`: Actual success probability marginalized over Alice's outcomes.
--   - `conditionalJoint`: Condition the joint distribution on the selected control outcome.
--   - `correlator`: PDF p.2, Eq.(2): temporal correlator with outcomes ±1.
--   - `temporal`: PDF pp.2–3, Eqs.(3),(6): fixed equatorial temporal CHSH value.
--   - `activation`: Extra violation beyond the deterministic baseline; equality at 1/2 is included.
--   - `independentCritical`: Exact crossing determined by Eq.(53), PDF p.9.
--   - `sharedCritical`: Exact crossing determined by Eq.(54), PDF p.9.
--   - `pauli`: Appendix A, p.11: Pauli coordinate order X,Y,Z.
--   - `bloch`: Dichotomic observable associated to a Bloch vector.
--   - `UnitDirection`: Unit Bloch direction, retaining all three axes.
--   - `bellDensity`: Appendix A, Eq.(A1): normalized Bell density, reference first.
--   - `choi`: Choi operator of any map; no trace-preserving assumption.
--   - `conditionalChoi`: Choi state of a successful selected CP map.
--   - `correlationTensor`: Appendix A, Eq.(A5): spatial tensor; Alice's Pauli has no temporal transpose here.
--   - `spatialCHSH`: Spatial CHSH expectation for arbitrary four unit Bloch axes.
--   - `spatialValues`: Attainable spatial CHSH values. IsGreatest states both attainment and the bound.
--   - `branchSuccess`: Success conditioned on Alice's recorded outcome, as distinct from marginal success.
--   - `adcChoiMatrix`: Formula (A4), PDF p.11, in reference/output order.
--   - `independentChoiMatrix`: Formula (A9), PDF p.12. Denominator 4-g is strictly positive on [0,1].
--   - `sharedChoiMatrix`: Formula (A13), PDF p.12. Denominator 2-g is strictly positive on [0,1].
--   - `independentSpatialMaximum`: Correct unrestricted maximum: the z eigenvalue overtakes an equatorial one above 8/9.
-- source:
--   Coherent Control of Channel Dilations Activate Temporal Bell Nonclassicality, arXiv:2607.05643v1, https://arxiv.org/abs/2607.05643v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Channel

/-!
Statements from arXiv:2607.05643v1. System/environment tensor order is S,E;
control/system order is C,S. Bool false/true denotes computational 0/1.
Outcome false/true denotes +1 and -1, respectively. All conditioning uses actual positive traces.
Compilation is pending the separate batch handoff.
-/

namespace QAlgorithms.Papers.Independent.Information100.P48

open scoped Matrix ComplexConjugate

noncomputable section

/-- Qubit operators, with the frozen library's Bool computational basis. -/
abbrev QOp := Matrix Bool Bool ℂ

/-- Two-qubit operators in first-register, second-register order. -/
abbrev QQOp := Matrix (Bool × Bool) (Bool × Bool) ℂ

/-- PDF p.3, Eq.(6): the sign of a dichotomic outcome; false is +. -/
def outcomeSign (minus : Bool) : ℝ := if minus then -1 else 1

/-- Computational ordering 00,01,10,11 used on PDF p.3. -/
def pairIndex (p : Bool × Bool) : Fin 4 :=
  if p.1 then (if p.2 then 3 else 2) else (if p.2 then 1 else 0)

/-- Reindex a displayed four-by-four matrix in the source's tensor order. -/
def pairMatrix (M : Matrix (Fin 4) (Fin 4) ℂ) : QQOp :=
  fun p q => M (pairIndex p) (pairIndex q)

/-- PDF p.3, Eq.(7): positive no-jump ADC Kraus operator. -/
def k0 (g : ℝ) : QOp :=
  Matrix.diagonal fun b => if b then (Real.sqrt (1 - g) : ℂ) else 1

/-- PDF p.3, Eq.(8): positive jump ADC Kraus operator. -/
def k1 (g : ℝ) : QOp :=
  fun a b => if a = false ∧ b = true then (Real.sqrt g : ℂ) else 0

/-- PDF p.3, Eq.(13): ADC on every input operator. -/
def adc (g : ℝ) (rho : QOp) : QOp :=
  k0 g * rho * (k0 g)ᴴ + k1 g * rho * (k1 g)ᴴ

/-- PDF p.3: principal angle, needed for the positive Kraus convention. -/
def principalAngle (g : ℝ) : ℝ := Real.arcsin (Real.sqrt g)

/-- PDF p.3, Eq.(10): dimensionless Hermitian ADC generator. -/
def adcDilationGenerator : QQOp :=
  (1 / 2 : ℂ) • (Matrix.kronecker pauliX pauliY - Matrix.kronecker pauliY pauliX)

/-- PDF p.3, Eq.(12): the displayed system/environment unitary. -/
def adcUnitary (theta : ℝ) : QQOp :=
  pairMatrix !![1, 0, 0, 0;
    0, (Real.cos theta : ℂ), (Real.sin theta : ℂ), 0;
    0, -(Real.sin theta : ℂ), (Real.cos theta : ℂ), 0;
    0, 0, 0, 1]

/-- Principal-angle physical ADC dilation, PDF p.3. -/
def dilation (g : ℝ) : QQOp := adcUnitary (principalAngle g)

/-- Partial trace over the second register, as used in Eqs.(9),(22),(42). -/
def traceEnv {S E : Type*} [Fintype E]
    (M : Matrix (S × E) (S × E) ℂ) : Matrix S S ℂ :=
  fun s t => ∑ e, M (s, e) (t, e)

/-- Initially uncorrelated input with the environment in a pure basis state. -/
def cleanInput {E : Type*} [DecidableEq E] (e : E) (rho : QOp) :
    Matrix (Bool × E) (Bool × E) ℂ :=
  Matrix.kronecker rho (Matrix.single e e 1)

/-- PDF p.7, Eqs.(38),(39): diagonal reductions and off-diagonal cross maps. -/
def cross {E : Type*} [Fintype E] [DecidableEq E]
    (U V : Matrix (Bool × E) (Bool × E) ℂ) (e : E) (rho : QOp) : QOp :=
  traceEnv (U * cleanInput e rho * Vᴴ)

/-- PDF p.4, Eq.(19): clean-input/clean-output interference block. -/
def interference {E : Type*} (U : Matrix (Bool × E) (Bool × E) ℂ) (e : E) : QOp :=
  fun s t => U (s, e) (t, e)

/-- PDF p.4: embed a dilation on S,E0, leaving E1 inactive. -/
def embed0 {E0 E1 : Type*} [DecidableEq E1]
    (U : Matrix (Bool × E0) (Bool × E0) ℂ) :
    Matrix (Bool × (E0 × E1)) (Bool × (E0 × E1)) ℂ :=
  fun p q => U (p.1, p.2.1) (q.1, q.2.1) * if p.2.2 = q.2.2 then 1 else 0

/-- PDF p.4: embed a dilation on S,E1, leaving E0 inactive. -/
def embed1 {E0 E1 : Type*} [DecidableEq E0]
    (U : Matrix (Bool × E1) (Bool × E1) ℂ) :
    Matrix (Bool × (E0 × E1)) (Bool × (E0 × E1)) ℂ :=
  fun p q => U (p.1, p.2.2) (q.1, q.2.2) * if p.2.1 = q.2.1 then 1 else 0

/-- PDF pp.4,7, Eqs.(21),(41): Hadamard-selected joint operator, initial control +. -/
def selectedOperator {E : Type*}
    (U V : Matrix (Bool × E) (Bool × E) ℂ) (minus : Bool) :
    Matrix (Bool × E) (Bool × E) ℂ :=
  (1 / 2 : ℂ) • (U + (outcomeSign minus : ℂ) • V)

/-- Operational CP outcome map, retaining the environment until after selection. -/
def branch {E : Type*} [Fintype E] [DecidableEq E]
    (U V : Matrix (Bool × E) (Bool × E) ℂ) (e : E) (minus : Bool) (rho : QOp) : QOp :=
  cross (selectedOperator U V minus) (selectedOperator U V minus) e rho

/-- PDF pp.4,6, Eqs.(14),(32): actual controlled system/environment unitary. -/
def controlledPair {E : Type*} [DecidableEq E]
    (U V : Matrix (Bool × E) (Bool × E) ℂ) :
    Matrix (Bool × (Bool × E)) (Bool × (Bool × E)) ℂ :=
  fun p q => if p.1 = q.1 then (if p.1 then V p.2 q.2 else U p.2 q.2) else 0

/-- PDF pp.4,7: evolve an uncorrelated control/system/environment input and discard E. -/
def jointCS {E : Type*} [Fintype E] [DecidableEq E]
    (tau : QOp) (U V : Matrix (Bool × E) (Bool × E) ℂ) (e : E) (rho : QOp) : QQOp :=
  let W := controlledPair U V
  let R := W * Matrix.kronecker tau (cleanInput e rho) * Wᴴ
  fun p q => ∑ f, R (p.1, (p.2, f)) (q.1, (q.2, f))

/-- Hadamard-basis control state/projector, PDF p.4. -/
def hadamardProjector (minus : Bool) : QOp :=
  fun a b => (1 / 2 : ℂ) *
    (if a then (outcomeSign minus : ℂ) else 1) *
    (if b then (outcomeSign minus : ℂ) else 1)

/-- Projectively measure the control and trace it out; no success normalization. -/
def selectControl (R : QQOp) (minus : Bool) : QOp :=
  let P := Matrix.kronecker (hadamardProjector minus) (1 : QOp)
  traceLeft (P * R * Pᴴ)

/-- Explicit control block matrix in Eqs.(18),(40). -/
def controlBlocks (D0 D1 C01 C10 : QOp) : QQOp :=
  fun p q => (1 / 2 : ℂ) *
    (if p.1 then (if q.1 then D1 p.2 q.2 else C10 p.2 q.2)
     else (if q.1 then C01 p.2 q.2 else D0 p.2 q.2))

/-- Finite-dimensional CP maps, without the trace-preserving Kraus condition. -/
def IsCP (Phi : QOp → QOp) : Prop :=
  ∃ (m : ℕ) (K : Fin m → QOp), ∀ rho, Phi rho = ∑ j, K j * rho * (K j)ᴴ

/-- Normalize an operator by its real trace; statements guard strict positivity. -/
def normalize {I : Type*} [Fintype I] (R : Matrix I I ℂ) : Matrix I I ℂ :=
  ((R.trace.re)⁻¹ : ℂ) • R

/-- PDF pp.5–6: independent-environment ADC coherent outcome maps. -/
def independentADC (g : ℝ) (minus : Bool) : QOp → QOp :=
  branch (embed0 (E1 := Bool) (dilation g)) (embed1 (E0 := Bool) (dilation g))
    (false, false) minus

/-- PDF p.8: shared-environment forward/inverse coherent outcome maps. -/
def sharedADC (g : ℝ) (minus : Bool) : QOp → QOp :=
  branch (dilation g) (dilation g)ᴴ false minus

/-- PDF pp.5,8: selected outcome for incoherent independent-environment control. -/
def incoherentIndependent (g : ℝ) (minus : Bool) (rho : QOp) : QOp :=
  selectControl (jointCS ((1 / 2 : ℂ) • (1 : QOp))
    (embed0 (E1 := Bool) (dilation g)) (embed1 (E0 := Bool) (dilation g))
    (false, false) rho) minus

/-- PDF p.8: selected outcome for incoherent forward/inverse control. -/
def incoherentShared (g : ℝ) (minus : Bool) (rho : QOp) : QOp :=
  selectControl (jointCS ((1 / 2 : ℂ) • (1 : QOp))
    (dilation g) (dilation g)ᴴ false rho) minus

/-- PDF p.3, Eq.(6): normalized initial system state I/2. -/
def mixedQubit : QOp := (1 / 2 : ℂ) • (1 : QOp)

/-- PDF p.3, Eq.(5): rank-one projector for a unit Bloch observable. -/
def projector (A : QOp) (minus : Bool) : QOp :=
  (1 / 2 : ℂ) • ((1 : QOp) + (outcomeSign minus : ℂ) • A)

/-- PDF pp.6,8, Eqs.(31),(52): joint probability before conditioning. -/
def rawJoint (Phi : QOp → QOp) (A B : QOp) (a b : Bool) : ℝ :=
  (1 / 2 : ℝ) * (projector B b * Phi (projector A a)).trace.re

/-- Actual success probability marginalized over Alice's outcomes. -/
def success (Phi : QOp → QOp) : ℝ := (Phi mixedQubit).trace.re

/-- Condition the joint distribution on the selected control outcome. -/
def conditionalJoint (Phi : QOp → QOp) (A B : QOp) (a b : Bool) : ℝ :=
  rawJoint Phi A B a b / success Phi

/-- PDF p.2, Eq.(2): temporal correlator with outcomes ±1. -/
def correlator (Phi : QOp → QOp) (A B : QOp) : ℝ :=
  ∑ a : Bool, ∑ b : Bool,
    outcomeSign a * outcomeSign b * conditionalJoint Phi A B a b

/-- PDF pp.2–3, Eqs.(3),(6): fixed equatorial temporal CHSH value. -/
def temporal (Phi : QOp → QOp) : ℝ :=
  let B0 := ((Real.sqrt 2)⁻¹ : ℂ) • (pauliX + pauliY)
  let B1 := ((Real.sqrt 2)⁻¹ : ℂ) • (pauliX - pauliY)
  correlator Phi pauliX B0 + correlator Phi pauliX B1 +
    correlator Phi pauliY B0 - correlator Phi pauliY B1

/-- Extra violation beyond the deterministic baseline; equality at 1/2 is included. -/
def activation (Phi : ℝ → QOp → QOp) : Set ℝ :=
  {g | 0 ≤ g ∧ g ≤ 1 ∧ temporal (adc g) ≤ 2 ∧ 2 < temporal (Phi g)}

/-- Exact crossing determined by Eq.(53), PDF p.9. -/
def independentCritical : ℝ := 4 * Real.sqrt 10 - 12

/-- Exact crossing determined by Eq.(54), PDF p.9. -/
def sharedCritical : ℝ := 2 * (Real.sqrt 2 - 1)

/-- Appendix A, p.11: Pauli coordinate order X,Y,Z. -/
def pauli (i : Fin 3) : QOp := ![pauliX, pauliY, pauliZ] i

/-- Dichotomic observable associated to a Bloch vector. -/
def bloch (a : Fin 3 → ℝ) : QOp := ∑ i, (a i : ℂ) • pauli i

/-- Unit Bloch direction, retaining all three axes. -/
def UnitDirection (a : Fin 3 → ℝ) : Prop := ∑ i, a i ^ 2 = 1

/-- Appendix A, Eq.(A1): normalized Bell density, reference first. -/
def bellDensity : QQOp :=
  fun p q => if p.1 = p.2 ∧ q.1 = q.2 then (1 / 2 : ℂ) else 0

/-- Choi operator of any map; no trace-preserving assumption. -/
def choi (Phi : QOp → QOp) : QQOp := idTensorSuperop Phi bellDensity

/-- Choi state of a successful selected CP map. -/
def conditionalChoi (Phi : QOp → QOp) : QQOp := normalize (choi Phi)

/-- Appendix A, Eq.(A5): spatial tensor; Alice's Pauli has no temporal transpose here. -/
def correlationTensor (J : QQOp) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => (J * Matrix.kronecker (pauli i) (pauli j)).trace.re

/-- Spatial CHSH expectation for arbitrary four unit Bloch axes. -/
def spatialCHSH (J : QQOp) (a0 a1 b0 b1 : Fin 3 → ℝ) : ℝ :=
  (J * (Matrix.kronecker (bloch a0) (bloch b0 + bloch b1) +
    Matrix.kronecker (bloch a1) (bloch b0 - bloch b1))).trace.re

/-- Attainable spatial CHSH values. IsGreatest states both attainment and the bound. -/
def spatialValues (J : QQOp) : Set ℝ :=
  {v | ∃ a0 a1 b0 b1, UnitDirection a0 ∧ UnitDirection a1 ∧
    UnitDirection b0 ∧ UnitDirection b1 ∧ v = spatialCHSH J a0 a1 b0 b1}

/-- Success conditioned on Alice's recorded outcome, as distinct from marginal success. -/
def branchSuccess (Phi : QOp → QOp) (a : Fin 3 → ℝ) (minus : Bool) : ℝ :=
  (Phi (projector (bloch a) minus)).trace.re

/-- Formula (A4), PDF p.11, in reference/output order. -/
def adcChoiMatrix (g : ℝ) : QQOp :=
  pairMatrix !![(1 / 2 : ℂ), 0, 0, (Real.sqrt (1 - g) : ℂ) / 2;
    0, 0, 0, 0;
    0, 0, (g : ℂ) / 2, 0;
    (Real.sqrt (1 - g) : ℂ) / 2, 0, 0, ((1 - g : ℝ) : ℂ) / 2]

/-- Formula (A9), PDF p.12. Denominator 4-g is strictly positive on [0,1]. -/
def independentChoiMatrix (g : ℝ) : QQOp :=
  (1 / ((4 - g : ℝ) : ℂ)) • pairMatrix !![2, 0, 0, 2 * (Real.sqrt (1 - g) : ℂ);
    0, 0, 0, 0; 0, 0, (g : ℂ), 0;
    2 * (Real.sqrt (1 - g) : ℂ), 0, 0, 2 * ((1 - g : ℝ) : ℂ)]

/-- Formula (A13), PDF p.12. Denominator 2-g is strictly positive on [0,1]. -/
def sharedChoiMatrix (g : ℝ) : QQOp :=
  (1 / ((2 - g : ℝ) : ℂ)) • pairMatrix !![1, 0, 0, (Real.sqrt (1 - g) : ℂ);
    0, 0, 0, 0; 0, 0, 0, 0;
    (Real.sqrt (1 - g) : ℂ), 0, 0, ((1 - g : ℝ) : ℂ)]

/-- Correct unrestricted maximum: the z eigenvalue overtakes an equatorial one above 8/9. -/
def independentSpatialMaximum (g : ℝ) : ℝ :=
  if g ≤ 8 / 9 then 8 * Real.sqrt (2 - 2 * g) / (4 - g)
  else 2 * Real.sqrt (16 * (1 - g) + (4 - 3 * g) ^ 2) / (4 - g)

/-! Definition sanity examples: small entries, tensor order, signs, and zero conventions. -/

example : outcomeSign false = 1 := rfl

example : pairIndex (true, false) = 2 := rfl

example : k0 0 false false = 1 := by simp [k0]

example : k1 0 false true = 0 := by simp [k1]

example : adcUnitary 0 (false, false) (false, false) = 1 := rfl

example : cleanInput false (1 : QOp) (false, true) (false, true) = 0 := by
  simp [cleanInput, Matrix.kronecker, Matrix.single]

example : hadamardProjector true false true = -(1 / 2 : ℂ) := by
  norm_num [hadamardProjector, outcomeSign]

example (rho : QOp) : normalize rho = ((rho.trace.re)⁻¹ : ℂ) • rho := rfl

example : bellDensity (false, false) (true, true) = (1 / 2 : ℂ) := rfl

example (A : QOp) : projector A false = (1 / 2 : ℂ) • ((1 : QOp) + A) := by
  simp [projector, outcomeSign]

example : pauli 1 = pauliY := rfl

example (g : ℝ) : sharedChoiMatrix g (false, true) (false, true) = 0 := by
  simp [sharedChoiMatrix, pairMatrix, pairIndex]

/-- Identical coherent paths have a zero-probability destructive outcome. -/
example {E : Type*} [Fintype E] [DecidableEq E]
    (U : Matrix (Bool × E) (Bool × E) ℂ) (e : E) (rho : QOp) :
    branch U U e true rho = 0 := by
  ext s t
  simp [branch, cross, selectedOperator, outcomeSign, traceEnv]

/-- The finite-Kraus CP predicate includes the zero outcome map. -/
example : IsCP (fun _ => 0) := by
  refine ⟨0, (fun i => Fin.elim0 i), ?_⟩
  intro rho
  simp

/-- A zero selected map has no success probability. -/
example : success (fun _ => 0) = 0 := by simp [success]

/-- Totalized conditioning of a zero map is zero, never a claimed probability law. -/
example (A B : QOp) (a b : Bool) : conditionalJoint (fun _ => 0) A B a b = 0 := by
  simp [conditionalJoint, rawJoint, success]

/-- The zero Bloch vector is excluded from the measurement optimization. -/
example : ¬ UnitDirection (fun _ => 0) := by simp [UnitDirection]

/-- The zero Bloch vector has zero observable, as distinct from a dichotomic axis. -/
example : bloch (fun _ => 0) = 0 := by simp [bloch]

/-- The zero Choi operator has zero spatial tensor. -/
example : correlationTensor 0 = 0 := by
  ext i j
  simp [correlationTensor]

/-- The zero Choi operator has zero CHSH expectation for all axes. -/
example (a0 a1 b0 b1 : Fin 3 → ℝ) : spatialCHSH 0 a0 a1 b0 b1 = 0 := by
  simp [spatialCHSH]

end

end QAlgorithms.Papers.Independent.Information100.P48


