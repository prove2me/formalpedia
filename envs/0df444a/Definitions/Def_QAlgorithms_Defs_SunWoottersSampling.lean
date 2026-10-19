-- Prove2me | Definitions.Def_QAlgorithms_Defs_SunWoottersSampling
-- name    : QAlgorithms_Defs_SunWoottersSampling
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:37:28.859806+00:00
-- url     : https://prove2.me/theorems/b72189c4-84be-4122-9bce-8269367a591b
-- title:
--   SunWoottersSampling
-- statement:
--   SunWoottersSampling
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\SunWoottersSampling.lean

import Definitions.Def_QAlgorithms_Defs_SunWoottersFibers
noncomputable section

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.SunWootters

/-- Actual ideal flagged attempt: preparation, reversible indexer, index Hadamard,
joint projection J=0,Q=1, then positive-phase final field QFT;
2607.16541 pp.13–14. Failed attempts emit none. -/
def idealAttempt {p m n : ℕ} [NeZero p]
    (H : Matrix (Fin n) (Fin m) (ZMod p)) (g : Fin m → ZMod p → ℂ)
    (D : ShellDomain m) (positive : 0 < errorNormSq g D) (q : ℕ)
    (lists : (Fin n → ZMod p) → List (Fin m → ZMod p))
    (nodup : ∀ s, (lists s).Nodup) (fits : ∀ s, (lists s).length ≤ 2^q)
    (_complete : ∀ s, (lists s).toFinset = shellFiber H D s) :
    Option (Fin n → ZMod p) → ℝ :=
  let before := tensorVec (labeledErrorState H g D positive) (ket (0,false))
  let U := listIndexer q lists nodup fits
  let indexH : Matrix (((Fin m → ZMod p) × (Fin n → ZMod p)) × (Qubits q × Bool))
      (((Fin m → ZMod p) × (Fin n → ZMod p)) × (Qubits q × Bool)) ℂ :=
    Matrix.kronecker 1 (Matrix.kronecker (hadamardN q) 1)
  let measured := act (indexH*U) before
  let branch : EuclideanSpace ℂ ((Fin m → ZMod p) × (Fin n → ZMod p)) :=
    WithLp.toLp 2 fun ys => measured (ys,(0,true))
  let final := act (Matrix.kronecker 1
    (piKron n ((qftMatrix p).submatrix (fun z : ZMod p => ⟨z.val,z.val_lt⟩)
      (fun z : ZMod p => ⟨z.val,z.val_lt⟩)))) branch
  fun output => match output with
    | none => 1-‖branch‖^2
    | some x => ∑ y : Fin m → ZMod p, prob final (y,x)

/-- Exact clean local Fourier preparation interface; 2607.16541 p.14, Definition 6.1.
The circuit is an actual membership-oracle circuit, and controlled U/U† are
used with their structurally counted implementation, not supplied for free. -/
structure LocalFourierPreparation (p m : ℕ) where
  prime : p.Prime
  m_pos : 0 < m
  c : ℕ
  c_pos : 0 < c
  c_lt : c < p
  ancillas : ℕ
  circuit : Fin m → OracleCircuit oneTwoQubitGateSet
    (fun _ : Fin 1 => Nat.clog 2 m+Nat.clog 2 p+1) (Nat.clog 2 p+ancillas)
  realizes : ∀ sets : Fin m → Finset (ZMod p), (∀ i, (sets i).card = c) → ∀ i,
    letI : NeZero p := ⟨prime.ne_zero⟩
    let rho := (c : ℝ)/p
    let g := fun a => ((if a ∈ sets i then 1 else 0)-rho)/Real.sqrt (rho*(1-rho))
    let ideal : EuclideanSpace ℂ (Qubits (Nat.clog 2 p+ancillas)) :=
      WithLp.toLp 2 fun z => if (qubitsAppendEquiv (Nat.clog 2 p) ancillas z).2 = 0 then
        if h : bitsToNat (qubitsAppendEquiv (Nat.clog 2 p) ancillas z).1 < p then
          localFourier g ((bitsToNat (qubitsAppendEquiv (Nat.clog 2 p) ancillas z).1 : ℕ) : ZMod p) else 0
      else 0
    act ((circuit i).unitary (fun _ => OPI.indexedQubitOracle sets)) (zeroKet _) = ideal
  controlledCircuit : Fin m → OracleCircuit oneTwoQubitGateSet
    (fun _ : Fin 1 => Nat.clog 2 m+Nat.clog 2 p+1) (Nat.clog 2 p+ancillas+1)
  controlledRealizes : ∀ sets : Fin m → Finset (ZMod p), (∀ i, (sets i).card = c) → ∀ i,
    letI : NeZero p := ⟨prime.ne_zero⟩
    (controlledCircuit i).unitary (fun _ => OPI.indexedQubitOracle sets) =
      controlledQubits ((circuit i).unitary (fun _ => OPI.indexedQubitOracle sets))

/-- Source Fourier-access cost from the actual plain/controlled circuits;
2607.16541 p.14, Definition 6.1. Adjoint access reverses the same finite circuits;
every membership call and elementary gate is included. -/
def LocalFourierPreparation.accessCost {p m : ℕ} (U : LocalFourierPreparation p m) : ℕ :=
  Finset.univ.sup fun i => max (U.circuit i).length (U.controlledCircuit i).length

/-- Full encoded-state/operator finite-precision specification;
2607.16541 p.16 (46). Invalid-code leakage is included in these full norms.
This contract includes both the precision bounds and the resulting success/conditional-TV
bounds; the corresponding theorem establishes the latter from the former. -/
def SuccessfulBranchAccuracy {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [DecidableEq X] (ideal implemented : EuclideanSpace ℂ I)
    (Pi : Matrix I I ℂ) (Qideal Qimplemented : Matrix I I ℂ)
    (decode : I → X) (L : ℕ) (eta : ℝ) : Prop :=
  0 < L ∧ 0 < eta ∧ eta < 1 ∧ IsState ideal ∧ IsState implemented ∧
    Pi.IsHermitian ∧ Pi*Pi = Pi ∧
    Qideal ∈ Matrix.unitaryGroup _ ℂ ∧ Qimplemented ∈ Matrix.unitaryGroup _ ℂ ∧
    1/(2*(L : ℝ)) ≤ ‖act Pi ideal‖^2 ∧
    ‖implemented-ideal‖ ≤ min (1/(8*(L : ℝ))) (eta/(4*Real.sqrt (2*(L : ℝ)))) ∧
    specNorm (Qimplemented-Qideal) ≤ eta/2 ∧
    let idealBranch := act Qideal (act Pi ideal)
    let implementedBranch := act Qimplemented (act Pi implemented)
    1/(4*(L : ℝ)) ≤ ‖act Pi implemented‖^2 ∧
    tvDist (fun x => probEvent implementedBranch (fun z => decode z = x) /
      ‖act Pi implemented‖^2)
      (fun x => probEvent idealBranch (fun z => decode z = x) / ‖act Pi ideal‖^2) ≤ eta

/-- Independent capped attempts, first success retained; 2607.16541 pp.16–17.
Costs belong to each executed attempt and add under this product law. -/
def restartLoop {X : Type*} (attempt : PMF (Option X)) : ℕ → PMF (Option X)
  | 0 => PMF.pure none
  | t+1 => attempt.bind fun output => match output with
      | some x => PMF.pure (some x)
      | none => restartLoop attempt t

/-- Restart execution with costs from each actual attempted leaf accumulated,
including failed attempts; 2607.16541 pp.16–17. -/
def pricedRestartLoop {X : Type*} (attempt : PMF (Option X × ℕ)) :
    ℕ → PMF (Option X × ℕ)
  | 0 => PMF.pure (none,0)
  | t+1 => attempt.bind fun result => match result.1 with
      | some x => PMF.pure (some x,result.2)
      | none => (pricedRestartLoop attempt t).map fun next => (next.1,result.2+next.2)

/-- Exactly ceil(4L log(1/beta)) independent attempts;
2607.16541 pp.16–17. -/
def restartLaw {X : Type*} (attempt : PMF (Option X × ℕ)) (L : ℕ) (_hL : 0 < L)
    (beta : ℝ) (_hbeta : 0 < beta ∧ beta < 1) : PMF (Option X × ℕ) :=
  pricedRestartLoop attempt ⌈4*(L : ℝ)*Real.log beta⁻¹⌉₊

example {X : Type*} (attempt : PMF (Option X)) :
    restartLoop attempt 0 = PMF.pure none := rfl

end QAlgorithms.SunWootters


