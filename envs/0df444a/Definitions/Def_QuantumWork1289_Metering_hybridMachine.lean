-- Prove2me | Definitions.Def_QuantumWork1289_Metering_hybridMachine
-- name    : QuantumWork1289_Metering_hybridMachine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T04:37:10.828419+00:00
-- url     : https://prove2.me/theorems/e3c24344-db8d-4553-b347-e2c10130cc64
-- title:
--   Hybrid oracle machines with retained quantum memory
-- statement:
--   Let $X$ be the entire address domain, $B$ a finite additive answer group, and $n$ an arbitrary finite quantum memory dimension. A machine has unrestricted classical control states and four actions: halt with a classical output; apply an oracle-independent complete finite Kraus instrument; read a classical address and receive its classical answer; or apply the coherent XOR oracle. For a routed query register the coherent action is
--
--   $$|x,y,z\rangle\longmapsto|x,y+f(x),z\rangle.$$
--
--   The remaining quantum memory $z$ is retained. A quantum input to a classical call is first measured by a private instrument; its classical outcome chooses the subsequent read. That read passes the conditional quantum state intact. Arbitrary further private instruments can depend on the read answer. Classical randomness, adaptive choices, loops, private channels and intermediate measurements are permitted.
--
--   Execution is calculated recursively to a finite horizon. Each branch retains its unnormalized density operator, and its Born mass is the real trace. A timeout keeps a frontier state but contributes no accepted output. Every actual read increments the classical count; every coherent call increments the quantum count. A budget holds on every positive-mass finite prefix for every fixed oracle, including preprocessing and prefixes that never terminate. Initial states are positive semidefinite with trace one.
--
--   This operational layer supplies a separately metered adversary model. It contains no low-degree certificate, candidate list, hardness assertion or success bound. Each finite-register computation can use an arbitrary dimension and arbitrary address routing; there is no common register-size, gate-count or address-length bound.
-- source:
--   Mohammed Barhoush, Proof of Quantum Work with Classical Verification, STOC 2027 submission #1289 (October 2026), pp. 12–14, §3.2 and the one-block experiment; p. 17, §5.1; pp. 20–21, Born-rule branch semantics

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QAlgorithms_Defs_QuantumInstruments
set_option autoImplicit false

open scoped ENNReal ComplexOrder

namespace QuantumWork1289.Metering

/-- A coherent call may address any finite register, routed into the entire oracle domain X.
No common address-length or dimension bound is imposed on machines. -/
structure QueryWire (X B : Type) (n : ℕ) where
  addresses : ℕ
  workspace : ℕ
  split : Fin n ≃ ((Fin addresses × B) × Fin workspace)
  address : Fin addresses → X

/-- Oracle-independent control, with separate classical reads and coherent calls.
A classical input is already a classical value. Measuring a quantum input first is a
private instrument followed by a read in its outcome continuation. Its answer is classical;
the retained quantum memory is passed intact. -/
inductive HybridAction (X B O S : Type) (n : ℕ) where
  | halt (output : O)
  | privateOp (b : ℕ)
      (instrument : QAlgorithms.CopyMeasurements.QuantumInstrument (Fin n) (Fin b))
      (next : Fin b → S)
  | classicalRead (address : X) (next : B → S)
  | coherentCall (wire : QueryWire X B n) (next : S)

/-- step and initial control are fixed independently of the sampled oracle.
Unbounded control types and loops impose no runtime, uniformity, or gate-count bound. -/
structure HybridMachine (X B O S : Type) (n : ℕ) where
  initial : S
  step : S → HybridAction X B O S n

/-- A terminal branch contains the actual two query counts and its unnormalized state. -/
structure Terminal (O : Type) (n : ℕ) where
  output : Option O
  classicalQueries : ℕ
  quantumQueries : ℕ
  state : Matrix (Fin n) (Fin n) ℂ

/-- Physical initial density operator, including arbitrary independent quantum advice. -/
structure InitialState (n : ℕ) where
  matrix : Matrix (Fin n) (Fin n) ℂ
  positive : matrix.PosSemidef
  normalized : Matrix.trace matrix = 1

open scoped Matrix in
/-- The published XOR query tensored with identity on every retained workspace register. -/
noncomputable def queryMatrix {X B : Type} [Fintype B] [DecidableEq B]
    [AddCommGroup B] {n : ℕ} (w : QueryWire X B n) (f : X → B) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun p q => Matrix.kronecker (QAlgorithms.xorOracle (f ∘ w.address))
    (1 : Matrix (Fin w.workspace) (Fin w.workspace) ℂ) (w.split p) (w.split q)

/-- Finite-horizon execution; a timeout carries a nonterminal frontier state. Private instruments retain the
subnormalized branch state, rather than measuring/reinitializing the whole memory. -/
noncomputable def execute {X B O S : Type} [Fintype B] [DecidableEq B]
    [AddCommGroup B] {n : ℕ} (A : HybridMachine X B O S n) (f : X → B) :
    ℕ → S → Matrix (Fin n) (Fin n) ℂ → List (Terminal O n)
  | 0, _, ρ => [⟨none, 0, 0, ρ⟩]
  | t + 1, s, ρ => match A.step s with
    | .halt o => [⟨some o, 0, 0, ρ⟩]
    | .privateOp b M next =>
        (List.ofFn fun j : Fin b => execute A f t (next j)
          (QAlgorithms.CopyMeasurements.instrumentBranch M j ρ)).flatten
    | .classicalRead x next =>
        (execute A f t (next (f x)) ρ).map fun z =>
          { z with classicalQueries := z.classicalQueries + 1 }
    | .coherentCall w next =>
        let U := queryMatrix w f
        (execute A f t next (U * ρ * U.conjTranspose)).map fun z =>
          { z with quantumQueries := z.quantumQueries + 1 }

/-- Actual Born mass; no normalization after selecting a branch. -/
noncomputable def branchMass {O : Type} {n : ℕ} (z : Terminal O n) : ℝ≥0∞ :=
  ENNReal.ofReal (Matrix.trace z.state).re

/-- Worst-case budgets on every positive-probability finite prefix, for every oracle.
Frontier states make nonterminating paths count too; every preprocessing call is charged. -/
def HasBudgets {X B O S : Type} [Fintype B] [DecidableEq B] [AddCommGroup B]
    {n : ℕ} (A : HybridMachine X B O S n) (ρ : InitialState n) (C Q : ℕ) : Prop :=
  ∀ f t z, z ∈ execute A f t A.initial ρ.matrix → 0 < branchMass z →
    z.classicalQueries ≤ C ∧ z.quantumQueries ≤ Q

open Classical in
/-- Weight of accepted outputs returned by this horizon, summed over measurement branches. -/
noncomputable def acceptedMass {X B O S : Type} [Fintype B] [DecidableEq B]
    [AddCommGroup B] {n : ℕ} (A : HybridMachine X B O S n) (ρ : InitialState n)
    (accept : (X → B) → O → Prop) (t : ℕ) (f : X → B) : ℝ≥0∞ :=
  ((execute A f t A.initial ρ.matrix).map fun z =>
    match z.output with
    | none => 0
    | some o => if accept f o then branchMass z else 0).sum

end QuantumWork1289.Metering


