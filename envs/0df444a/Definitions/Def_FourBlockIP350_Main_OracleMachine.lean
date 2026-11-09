-- Prove2me | Definitions.Def_FourBlockIP350_Main_OracleMachine
-- name    : FourBlockIP350_Main_OracleMachine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:33:14.632289+00:00
-- url     : https://prove2.me/theorems/e8b61811-806e-47f1-8511-ae57c91c52b5
-- title:
--   Separate comparison-oracle arithmetic computation and query charges
-- statement:
--   A comparison algorithm is a finite list of instructions using rational constants, indexed real registers, arithmetic, integer rounding, branching and comparison-oracle queries. The input registers initially contain the dimension $d$ and radius $\rho$. A query compares two $d$-coordinate lattice points assembled from registers, without returning either function value.
--   $$B_\rho\cap\mathbb Z^d=\left\{z:\sum_j z_j^2\le\rho^2\right\}.$$
--   Every query on a valid run must belong to this full domain; division by zero and an invalid program counter are disallowed. A halting instruction points to the output registers. Queries and all other executed instructions are charged separately. The statement imposes correctness and bounds on actual execution prefixes, rather than assigning abstract costs to a solver.
--
--   **Formalization Note** This arithmetic model is used only for Theorem 2.9. Its unit-cost real operations are never identified with binary steps of the main solver. Registers not mentioned in input initially hold zero, and indirect addresses use nonnegative integer floor.
-- source:
--   Klaus Jansen, Felix Ohnesorge, Corinna Wambsganz, A Fixed-Parameter Algorithm for 4-Block Integer Programming, STOC 2027 submission #350 (October 2026), p. 5–6, Definition 2.4 and Theorem 2.9

import Mathlib
import Definitions.Def_FourBlockIP350_Main_LatticeConvexity

namespace FourBlockIP350.Main

open scoped BigOperators

/-- Addressing and elementary rational constants are finite program data. -/
inductive Address
  | direct (j : ℕ)
  | indirect (j : ℕ)
  deriving DecidableEq

/-- Arithmetic/comparison machine, distinct from the binary-time solver model.
Registers are real, addresses are nonnegative integers. Floor is integer rounding.
There are no function-evaluation, minimization, or geometric-oracle instructions. -/
inductive OracleInstruction
  | constant (dst : Address) (q : ℚ)
  | copy (dst src : Address)
  | add (dst a b : Address)
  | sub (dst a b : Address)
  | mul (dst a b : Address)
  | divide (dst a b : Address)
  | floor (dst src : Address)
  | branch (a b : Address) (lt eq gt : ℕ)
  | jump (pc : ℕ)
  | query (a b : Address) (lt eq gt : ℕ)
  | halt (output : Address)
  deriving DecidableEq

abbrev OracleProgram := List OracleInstruction

structure OracleConfig where
  pc : ℕ
  registers : ℕ → ℝ

noncomputable def addressValue (s : OracleConfig) : Address → ℕ
  | .direct j => j
  | .indirect j => ⌊s.registers j⌋₊

noncomputable def readReg (s : OracleConfig) (a : Address) : ℝ := s.registers (addressValue s a)

noncomputable def storeReg (s : OracleConfig) (a : Address) (x : ℝ) : OracleConfig :=
  ⟨s.pc + 1, Function.update s.registers (addressValue s a) x⟩

noncomputable def pointAt (d : ℕ) (s : OracleConfig) (a : Address) : RVec d :=
  fun j => s.registers (addressValue s a + j.val)

noncomputable def compareReal (x y : ℝ) : Ordering :=
  if x < y then .lt else if x = y then .eq else .gt

def selectBranch (v : Ordering) (lt eq gt : ℕ) : ℕ :=
  match v with | .lt => lt | .eq => eq | .gt => gt

/-- Oracle results are supplied only for comparing two lattice points.
No numerical value of the objective enters the execution state. -/
noncomputable def oracleStep (d : ℕ) (P : OracleProgram)
    (O : RVec d → RVec d → Ordering) (s : OracleConfig) : OracleConfig :=
  match P[s.pc]? with
  | some (.constant dst q) => storeReg s dst q
  | some (.copy dst src) => storeReg s dst (readReg s src)
  | some (.add dst a b) => storeReg s dst (readReg s a + readReg s b)
  | some (.sub dst a b) => storeReg s dst (readReg s a - readReg s b)
  | some (.mul dst a b) => storeReg s dst (readReg s a * readReg s b)
  | some (.divide dst a b) => storeReg s dst (readReg s a / readReg s b)
  | some (.floor dst src) => storeReg s dst (Int.floor (readReg s src))
  | some (.branch a b lt eq gt) =>
      {s with pc := selectBranch (compareReal (readReg s a) (readReg s b)) lt eq gt}
  | some (.jump pc) => {s with pc := pc}
  | some (.query a b lt eq gt) =>
      {s with pc := selectBranch (O (pointAt d s a) (pointAt d s b)) lt eq gt}
  | _ => s

def oracleInitial (d : ℕ) (ρ : ℝ) : OracleConfig :=
  ⟨0, fun j => if j = 0 then (d : ℝ) else if j = 1 then ρ else 0⟩

noncomputable def oracleState (d : ℕ) (ρ : ℝ) (P : OracleProgram)
    (O : RVec d → RVec d → Ordering) (t : ℕ) : OracleConfig :=
  (oracleStep d P O)^[t] (oracleInitial d ρ)

/-- Closed Euclidean ball; the square is a sum of coordinate squares, not the sup norm. -/
def BallLattice (d : ℕ) (ρ : ℝ) : Set (ZVec d) :=
  {x | (∑ j, (x j : ℝ)^2) ≤ ρ^2}

def RealBallLattice (d : ℕ) (ρ : ℝ) : Set (RVec d) :=
  {x | ∃ z ∈ BallLattice d ρ, realVec z = x}

noncomputable def ComparisonOracle {d : ℕ} (ρ : ℝ) (h : ZVec d → ℝ)
    (O : RVec d → RVec d → Ordering) : Prop :=
  ∀ x ∈ BallLattice d ρ, ∀ y ∈ BallLattice d ρ,
    O (realVec x) (realVec y) = compareReal (h x) (h y)

/-- Every instruction and address in the executed prefix is legitimate. In particular,
queries lie on the entire stated ball-domain, and division by zero is forbidden. -/
noncomputable def OraclePrefixValid (d : ℕ) (ρ : ℝ) (P : OracleProgram)
    (O : RVec d → RVec d → Ordering) (t : ℕ) : Prop :=
  ∀ j < t, let s := oracleState d ρ P O j
    match P[s.pc]? with
    | none => False
    | some (.divide _ _ b) => readReg s b ≠ 0
    | some (.query a b _ _ _) =>
        pointAt d s a ∈ RealBallLattice d ρ ∧ pointAt d s b ∈ RealBallLattice d ρ
    | some (.halt _) => False
    | _ => True

noncomputable def queryCount (d : ℕ) (ρ : ℝ) (P : OracleProgram)
    (O : RVec d → RVec d → Ordering) (t : ℕ) : ℕ :=
  ((List.range t).filter fun j => match P[(oracleState d ρ P O j).pc]? with
    | some (.query _ _ _ _ _) => true
    | _ => false).length

/-- Non-query instructions are charged separately from queries. -/
noncomputable def arithmeticCount (d : ℕ) (ρ : ℝ) (P : OracleProgram)
    (O : RVec d → RVec d → Ordering) (t : ℕ) : ℕ :=
  t - queryCount d ρ P O t

end FourBlockIP350.Main


