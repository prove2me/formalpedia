-- Prove2me | Definitions.Def_PermanentStars_Counting_Execution
-- name    : PermanentStars_Counting_Execution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:51:16.497166+00:00
-- url     : https://prove2.me/theorems/d651e013-4e64-470b-bf3f-bc77209f710d
-- title:
--   Counted uniform construction and ring evaluation
-- statement:
--   A uniform constructor is a single finite deterministic RAM program with input $n$. The reused RAM executes literal assignments, addition, truncated subtraction, halving, indirect access and conditional branches, charging actual logarithmic operand and address lengths. At halt its memory contains a literal four-word graph header and five words per transition (tail, head, label tag, row and column). No instruction returns an entire graph.
--
--   The ring evaluator visits numerically ordered vertices and accumulates incoming transition contributions. Its returned count increases by two for each executed multiplication-and-addition pair; it never tests equality of ring elements. Fixed units and matrix entries are input reads.
--
--   The full target predicate requires a positive $C$ and natural $d$, chosen with the constructor before every input, with bound
--   $$B(n)=C(n+1)^d(2-10^{-40})^n.$$
--   It asserts actual halting, the emitted ABP, elementary labels, equality to the symbolic permanent over integer coefficients, correctness and counted evaluation over every commutative ring, and bounds for construction cost, total graph size and ring operations. These are propositions to prove, not certificates supplied as algorithm data.
-- source:
--   Radu Curticapean, STOC 2027 submission #1331 (October 2026), Theorem 1.1, p.1; §2, p.5; Definition 2.2, p.6; §6, p.12

import Definitions.Def_PermanentStars_Counting_Graphs
import Definitions.Def_MinrankTW_RAM

universe u_countExecution

namespace PermanentStars.Counting

def inputMemory (n : ℕ) : ℕ → ℕ := fun i => if i = 0 then n else 0

def Label.tag {n : ℕ} : Label n → ℕ
  | .zero => 0 | .one => 1 | .negOne => 2 | .var _ _ => 3 | .negVar _ _ => 4

def Label.row {n : ℕ} : Label n → ℕ
  | .var i _ | .negVar i _ => i.val | _ => 0

def Label.col {n : ℕ} : Label n → ℕ
  | .var _ j | .negVar _ j => j.val | _ => 0

/-- A literal output array: four header words, followed by five words per edge occurrence. -/
def Emits {n v : ℕ} (m : ℕ → ℕ) (G : Graph (Fin v) (Label n)) : Prop :=
  m 0 = v ∧ m 1 = G.source.val ∧ m 2 = G.sink.val ∧ m 3 = G.edges.length ∧
  ∀ (i : ℕ) (e : Fin v × Fin v × Label n), G.edges[i]? = some e →
    m (4 + 5 * i) = e.1.val ∧ m (5 + 5 * i) = e.2.1.val ∧
    m (6 + 5 * i) = e.2.2.tag ∧ m (7 + 5 * i) = e.2.2.row ∧
    m (8 + 5 * i) = e.2.2.col

def Ordered {n v : ℕ} (G : Graph (Fin v) (Label n)) : Prop :=
  ∀ e ∈ G.edges, e.1.val < e.2.1.val

/-- One node evaluation. Each contributing edge executes one multiplication and one addition.
The fixed units and the input entries are reads, not ring arithmetic instructions. -/
def evalNode {n v : ℕ} {R : Type*} [CommRing R]
    (G : Graph (Fin v) (Label n)) (A : Matrix (Fin n) (Fin n) R)
    (mem : Fin v → R) (i : Fin v) : R × ℕ :=
  G.edges.foldl (fun acc e => if e.2.1 = i then
      (acc.1 + mem e.1 * e.2.2.eval A, acc.2 + 2) else acc)
    (if i = G.source then (1, 0) else (0, 0))

/-- Topological evaluation is a concrete fold, with the count accumulated during execution. -/
def evaluate {n v : ℕ} {R : Type*} [CommRing R]
    (G : Graph (Fin v) (Label n)) (A : Matrix (Fin n) (Fin n) R) : R × ℕ :=
  let result := (List.finRange v).foldl (fun state i =>
    let z := evalNode G A state.1 i
    (Function.update state.1 i z.1, state.2 + z.2)) ((fun _ => 0), 0)
  (result.1 G.sink, result.2)

noncomputable def resourceBound (C : ℝ) (d n : ℕ) : ℝ :=
  C * (n + 1 : ℝ) ^ d * (2 - (10 : ℝ)⁻¹ ^ 40) ^ n

/-- Full-strength target predicate. Program code and constants are outside all inputs.
Construction uses the reused finite-instruction RAM's actual logarithmic execution cost.
This predicate contains assertions to prove; none are fields of a graph or an algorithm. -/
def FastPermanent : Prop :=
  ∃ (P : List MinrankTW.Instr) (C : ℝ) (d : ℕ), 0 < C ∧
    ∀ n : ℕ, ∃ (steps v : ℕ) (G : Graph (Fin v) (Label n)),
      MinrankTW.IsHalted P (MinrankTW.run P ⟨0, inputMemory n⟩ steps) ∧
      Emits (MinrankTW.run P ⟨0, inputMemory n⟩ steps).mem G ∧
      (MinrankTW.runCost P ⟨0, inputMemory n⟩ steps : ℝ) ≤ resourceBound C d n ∧
      G.IsABP ∧ Ordered G ∧ (∀ e ∈ G.edges, e.2.2.elementary) ∧
      G.output (Label.symbolic (n := n)) =
        Matrix.permanent (fun i j : Fin n => (MvPolynomial.X (i, j) : MvPolynomial (Fin n × Fin n) ℤ)) ∧
      (G.size : ℝ) ≤ resourceBound C d n ∧
      (∀ (R : Type u_countExecution) [CommRing R] (A : Matrix (Fin n) (Fin n) R),
        G.output (Label.eval A) = Matrix.permanent A ∧
        (evaluate G A).1 = Matrix.permanent A ∧
        ((evaluate G A).2 : ℝ) ≤ resourceBound C d n)

end PermanentStars.Counting


