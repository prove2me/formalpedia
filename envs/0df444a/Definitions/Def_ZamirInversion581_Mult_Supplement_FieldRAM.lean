-- Prove2me | Definitions.Def_ZamirInversion581_Mult_Supplement_FieldRAM
-- name    : ZamirInversion581_Mult_Supplement_FieldRAM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:48:23.514553+00:00
-- url     : https://prove2.me/theorems/b25372f3-239e-4c75-84b6-fc41a25fa13b
-- title:
--   Oracle-free randomized field RAM
-- statement:
--   Fix a finite field $F$. A program is a finite list of field-operation and index instructions. Field registers and memory store elements of $F$; index registers store integers. Arithmetic, indirect loads and stores, equality tests, branches, and uniform field sampling each cost one operation. Index operations are zero, copy, increment, decrement, addition, subtraction and comparison. There is no function-valued instruction, index multiplication, or matrix-operation primitive. A halt returns failure, a field value, an integer, or one or two views of finite memory blocks. The empty program does not halt.
--
--   For a program $P$ on an initialized configuration $\sigma$, let $L_{P,\sigma}$ be its law at the least fuel by which every run has halted. Then
--   $$
--   \operatorname{HaltWithin}(P,\sigma,B)\iff\exists N\ \forall\delta\in\operatorname{supp}(\operatorname{run}_N(P,\sigma)),\quad\delta\text{ has halted and }\operatorname{ops}(\delta)\le B.
--   $$
--   The terminal-law convention uses fuel zero if no surely halting fuel exists; every theorem using terminal probabilities also guarantees termination. An integer output is accepted as a bit only when it is exactly zero or one. A single matrix algorithm is polynomial time when one exponent $k$ bounds every run by $(n+2)^k$ on every $n\times n$ matrix. Nonuniform distinguishers are dimension-indexed lists of polynomial length and polynomial running time, with bit outputs. A separate arbitrary $T(n)$ bounds the same runs, without any monotonicity assumption.
--
--   This common execution model lets pseudorandomness apply to distinguishers that contain the average-case algorithm. Initialization supplies row-major input memory; returning a memory view performs no arithmetic or writes.
-- source:
--   Or Zamir, STOC 2027 submission #581 (October 2026), source.pdf SHA-256 175df18b5c98634c390c15a304942f462478044bddc6b15bad02e5a2db2bb917, p.3–4, 11, Theorems 1.2–1.3; §3.1 field-operation convention. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/581.pdf

import Mathlib

set_option autoImplicit false

namespace ZamirInversion581.Mult.Supplement

/-! Oracle-free field RAM for pp.3–4 and §3.1, p.11 of Zamir, STOC 2027 #581.
One finite instruction list, no function-valued instructions. Each instruction costs one operation.
Field and integer index registers and field memory use the published base machine's discipline;
there is no index multiplication, field/index cast, or matrix-operation primitive.
Halting exposes a field value, integer, one block, or two blocks already stored in memory.
Block exposure reads an output view; it does not write or compute its cells. -/

inductive Instr (F : Type*) where
  | const (d : ℕ) (c : F)
  | add (d a b : ℕ)
  | sub (d a b : ℕ)
  | mul (d a b : ℕ)
  | inv (d a : ℕ)
  | sample (d : ℕ)
  | load (d i : ℕ)
  | store (i a : ℕ)
  | jeq (a b L : ℕ)
  | iset0 (d : ℕ)
  | icopy (d a : ℕ)
  | iinc (d : ℕ)
  | idec (d : ℕ)
  | iadd (d a b : ℕ)
  | isub (d a b : ℕ)
  | ijle (a b L : ℕ)
  | jmp (L : ℕ)
  | halt
  | haltField (a : ℕ)
  | haltIndex (a : ℕ)
  | haltBlock (a l : ℕ)
  | haltBlocks (a l b k : ℕ)


abbrev Program (F : Type*) := List (Instr F)


inductive Output (F : Type*) where
  | field (x : F)
  | index (x : ℤ)
  | block (xs : List F)
  | blocks (xs ys : List F)

inductive Status (F : Type*) where
  | running
  | done (out : Option (Output F))


structure Config (F : Type*) where
  pc : ℕ
  reg : ℕ → F
  ireg : ℕ → ℤ
  mem : ℤ → F
  ops : ℕ
  status : Status F


def readMat {F : Type*} (m : ℕ) (mem : ℤ → F) (base : ℤ) : Matrix (Fin m) (Fin m) F :=
  fun i j => mem (base + (m : ℤ) * (i : ℤ) + (j : ℤ))


def writeMat {F : Type*} (m : ℕ) (mem : ℤ → F) (base : ℤ) (M : Matrix (Fin m) (Fin m) F) : ℤ → F :=
  fun x =>
    match ((List.finRange m).flatMap fun i => (List.finRange m).map fun j => (i, j)).find?
        (fun p : Fin m × Fin m => decide (base + (m : ℤ) * (p.1 : ℤ) + (p.2 : ℤ) = x)) with
    | some p => M p.1 p.2
    | none => mem x


def Config.tick {F : Type*} (σ : Config F) : Config F :=
  { σ with pc := σ.pc + 1, ops := σ.ops + 1 }


def Config.jumpTo {F : Type*} (σ : Config F) (L : ℕ) : Config F :=
  { σ with pc := L, ops := σ.ops + 1 }

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]


noncomputable def exec (ins : Instr F) (σ : Config F) :
    PMF (Config F) :=
  match ins with
  | .const d c => PMF.pure { σ.tick with reg := Function.update σ.reg d c }
  | .add d a b => PMF.pure { σ.tick with reg := Function.update σ.reg d (σ.reg a + σ.reg b) }
  | .sub d a b => PMF.pure { σ.tick with reg := Function.update σ.reg d (σ.reg a - σ.reg b) }
  | .mul d a b => PMF.pure { σ.tick with reg := Function.update σ.reg d (σ.reg a * σ.reg b) }
  | .inv d a => PMF.pure { σ.tick with reg := Function.update σ.reg d (σ.reg a)⁻¹ }
  | .sample d => (PMF.uniformOfFintype F).map fun c =>
      { σ.tick with reg := Function.update σ.reg d c }
  | .load d i => PMF.pure { σ.tick with reg := Function.update σ.reg d (σ.mem (σ.ireg i)) }
  | .store i a => PMF.pure { σ.tick with mem := Function.update σ.mem (σ.ireg i) (σ.reg a) }
  | .jeq a b L => PMF.pure (if σ.reg a = σ.reg b then σ.jumpTo L else σ.tick)
  | .iset0 d => PMF.pure { σ.tick with ireg := Function.update σ.ireg d 0 }
  | .icopy d a => PMF.pure { σ.tick with ireg := Function.update σ.ireg d (σ.ireg a) }
  | .iinc d => PMF.pure { σ.tick with ireg := Function.update σ.ireg d (σ.ireg d + 1) }
  | .idec d => PMF.pure { σ.tick with ireg := Function.update σ.ireg d (σ.ireg d - 1) }
  | .iadd d a b => PMF.pure { σ.tick with ireg := Function.update σ.ireg d (σ.ireg a + σ.ireg b) }
  | .isub d a b => PMF.pure { σ.tick with ireg := Function.update σ.ireg d (σ.ireg a - σ.ireg b) }
  | .ijle a b L => PMF.pure (if σ.ireg a ≤ σ.ireg b then σ.jumpTo L else σ.tick)
  | .jmp L => PMF.pure (σ.jumpTo L)
  | .halt => PMF.pure { σ with ops := σ.ops + 1, status := .done none }
  | .haltField a => PMF.pure { σ with ops := σ.ops + 1, status := .done (some (.field (σ.reg a))) }
  | .haltIndex a => PMF.pure { σ with ops := σ.ops + 1, status := .done (some (.index (σ.ireg a))) }
  | .haltBlock a l => PMF.pure { σ with
      ops := σ.ops + 1
      status := .done (some (.block ((List.range (σ.ireg l).toNat).map
        (fun i => σ.mem (σ.ireg a + (i : ℤ)))))) }
  | .haltBlocks a l b k => PMF.pure { σ with
      ops := σ.ops + 1
      status := .done (some (.blocks ((List.range (σ.ireg l).toNat).map
        (fun i => σ.mem (σ.ireg a + (i : ℤ)))) ((List.range (σ.ireg k).toNat).map
        (fun i => σ.mem (σ.ireg b + (i : ℤ)))))) }


noncomputable def step (P : Program F) (σ : Config F) :
    PMF (Config F) :=
  match σ.status with
  | .done _ => PMF.pure σ
  | .running =>
      match P[σ.pc]? with
      | none => PMF.pure { σ with ops := σ.ops + 1 }
      | some ins => exec ins σ


noncomputable def run (P : Program F) :
    ℕ → Config F → PMF (Config F)
  | 0, σ => PMF.pure σ
  | N + 1, σ => (run P N σ).bind (step P)


def initConfig {F : Type*} [Zero F] (args : List ℕ) (mem : ℤ → F) : Config F where
  pc := 0
  reg := fun _ => 0
  ireg := fun r => ((args.getD r 0 : ℕ) : ℤ)
  mem := mem
  ops := 0
  status := .running


/-- Dense row-major matrix input, with all other memory zero. -/
def matrixInput (n : ℕ) (args : List ℕ) (X : Matrix (Fin n) (Fin n) F) : Config F :=
  initConfig args (writeMat n (fun _ => 0) 0 X)

/-- Finite block input; all other cells are zero. -/
def blockInput (args : List ℕ) (xs : List F) : Config F :=
  initConfig args (fun i => if 0 ≤ i then xs.getD i.toNat 0 else 0)

/-- Every supported run has halted by this fuel. -/
def HaltedAt (P : Program F) (σ₀ : Config F) (N : ℕ) : Prop :=
  ∀ σ ∈ (run P N σ₀).support, σ.status ≠ .running

/-- The first surely halting fuel; zero if no such fuel exists. -/
noncomputable def finalFuel (P : Program F) (σ₀ : Config F) : ℕ :=
  sInf {N | HaltedAt P σ₀ N}

/-- The terminal law; only used with a surely terminating input. -/
noncomputable def finalLaw (P : Program F) (σ₀ : Config F) : PMF (Config F) :=
  run P (finalFuel P σ₀) σ₀

/-- Worst-case time, counting every executed instruction and every supported random branch. -/
def HaltWithin (P : Program F) (σ₀ : Config F) (B : ℝ) : Prop :=
  ∃ N : ℕ, HaltedAt P σ₀ N ∧
    ∀ σ ∈ (run P N σ₀).support, (σ.ops : ℝ) ≤ B

/-- Probability of a predicate on a discrete law, in real numbers. -/
noncomputable def eventProb {α : Type*} (μ : PMF α) (E : α → Prop) : ℝ := by
  classical
  exact ((μ.map (fun x => decide (E x))) true).toReal

/-- Probability of a halting output satisfying a predicate; other output kinds are wrong. -/
noncomputable def accepts (P : Program F) (σ₀ : Config F) (E : Output F → Prop) : ℝ :=
  eventProb (finalLaw P σ₀) (fun σ => ∃ o, σ.status = .done (some o) ∧ E o)

/-- A single uniform program, polynomial in dimension on every matrix and every random branch. -/
def PolyTime (P : Program F) : Prop :=
  ∃ k : ℕ, ∀ n (X : Matrix (Fin n) (Fin n) F),
    HaltWithin P (matrixInput n [n] X) ((n + 2 : ℝ) ^ k)

/-- An arbitrary additional time bound. No monotonicity is imposed. -/
def TimeBound (P : Program F) (T : ℕ → NNReal) : Prop :=
  ∀ n (X : Matrix (Fin n) (Fin n) F), HaltWithin P (matrixInput n [n] X) (T n : ℝ)

/-- Nonuniform probabilistic polynomial-time bit distinguishers. -/
def NonuniformPPT (D : ℕ → Program F) : Prop :=
  ∃ k : ℕ, ∀ n, (D n).length ≤ (n + 2) ^ k ∧
    ∀ X : Matrix (Fin n) (Fin n) F,
      HaltWithin (D n) (matrixInput n [n] X) ((n + 2 : ℝ) ^ k) ∧
      ∀ σ ∈ (finalLaw (D n) (matrixInput n [n] X)).support,
        σ.status = .done (some (.index 0)) ∨ σ.status = .done (some (.index 1))

end ZamirInversion581.Mult.Supplement


