-- Prove2me | Definitions.Def_QuantumGroupCodes836_Addressability_Decoder
-- name    : QuantumGroupCodes836_Addressability_Decoder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T17:10:46.142795+00:00
-- url     : https://prove2.me/theorems/f9d7c4db-2e35-484b-983b-56e4eb0dfd0c
-- title:
--   Operational syndrome-decoder programs and Las Vegas charged cost
-- statement:
--   A decoder is a fixed finite register program with field arithmetic, bounded word arithmetic, memory, branches and uniform random field symbols. Its input contains measured syndrome and immutable stabilizer matrices with self-delimiting size headers, followed by bounded reusable auxiliary data. It never receives the unknown error.
--
--   $$\mathbb E[T]=\sum_{s\ge0}\Pr(T>s).$$
--
--   The tail probabilities are computed from finite random prefixes of actual execution. Almost-sure termination is their convergence to zero. Every halting execution must return a correction in the proper error coset; output reads are charged. Alphabet transport only relabels literal field constants. The code description is reused across calls; all accesses and all per-call arithmetic are charged.
-- source:
--   Virgile Guemard, Jean Gasnier, STOC 2027 submission #836 (October 2026), Theorem 4.7, p.18; footnotes 3 and 7, pp.3,18; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/836.pdf

import Mathlib
import Definitions.Def_QuantumGroupCodes836_Addressability_Quantum

set_option autoImplicit false
noncomputable section

open scoped ENNReal NNReal

namespace QuantumGroupCodes836.Addressability

/-- Unit-cost field RAM. Word registers and addresses are reduced modulo W.
The program and word-size exponent are fixed before code length or syndrome. -/
inductive DecoderInstruction (F : Type)
  | fieldConstant (dst : ℕ) (c : F)
  | fieldAdd (dst x y : ℕ)
  | fieldMul (dst x y : ℕ)
  | fieldInv (dst x : ℕ)
  | randomField (dst : ℕ)
  | wordConstant (dst value : ℕ)
  | wordAdd (dst x y : ℕ)
  | wordMul (dst x y : ℕ)
  | wordSub (dst x y : ℕ)
  | load (dst address : ℕ)
  | store (address src : ℕ)
  | input (dst address : ℕ)
  | branchFieldZero (src target : ℕ)
  | branchWordZero (src target : ℕ)
  | jump (target : ℕ)
  | halt

structure DecoderProgram (F : Type) where
  instructions : List (DecoderInstruction F)
  wordExponent : ℕ

/-- Relabelling a fixed finite alphabet changes only the literal field constants. -/
def mapDecoderInstruction {F E : Type} (f : F → E) : DecoderInstruction F → DecoderInstruction E
  | .fieldConstant d c => .fieldConstant d (f c)
  | .fieldAdd d x y => .fieldAdd d x y
  | .fieldMul d x y => .fieldMul d x y
  | .fieldInv d x => .fieldInv d x
  | .randomField d => .randomField d
  | .wordConstant d v => .wordConstant d v
  | .wordAdd d x y => .wordAdd d x y
  | .wordMul d x y => .wordMul d x y
  | .wordSub d x y => .wordSub d x y
  | .load d a => .load d a
  | .store a x => .store a x
  | .input d a => .input d a
  | .branchFieldZero x t => .branchFieldZero x t
  | .branchWordZero x t => .branchWordZero x t
  | .jump t => .jump t
  | .halt => .halt

def mapDecoderProgram {F E : Type} (e : F ≃ E) (P : DecoderProgram F) : DecoderProgram E :=
  ⟨P.instructions.map (mapDecoderInstruction e), P.wordExponent⟩

structure DecoderState (F : Type) [Zero F] where
  pc : ℕ
  halted : Bool
  fields : ℕ → F
  words : ℕ → ℕ
  memory : ℕ → F

def initialDecoderState {F : Type} [Zero F] : DecoderState F :=
  ⟨0, false, fun _ => 0, fun _ => 0, fun _ => 0⟩

def decoderStep {F : Type} [Field F] (P : DecoderProgram F) (W : ℕ)
    (input : ℕ → F) (coin : F) (s : DecoderState F) : DecoderState F := by
  classical
  if s.halted then exact s else
  let next := {s with pc := s.pc + 1}
  let putF := fun dst value => {next with fields := Function.update s.fields (dst % W) value}
  let putW := fun dst value => {next with words := Function.update s.words (dst % W) (value % W)}
  let f := fun j => s.fields (j % W)
  let w := fun j => s.words (j % W)
  exact match P.instructions[s.pc]? with
    | none => {s with halted := true}
    | some (.halt) => {s with halted := true}
    | some (.fieldConstant d c) => putF d c
    | some (.fieldAdd d x y) => putF d (f x + f y)
    | some (.fieldMul d x y) => putF d (f x * f y)
    | some (.fieldInv d x) => putF d (f x)⁻¹
    | some (.randomField d) => putF d coin
    | some (.wordConstant d c) => putW d c
    | some (.wordAdd d x y) => putW d (w x + w y)
    | some (.wordMul d x y) => putW d (w x * w y)
    | some (.wordSub d x y) => putW d (w x - w y)
    | some (.load d a) => putF d (s.memory (w a))
    | some (.store a x) => {next with memory := Function.update s.memory (w a) (f x)}
    | some (.input d a) => putF d (input (w a))
    | some (.branchFieldZero x t) => if f x = 0 then {s with pc := t} else next
    | some (.branchWordZero x t) => if w x = 0 then {s with pc := t} else next
    | some (.jump t) => {s with pc := t}

/-- Every step consumes one independent uniform field symbol; unused symbols do no work. -/
def decoderRun {F : Type} [Field F] (P : DecoderProgram F) (W : ℕ)
    (input : ℕ → F) (s : ℕ) (coins : Fin s → F) : DecoderState F :=
  ((List.ofFn coins).foldl (fun state coin => decoderStep P W input coin state) initialDecoderState)

def survivalProbability {F : Type} [Field F] [Fintype F]
    (P : DecoderProgram F) (W : ℕ) (input : ℕ → F) (s : ℕ) : ℝ≥0∞ := by
  classical
  exact (Finset.univ.filter fun coins : Fin s → F =>
    (decoderRun P W input s coins).halted = false).card / (Fintype.card F : ℝ≥0∞) ^ s

/-- The tail sum is the expected charged number of steps, even when it is infinite. -/
def expectedSteps {F : Type} [Field F] [Fintype F]
    (P : DecoderProgram F) (W : ℕ) (input : ℕ → F) : ℝ≥0∞ :=
  ∑' s, survivalProbability P W input s

def AlmostSureHalting {F : Type} [Field F] [Fintype F]
    (P : DecoderProgram F) (W : ℕ) (input : ℕ → F) : Prop :=
  Filter.Tendsto (survivalProbability P W input) Filter.atTop (nhds 0)

inductive ErrorType | X | Z

def checks {F : Type} [Field F] (Q : CSS F) : ErrorType → Code F (Fin Q.n)
  | .X => dual Q.classical
  | .Z => Q.stabilizerX

def harmlessErrors {F : Type} [Field F] (Q : CSS F) : ErrorType → Code F (Fin Q.n)
  | .X => Q.stabilizerX
  | .Z => dual Q.classical

/-- A measured syndrome is the list of pairings with a basis of stabilizer checks. -/
def syndrome {F : Type} [Field F] (Q : CSS F) (kind : ErrorType) (e : Fin Q.n → F) : List F :=
  List.ofFn fun j : Fin (Module.finrank F (checks Q kind)) =>
    ∑ i, ((Module.finBasis F (checks Q kind)) j : Fin Q.n → F) i * e i

/-- Immutable code data: the two stabilizer matrices, followed by reusable auxiliary data. -/
def codeMatrices {F : Type} [Field F] (Q : CSS F) : List F :=
  (List.ofFn fun j : Fin (Module.finrank F Q.stabilizerX) =>
    List.ofFn fun i => ((Module.finBasis F Q.stabilizerX) j : Fin Q.n → F) i).flatten ++
  (List.ofFn fun j : Fin (Module.finrank F (dual Q.classical)) =>
    List.ofFn fun i => ((Module.finBasis F (dual Q.classical)) j : Fin Q.n → F) i).flatten

def decoderInput {F : Type} [Field F] (Q : CSS F) (kind : ErrorType)
    (aux : List F) (e : Fin Q.n → F) : ℕ → F := fun j =>
  ((List.replicate Q.n 1 ++ [0] ++
    List.replicate (Module.finrank F Q.stabilizerX) 1 ++ [0] ++
    List.replicate (Module.finrank F (dual Q.classical)) 1 ++ [0] ++
    syndrome Q kind e ++ codeMatrices Q ++ aux)[j]?).getD 0

/-- The unknown error reaches the algorithm only through its measured syndrome.
Every halting execution must give the right correction coset. Output reads are charged. -/
def Decodes {F : Type} [Field F] [Fintype F]
    (Q : CSS F) (kind : ErrorType) (P : DecoderProgram F) (aux : List F)
    (radius : ℤ) (cost : ℝ) : Prop :=
  let W := 2 ^ (P.wordExponent * Nat.clog 2 (Q.n + 2))
  ∀ e : Fin Q.n → F, (weight e : ℤ) ≤ radius →
    AlmostSureHalting P W (decoderInput Q kind aux e) ∧
    (∀ s coins, (decoderRun P W (decoderInput Q kind aux e) s coins).halted = true →
      (fun i => e i - (decoderRun P W (decoderInput Q kind aux e) s coins).memory i) ∈
        harmlessErrors Q kind) ∧
    (Q.n : ℝ≥0∞) + expectedSteps P W (decoderInput Q kind aux e) ≤ ENNReal.ofReal cost

end QuantumGroupCodes836.Addressability


