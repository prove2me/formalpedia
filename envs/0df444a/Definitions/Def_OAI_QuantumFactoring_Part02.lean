-- Prove2me | Definitions.Def_OAI_QuantumFactoring_Part02
-- name    : OAI_QuantumFactoring_Part02
-- status  : Definition
-- author  : @SamenHossain
-- created : 2026-10-12T06:55:53.765586+00:00
-- url     : https://prove2.me/theorems/848f26ac-771a-47b6-8731-0ef2e9aa16ac
-- title:
--   Exact quantum factoring, part 2 of 38 (port of OpenAI's formalization)
-- statement:
--   Part 2 of 38 of a port of OpenAI's Lean formalization of the manuscript *Exact quantum factoring over a fixed finite gate set* (OpenAI, September 25, 2026). This part contains the modules `AIGCompiler`, `AIGBounds`, `AIGInputs`, `BitEncoding`, `BitArithmetic`, `AIGDivisionBounds`, `BitArithmeticDivision`, `WordNetworks`, `ModularMultiply`, `ModularPower`, `BitNumbers`, `TriangularPaths`.
--
--   **Attribution.** The code is adapted from the OpenAI "math" repository, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, directory `lean/OAI/Computability/QuantumFactoring`. It is © OpenAI and licensed under the Apache License 2.0; the adapted code is redistributed under the same license.
--
--   **Modifications.** Modules are concatenated in dependency order, with their imports replaced by the previous part. The model definitions come from the platform definition `ExactQuantumFactoring`, which is identical to upstream `Basic.lean`.
--
--   The development is split into 38 parts only so that each compiles within the platform's time limit. Together the parts supply the circuit family `PhysicalTree.finalCircuit` and its specification, used to prove `OAI.ExactQuantumFactoring.zero_amplitude_core`.
-- source:
--   OpenAI, openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Computability/QuantumFactoring: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/AIGCompiler.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/AIGBounds.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/AIGInputs.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/BitEncoding.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/BitArithmetic.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/AIGDivisionBounds.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/BitArithmeticDivision.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/WordNetworks.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/ModularMultiply.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/ModularPower.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/BitNumbers.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/TriangularPaths.lean (Apache License 2.0); manuscript https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-quantum-factoring-over-a-fixed-finite-gate-set-September-25-2026/main.pdf

/-
Exact quantum factoring development (port of OpenAI's formalization), part 2 of 38.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/QuantumFactoring/: AIGCompiler.lean, AIGBounds.lean, AIGInputs.lean, BitEncoding.lean, BitArithmetic.lean, AIGDivisionBounds.lean, BitArithmeticDivision.lean, WordNetworks.lean, ModularMultiply.lean, ModularPower.lean, BitNumbers.lean, TriangularPaths.lean
These files formalize the manuscript "Exact quantum factoring over a fixed finite gate set"
(OpenAI, September 25, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Basic.lean) come from the platform definition `ExactQuantumFactoring`, to which upstream
Basic.lean is identical; the final assembly (Main.lean) is omitted.
-/
import Mathlib
import Definitions.Def_OAI_QuantumFactoring_Part01

set_option autoImplicit false

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/AIGCompiler.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

open BooleanNetwork Std.Sat

namespace AIGCompiler

variable {n : ℕ} (g : AIG (Fin n))

def graphWire (i : Fin g.decls.size) : Fin (n + g.decls.size) := Fin.natAdd n i

def faninNet (f : AIG.Fanin) : BooleanNetwork (n + g.decls.size) 1 :=
  let v := if h : f.gate < g.decls.size then bit (graphWire g ⟨f.gate,h⟩) else constant false
  if f.invert then v.bnot else v

lemma fanin_count (f : AIG.Fanin) : (faninNet g f).net.count ≤ 2 := by
  have hv : (if h : f.gate < g.decls.size then bit (graphWire g ⟨f.gate,h⟩)
      else constant false : BooleanNetwork (n+g.decls.size) 1).net.count ≤ 1 := by
    by_cases h : f.gate < g.decls.size
    · rw [dite_eq_left h]; simp
    · rw [dite_eq_right h]; simp
  unfold faninNet
  generalize (if h : f.gate < g.decls.size then bit (graphWire g ⟨f.gate,h⟩)
      else constant false : BooleanNetwork (n+g.decls.size) 1) = v at *
  cases hf : f.invert
  · change v.net.count ≤ 2
    omega
  · change v.bnot.net.count ≤ 2
    rw [count_bnot]
    omega

lemma fanin_eval (f : AIG.Fanin) (h : f.gate < g.decls.size) (x : Fin (n+g.decls.size) → Bool) :
    (faninNet g f).eval x 0 = Bool.xor (x (graphWire g ⟨f.gate,h⟩)) f.invert := by
  simp only [faninNet, dite_eq_left h]
  cases f.invert <;> simp

def nodeNet (i : Fin g.decls.size) : BooleanNetwork (n+g.decls.size) 1 :=
  match g.decls[i.val] with
  | .false => constant false
  | .atom v => bit (Fin.castAdd g.decls.size v)
  | .gate a b => (faninNet g a).band (faninNet g b)

lemma node_count (i : Fin g.decls.size) : (nodeNet g i).net.count ≤ 5 := by
  unfold nodeNet
  cases g.decls[i.val] with
  | false => simp
  | atom v => simp
  | gate a b =>
    rw [count_band]
    have := fanin_count g a
    have := fanin_count g b
    omega

def nodeDenote (x : Fin n → Bool) (i : Fin g.decls.size) : Bool :=
  AIG.denote x ⟨g, ⟨i.val, false, i.isLt⟩⟩

lemma node_eval (i : Fin g.decls.size) (x : Fin n → Bool)
    (y : Fin (n+g.decls.size) → Bool)
    (hi : ∀ j, y (j.castAdd g.decls.size) = x j)
    (hg : ∀ j : Fin g.decls.size, j.val < i.val → y (graphWire g j) = nodeDenote g x j) :
    (nodeNet g i).eval y 0 = nodeDenote g x i := by
  unfold nodeNet nodeDenote
  cases h : g.decls[i.val] with
  | false => simpa only [eval_constant] using (AIG.denote_idx_false (assign := x) (invert := false) h).symm
  | atom v => simpa only [eval_bit, hi, Bool.xor_false] using (AIG.denote_idx_atom (assign := x) (invert := false) h).symm
  | gate a b =>
    have hab := g.hdag i.isLt h
    dsimp only
    rw [eval_band, fanin_eval g a (by omega), fanin_eval g b (by omega),
      hg ⟨a.gate, by omega⟩ hab.1, hg ⟨b.gate, by omega⟩ hab.2]
    have he := (AIG.denote_idx_gate (assign := x) (invert := false) h).symm
    simpa only [AIG.denote, nodeDenote, Bool.xor_false] using he

def nodeStep (i : Fin g.decls.size) : BooleanNetwork (n+g.decls.size) (n+g.decls.size) :=
  assign (graphWire g i) (nodeNet g i)

def partialGraph (g : AIG (Fin n)) : (k : ℕ) → k ≤ g.decls.size →
    BooleanNetwork (n+g.decls.size) (n+g.decls.size)
  | 0, _ => select id
  | k+1, h => (partialGraph g k (by omega)).comp (nodeStep g ⟨k, by omega⟩)

lemma graph_count (k : ℕ) (h : k ≤ g.decls.size) : (partialGraph g k h).net.count ≤ 5*k := by
  induction k with
  | zero => simp [partialGraph]
  | succ k ih =>
    rw [partialGraph, count_comp, nodeStep, count_assign]
    have := node_count g ⟨k, by omega⟩
    have := ih (by omega)
    omega

lemma graph_input (k : ℕ) (h : k ≤ g.decls.size) (x : Fin (n+g.decls.size) → Bool) (j : Fin n) :
    (partialGraph g k h).eval x (j.castAdd g.decls.size) = x (j.castAdd g.decls.size) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [partialGraph, eval_comp, nodeStep, eval_assign, Function.update_of_ne, ih]
    intro he
    have := congrArg Fin.val he
    simp [graphWire] at this
    omega

lemma graph_value (k : ℕ) (h : k ≤ g.decls.size) (x : Fin (n+g.decls.size) → Bool)
    (j : Fin g.decls.size) (hj : j.val < k) :
    (partialGraph g k h).eval x (graphWire g j) =
      nodeDenote g (fun i => x (i.castAdd g.decls.size)) j := by
  induction k generalizing j with
  | zero => omega
  | succ k ih =>
    rw [partialGraph, eval_comp, nodeStep, eval_assign]
    by_cases hjk : j.val = k
    · have hj' : j = ⟨k, by omega⟩ := Fin.ext hjk
      rw [hj', Function.update_self]
      apply node_eval g
      · exact fun i => graph_input g k (by omega) x i
      · exact fun i hi => ih (by omega) i (by simpa using hi)
    · rw [Function.update_of_ne]
      · exact ih (by omega) j (by omega)
      · intro he
        have := congrArg Fin.val he
        simp [graphWire] at this
        omega

/-- The circuit interpreter's own, already verified, AIG semantics is preserved
by a retained-trace network of at most five nodes per AIG declaration. -/
theorem graph_correct (x : Fin (n+g.decls.size) → Bool) (j : Fin g.decls.size) :
    (partialGraph g g.decls.size le_rfl).eval x (graphWire g j) =
      nodeDenote g (fun i => x (i.castAdd g.decls.size)) j :=
  graph_value g _ le_rfl x j j.isLt

/-- Compile designated references of an AIG, starting only with its input bits.
All graph slots and their retained evaluation traces are genuine ancillas. -/
def compile {m : ℕ} (refs : Fin m → AIG.Ref g) : BooleanNetwork n m :=
  ((padRight n g.decls.size).comp (partialGraph g g.decls.size le_rfl)).comp
    (vector (fun i => faninNet g (AIG.Fanin.mk (refs i).gate (refs i).invert)))

lemma compile_count {m : ℕ} (refs : Fin m → AIG.Ref g) :
    (compile g refs).net.count ≤ 6*g.decls.size + 2*m := by
  rw [compile, count_comp, count_comp, count_padRight]
  have hg := graph_count g g.decls.size le_rfl
  have hv := count_vector_le (fun i => faninNet g (AIG.Fanin.mk (refs i).gate (refs i).invert))
    (fun i => fanin_count g (AIG.Fanin.mk (refs i).gate (refs i).invert))
  omega

lemma compile_correct {m : ℕ} (refs : Fin m → AIG.Ref g) (x : Fin n → Bool) (i : Fin m) :
    (compile g refs).eval x i = AIG.denote x ⟨g, refs i⟩ := by
  rw [compile, eval_comp, eval_comp, eval_vector, fanin_eval g _ (by simpa using (refs i).hgate),
    graph_correct, eval_padRight]
  have he : (fun j : Fin n => Fin.append x (fun _ : Fin g.decls.size => false)
      (j.castAdd g.decls.size)) = x := by funext j; exact Fin.append_left ..
  rw [he]
  simp only [nodeDenote, AIG.denote, Bool.xor_false, AIG.Fanin.gate_mk, AIG.Fanin.invert_mk]

/-- The whole output BitVec of a native, already verified, arithmetic bitblaster
is now a Boolean network with a linear overhead in its AIG graph size. -/
def compileVec {w : ℕ} (refs : AIG.RefVec g w) : BooleanNetwork n w :=
  compile g (fun i => refs.get i.val i.isLt)

lemma compileVec_correct {w : ℕ} (refs : AIG.RefVec g w) (x : Fin n → Bool) (i : Fin w) :
    (compileVec g refs).eval x i = AIG.denote x ⟨g, refs.get i.val i.isLt⟩ :=
  compile_correct ..

lemma compileVec_count {w : ℕ} (refs : AIG.RefVec g w) :
    (compileVec g refs).net.count ≤ 6*g.decls.size + 2*w := compile_count ..

end AIGCompiler
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/AIGBounds.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.AIGBounds
open Std.Sat
open Std.Tactic.BVDecide.BVExpr.bitblast

variable {α : Type} [Hashable α] [DecidableEq α]

lemma cached_go_size (aig : AIG α) (input : AIG.BinaryInput aig) :
    (AIG.mkGateCached.go aig input).aig.decls.size ≤ aig.decls.size + 1 := by
  dsimp only [AIG.mkGateCached.go]
  split
  · simp
  · split <;> try simp
    split
    · split <;> simp
    · simp

lemma cached_size (aig : AIG α) (input : AIG.BinaryInput aig) :
    (aig.mkGateCached input).aig.decls.size ≤ aig.decls.size + 1 := by
  dsimp only [AIG.mkGateCached]
  split <;> apply cached_go_size

lemma atom_size (aig : AIG α) (v : α) :
    (aig.mkAtomCached v).aig.decls.size ≤ aig.decls.size + 1 := by
  dsimp only [AIG.mkAtomCached]
  split <;> simp

lemma and_size (aig : AIG α) (input : AIG.BinaryInput aig) :
    (aig.mkAndCached input).aig.decls.size ≤ aig.decls.size + 1 := cached_size _ _

lemma or_size (aig : AIG α) (input : AIG.BinaryInput aig) :
    (aig.mkOrCached input).aig.decls.size ≤ aig.decls.size + 1 := cached_size _ _

lemma xor_size (aig : AIG α) (input : AIG.BinaryInput aig) :
    (aig.mkXorCached input).aig.decls.size ≤ aig.decls.size + 3 := by
  unfold AIG.mkXorCached
  dsimp only
  exact (cached_size _ _).trans (by
    have := cached_size aig input
    have := cached_size (aig.mkGateCached input).aig
      ((input.cast (AIG.LawfulOperator.le_size ..)).invert true true)
    omega)

lemma fullAdderOut_size (aig : AIG α) (input : FullAdderInput aig) :
    (mkFullAdderOut aig input).aig.decls.size ≤ aig.decls.size + 6 := by
  unfold mkFullAdderOut
  dsimp only
  exact (xor_size _ _).trans (by
    have := xor_size aig ⟨input.lhs,input.rhs⟩
    omega)

lemma fullAdderCarry_size (aig : AIG α) (input : FullAdderInput aig) :
    (mkFullAdderCarry aig input).aig.decls.size ≤ aig.decls.size + 6 := by
  unfold mkFullAdderCarry
  dsimp only
  apply (or_size _ _).trans
  apply Nat.add_le_add_right ?_ 1
  apply (and_size _ _).trans
  apply Nat.add_le_add_right ?_ 1
  apply (and_size _ _).trans
  apply Nat.add_le_add_right ?_ 1
  exact xor_size _ _

lemma fullAdder_size (aig : AIG α) (input : FullAdderInput aig) :
    (mkFullAdder aig input).aig.decls.size ≤ aig.decls.size + 12 := by
  unfold mkFullAdder
  dsimp only
  apply (fullAdderCarry_size _ _).trans
  have := fullAdderOut_size aig input
  omega

lemma add_go_size {w : ℕ} (aig : AIG α) (lhs rhs : AIG.RefVec aig w)
    (curr : ℕ) (hcurr : curr ≤ w) (cin : AIG.Ref aig) (s : AIG.RefVec aig curr) :
    (blastAdd.go aig lhs rhs curr hcurr cin s).aig.decls.size ≤
      aig.decls.size + 12*(w-curr) := by
  rw [blastAdd.go]
  split
  next h =>
    dsimp only
    apply (add_go_size _ _ _ _ _ _ _).trans
    have hh := fullAdder_size aig ⟨lhs.get curr h, rhs.get curr h, cin⟩
    omega
  next h => simp
termination_by w-curr

/-- A verified native ripple circuit has linear declaration count. The cache
can only decrease this upper bound. -/
theorem add_size {w : ℕ} (aig : AIG α) (input : AIG.BinaryRefVec aig w) :
    (blastAdd aig input).aig.decls.size ≤ aig.decls.size + 12*w := by
  unfold blastAdd
  split <;> unfold blastAdd.blast <;> apply add_go_size

lemma if_size (aig : AIG α) (input : AIG.TernaryInput aig) :
    (aig.mkIfCached input).aig.decls.size ≤ aig.decls.size + 3 := by
  unfold AIG.mkIfCached
  dsimp only
  apply (or_size _ _).trans
  apply Nat.add_le_add_right ?_ 1
  apply (and_size _ _).trans
  apply Nat.add_le_add_right ?_ 1
  exact and_size _ _

lemma ite_go_size {w : ℕ} (aig : AIG α) (curr : ℕ) (hcurr : curr ≤ w)
    (discr : AIG.Ref aig) (lhs rhs : AIG.RefVec aig w) (s : AIG.RefVec aig curr) :
    (AIG.RefVec.ite.go aig curr hcurr discr lhs rhs s).aig.decls.size ≤
      aig.decls.size + 3*(w-curr) := by
  rw [AIG.RefVec.ite.go]
  split
  next h =>
    dsimp only
    apply (ite_go_size _ _ _ _ _ _ _).trans
    have hh := if_size aig ⟨discr, lhs.get curr h, rhs.get curr h⟩
    omega
  next h => simp
termination_by w-curr

lemma ite_size {w : ℕ} (aig : AIG α) (input : AIG.RefVec.IfInput aig w) :
    (AIG.RefVec.ite aig input).aig.decls.size ≤ aig.decls.size + 3*w :=
  ite_go_size _ 0 _ _ _ _ _

lemma shift_go_size {w : ℕ} (aig : AIG α) (input : AIG.RefVec aig w)
    (distance curr : ℕ) (hcurr : curr ≤ w) (s : AIG.RefVec aig curr) :
    (blastShiftLeftConst.go aig input distance curr hcurr s).aig.decls.size = aig.decls.size := by
  rw [blastShiftLeftConst.go]
  split
  · split <;> apply shift_go_size
  · simp
termination_by w-curr

lemma shift_size {w : ℕ} (aig : AIG α) (input : AIG.ShiftTarget aig w) :
    (blastShiftLeftConst aig input).aig.decls.size = aig.decls.size := shift_go_size ..

lemma mul_go_size {w : ℕ} (aig : AIG α) (lhs rhs : AIG.RefVec aig w)
    (curr : ℕ) (acc : AIG.RefVec aig w) :
    (blastMul.go aig lhs rhs curr acc).aig.decls.size ≤ aig.decls.size + 15*w*(w-curr) := by
  rw [blastMul.go]
  split
  next h =>
    split
    · apply (mul_go_size _ _ _ _ _).trans
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
    · dsimp only
      apply (mul_go_size _ _ _ _ _).trans
      have hshift := shift_size aig ⟨lhs,curr⟩
      refine (Nat.add_le_add_right (ite_size _ _) _).trans ?_
      have hadd : (blastAdd (blastShiftLeftConst aig ⟨lhs,curr⟩).aig
            ⟨acc.cast (AIG.LawfulVecOperator.le_size ..),
              (blastShiftLeftConst aig ⟨lhs,curr⟩).vec⟩).aig.decls.size ≤ aig.decls.size + 12*w := by
          rw [← hshift]
          apply add_size
      have he : w-curr = (w-(curr+1))+1 := by omega
      rw [he, Nat.mul_add, Nat.mul_one]
      omega
  next h => simp
termination_by w-curr

lemma mul_blast_size {w : ℕ} (aig : AIG α) (input : AIG.BinaryRefVec aig w) :
    (blastMul.blast aig input).aig.decls.size ≤ aig.decls.size + 15*w*w := by
  unfold blastMul.blast
  split
  · simp_all
  next h =>
    dsimp only
    apply (mul_go_size _ _ _ _ _).trans
    have hh := ite_size aig ⟨input.rhs.get 0 (by omega), input.lhs, blastConst aig 0⟩
    have he : w-1+1=w := by omega
    nlinarith

/-- The native shift-and-add multiplier has quadratic declaration count. -/
theorem mul_size {w : ℕ} (aig : AIG α) (input : AIG.BinaryRefVec aig w) :
    (blastMul aig input).aig.decls.size ≤ aig.decls.size + 15*w*w := by
  unfold blastMul
  split <;> apply mul_blast_size

end ExactQuantumFactoring.AIGBounds


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/AIGInputs.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.AIGCompiler
open Std.Sat

/-- One real AIG atom per input bit. The initial graph has one false node. -/
def inputsPrefix (n : ℕ) : (k : ℕ) → k ≤ n →
    (g : AIG (Fin n)) × (Fin k → AIG.Ref g)
  | 0, _ => ⟨AIG.empty, Fin.elim0⟩
  | k+1, h =>
    let old := inputsPrefix n k (by omega)
    let res := old.1.mkAtom ⟨k, by omega⟩
    ⟨res.aig, Fin.snoc (fun i => (old.2 i).cast (AIG.LawfulOperator.le_size (f := AIG.mkAtom) old.1 (⟨k, by omega⟩ : Fin n))) res.ref⟩

lemma inputsPrefix_size (n k : ℕ) (h : k ≤ n) : (inputsPrefix n k h).1.decls.size = k+1 := by
  induction k with
  | zero => simp [inputsPrefix, AIG.empty]
  | succ k ih => simp [inputsPrefix, AIG.mkAtom, ih]

lemma inputsPrefix_correct (n k : ℕ) (h : k ≤ n) (x : Fin n → Bool) (i : Fin k) :
    AIG.denote x ⟨(inputsPrefix n k h).1, (inputsPrefix n k h).2 i⟩ = x (i.castLE h) := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [inputsPrefix, Fin.snoc_last]
      change AIG.denote x ((inputsPrefix n k (by omega)).1.mkAtom ⟨k, by omega⟩) = _
      rw [AIG.denote_mkAtom]
      rfl
    · simp only [inputsPrefix, Fin.snoc_castSucc]
      rw [AIG.LawfulOperator.denote_cast_entry (f := @AIG.mkAtom (Fin n) _ _)
        (entry := ⟨(inputsPrefix n k (by omega)).1, (inputsPrefix n k (by omega)).2 j⟩)]
      exact ih (by omega) j

def inputs (n : ℕ) := inputsPrefix n n le_rfl

lemma inputs_size (n : ℕ) : (inputs n).1.decls.size = n+1 := inputsPrefix_size ..

lemma inputs_correct (n : ℕ) (x : Fin n → Bool) (i : Fin n) :
    AIG.denote x ⟨(inputs n).1, (inputs n).2 i⟩ = x i := inputsPrefix_correct ..

/-- A vector of ordinary references; this constructor emits no graph nodes. -/
def refVector {α : Type} [Hashable α] [DecidableEq α] {g : AIG α} {w : ℕ}
    (f : Fin w → AIG.Ref g) : AIG.RefVec g w where
  refs := Vector.ofFn (fun i => AIG.Fanin.mk (f i).gate (f i).invert)
  hrefs := by intro i hi; simpa using (f ⟨i,hi⟩).hgate

lemma refVector_get {α : Type} [Hashable α] [DecidableEq α] {g : AIG α} {w : ℕ}
    (f : Fin w → AIG.Ref g) (i : ℕ) (hi : i < w) :
    (refVector f).get i hi = f ⟨i,hi⟩ := by
  simp [refVector, AIG.RefVec.get, AIG.Fanin.gate_mk, AIG.Fanin.invert_mk]

end ExactQuantumFactoring.AIGCompiler


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitEncoding.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

/-- Little-endian computational wires, with the same bit ordering as the
manuscript and input/output interface. -/
def bitsValue : {b : ℕ} → (Fin b → Bool) → BitVec b
  | 0, _ => 0
  | b+1, x => BitVec.cons (x (Fin.last b)) (bitsValue (fun i => x i.castSucc))

lemma bitsValue_bit {b : ℕ} (x : Fin b → Bool) (i : Fin b) :
    (bitsValue x).getLsbD i.val = x i := by
  induction b with
  | zero => exact Fin.elim0 i
  | succ b ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [bitsValue, Fin.val_last, BitVec.getLsbD_cons, ite_true]
    · simp only [bitsValue, BitVec.getLsbD_cons, Fin.val_castSucc,
        ite_eq_right (Nat.ne_of_lt j.isLt)]
      exact ih _ j

lemma bitsValue_bits {b : ℕ} (x : BitVec b) :
    bitsValue (fun i : Fin b => x.getLsbD i.val) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact bitsValue_bit _ ⟨i,hi⟩

def bitsEquiv (b : ℕ) : (Fin b → Bool) ≃ BitVec b where
  toFun := bitsValue
  invFun := fun x i => x.getLsbD i.val
  left_inv := by intro x; funext i; exact bitsValue_bit x i
  right_inv := bitsValue_bits

/-- The exact integer in the two most significant wires is the quarter-bin. -/
lemma bitsValue_quarter (b : ℕ) (x : Fin (b+2) → Bool) :
    (bitsValue x).toNat / 2^b =
      2*(x (Fin.last (b+1))).toNat + (x ((Fin.last b).castSucc)).toNat := by
  have hlow := (bitsValue (fun i : Fin b => x i.castSucc.castSucc)).isLt
  simp only [bitsValue, BitVec.toNat_cons', Nat.shiftLeft_eq]
  have he : (x (Fin.last (b+1))).toNat * 2^(b+1) +
      ((x ((Fin.last b).castSucc)).toNat * 2^b +
        (bitsValue (fun i : Fin b => x i.castSucc.castSucc)).toNat) =
      (2*(x (Fin.last (b+1))).toNat + (x ((Fin.last b).castSucc)).toNat) * 2^b +
        (bitsValue (fun i : Fin b => x i.castSucc.castSucc)).toNat := by
    rw [pow_succ]
    ring
  rw [he, Nat.mul_comm _ (2^b), Nat.mul_add_div (by positivity),
    Nat.div_eq_of_lt hlow, Nat.add_zero]

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitArithmetic.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
namespace BitArithmetic
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast
open AIGCompiler BooleanNetwork

/-- The two actual little-endian input words of the bitblaster. -/
def binaryInputs (w : ℕ) : AIG.BinaryRefVec (inputs (w+w)).1 w :=
  ⟨refVector (fun i => (inputs (w+w)).2 (i.castAdd w)),
   refVector (fun i => (inputs (w+w)).2 (Fin.natAdd w i))⟩

def leftWord {w : ℕ} (x : Fin (w+w) → Bool) : BitVec w :=
  bitsValue (fun i => x (i.castAdd w))
def rightWord {w : ℕ} (x : Fin (w+w) → Bool) : BitVec w :=
  bitsValue (fun i => x (Fin.natAdd w i))

lemma binaryInputs_left (w : ℕ) (x : Fin (w+w) → Bool) (i : ℕ) (hi : i < w) :
    AIG.denote x ⟨(inputs (w+w)).1, (binaryInputs w).lhs.get i hi⟩ =
      (leftWord x).getLsbD i := by
  rw [binaryInputs, refVector_get, inputs_correct]
  exact (bitsValue_bit (fun j => x (j.castAdd w)) ⟨i,hi⟩).symm

lemma binaryInputs_right (w : ℕ) (x : Fin (w+w) → Bool) (i : ℕ) (hi : i < w) :
    AIG.denote x ⟨(inputs (w+w)).1, (binaryInputs w).rhs.get i hi⟩ =
      (rightWord x).getLsbD i := by
  rw [binaryInputs, refVector_get, inputs_correct]
  exact (bitsValue_bit (fun j => x (Fin.natAdd w j)) ⟨i,hi⟩).symm

def add (w : ℕ) : BooleanNetwork (w+w) w :=
  let res := blastAdd (inputs (w+w)).1 (binaryInputs w)
  compileVec res.aig res.vec

lemma add_correct (w : ℕ) (x : Fin (w+w) → Bool) (i : Fin w) :
    (add w).eval x i = (leftWord x + rightWord x).getLsbD i.val := by
  rw [add, compileVec_correct]
  exact denote_blastAdd _ _ _ _ _ (binaryInputs_left w x) (binaryInputs_right w x) _ _

def mul (w : ℕ) : BooleanNetwork (w+w) w :=
  let res := blastMul (inputs (w+w)).1 (binaryInputs w)
  compileVec res.aig res.vec

lemma mul_correct (w : ℕ) (x : Fin (w+w) → Bool) (i : Fin w) :
    (mul w).eval x i = (leftWord x * rightWord x).getLsbD i.val := by
  rw [mul, compileVec_correct]
  exact denote_blastMul _ _ _ _ _ (binaryInputs_left w x) (binaryInputs_right w x) _ _

lemma add_count (w : ℕ) : (add w).net.count ≤ 86*w+6 := by
  have h := compileVec_count (blastAdd (inputs (w+w)).1 (binaryInputs w)).aig
    (blastAdd (inputs (w+w)).1 (binaryInputs w)).vec
  have hs := AIGBounds.add_size (inputs (w+w)).1 (binaryInputs w)
  rw [inputs_size] at hs
  dsimp only [add]
  omega

lemma mul_count (w : ℕ) : (mul w).net.count ≤ 90*w*w+14*w+6 := by
  have h := compileVec_count (blastMul (inputs (w+w)).1 (binaryInputs w)).aig
    (blastMul (inputs (w+w)).1 (binaryInputs w)).vec
  have hs := AIGBounds.mul_size (inputs (w+w)).1 (binaryInputs w)
  rw [inputs_size] at hs
  dsimp only [mul]
  nlinarith

end BitArithmetic
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/AIGDivisionBounds.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.AIGBounds
open Std.Sat Std.Tactic.BVDecide
open BVExpr.bitblast
variable {α : Type} [Hashable α] [DecidableEq α]

lemma not_go_size {w : ℕ} (aig : AIG α) (i : ℕ) (hi : i ≤ w)
    (s : AIG.RefVec aig i) (input : AIG.RefVec aig w) :
    (AIG.RefVec.map.go aig i hi s input AIG.mkNotCached).aig.decls.size = aig.decls.size := by
  rw [AIG.RefVec.map.go]
  split
  · dsimp only
    rw [not_go_size]
    rfl
  · rfl
termination_by w-i

lemma not_size {w : ℕ} (aig : AIG α) (input : AIG.RefVec aig w) :
    (blastNot aig input).aig.decls.size = aig.decls.size :=
  not_go_size ..

lemma neg_size {w : ℕ} (aig : AIG α) (input : AIG.RefVec aig w) :
    (blastNeg aig input).aig.decls.size ≤ aig.decls.size+12*w := by
  unfold blastNeg
  have h := add_size (blastNot aig input).aig
    ⟨(blastNot aig input).vec, blastConst (blastNot aig input).aig (1#w)⟩
  simpa only [not_size] using h

lemma sub_size {w : ℕ} (aig : AIG α) (input : AIG.BinaryRefVec aig w) :
    (blastSub aig input).aig.decls.size ≤ aig.decls.size+24*w := by
  unfold blastSub
  dsimp only
  apply (add_size _ _).trans
  have h := neg_size aig input.rhs
  omega

lemma overflow_go_size {w : ℕ} (aig : AIG α) (lhs rhs : AIG.RefVec aig w)
    (curr : ℕ) (cin : AIG.Ref aig) :
    (mkOverflowBit.go aig lhs rhs curr cin).aig.decls.size ≤
      aig.decls.size+6*(w-curr) := by
  rw [mkOverflowBit.go]
  split
  next h =>
    dsimp only
    apply (overflow_go_size _ _ _ _ _).trans
    have hh := fullAdderCarry_size aig ⟨lhs.get curr h, rhs.get curr h, cin⟩
    omega
  · simp
termination_by w-curr

lemma overflow_size (aig : AIG α) (input : OverflowInput aig) :
    (mkOverflowBit aig input).aig.decls.size ≤ aig.decls.size+6*input.w :=
  overflow_go_size ..

lemma ult_size {w : ℕ} (aig : AIG α) (input : AIG.BinaryRefVec aig w) :
    (BVPred.mkUlt aig input).aig.decls.size ≤ aig.decls.size+6*w := by
  unfold BVPred.mkUlt
  dsimp only
  change (mkOverflowBit _ _).aig.decls.size ≤ _
  apply (overflow_size _ _).trans
  simp only [not_size, le_refl]

lemma extend_go_size (aig : AIG α) (w : ℕ) (input : AIG.RefVec aig w)
    (newWidth curr : ℕ) (hcurr : curr ≤ newWidth) (s : AIG.RefVec aig curr) :
    (blastZeroExtend.go aig w input newWidth curr hcurr s).aig.decls.size = aig.decls.size := by
  rw [blastZeroExtend.go]
  split
  · dsimp only
    split <;> apply extend_go_size
  · rfl
termination_by newWidth-curr

lemma extend_size {w : ℕ} (aig : AIG α) (input : AIG.ExtendTarget aig w) :
    (blastZeroExtend aig input).aig.decls.size = aig.decls.size := extend_go_size ..

lemma shiftConcat_size {w : ℕ} (aig : AIG α) (input : blastUdiv.ShiftConcatInput aig w) :
    (blastUdiv.blastShiftConcat aig input).aig.decls.size = aig.decls.size := extend_size ..

lemma div_step_size {w : ℕ} (aig : AIG α) (n d : AIG.RefVec aig w)
    (wn wr : ℕ) (q r : AIG.RefVec aig w) :
    (blastUdiv.blastDivSubtractShift aig n d wn wr q r).aig.decls.size ≤
      aig.decls.size+36*w := by
  unfold blastUdiv.blastDivSubtractShift
  dsimp only
  apply (ite_size _ _).trans
  apply (Nat.add_le_add_right (ite_size _ _) (3*w)).trans
  apply (Nat.add_le_add_right (Nat.add_le_add_right (ult_size _ _) (3*w)) (3*w)).trans
  apply (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_right (sub_size _ _) (6*w)) (3*w)) (3*w)).trans
  simp only [shiftConcat_size]
  omega

lemma div_go_size {w : ℕ} (aig : AIG α) (curr : ℕ) (n d : AIG.RefVec aig w)
    (wn wr : ℕ) (q r : AIG.RefVec aig w) :
    (blastUdiv.go aig curr n d wn wr q r).aig.decls.size ≤ aig.decls.size+36*w*curr := by
  induction curr generalizing aig wn wr with
  | zero => simp [blastUdiv.go]
  | succ curr ih =>
    rw [blastUdiv.go]
    dsimp only
    apply (ih _ _ _ _ _ _ _).trans
    have h := div_step_size aig n d wn wr q r
    nlinarith

lemma beq_size (aig : AIG α) (input : AIG.BinaryInput aig) :
    (aig.mkBEqCached input).aig.decls.size ≤ aig.decls.size+3 := by
  unfold AIG.mkBEqCached
  dsimp only
  apply (cached_size _ _).trans
  apply (Nat.add_le_add_right (cached_size _ _) 1).trans
  apply (Nat.add_le_add_right (Nat.add_le_add_right (cached_size _ _) 1) 1).trans
  omega

lemma zip_go_size (f : (aig : AIG α) → AIG.BinaryInput aig → AIG.Entrypoint α)
    [AIG.LawfulOperator α AIG.BinaryInput f] [AIG.RefVec.LawfulZipOperator α f]
    (c : ℕ) (hf : ∀ aig input, (f aig input).aig.decls.size ≤ aig.decls.size+c)
    {w : ℕ} (aig : AIG α) (idx : ℕ) (s : AIG.RefVec aig idx) (hi : idx ≤ w)
    (lhs rhs : AIG.RefVec aig w) :
    (AIG.RefVec.zip.go aig idx s hi lhs rhs f).aig.decls.size ≤ aig.decls.size+c*(w-idx) := by
  rw [AIG.RefVec.zip.go]
  split
  next h =>
    dsimp only
    apply (zip_go_size f c hf _ _ _ _ _ _).trans
    have hh := hf aig ⟨lhs.get idx h, rhs.get idx h⟩
    have he : w-idx = w-(idx+1)+1 := by omega
    rw [he]
    nlinarith
  · simp
termination_by w-idx

lemma zip_size (f : (aig : AIG α) → AIG.BinaryInput aig → AIG.Entrypoint α)
    [AIG.LawfulOperator α AIG.BinaryInput f] [AIG.RefVec.LawfulZipOperator α f]
    (c : ℕ) (hf : ∀ aig input, (f aig input).aig.decls.size ≤ aig.decls.size+c)
    {w : ℕ} (aig : AIG α) (input : AIG.BinaryRefVec aig w) :
    (AIG.RefVec.zip aig input f).aig.decls.size ≤ aig.decls.size+c*w := zip_go_size f c hf aig 0 _ (by omega) input.lhs input.rhs

lemma fold_go_size (f : (aig : AIG α) → AIG.BinaryInput aig → AIG.Entrypoint α)
    [AIG.LawfulOperator α AIG.BinaryInput f]
    (c : ℕ) (hf : ∀ aig input, (f aig input).aig.decls.size ≤ aig.decls.size+c)
    {w : ℕ} (aig : AIG α) (acc : AIG.Ref aig) (idx : ℕ) (input : AIG.RefVec aig w) :
    (AIG.RefVec.fold.go aig acc idx w input f).aig.decls.size ≤ aig.decls.size+c*(w-idx) := by
  rw [AIG.RefVec.fold.go]
  split
  next h =>
    dsimp only
    apply (fold_go_size f c hf _ _ _ _).trans
    have hh := hf aig ⟨acc, input.get idx h⟩
    have he : w-idx = w-(idx+1)+1 := by omega
    rw [he]
    nlinarith
  · simp
termination_by w-idx

lemma fold_size (f : (aig : AIG α) → AIG.BinaryInput aig → AIG.Entrypoint α)
    [AIG.LawfulOperator α AIG.BinaryInput f]
    (c : ℕ) (hf : ∀ aig input, (f aig input).aig.decls.size ≤ aig.decls.size+c)
    {w : ℕ} (aig : AIG α) (input : AIG.RefVec aig w) :
    (AIG.RefVec.fold aig input f).aig.decls.size ≤ aig.decls.size+c*w := fold_go_size f c hf aig (aig.mkConstCached true) 0 input

lemma eq_size {w : ℕ} (aig : AIG α) (input : AIG.BinaryRefVec aig w) :
    (BVPred.mkEq aig input).aig.decls.size ≤ aig.decls.size+4*w := by
  unfold BVPred.mkEq
  dsimp only
  apply (fold_size _ 1 and_size _ _).trans
  have hh := zip_size _ 3 beq_size aig input
  omega

lemma div_size {w : ℕ} (aig : AIG α) (input : AIG.BinaryRefVec aig w) :
    (blastUdiv aig input).aig.decls.size ≤ aig.decls.size+36*w*w+7*w := by
  unfold blastUdiv
  dsimp only
  apply (ite_size _ _).trans
  apply (Nat.add_le_add_right (div_go_size _ _ _ _ _ _ _ _) (3*w)).trans
  have hh := eq_size aig ⟨input.rhs, blastConst aig 0#w⟩
  omega

lemma mod_size {w : ℕ} (aig : AIG α) (input : AIG.BinaryRefVec aig w) :
    (blastUmod aig input).aig.decls.size ≤ aig.decls.size+36*w*w+7*w := by
  unfold blastUmod
  dsimp only
  apply (ite_size _ _).trans
  apply (Nat.add_le_add_right (div_go_size _ _ _ _ _ _ _ _) (3*w)).trans
  have hh := eq_size aig ⟨input.rhs, blastConst aig 0#w⟩
  omega

end ExactQuantumFactoring.AIGBounds


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitArithmeticDivision.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast
open AIGCompiler BooleanNetwork

def sub (w : ℕ) : BooleanNetwork (w+w) w :=
  let res := blastSub (inputs (w+w)).1 (binaryInputs w)
  compileVec res.aig res.vec

lemma sub_correct (w : ℕ) (x : Fin (w+w) → Bool) (i : Fin w) :
    (sub w).eval x i = (leftWord x - rightWord x).getLsbD i.val := by
  rw [sub, compileVec_correct]
  exact denote_blastSub _ _ _ _ _ (binaryInputs_left w x) (binaryInputs_right w x) _ _

lemma sub_count (w : ℕ) : (sub w).net.count ≤ 158*w+6 := by
  have h := compileVec_count (blastSub (inputs (w+w)).1 (binaryInputs w)).aig
    (blastSub (inputs (w+w)).1 (binaryInputs w)).vec
  have hs := AIGBounds.sub_size (inputs (w+w)).1 (binaryInputs w)
  rw [inputs_size] at hs
  dsimp only [sub]
  nlinarith

def div (w : ℕ) : BooleanNetwork (w+w) w :=
  let res := blastUdiv (inputs (w+w)).1 (binaryInputs w)
  compileVec res.aig res.vec

lemma div_correct (w : ℕ) (x : Fin (w+w) → Bool) (i : Fin w) :
    (div w).eval x i = (leftWord x / rightWord x).getLsbD i.val := by
  rw [div, compileVec_correct]
  exact denote_blastUdiv _ _ _ _ _ (binaryInputs_left w x) (binaryInputs_right w x) _ _

lemma div_count (w : ℕ) : (div w).net.count ≤ 216*w*w+56*w+6 := by
  have h := compileVec_count (blastUdiv (inputs (w+w)).1 (binaryInputs w)).aig
    (blastUdiv (inputs (w+w)).1 (binaryInputs w)).vec
  have hs := AIGBounds.div_size (inputs (w+w)).1 (binaryInputs w)
  rw [inputs_size] at hs
  dsimp only [div]
  nlinarith

def mod (w : ℕ) : BooleanNetwork (w+w) w :=
  let res := blastUmod (inputs (w+w)).1 (binaryInputs w)
  compileVec res.aig res.vec

lemma mod_correct (w : ℕ) (x : Fin (w+w) → Bool) (i : Fin w) :
    (mod w).eval x i = (leftWord x % rightWord x).getLsbD i.val := by
  rw [mod, compileVec_correct]
  exact denote_blastUmod _ _ _ _ _ (binaryInputs_left w x) (binaryInputs_right w x) _ _

lemma mod_count (w : ℕ) : (mod w).net.count ≤ 216*w*w+56*w+6 := by
  have h := compileVec_count (blastUmod (inputs (w+w)).1 (binaryInputs w)).aig
    (blastUmod (inputs (w+w)).1 (binaryInputs w)).vec
  have hs := AIGBounds.mod_size (inputs (w+w)).1 (binaryInputs w)
  rw [inputs_size] at hs
  dsimp only [mod]
  nlinarith

end ExactQuantumFactoring.BitArithmetic


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/WordNetworks.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
namespace BitArithmetic
open BooleanNetwork

lemma leftWord_append {w : ℕ} (a b : Basis w) : leftWord (Fin.append a b) = bitsValue a := by
  simp [leftWord]
lemma rightWord_append {w : ℕ} (a b : Basis w) : rightWord (Fin.append a b) = bitsValue b := by
  simp only [rightWord, Fin.append_right]

lemma mul_word (w : ℕ) (a b : Basis w) :
    bitsValue ((mul w).eval (Fin.append a b)) = bitsValue a * bitsValue b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show (bitsValue ((mul w).eval (Fin.append a b))).getLsbD i =
    (mul w).eval (Fin.append a b) ⟨i,hi⟩ from bitsValue_bit _ ⟨i,hi⟩,
    mul_correct, leftWord_append, rightWord_append]

lemma mod_word (w : ℕ) (a b : Basis w) :
    bitsValue ((mod w).eval (Fin.append a b)) = bitsValue a % bitsValue b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show (bitsValue ((mod w).eval (Fin.append a b))).getLsbD i =
    (mod w).eval (Fin.append a b) ⟨i,hi⟩ from bitsValue_bit _ ⟨i,hi⟩,
    mod_correct, leftWord_append, rightWord_append]

lemma add_word (w : ℕ) (a b : Basis w) :
    bitsValue ((add w).eval (Fin.append a b)) = bitsValue a + bitsValue b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show (bitsValue ((add w).eval (Fin.append a b))).getLsbD i =
    (add w).eval (Fin.append a b) ⟨i,hi⟩ from bitsValue_bit _ ⟨i,hi⟩,
    add_correct, leftWord_append, rightWord_append]

lemma bitsValue_append_zero {w t : ℕ} (x : Basis w) :
    bitsValue (Fin.append x (fun _ : Fin t => false)) = (bitsValue x).setWidth (w+t) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show (bitsValue (Fin.append x (fun _ : Fin t => false))).getLsbD i =
    Fin.append x (fun _ => false) ⟨i,hi⟩ from bitsValue_bit _ ⟨i,hi⟩,
    BitVec.getLsbD_setWidth]
  simp only [hi, decide_true, Bool.true_and]
  by_cases hw : i < w
  · have he : (⟨i,hi⟩ : Fin (w+t)) = (⟨i,hw⟩ : Fin w).castAdd t := Fin.ext rfl
    rw [he, Fin.append_left]
    exact (bitsValue_bit x ⟨i,hw⟩).symm
  · have he : (⟨i,hi⟩ : Fin (w+t)) = Fin.natAdd w (⟨i-w,by omega⟩ : Fin t) := by
      apply Fin.ext
      simp only [Fin.val_natAdd]
      omega
    rw [he, Fin.append_right, BitVec.getLsbD_of_ge _ _ (by omega)]

lemma padRight_word (w t : ℕ) (x : Basis w) :
    bitsValue ((padRight w t).eval x) = (bitsValue x).setWidth (w+t) := by
  rw [eval_padRight, bitsValue_append_zero]

lemma bitsValue_take {w t : ℕ} (x : Basis (w+t)) :
    bitsValue (x ∘ (Fin.castAdd t)) = (bitsValue x).setWidth w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show (bitsValue (x ∘ Fin.castAdd t)).getLsbD i = x ((⟨i,hi⟩ : Fin w).castAdd t) from
    bitsValue_bit _ ⟨i,hi⟩, BitVec.getLsbD_setWidth]
  simp only [hi, decide_true, Bool.true_and]
  exact (bitsValue_bit x ((⟨i,hi⟩ : Fin w).castAdd t)).symm

lemma setWidth_toNat_of_le {w t : ℕ} (h : w ≤ t) (x : BitVec w) :
    (x.setWidth t).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt]
  exact lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) h)

/-- A word of constants uses at most one Boolean node per output bit. -/
def wordConstant {n : ℕ} {w : ℕ} (v : BitVec w) : BooleanNetwork n w :=
  vector (fun i => constant (v.getLsbD i.val))

lemma wordConstant_eval {n w : ℕ} (v : BitVec w) (x : Basis n) :
    bitsValue ((wordConstant v).eval x) = v := by
  have he : (wordConstant (n := n) v).eval x = fun i => v.getLsbD i.val := by
    funext i
    simp [wordConstant]
  rw [he, bitsValue_bits]

lemma wordConstant_count {n w : ℕ} (v : BitVec w) :
    (wordConstant (n := n) v).net.count = w := by
  simp [wordConstant]

end BitArithmetic
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ModularMultiply.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

/-- Full double-width product followed by full double-width remainder, with no
word overflow. The narrow remainder is valid because the modulus is a word. -/
def mulMod {n w : ℕ} (a b m : BooleanNetwork n w) : BooleanNetwork n w :=
  let p := ((a.comp (padRight w w)).pair (b.comp (padRight w w))).comp (mul (w+w))
  ((p.pair (m.comp (padRight w w))).comp (mod (w+w))).rewire (Fin.castAdd w)

lemma mulMod_count {n w : ℕ} (a b m : BooleanNetwork n w) :
    (mulMod a b m).net.count ≤
      a.net.count + b.net.count + m.net.count + (1224*w*w+143*w+12) := by
  have h₁ := mul_count (w+w)
  have h₂ := mod_count (w+w)
  simp only [mulMod, count_rewire, count_comp, count_pair, count_padRight]
  nlinarith

lemma mulMod_word {n w : ℕ} (a b m : BooleanNetwork n w) (x : Basis n)
    (hm : 0 < (bitsValue (m.eval x)).toNat) :
    (bitsValue ((mulMod a b m).eval x)).toNat =
      (bitsValue (a.eval x)).toNat * (bitsValue (b.eval x)).toNat %
        (bitsValue (m.eval x)).toNat := by
  simp only [mulMod, eval_rewire, eval_comp, eval_pair]
  rw [bitsValue_take, mod_word, BitVec.toNat_setWidth, BitVec.toNat_umod,
    mul_word, BitVec.toNat_mul]
  simp only [padRight_word, setWidth_toNat_of_le (by omega : w ≤ w+w)]
  have hp : (bitsValue (a.eval x)).toNat * (bitsValue (b.eval x)).toNat < 2^(w+w) := by
    rw [pow_add]
    exact Nat.mul_lt_mul_of_lt_of_lt (bitsValue (a.eval x)).isLt
      (bitsValue (b.eval x)).isLt
  rw [Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt]
  exact (Nat.mod_lt _ hm).trans (bitsValue (m.eval x)).isLt

/-- A word mux shares previously computed word outputs via fanout; it does not
recompute the operand circuit separately at every bit. -/
def wordMux {n w : ℕ} (c : BooleanNetwork n 1) (a b : BooleanNetwork n w) :
    BooleanNetwork n w :=
  ((c.pair a).pair b).comp (vector (fun i =>
    mux (bit ⟨0,by omega⟩) (bit ⟨1+i.val,by omega⟩)
      (bit ⟨1+w+i.val,by omega⟩)))

lemma wordMux_eval {n w : ℕ} (c : BooleanNetwork n 1) (a b : BooleanNetwork n w)
    (x : Basis n) :
    (wordMux c a b).eval x = if c.eval x 0 then a.eval x else b.eval x := by
  funext i
  simp only [wordMux, eval_comp, eval_vector, eval_mux, eval_bit, eval_pair]
  have h₀ : (⟨0,by omega⟩ : Fin (1+w+w)) = (Fin.castAdd w ((0 : Fin 1).castAdd w)) := rfl
  have h₁ : (⟨1+i.val,by omega⟩ : Fin (1+w+w)) = (Fin.natAdd 1 i).castAdd w := rfl
  have h₂ : (⟨1+w+i.val,by omega⟩ : Fin (1+w+w)) = Fin.natAdd (1+w) i := rfl
  simp only [h₀,h₁,h₂,Fin.append_left,Fin.append_right]
  split <;> rfl

lemma wordMux_count {n w : ℕ} (c : BooleanNetwork n 1) (a b : BooleanNetwork n w) :
    (wordMux c a b).net.count = c.net.count+a.net.count+b.net.count+7*w := by
  simp [wordMux, count_comp, count_pair, Nat.mul_comm]

end ExactQuantumFactoring.BitArithmetic


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ModularPower.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork
open scoped BigOperators

abbrev powerWidth (w b : ℕ) := ((w+w)+b)+w

def powerPack {w b : ℕ} (a m : Basis w) (e : Basis b) (z : Basis w) :
    Basis (powerWidth w b) := Fin.append (Fin.append (Fin.append a m) e) z

def powerBase (w b : ℕ) : BooleanNetwork (powerWidth w b) w :=
  select (fun i => ((i.castAdd w).castAdd b).castAdd w)
def powerModulus (w b : ℕ) : BooleanNetwork (powerWidth w b) w :=
  select (fun i => ((Fin.natAdd w i).castAdd b).castAdd w)
def powerAcc (w b : ℕ) : BooleanNetwork (powerWidth w b) w :=
  select (Fin.natAdd ((w+w)+b))
def powerBit (w : ℕ) {b : ℕ} (i : Fin b) : BooleanNetwork (powerWidth w b) 1 :=
  bit ((Fin.natAdd (w+w) i).castAdd w)

@[simp] lemma powerBase_eval {w b : ℕ} (a m : Basis w) (e : Basis b) (z : Basis w) :
    (powerBase w b).eval (powerPack a m e z) = a := by
  funext i
  simp only [powerBase, eval_select, Function.comp_apply, powerPack, Fin.append_left]
@[simp] lemma powerModulus_eval {w b : ℕ} (a m : Basis w) (e : Basis b) (z : Basis w) :
    (powerModulus w b).eval (powerPack a m e z) = m := by
  funext i
  simp only [powerModulus, eval_select, Function.comp_apply, powerPack, Fin.append_left,
    Fin.append_right]
@[simp] lemma powerAcc_eval {w b : ℕ} (a m : Basis w) (e : Basis b) (z : Basis w) :
    (powerAcc w b).eval (powerPack a m e z) = z := by
  funext i
  simp only [powerAcc, eval_select, Function.comp_apply, powerPack, Fin.append_right]
@[simp] lemma powerBit_eval {w b : ℕ} (a m : Basis w) (e : Basis b) (z : Basis w) (i : Fin b) :
    (powerBit w i).eval (powerPack a m e z) 0 = e i := by
  simp only [powerBit, eval_bit, powerPack, Fin.append_left, Fin.append_right]

def powerNew (w : ℕ) {b : ℕ} (i : Fin b) : BooleanNetwork (powerWidth w b) w :=
  let sq := mulMod (powerAcc w b) (powerAcc w b) (powerModulus w b)
  wordMux (powerBit w i) (mulMod sq (powerBase w b) (powerModulus w b)) sq

def powerStep (w : ℕ) {b : ℕ} (i : Fin b) :
    BooleanNetwork (powerWidth w b) (powerWidth w b) :=
  (select (Fin.castAdd w)).pair (powerNew w i)

lemma powerNew_count (w : ℕ) {b : ℕ} (i : Fin b) :
    (powerNew w i).net.count ≤ 3*(1224*w*w+143*w+12)+7*w := by
  have h₁ := mulMod_count (powerAcc w b) (powerAcc w b) (powerModulus w b)
  have h₂ := mulMod_count
    (mulMod (powerAcc w b) (powerAcc w b) (powerModulus w b))
    (powerBase w b) (powerModulus w b)
  have h₀ : (powerAcc w b).net.count = 0 ∧ (powerModulus w b).net.count = 0 ∧
      (powerBase w b).net.count = 0 := ⟨rfl,rfl,rfl⟩
  simp only [h₀.1, h₀.2.1, h₀.2.2, zero_add, add_zero] at h₁ h₂
  simp only [powerNew, wordMux_count, powerBit, count_bit, zero_add]
  omega

lemma powerStep_count (w : ℕ) {b : ℕ} (i : Fin b) :
    (powerStep w i).net.count ≤ 3672*w*w+436*w+36 := by
  have h := powerNew_count w i
  simp only [powerStep, count_pair, count_select, zero_add]
  nlinarith

lemma powerStep_pack {w b : ℕ} (a m : Basis w) (e : Basis b) (z : Basis w) (i : Fin b) :
    (powerStep w i).eval (powerPack a m e z) =
      powerPack a m e ((powerNew w i).eval (powerPack a m e z)) := by
  simp only [powerStep, eval_pair, eval_select, powerPack]
  congr 1
  funext j
  exact Fin.append_left _ _ j

lemma powerNew_value {w b : ℕ} (a m : Basis w) (e : Basis b) (z : Basis w) (i : Fin b)
    (hm : 0 < (bitsValue m).toNat) :
    (bitsValue ((powerNew w i).eval (powerPack a m e z))).toNat =
      (if e i then ((bitsValue z).toNat^2 % (bitsValue m).toNat)*
        (bitsValue a).toNat % (bitsValue m).toNat
      else (bitsValue z).toNat^2 % (bitsValue m).toNat) := by
  rw [powerNew, wordMux_eval, powerBit_eval]
  have hm' : 0 < (bitsValue ((powerModulus w b).eval (powerPack a m e z))).toNat := by
    simpa only [powerModulus_eval] using hm
  split <;> rw [mulMod_word _ _ _ _ hm']
  · rw [mulMod_word _ _ _ _ hm']
    simp only [powerAcc_eval, powerBase_eval, powerModulus_eval, pow_two]
  · simp only [powerAcc_eval, powerModulus_eval, pow_two]

/-- Horner value processes the actual physical data bits from low wire to high
wire, matching the reversed input convention of the triangular transform. -/
def horner {b : ℕ} (e : Basis b) : (k : ℕ) → k ≤ b → ℕ
  | 0, _ => 0
  | k+1, h => 2*horner e k (by omega) + (e ⟨k,by omega⟩).toNat

def powerPrefix (w b : ℕ) : (k : ℕ) → k ≤ b → BooleanNetwork (powerWidth w b) (powerWidth w b)
  | 0, _ => select id
  | k+1, h => (powerPrefix w b k (by omega)).comp (powerStep w ⟨k,by omega⟩)

lemma powerPrefix_count (w b k : ℕ) (hk : k ≤ b) :
    (powerPrefix w b k hk).net.count ≤ k*(3672*w*w+436*w+36) := by
  induction k with
  | zero => simp [powerPrefix]
  | succ k ih =>
    have h := powerStep_count w (⟨k,by omega⟩ : Fin b)
    simp only [powerPrefix, count_comp]
    have hh := ih (by omega)
    nlinarith

lemma horner_pow_step (a m v : ℕ) (b : Bool) :
    (if b then ((a^v % m)^2 % m)*a % m else (a^v % m)^2 % m) =
      a^(2*v+b.toNat) % m := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.toNat_false, Nat.add_zero]
    rw [← Nat.pow_mod, ← pow_mul]
    congr 2
    omega
  · simp only [↓reduceIte, Bool.toNat_true]
    rw [← Nat.pow_mod, Nat.mod_mul_mod, ← pow_mul, pow_succ, Nat.mul_comm v 2]

lemma powerPrefix_value {w b : ℕ} (a m : Basis w) (e : Basis b)
    (hm : 2 ≤ (bitsValue m).toNat) (k : ℕ) (hk : k ≤ b) :
    ∃ z : Basis w,
      (powerPrefix w b k hk).eval
        (powerPack a m e (fun i => (BitVec.ofNat w 1).getLsbD i.val)) = powerPack a m e z ∧
      (bitsValue z).toNat = (bitsValue a).toNat ^ horner e k hk % (bitsValue m).toNat := by
  induction k with
  | zero =>
    refine ⟨(fun i => (BitVec.ofNat w 1).getLsbD i.val),?_,?_⟩
    · simp only [powerPrefix, eval_select, Function.comp_id]
    · rw [bitsValue_bits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
      · simp [horner, Nat.mod_eq_of_lt (by omega : 1 < (bitsValue m).toNat)]
      · have h := (bitsValue m).isLt
        omega
  | succ k ih =>
    obtain ⟨z,hz,hv⟩ := ih (by omega)
    refine ⟨(powerNew w ⟨k,by omega⟩).eval (powerPack a m e z),?_,?_⟩
    · rw [powerPrefix,eval_comp,hz,powerStep_pack]
    · rw [powerNew_value _ _ _ _ _ (by omega), hv, horner_pow_step]
      rfl

/-- The complete bounded binary-power network. Inputs remain available for
copying; the result is a separate output word. -/
def modularPower (w b : ℕ) : BooleanNetwork ((w+w)+b) w :=
  ((select id).pair (wordConstant (BitVec.ofNat w 1))).comp
    ((powerPrefix w b b le_rfl).rewire (Fin.natAdd ((w+w)+b)))

lemma modularPower_count (w b : ℕ) :
    (modularPower w b).net.count ≤ w+b*(3672*w*w+436*w+36) := by
  have h := powerPrefix_count w b b le_rfl
  simp only [modularPower,count_comp,count_pair,count_select,wordConstant_count,
    count_rewire,zero_add]
  omega

lemma modularPower_value {w b : ℕ} (a m : Basis w) (e : Basis b)
    (hm : 2 ≤ (bitsValue m).toNat) :
    (bitsValue ((modularPower w b).eval (Fin.append (Fin.append a m) e))).toNat =
      (bitsValue a).toNat ^ horner e b le_rfl % (bitsValue m).toNat := by
  obtain ⟨z,hz,hv⟩ := powerPrefix_value a m e hm b le_rfl
  have hc : (wordConstant (n := (w+w)+b) (BitVec.ofNat w 1)).eval
      (Fin.append (Fin.append a m) e) =
        (fun i => (BitVec.ofNat w 1).getLsbD i.val) := by
    funext i
    simp [wordConstant]
  simp only [modularPower,eval_comp,eval_rewire,eval_pair,eval_select,
    Function.comp_id,hc]
  change (bitsValue (((powerPrefix w b b le_rfl).eval
    (powerPack a m e (fun i => (BitVec.ofNat w 1).getLsbD i.val))) ∘
      Fin.natAdd ((w+w)+b))).toNat = _
  rw [hz]
  have he : powerPack a m e z ∘ Fin.natAdd ((w+w)+b) = z := by
    funext i
    exact Fin.append_right _ _ i
  rw [he,hv]

end ExactQuantumFactoring.BitArithmetic


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitNumbers.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

lemma bitsValue_toNat {b : ℕ} (x : Fin b → Bool) :
    (bitsValue x).toNat = ∑ i : Fin b, 2^i.val*(x i).toNat := by
  induction b with
  | zero => simp [bitsValue]
  | succ b ih =>
    rw [bitsValue, BitVec.toNat_cons', Nat.shiftLeft_eq, ih, Fin.sum_univ_castSucc]
    simp only [Fin.val_last, Fin.val_castSucc]
    ring

lemma bitsValue_ofFn {b : ℕ} (v : Fin (2^b)) :
    (bitsValue (fun i : Fin b => v.val.testBit i.val)).toNat = v.val := by
  have he : (fun i : Fin b => v.val.testBit i.val) =
      (fun i : Fin b => (BitVec.ofNat b v.val).getLsbD i.val) := by simp
  rw [he, bitsValue_bits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt v.isLt]

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TriangularPaths.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.Triangular
open scoped BigOperators

abbrev Bits (b : ℕ) := Fin b → Bool

def hybrid {b : ℕ} (x y : Bits b) (k : ℕ) : Bits b :=
  fun i => if i.val < k then y i else x i

def TailEq {b : ℕ} (k : ℕ) (x y : Bits b) : Prop :=
  ∀ i : Fin b, k ≤ i.val → y i = x i

instance {b k : ℕ} (x y : Bits b) : Decidable (TailEq k x y) := by
  unfold TailEq
  infer_instance

lemma hybrid_update {b k : ℕ} (x y : Bits b) (t : Fin b) (v : Bool) (h : k ≤ t.val) :
    hybrid x (Function.update y t v) k = hybrid x y k := by
  funext i
  unfold hybrid
  by_cases hi : i.val < k
  · rw [ite_eq_left hi, ite_eq_left hi, Function.update_of_ne]
    intro he; subst i; omega
  · rw [ite_eq_right hi, ite_eq_right hi]

lemma hybrid_of_tail {b k : ℕ} (x y : Bits b) (h : TailEq k x y) :
    hybrid x y k = y := by
  funext i
  unfold hybrid
  split_ifs with hi
  · rfl
  · exact (h i (by omega)).symm

lemma tail_update {b k : ℕ} (hk : k < b) (x y : Bits b) (v : Bool) :
    TailEq k x (Function.update y ⟨k,hk⟩ v) ↔
      v = x ⟨k,hk⟩ ∧ TailEq (k+1) x y := by
  constructor
  · intro h
    constructor
    · simpa using h ⟨k,hk⟩ le_rfl
    · intro i hi
      have hn : i ≠ (⟨k,hk⟩ : Fin b) := by intro he; have hh := congrArg Fin.val he; change i.val=k at hh; omega
      simpa only [Function.update_of_ne hn] using h i (by omega)
  · rintro ⟨hv,h⟩ i hi
    by_cases he : i.val = k
    · have hi' : i = (⟨k,hk⟩ : Fin b) := Fin.ext he
      subst i; simpa using hv
    · rw [Function.update_of_ne (by intro hh; exact he (congrArg Fin.val hh))]
      exact h i (by omega)

variable {A : Type*} [AddCommGroup A]

/-- Path translations for H on ascending physical wires followed by a
classically controlled translation on a separate additive register. -/
def pathShift {b : ℕ} (δ : Fin b → Bits b → A) (x y : Bits b) :
    (k : ℕ) → k ≤ b → A
  | 0, _ => 0
  | k+1, h => pathShift δ x y k (by omega) + δ ⟨k,by omega⟩ (hybrid x y (k+1))

noncomputable def hEntry (a c : Bool) : ℂ :=
  (if a && c then -1 else 1) / (Real.sqrt 2 : ℂ)

noncomputable def pathWeight {b : ℕ} (x y : Bits b) : (k : ℕ) → k ≤ b → ℂ
  | 0, _ => 1
  | k+1, h => pathWeight x y k (by omega) * hEntry (x ⟨k,by omega⟩) (y ⟨k,by omega⟩)

lemma pathShift_update {b k : ℕ} (hk : k ≤ b) (δ : Fin b → Bits b → A)
    (x y : Bits b) (t : Fin b) (v : Bool) (h : k ≤ t.val) :
    pathShift δ x (Function.update y t v) k hk = pathShift δ x y k hk := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pathShift, pathShift, ih (by omega) (by omega), hybrid_update _ _ _ _ h]

lemma pathWeight_update {b k : ℕ} (hk : k ≤ b) (x y : Bits b)
    (t : Fin b) (v : Bool) (h : k ≤ t.val) :
    pathWeight x (Function.update y t v) k hk = pathWeight x y k hk := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pathWeight, pathWeight, ih (by omega) (by omega), Function.update_of_ne]
    intro he; have hh := congrArg Fin.val he; change k=t.val at hh; omega

/-- Exact pointwise action of the H/conditional-forward-translation sequence.
There is no projection or forced-success operation in this evolution. -/
noncomputable def evolve {b : ℕ} (δ : Fin b → Bits b → A) (x : Bits b) (χ : A → ℂ) :
    (k : ℕ) → k ≤ b → Bits b → A → ℂ
  | 0, _, y, z => if y = x then χ z else 0
  | k+1, h, y, z =>
    (evolve δ x χ k (by omega) (Function.update y ⟨k,by omega⟩ false)
      (z-δ ⟨k,by omega⟩ y) +
     (if y ⟨k,by omega⟩ then (-1:ℂ) else 1) *
     evolve δ x χ k (by omega) (Function.update y ⟨k,by omega⟩ true)
      (z-δ ⟨k,by omega⟩ y)) / (Real.sqrt 2 : ℂ)

/-- Every data wire has a single H and therefore exactly one compatible path
for each input/output pair, even though the phase register is coherent. -/
theorem evolve_path {b : ℕ} (δ : Fin b → Bits b → A) (x y : Bits b) (χ : A → ℂ)
    (k : ℕ) (hk : k ≤ b) (z : A) :
    evolve δ x χ k hk y z =
      if TailEq k x y then pathWeight x y k hk * χ (z-pathShift δ x y k hk) else 0 := by
  classical
  induction k generalizing y z with
  | zero =>
    have he : TailEq 0 x y ↔ y=x := by simp [TailEq, funext_iff]
    simp [evolve, pathWeight, pathShift, he]
  | succ k ih =>
    rw [evolve, ih _ (by omega), ih _ (by omega)]
    simp only [tail_update]
    rw [pathShift_update _ _ _ _ _ _ le_rfl,
      pathShift_update _ _ _ _ _ _ le_rfl,
      pathWeight_update _ _ _ _ _ le_rfl, pathWeight_update _ _ _ _ _ le_rfl]
    by_cases ht : TailEq (k+1) x y
    · rw [ite_eq_left ht, pathShift, pathWeight, hybrid_of_tail _ _ ht]
      rw [show z-δ ⟨k,by omega⟩ y-pathShift δ x y k (by omega) =
        z-(pathShift δ x y k (by omega)+δ ⟨k,by omega⟩ y) by abel]
      cases hx : x ⟨k,by omega⟩ <;> cases hy : y ⟨k,by omega⟩ <;>
        simp [ht, hEntry] <;> ring
    · simp [ht]

lemma evolve_full {b : ℕ} (δ : Fin b → Bits b → A) (x y : Bits b) (χ : A → ℂ) (z : A) :
    evolve δ x χ b le_rfl y z =
      pathWeight x y b le_rfl * χ (z-pathShift δ x y b le_rfl) := by
  rw [evolve_path, ite_eq_left (by intro i hi; exact False.elim (Nat.not_le.mpr i.isLt hi))]

end ExactQuantumFactoring.Triangular


end

end OAI


