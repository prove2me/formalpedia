-- Prove2me | Definitions.Def_HighPrecSAC1_Main_ArithmeticCircuit
-- name    : HighPrecSAC1_Main_ArithmeticCircuit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:22:24.364196+00:00
-- url     : https://prove2.me/theorems/1d19cec6-904e-4763-8522-14a48c75b7fd
-- title:
--   Positive semi-unbounded arithmetic DAGs with arbitrary source atoms
-- statement:
--   A general arithmetic DAG lists its gates in topological order. A gate is a source atom, an unbounded finite sum of preceding gates, or a product of exactly two preceding gates. Multiple outputs designate gates. Evaluation works over any semiring. The module defines the gate and wire count, depth with source gates at zero, and an explicit binary description parametrized by the encoding of source atoms. It imposes no source-value or conclusion-dependent restrictions.
-- source:
--   Cheng, Huang and Wu (2026), arXiv:2610.25623 (preprint; held version, version number not printed in the PDF, sha256 8c9ac662…), Definitions and constructions, §§2, 3, 6, 7, printed p. 10 (PDF 11)

import Definitions.Def_HighPrecSAC1_Main_Uniformity

namespace HighPrecSAC1.Main

/-- General positive semi-unbounded arithmetic DAG, unbundled from the paper's literals. -/
inductive AGate (α : Type) (g : ℕ) where
  | atom (a : α)
  | add (inputs : List (Fin g))
  | mul (left right : Fin g)

structure ACircuit (α : Type) (o : ℕ) where
  gates : ℕ
  gate : (j : Fin gates) → AGate α j.val
  out : Fin o → Fin gates

def AGate.eval {α R : Type} [Semiring R] {g : ℕ} (a : α → R) (v : Fin g → R) : AGate α g → R
  | .atom x => a x
  | .add xs => (xs.map v).sum
  | .mul j k => v j * v k

def ACircuit.prefix {α R : Type} [Semiring R] {o : ℕ} (C : ACircuit α o) (a : α → R) :
    (k : ℕ) → k ≤ C.gates → Fin k → R
  | 0, _ => Fin.elim0
  | k+1, h => Fin.snoc (α := fun _ => R) (C.prefix a k (Nat.le_of_succ_le h))
      ((C.gate ⟨k,h⟩).eval a (C.prefix a k (Nat.le_of_succ_le h)))

def ACircuit.eval {α R : Type} [Semiring R] {o : ℕ} (C : ACircuit α o) (a : α → R) : Fin o → R :=
  fun j => C.prefix a C.gates le_rfl (C.out j)

def AGate.depth {α : Type} {g : ℕ} (d : Fin g → ℕ) : AGate α g → ℕ
  | .atom _ => 0
  | .add xs => 1 + (xs.map d).foldl max 0
  | .mul j k => 1 + max (d j) (d k)

def ACircuit.prefixDepth {α : Type} {o : ℕ} (C : ACircuit α o) :
    (k : ℕ) → k ≤ C.gates → Fin k → ℕ
  | 0, _ => Fin.elim0
  | k+1, h => Fin.snoc (α := fun _ => ℕ) (C.prefixDepth k (Nat.le_of_succ_le h))
      ((C.gate ⟨k,h⟩).depth (C.prefixDepth k (Nat.le_of_succ_le h)))

def ACircuit.depth {α : Type} {o : ℕ} (C : ACircuit α o) : ℕ :=
  Finset.univ.sup fun j => C.prefixDepth C.gates le_rfl (C.out j)

def AGate.arity {α : Type} {g : ℕ} : AGate α g → ℕ
  | .atom _ => 0
  | .add xs => xs.length
  | .mul _ _ => 2

def ACircuit.size {α : Type} {o : ℕ} (C : ACircuit α o) : ℕ :=
  C.gates + (∑ j, (C.gate j).arity) + o

def AGate.code {α : Type} {g : ℕ} (a : α → List Bool) : AGate α g → List Bool
  | .atom x => [false,false] ++ a x
  | .add xs => [false,true] ++ codeList (fun j => codeNat j.val) xs
  | .mul j k => [true,false] ++ codeNat j.val ++ codeNat k.val

def ACircuit.description {α : Type} {o : ℕ} (C : ACircuit α o) (a : α → List Bool) : List Bool :=
  codeNat C.gates ++ (List.finRange C.gates).flatMap (fun j => (C.gate j).code a) ++
    codeList (fun j => codeNat j.val) ((List.finRange o).map C.out)

end HighPrecSAC1.Main


