-- Prove2me | Definitions.Def_DetDLP_BorderedBitIO
-- name    : DetDLP_BorderedBitIO
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-23T14:14:48.233996+00:00
-- url     : https://prove2.me/theorems/4cc4e014-6567-4c0c-be63-a60a29786e3f
-- title:
--   Binary input and output ports for the bordered lattice update
-- statement:
--   The input command parses the canonical encoding of a modular coset update, retains the original input and prepares the nine parameters of the packed Hermite routine. The output command reads a completed Hermite result and the saved input, writes the translated representative and signed trailing basis to a fresh output, and marks success. Both contracts require actual polynomial-length evaluations on the finite Boolean-stack model.
-- source:
--   DetDLP mission, Lemma 4.4. Computational interfaces for composing the bordered update.

import Definitions.Def_DetDLP_BorderedHermite
import Definitions.Def_OAIQ081S067

namespace DetDLP.BorderedBitIO
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls
open BorderedHermite

abbrev Stacks (s : ℕ) := Fin (55+(s+2)) → List Bool
abbrev Code (s : ℕ) := Cmd 8 (55+(s+2))
def backup (s : ℕ) : Fin (55+(s+2)) := Fin.natAdd 55 0
def answer (s : ℕ) : Fin (55+(s+2)) := Fin.natAdd 55 1
def initialStacks (s : ℕ) (input : List Bool) : Stacks s :=
  fun i => if i=backup s then input else []
def withBackup (s : ℕ) (v : Fin 55 → List Bool) (input : List Bool) : Stacks s :=
  fun i => Fin.addCases (m:=55) (n:=s+2) (motive:=fun _ => List Bool) v (fun k => if k=0 then input else []) i

def columns {n : ℕ} (a : Fin n → ℕ) (B : Matrix (Fin n) (Fin n) ℤ) : Array (Column (n+1)) :=
  (Vector.ofFn (fun j => Vector.ofFn (fun i => B i j))).toArray.map fun col =>
    Vector.ofFn (Fin.cases ((List.finRange n).foldl (fun s i => s+(a i:ℤ)*col.get i) 0) (fun i => col.get i))

def serialize {n : ℕ} (m : ℕ) (cols : Array (Column n)) :=
  Nat.ofDigits ((m+1)^n) ((cols.toList.map (fun col =>
    Nat.ofDigits (m+1) (List.ofFn fun i => (col.get i).toNat)))++[1])
def staged {n : ℕ} (m : ℕ) (cols : Array (Column n)) : Fin 55 → List Bool :=
  let b := m+1
  let D := b^n
  let ports : Fin 9 → ℕ := ![m,b,D,1,1,serialize m (cols.map fun c => c.map (·%(m:ℤ))),D/b,1,0]
  fun i => Fin.addCases (m:=46) (n:=9) (motive:=fun _ => List Bool) (fun _ => []) (fun j => (ports j).bits) i

def Valid {n : ℕ} (m : ℕ) (x a : Fin n → ℕ) (B : Matrix (Fin n) (Fin n) ℤ) (c : ℕ) :=
  2 ≤ m ∧ 1 ≤ n ∧ (∀ i,x i < m) ∧ (∀ i,a i < m) ∧ c < m ∧ ∀ i j,|B i j| ≤ (m:ℤ)

def rep {n : ℕ} (m : ℕ) (x a : Fin n → ℕ) (B : Matrix (Fin n) (Fin n) ℤ) (c : ℕ) :=
  let res := update m (Vector.ofFn x) (Vector.ofFn fun j => Vector.ofFn fun i => B i j) (Vector.ofFn a) c
  encodeCosetRep res.1.get (fun i j => (res.2.get j).get i)

/-- The program reads the canonical binary input and arranges the reduced bordered columns
on the normal-form routine's input ports. A separate stack retains the original input. -/
def InputPreparation :=
  ∃ threshold,∀ s : ℕ,threshold ≤ s → ∃ (q : Code s) (k : ℕ),
    ∀ {n} (m : ℕ) (x a : Fin n → ℕ) (B : Matrix (Fin n) (Fin n) ℤ) (c : ℕ),
      Valid m x a B c →
      let input := encodeCosetUpdateInput m x B a c
      ∃ t r,t ≤ (n+bitLen m+2)^k ∧
        Eval q t ⟨fun _ => false,initialStacks s input⟩
          ⟨r,withBackup s (staged m (columns a B)) input⟩

/-- From the original input and a packed Hermite result, translate the representative
and emit the canonical row-major signed basis encoding and the success flag. -/
def OutputRecovery :=
  ∃ threshold,∀ s : ℕ,threshold ≤ s → ∀ o : Fin 55,∃ (q : Code s) (k : ℕ),
    ∀ {n} (m : ℕ) (x a : Fin n → ℕ) (B : Matrix (Fin n) (Fin n) ℤ) (c : ℕ),
      Valid m x a B c → ∀ (r : Fin 8 → Bool) (v : Fin 55 → List Bool),
      v o=(serialize m (normalForm (m:ℤ) (columns a B))).bits →
      let input := encodeCosetUpdateInput m x B a c
      ∃ (t : ℕ) (final : StructuredProgram.State 8 (55+(s+2))), t ≤ (n+bitLen m+2)^k ∧
        Eval q t ⟨r,withBackup s v input⟩ final ∧ final.stacks (answer s)=rep m x a B c ∧
        final.stacks (backup s)=[true]

end DetDLP.BorderedBitIO


