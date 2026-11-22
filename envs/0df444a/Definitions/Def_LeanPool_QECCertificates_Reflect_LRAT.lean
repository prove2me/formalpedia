-- Prove2me | Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
-- name    : LeanPool_QECCertificates_Reflect_LRAT
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:41:14.491078+00:00
-- url     : https://prove2.me/theorems/5a77b392-e66e-4400-bab2-c1e3b41e708b
-- title:
--   LRAT
-- statement:
--   Definitions and structural lemmas for LRAT, from Shuoming An; LeanPool contributors's pinned Quantum code certificates and hypergraph-product theory development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/LRAT.lean

module
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Basic
public import Std.Data.TreeMap.Lemmas
public import Std.Data.DTreeMap.Lemmas
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace QECCertificates.LRAT
abbrev Lit := Nat × Bool
abbrev Clause := List Lit
abbrev CNF := List Clause
abbrev Assign := Nat → Bool
abbrev PAssign := List Lit
def litNeg (l : Lit) : Lit := (l.1, !l.2)
def SatClause (σ : Assign) (C : Clause) : Prop := ∃ l ∈ C, σ l.1 = l.2
def SatFormula (σ : Assign) (F : CNF) : Prop := ∀ C ∈ F, SatClause σ C
def Satisfiable (F : CNF) : Prop := ∃ σ, SatFormula σ F
def agrees (σ : Assign) (a : PAssign) : Prop := ∀ l ∈ a, σ l.1 = l.2
def litFree (a : PAssign) (l : Lit) : Bool := !(decide (litNeg l ∈ a))
def scanAux (a : PAssign) (fr : List Lit) : Clause → List Lit
  | [] => fr
  | l :: rest => if litFree a l then scanAux a (l :: fr) rest else scanAux a fr rest
def scan (a : PAssign) (D : Clause) : List Lit := scanAux a [] D
structure ClauseDB (Carrier : Type) where
  /-- Look up a clause at a zero-based index. -/
  get? : Carrier → Nat → Option Clause
  /-- The index at which the next clause is appended. -/
  size : Carrier → Nat
  /-- Append a clause to the database. -/
  push : Carrier → Clause → Carrier
  /-- Semantic membership of a clause in the database. -/
  Mem : Carrier → Clause → Prop
  /-- A clause that is looked up is certainly in the database. -/
  get?_mem : ∀ {d i C}, get? d i = some C → Mem d C
  /-- After one append, every clause in the database is **either the new one or was already
  there**. **Only the half that soundness needs** is required: `checkAux_sound` consumes
  this direction only, while the missing converse,
  `C' = C ∨ Mem d C' → Mem (push d C) C'`, is exactly where a balanced-tree instance needs
  the invariant "key < size". Stating the laws at the **strength that is used** keeps both
  instances clean. -/
  push_mem : ∀ {d C C'}, Mem (push d C) C' → C' = C ∨ Mem d C'
  /-- Build a database from a CNF. -/
  ofCNF : CNF → Carrier
  /-- Every clause of the initial database **comes from** that CNF, again only the half
  that is used. -/
  ofCNF_mem : ∀ {F C}, Mem (ofCNF F) C → C ∈ F
namespace ClauseDB
def array : ClauseDB (Array Clause) where
  get? := fun d i => d[i]?
  size := Array.size
  push := Array.push
  Mem := fun d C => C ∈ d
  get?_mem := by
    intro d i C h
    rw [Array.mem_def]
    exact List.mem_of_getElem? (by simpa using h)
  push_mem := by
    intro d C C' h
    rw [Array.mem_push] at h
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h
  ofCNF := List.toArray
  ofCNF_mem := by
    intro F C h
    exact (List.mem_toArray).mp h
def treeMem (d : Std.TreeMap Nat Clause compare) (C : Clause) : Prop := ∃ i, d.get? i = some C
def tree : ClauseDB (Std.TreeMap Nat Clause compare) where
  get? := fun d i => d.get? i
  size := fun d => Std.TreeMap.size d
  push := fun (d : Std.TreeMap Nat Clause compare) C =>
    Std.TreeMap.insert d (Std.TreeMap.size d) C
  Mem := treeMem
  get?_mem := fun h => ⟨_, h⟩
  push_mem := by
    intro d C C' h
    obtain ⟨i, hi⟩ := h
    simp only [Std.TreeMap.get?, Std.TreeMap.insert] at hi
    rw [Std.DTreeMap.Const.get?_insert] at hi
    split at hi
    · exact Or.inl (Option.some.inj hi).symm
    · exact Or.inr ⟨i, hi⟩
  ofCNF := fun F =>
    F.foldl (fun (d : Std.TreeMap Nat Clause compare) C =>
      Std.TreeMap.insert d (Std.TreeMap.size d) C) ∅
  ofCNF_mem := by
    intro F C h
    -- Generalize over the accumulator: intermediate folds start from a nonempty database.
    have key : ∀ (l : List Clause) (acc : Std.TreeMap Nat Clause compare),
        treeMem (l.foldl (fun (d : Std.TreeMap Nat Clause compare) C =>
          Std.TreeMap.insert d (Std.TreeMap.size d) C) acc) C
          → C ∈ l ∨ treeMem acc C := by
      intro l
      induction l with
      | nil =>
          intro acc h
          exact Or.inr h
      | cons D ds ih =>
          intro acc h
          rw [List.foldl_cons] at h
          rcases ih _ h with hmem | hmem
          · exact Or.inl (List.mem_cons_of_mem _ hmem)
          · obtain ⟨i, hi⟩ := hmem
            simp only [Std.TreeMap.get?, Std.TreeMap.insert] at hi
            rw [Std.DTreeMap.Const.get?_insert] at hi
            split at hi
            · exact Or.inl (by simp [Option.some.inj hi])
            · exact Or.inr ⟨i, hi⟩
    rcases key F ∅ h with hmem | hmem
    · exact hmem
    · -- Simplification matches the empty-tree lemma up to definitional equality.
      obtain ⟨i, hi⟩ := hmem
      simp at hi
end ClauseDB
def rupAux {K : Type} (D : ClauseDB K) (d : K) (a : PAssign) : List Nat → Bool
  | [] => false
  | h :: rest =>
      match D.get? d (h - 1) with
      | none => false
      | some E =>
          match scan a E with
          | [] => true
          | [l] => rupAux D d (l :: a) rest
          | _ => false
def rupCheck {K : Type} (D : ClauseDB K) (d : K) (C : Clause) (hints : List Nat) : Bool :=
  rupAux D d (C.map litNeg) hints
structure LStep where
  /-- One-based number of the added clause. -/
  id : Nat
  /-- The clause justified by this step. -/
  clause : Clause
  /-- One-based indices to follow during reverse unit propagation. -/
  hints : List Nat
def checkAux {K : Type} (D : ClauseDB K) (d : K) : List LStep → Bool
  | [] => false
  | s :: rest =>
      if s.id = D.size d + 1 ∧ rupCheck D d s.clause s.hints then
        s.clause.isEmpty || checkAux D (D.push d s.clause) rest
      else false
def checkStepsWith {K : Type} (D : ClauseDB K) (F : CNF) (steps : List LStep) : Bool :=
  checkAux D (D.ofCNF F) steps
abbrev checkSteps (F : CNF) (steps : List LStep) : Bool := checkStepsWith ClauseDB.array F steps
end QECCertificates.LRAT


