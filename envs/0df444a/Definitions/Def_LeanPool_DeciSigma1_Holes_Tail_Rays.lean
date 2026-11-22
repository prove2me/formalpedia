-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
-- name    : LeanPool_DeciSigma1_Holes_Tail_Rays
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:43:06.0648+00:00
-- url     : https://prove2.me/theorems/61c9f257-9812-44cf-b854-7d2ad40b74d5
-- title:
--   Rays
-- statement:
--   Definitions and structural lemmas for Rays, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
public import Mathlib.Order.Nat
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Ring.RingNF
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.length_suffixOfLength
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Holes.Tail
open DeciSigma1.Readers
open DeciSigma1.Words (pow)
open DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
def windowState (T : Table α S k) (q0 : S) (x : List α) (b c : ℕ) : S × List α :=
  (runFrom T.step q0 (x.take (c - b)), (x.take c).drop (c - b))
def ClosedAt (T : Table α S k) (q0 : S) (x : List α) (B c c' : ℕ) : Prop :=
  B ≤ c ∧ c < c' ∧ c' ≤ x.length ∧ windowState T q0 x B c = windowState T q0 x B c'
def NoSuffixOccurrenceEndsBetween [DecidableEq α] (x t : List α) (B c c' : ℕ) : Prop :=
  ∀ e ∈ Words.occurrences x t B, e ≤ c ∨ c' < e
def pumpFactor (x : List α) (c c' L : ℕ) : List α :=
  x.take c ++ (pow ((x.drop c).take (c' - c)) (L + 1)).take L
section Dictionary
variable [DecidableEq α]
def nonemptyFactors (w : List α) : Finset (List α) :=
  (Finset.range w.length).biUnion fun i =>
    (Finset.range (w.length - i)).image fun j => (w.drop i).take (j + 1)
def suffixDictionary (ts : List (List α)) (B : ℕ) : Finset (List α) :=
  insert [] (ts.toFinset.biUnion fun t => nonemptyFactors (Words.suffixOfLength t B))
variable {ts : List (List α)} {B : ℕ}
end Dictionary
section Nodes
variable [DecidableEq α] {D : Finset (List α)}
def dictSuffix (D : Finset (List α)) : List α → List α
  | [] => []
  | a :: w => if a :: w ∈ D then a :: w else dictSuffix D w
def suffixNode (T : Table α S k) (q0 : S) (D : Finset (List α)) (w : List α) : List α × S :=
  (dictSuffix D w, runFrom T.step q0 (w.take (w.length - (dictSuffix D w).length)))
def suffixNodeStep (T : Table α S k) (D : Finset (List α)) (n : List α × S) (a : α) :
    List α × S :=
  (dictSuffix D (n.1 ++ [a]),
    runFrom T.step n.2 ((n.1 ++ [a]).take (n.1.length + 1 - (dictSuffix D (n.1 ++ [a])).length)))
def NodeClosedAt (T : Table α S k) (q0 : S) (D : Finset (List α)) (x : List α) (c c' : ℕ) :
    Prop :=
  c < c' ∧ c' ≤ x.length ∧ suffixNode T q0 D (x.take c) = suffixNode T q0 D (x.take c')
variable {T : Table α S k} {q0 : S} {x : List α} {B c c' : ℕ}
def suffixNodeBound (m N B : ℕ) : ℕ := N * (m * (B * (B + 1) / 2) + 1)
def factorLengthBound (m N B : ℕ) : ℕ := (B + 1) * suffixNodeBound m N B
end Nodes
section PumpFactor
variable {x : List α} {c c' L : ℕ}
theorem length_loop (hc' : c' ≤ x.length) :
    ((x.drop c).take (c' - c)).length = c' - c := by simp; omega
theorem loop_ne_nil (hcc : c < c') (hc' : c' ≤ x.length) : (x.drop c).take (c' - c) ≠ [] := by
  intro h; have := congrArg List.length h; rw [length_loop hc'] at this; simp at this; omega
end PumpFactor
section Closed
variable {T : Table α S k} {q0 : S} {x : List α} {B c c' L : ℕ}
end Closed
open DeciSigma1.Arithmetic DeciSigma1.Words DeciSigma1.Automata
variable {ι : Type}
section Runs
variable (M : StructuralReader α S k)
def rayState (q : S) (Ω : Ray α) (a : ℕ) : S := runFrom M.step q (streamPrefix Ω.stream a)
variable {M}
variable [DecidableEq α] [Fintype S]
def rayHorizon (S : Type) [Fintype S] (Ω : Ray α) : ℕ := Ω.onset + Fintype.card S * Ω.period
end Runs
def repeatFactorRay (x : List α) (c c' : ℕ) (hcc : c < c') (hc' : c' ≤ x.length) : Ray α :=
  ⟨x.take c, (x.drop c).take (c' - c), loop_ne_nil hcc hc'⟩
section System
variable [DecidableEq α] [Fintype S] (M : StructuralReader α S k) [Fintype ι] [DecidableEq ι]
def maxOnset (Ω : ι → Ray α) : ℕ := Finset.univ.sup fun i => (Ω i).onset
def maxPeriod (Ω : ι → Ray α) : ℕ := Finset.univ.sup fun i => (Ω i).period
def rayEdges (st : ι → S) (Ω : ι → Ray α) (J : ι → ℕ) : Finset (ι × ι × ℤ) :=
  Finset.univ.biUnion fun i => Finset.univ.biUnion fun j =>
    if i = j then ∅ else
      (((Finset.range (rayHorizon S (Ω i))) ×ˢ (Finset.range (J j + 1))).filter
        (fun ab => M.admitted (rayState M (st i) (Ω i) ab.1) (rayState M (st j) (Ω j) ab.2) = true ∧
          ∀ t, (Ω i).stream (ab.1 + t) = (Ω j).stream (ab.2 + t))).image
        (fun ab => (i, j, (ab.2 : ℤ) - ab.1 + 1))
def raySystem (st : ι → S) (Ω : ι → Ray α) (J : ι → ℕ) : DifferenceSystem ι :=
  DifferenceSystem.ofFinset (rayEdges M st Ω J)
variable {M}
end System
end DeciSigma1.Holes.Tail


