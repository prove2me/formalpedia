-- Prove2me | Definitions.Def_SeedRecyclingDL_Codes_Channel
-- name    : SeedRecyclingDL_Codes_Channel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:03:44.460395+00:00
-- url     : https://prove2.me/theorems/8cafb3bf-c090-4a45-aed7-b7359ee9275b
-- title:
--   Binary words, unrestricted DL scripts, and channels
-- statement:
--   A word is a finite binary string. Insertions, deletions, substitutions, and adjacent transpositions act at their current positions; operations may overlap or repeat. A script of at most $q$ operations defines reachability, its least possible length defines $d_{\rm DL}$, and $B_q(u)$ includes the zero-step script.
--
--   Channels assign sets of finite outputs to fixed-length inputs. Confusability means a common output, correction means distinct codewords are never confusable, and splittability controls suffix confusability. The exact same-suffix payload competitors are defined independently of the DL ball. This shared layer also gives the actual depth-first ball enumeration and $M(\ell,q)=(q+1)(5(\ell+q)+2)^q$.
--
--   **Formalization Note** Positions are zero based. Reachability of every pair is proved before using a least script length; no empty infimum defaults to zero.
-- source:
--   Quan D. Bui, Manabu Hagiwara, Shuche Wang, Van Khu Vu, STOC 2027 submission #1449 (October 2026), §§1.3, 3.1, 4, PDF pp. 6–7, 10, 12–14 (printed pp. 4–5, 8, 10–12); Appendix C.4, PDF p. 22 (printed p. 20); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1449.pdf

import Definitions.Def_EditMulticoloring_Code_Machine

set_option autoImplicit false

namespace SeedRecyclingDL.Codes

abbrev Bit := Fin 2
abbrev Word := List Bit
abbrev FixedWord (n : ℕ) := Fin n → Bit

def toWord {n : ℕ} (x : FixedWord n) : Word := List.ofFn x

/-- Current-word, zero-based positions. No restriction on overlapping edits. -/
inductive Operation where
  | insert (i : ℕ) (a : Bit)
  | delete (i : ℕ)
  | substitute (i : ℕ) (a : Bit)
  | transpose (i : ℕ)
  deriving DecidableEq

def applyOperation (u : Word) : Operation → Option Word
  | .insert i a => if i ≤ u.length then some (u.take i ++ a :: u.drop i) else none
  | .delete i => if i < u.length then some (u.take i ++ u.drop (i + 1)) else none
  | .substitute i a => if i < u.length ∧ u[i]? ≠ some a then
      some (u.take i ++ a :: u.drop (i + 1)) else none
  | .transpose i => match u[i]?, u[i + 1]? with
      | some a, some c => some (u.take i ++ [c, a] ++ u.drop (i + 2))
      | _, _ => none

def applyScript : List Operation → Word → Option Word
  | [], u => some u
  | e :: es, u => (applyOperation u e).bind (applyScript es)

def Reaches (q : ℕ) (u v : Word) : Prop :=
  ∃ es : List Operation, es.length ≤ q ∧ applyScript es u = some v

/-- A witness of reachability, used solely to totalize the least script length. -/
def deleteAll : ℕ → List Operation
  | 0 => []
  | n + 1 => Operation.delete 0 :: deleteAll n

theorem deleteAll_spec (u : Word) : applyScript (deleteAll u.length) u = some [] := by
  induction u with
  | nil => rfl
  | cons a u ih => simpa [deleteAll, applyScript, applyOperation] using ih

def appendAll (u : Word) (n : ℕ) : List Operation :=
  u.zipIdx.map fun (a, i) => Operation.insert (n + i) a

theorem applyScript_append (es fs : List Operation) (u : Word) :
    applyScript (es ++ fs) u = (applyScript es u).bind (applyScript fs) := by
  induction es generalizing u with
  | nil => simp [applyScript]
  | cons e es ih =>
    simp only [List.cons_append, applyScript]
    cases applyOperation u e <;> simp [ih]

def writeWord : Word → List Operation
  | [] => []
  | a :: u => writeWord u ++ [Operation.insert 0 a]

theorem writeWord_spec (u : Word) : applyScript (writeWord u) [] = some u := by
  induction u with
  | nil => rfl
  | cons a u ih => simp [writeWord, applyScript_append, ih, applyScript, applyOperation]

theorem pair_reachable (u v : Word) : ∃ q : ℕ, Reaches q u v := by
  let es := deleteAll u.length ++ writeWord v
  refine ⟨es.length, es, le_rfl, ?_⟩
  simp [es, applyScript_append, deleteAll_spec, writeWord_spec]

/-- Unrestricted DL distance, with a reachability proof rather than a default
for an empty set of possible lengths. -/
noncomputable def distance (u v : Word) : ℕ := by
  classical
  exact Nat.find (pair_reachable u v)

def ball (q : ℕ) (u : Word) : Set Word := {v | Reaches q u v}

def availableOperations (u : Word) : List Operation :=
  ((List.range (u.length + 1)).flatMap fun i =>
    (List.finRange 2).map fun a => Operation.insert i a) ++
  ((List.range u.length).map Operation.delete) ++
  ((List.range u.length).flatMap fun i =>
    ((List.finRange 2).filter fun a => u[i]? ≠ some a).map fun a => Operation.substitute i a) ++
  ((List.range (u.length - 1)).map Operation.transpose)

/-- Appendix C.6: output the root and all children through depth q; keep repetitions. -/
def enumerateBall : ℕ → Word → List Word
  | 0, u => [u]
  | q + 1, u => u :: (availableOperations u).flatMap fun e =>
      match applyOperation u e with
      | none => []
      | some v => enumerateBall q v

def ballListBound (ell q : ℕ) : ℕ := (q + 1) * (5 * (ell + q) + 2) ^ q

abbrev Channel := ℕ → Word → Set Word

def ContainsInput (E : Channel) : Prop :=
  ∀ (n : ℕ) (u : Word), u.length = n → u ∈ E n u

def Confusable (E : Channel) (n : ℕ) (u v : Word) : Prop :=
  ∃ y : Word, y ∈ E n u ∧ y ∈ E n v

def Corrects (E : Channel) (n : ℕ) (C : Set Word) : Prop :=
  (∀ u ∈ C, u.length = n) ∧
  ∀ u ∈ C, ∀ v ∈ C, Confusable E n u v → u = v

def dlChannel (t : ℕ) : Channel := fun _ u => ball t u

def Splittable (E : Channel) (m N : ℕ) (R : Word → Word → Prop) : Prop :=
  (∀ s : Word, s.length = N → R s s) ∧
  (∀ s s' : Word, s.length = N → s'.length = N → R s s' → R s' s) ∧
  ∀ x x' s s' : Word, x.length = m → x'.length = m →
    s.length = N → s'.length = N →
    Confusable E (m + N) (x ++ s) (x' ++ s') → R s s'

def payloadCompetitors (E : Channel) (m N : ℕ) (x : Word) : Set Word :=
  {x' | x'.length = m ∧ x' ≠ x ∧
    ∃ s : Word, s.length = N ∧ Confusable E (m + N) (x ++ s) (x' ++ s)}

def dlCompetitors (t m : ℕ) (x : Word) : Set Word :=
  {x' | x'.length = m ∧ x' ≠ x ∧ Reaches (2 * t) x x'}

end SeedRecyclingDL.Codes


