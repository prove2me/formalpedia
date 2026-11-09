-- Prove2me | Definitions.Def_EditMulticoloring_Code_Words
-- name    : EditMulticoloring_Code_Words
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T18:47:43.049963+00:00
-- url     : https://prove2.me/theorems/ec5fbbd5-541c-4aba-8583-f9598ddf8856
-- title:
--   Words, positioned scripts, edit balls and exact integer representations
-- statement:
--   Let $A=\{0,\ldots,q-1\}$ and let $A^*$ denote all finite words, including the empty word. A positioned insertion, deletion or changing-symbol substitution acts on the current word and costs one edit. The list of scripts of budget $s$ contains the empty script and every legal ordered script of at most $s$ operations, retaining different scripts that produce the same word. Its set of outputs is the enumerated ball.
--
--   $$r_s(m)=(s+1)(2q(m+s+1))^s.$$
--
--   The published unit-cost edit distance is reused. Fixed words are functions on a finite coordinate type; the conversion to lists preserves their order. One-based inclusive intervals are implemented by dropping $\ell_0-1$ symbols and taking $\ell_1-\ell_0+1$. Integer value and fixed-width base-$q$ representations retain leading zeros. Exact floor and ceiling logarithms are defined by integer logarithms and power comparisons. These interfaces are shared by every result in the mission.
-- source:
--   Huiling Xie, Zitan Chen, Explicit Edit Codes via Multicoloring, STOC 2027 submission #819 (October 2026), §2, Definition 2 and Eq. (2), printed pp. 4–5 (PDF pp. 5–6); §3.1, printed p. 10 (PDF p. 11); pinned repository artifact papers/stoc2027-819/source.pdf, SHA256 00172d5da76bf6bc886b8a1f87450befb76480107f54cb367988a065737eb376.

import Mathlib
import Definitions.Def_EditDistance

namespace EditMulticoloring.Code

abbrev Word (q : ℕ) := List (Fin q)
abbrev FixedWord (q n : ℕ) := Fin n → Fin q

def toWord {q n : ℕ} (x : FixedWord q n) : Word q := List.ofFn x

noncomputable def distance {q : ℕ} (x y : Word q) : ℕ :=
  OAI.EditDistortion.edit x y

def interval {q : ℕ} (x : Word q) (lo hi : ℕ) : Word q :=
  (x.drop (lo - 1)).take (hi - lo + 1)

def radiusBound (q s m : ℕ) : ℕ := (s + 1) * (2 * q * (m + s + 1)) ^ s

/-- Positions are zero based in the word just before the operation. -/
inductive PositionedEdit (q : ℕ) where
  | insert : ℕ → Fin q → PositionedEdit q
  | delete : ℕ → PositionedEdit q
  | replace : ℕ → Fin q → PositionedEdit q
  deriving DecidableEq

def applyEdit {q : ℕ} (x : Word q) : PositionedEdit q → Option (Word q)
  | .insert i a => if i ≤ x.length then some (x.take i ++ a :: x.drop i) else none
  | .delete i => if i < x.length then some (x.take i ++ x.drop (i + 1)) else none
  | .replace i a => if i < x.length ∧ x[i]? ≠ some a then
      some (x.take i ++ a :: x.drop (i + 1)) else none

def availableEdits {q : ℕ} (x : Word q) : List (PositionedEdit q) :=
  ((List.range (x.length + 1)).flatMap fun i =>
    (List.finRange q).map fun a => .insert i a) ++
  ((List.range x.length).map fun i => .delete i) ++
  ((List.range x.length).flatMap fun i =>
    ((List.finRange q).filter fun a => x[i]? ≠ some a).map fun a => .replace i a)

/-- Operational scripts, including positions and multiplicities of equal outputs. -/
def scripts {q : ℕ} : ℕ → Word q → List (List (PositionedEdit q) × Word q)
  | 0, x => [([], x)]
  | s + 1, x => ([], x) :: (availableEdits x).flatMap fun e =>
      match applyEdit x e with
      | none => []
      | some z => (scripts s z).map fun (es, y) => (e :: es, y)

/-- Finite enumerated ball; the theorem establishes equality with the metric ball. -/
def ball {q : ℕ} (s : ℕ) (x : Word q) : Finset (Word q) :=
  ((scripts s x).map Prod.snd).toFinset

def Corrects {q : ℕ} (t : ℕ) (C : Set (Word q)) : Prop :=
  ∀ x ∈ C, ∀ z ∈ C, x ≠ z → ∀ y : Word q,
    ¬ (distance x y ≤ t ∧ distance z y ≤ t)

/-- Lexicographic order, retaining leading zeros, including the single empty word. -/
def words (q : ℕ) : ℕ → List (Word q)
  | 0 => [[]]
  | n + 1 => (List.finRange q).flatMap fun a => (words q n).map (a :: ·)

def value {q : ℕ} (x : Word q) : ℕ := x.foldl (fun a b => q * a + b.val) 0

def repr (q w N : ℕ) : Word q :=
  (List.range w).filterMap fun i =>
    let a := (N / q ^ (w - 1 - i)) % q
    if h : a < q then some ⟨a, h⟩ else none

/-- Exact integer floor/ceiling logarithms; q ≥ 2 in every source application. -/
def floorLog (q N : ℕ) : ℕ := Nat.log q N

def ceilLog (q N : ℕ) : ℕ :=
  let a := floorLog q N
  if N ≤ q ^ a then a else a + 1

noncomputable def logBase (q : ℕ) (x : ℝ) : ℝ := Real.log x / Real.log q

end EditMulticoloring.Code


