-- Prove2me | Definitions.Def_OAIQ18Pg000
-- name    : OAIQ18Pg000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T15:54:21.801324+00:00
-- url     : https://prove2.me/theorems/63c5c6c8-464e-497c-94c6-1f6ce49a0b41
-- title:
--   Definitions bundle OAIQ18Pg000 of the split of OpenAI, An infinite finitely presented periodic group
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SourceBurnside.thm_main`, carved from OpenAI's openai/math development (OpenAI, *An infinite finitely presented periodic group*, OpenAI Math Release, September 23, 2026, result family 247, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 634 declarations of OpenAI's Lean: 303 definitions, 29 inductive types or structures, 8 instances and 294 theorems. The definitions and types are `OAI.SourceBurnside.AddressFormula.Exponents`, `OAI.SourceBurnside.AddressFormula.Expr`, `OAI.SourceBurnside.AddressFormula.certificate`, `OAI.SourceBurnside.AddressFormula.data`, `OAI.SourceBurnside.AddressFormula.evaluate`, `OAI.SourceBurnside.AddressFormula.readAt`, `OAI.SourceBurnside.AddressFormula.record`, `OAI.SourceBurnside.Addressable.Clause`, `OAI.SourceBurnside.Addressable.Clause.Holds`, `OAI.SourceBurnside.Addressable.Clause.compile`, `OAI.SourceBurnside.Addressable.DataAddress`, `OAI.SourceBurnside.Addressable.InputBit`, `OAI.SourceBurnside.Addressable.InputBit.eval`, `OAI.SourceBurnside.Addressable.InputBit.mapBool`, `OAI.SourceBurnside.Addressable.Layout`, `OAI.SourceBurnside.Addressable.Layout.BoundaryIndex`, `OAI.SourceBurnside.Addressable.Layout.CIndex`, `OAI.SourceBurnside.Addressable.Layout.ClauseIndex`, `OAI.SourceBurnside.Addressable.Layout.FiniteValid`, `OAI.SourceBurnside.Addressable.Layout.InitialIndex`, `OAI.SourceBurnside.Addressable.Layout.LocalIndex`, `OAI.SourceBurnside.Addressable.Layout.XIndex`, `OAI.SourceBurnside.Addressable.Layout.YIndex`, `OAI.SourceBurnside.Addressable.Layout.assemble`, `OAI.SourceBurnside.Addressable.Layout.boundary`, `OAI.SourceBurnside.Addressable.Layout.certEquiv`, `OAI.SourceBurnside.Addressable.Layout.certificate`, `OAI.SourceBurnside.Addressable.Layout.clause`, `OAI.SourceBurnside.Addressable.Layout.clauseAt`, `OAI.SourceBurnside.Addressable.Layout.clauseEquiv`, `OAI.SourceBurnside.Addressable.Layout.coordinates`, `OAI.SourceBurnside.Addressable.Layout.core`, `OAI.SourceBurnside.Addressable.Layout.currentTime`, `OAI.SourceBurnside.Addressable.Layout.directIndex`, `OAI.SourceBurnside.Addressable.Layout.family`, `OAI.SourceBurnside.Addressable.Layout.gates`, `OAI.SourceBurnside.Addressable.Layout.inputRow`, `OAI.SourceBurnside.Addressable.Layout.interior`, `OAI.SourceBurnside.Addressable.Layout.localClause`, `OAI.SourceBurnside.Addressable.Layout.localRead` and 292 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory/PeriodicGroups, in whole or in part: `PeriodicGroups_Algebra_DirectCancellation`, `PeriodicGroups_Algebra_WordAlgebra`, `PeriodicGroups_Formulas_Addressable`, `PeriodicGroups_Formulas_BooleanCircuits`, `PeriodicGroups_Formulas_ClauseEncoding`, `PeriodicGroups_Formulas_LocalPredicates`, `PeriodicGroups_Formulas_PredicateCompilation`, `PeriodicGroups_Formulas_Tableaux`, `PeriodicGroups_Machines_ArithmeticDevices`, `PeriodicGroups_Machines_BinaryRegisters`, `PeriodicGroups_Machines_Compilation`, `PeriodicGroups_Machines_RegisterLoops`, `PeriodicGroups_Machines_TimedExecution`, `PeriodicGroups_Machines_UniversalInput`, `PeriodicGroups_Rules_HeadTour`, `PeriodicGroups_Rules_LocalSyntax`, `PeriodicGroups_Rules_Palette`, `PeriodicGroups_Rules_Recognizer`, `PeriodicGroups_Rules_TableEncoding`, `PeriodicGroups_Rules_Transactions`, `PeriodicGroups_Rules_WordComponents`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ18Pg005`, `OAIQ18Pg006`, `OAIQ18Pg007`, `OAIQ18Pg008` and `OAIQ18Pg010`.
-- source:
--   OpenAI, An infinite finitely presented periodic group, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 247; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-infinite-finitely-presented-periodic-group-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory/PeriodicGroups at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ18_PG.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Formulas_Tableaux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.Tableau

abbrev Wire (n : ℕ) := Bool ⊕ Fin n

def Wire.eval {n : ℕ} (v : Fin n → Bool) : Wire n → Bool
  | .inl b => b
  | .inr i => v i

@[simp] lemma Wire.eval_map {n m : ℕ} (f : Fin n → Fin m)
    (w : Wire n) (v : Fin m → Bool) :
    Wire.eval v (Sum.map id f w) = w.eval (v ∘ f) := by
  cases w <;> rfl

def nand (a b : Bool) : Bool := !(a && b)

inductive Circuit (inputs : ℕ) : ℕ → Type
  | nil : Circuit inputs 0
  | snoc {g : ℕ} (c : Circuit inputs g) (a b : Wire (inputs + g)) :
      Circuit inputs (g + 1)

namespace Circuit

variable {I g : ℕ}

def evaluate : {g : ℕ} → Circuit I g → (Fin I → Bool) → Fin (I + g) → Bool
  | _, .nil, v => v
  | _, .snoc c a b, v => Fin.lastCases
      (nand (a.eval (c.evaluate v)) (b.eval (c.evaluate v))) (c.evaluate v)

def Satisfies : {g : ℕ} → Circuit I g → (Fin (I + g) → Bool) → Prop
  | _, .nil, _ => True
  | _, .snoc c a b, v =>
      c.Satisfies (v ∘ Fin.castSucc) ∧
      v (Fin.last _) = nand (a.eval (v ∘ Fin.castSucc)) (b.eval (v ∘ Fin.castSucc))

@[simp] theorem evaluate_input (c : Circuit I g) (v : Fin I → Bool) (i : Fin I) :
    c.evaluate v (Fin.castAdd g i) = v i := by
  induction c with
  | nil => rfl
  | snoc c a b ih =>
    change Fin.lastCases (motive := fun _ => Bool) (nand (a.eval (c.evaluate v)) (b.eval (c.evaluate v)))
      (c.evaluate v) (Fin.castSucc (Fin.castAdd _ i)) = _
    rw [Fin.lastCases_castSucc]
    exact ih

theorem evaluate_satisfies (c : Circuit I g) (v : Fin I → Bool) :
    c.Satisfies (c.evaluate v) := by
  induction c with
  | nil => trivial
  | snoc c a b ih =>
    simpa only [Satisfies, evaluate, Function.comp_def, Fin.lastCases_castSucc,
      Fin.lastCases_last, and_true] using ih

theorem assignment_unique (c : Circuit I g) (v : Fin (I + g) → Bool)
    (input : Fin I → Bool) (hv : c.Satisfies v)
    (hi : ∀ i, v (Fin.castAdd g i) = input i) : v = c.evaluate input := by
  induction c with
  | nil =>
    funext i
    exact hi i
  | snoc c a b ih =>
    have hp : v ∘ Fin.castSucc = c.evaluate input :=
      ih (v ∘ Fin.castSucc) hv.1 (fun i => hi i)
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [evaluate, Fin.lastCases_last, hp] using hv.2
    · simpa only [evaluate, Fin.lastCases_castSucc, Function.comp_def] using congrFun hp j

structure Clause (n : ℕ) where
  wires : Fin 3 → Wire n
  truth : (Fin 3 → Bool) → Bool

def Clause.Holds {n : ℕ} (c : Clause n) (v : Fin n → Bool) : Prop :=
  c.truth (fun i => (c.wires i).eval v) = true

def Clause.map {n m : ℕ} (f : Fin n → Fin m) (c : Clause n) : Clause m where
  wires i := (c.wires i).map id f
  truth := c.truth

@[simp] lemma Clause.map_holds {n m : ℕ} (f : Fin n → Fin m)
    (c : Clause n) (v : Fin m → Bool) :
    (c.map f).Holds v ↔ c.Holds (v ∘ f) := by
  simp only [Clause.Holds, Clause.map, Wire.eval_map]

def nandClauses {n : ℕ} (a b z : Wire n) : List (Clause n) :=
  [⟨![a, z, z], fun x => x 0 || x 1⟩,
   ⟨![b, z, z], fun x => x 0 || x 1⟩,
   ⟨![a, b, z], fun x => !x 0 || !x 1 || !x 2⟩]

lemma nandClauses_iff {n : ℕ} (a b z : Wire n) (v : Fin n → Bool) :
    (∀ c ∈ nandClauses a b z, c.Holds v) ↔ z.eval v = nand (a.eval v) (b.eval v) := by
  simp only [nandClauses, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true, Clause.Holds, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Fin.isValue]
  cases a.eval v <;> cases b.eval v <;> cases z.eval v <;> decide

def clauses : {g : ℕ} → (c : Circuit I g) → List (Clause (I + g))
  | _, .nil => []
  | _, .snoc c a b =>
      c.clauses.map (Clause.map Fin.castSucc) ++
      nandClauses (a.map id Fin.castSucc) (b.map id Fin.castSucc) (.inr (Fin.last _))

@[simp] theorem clauses_length (c : Circuit I g) : c.clauses.length = 3 * g := by
  induction c with
  | nil => rfl
  | snoc c a b ih => simp only [clauses, List.length_append, List.length_map,
      nandClauses, List.length_cons, List.length_nil, ih]; omega

theorem clauses_iff (c : Circuit I g) (v : Fin (I + g) → Bool) :
    (∀ C ∈ c.clauses, C.Holds v) ↔ c.Satisfies v := by
  induction c with
  | nil => simp [clauses, Satisfies]
  | snoc c a b ih =>
    rw [clauses, List.forall_mem_append, List.forall_mem_map, nandClauses_iff]
    simp only [Clause.map_holds, ih, Satisfies]
    cases a <;> cases b <;> rfl

end Circuit

namespace Rectangle

variable {β g : ℕ}

abbrev Bits (β : ℕ) := Fin β → Bool
abbrev Row (β : ℕ) := ℕ → Bits β

def neighborhood (row : Row β) (j : ℕ) : Fin (3 * β) → Bool := fun i =>
  let p : Fin 3 × Fin β := finProdFinEquiv.symm i
  row (j + p.1.val) p.2

variable (c : Circuit (3 * β) g) (output : Fin β → Wire (3 * β + g))

def localOutput (row : Row β) (j : ℕ) : Bits β := fun r =>
  (output r).eval (c.evaluate (neighborhood row j))

def step (W : ℕ) (blank : Bits β) (row : Row β) : Row β := fun j =>
  if 0 < j ∧ j + 1 < W then localOutput c output row (j - 1) else blank

def run (W : ℕ) (blank : Bits β) (initial : Row β) : ℕ → Row β
  | 0 => initial
  | t + 1 => step c output W blank (run W blank initial t)

def assignment (row : Row β) (j : ℕ) (gates : Fin g → Bool) :
    Fin (3 * β + g) → Bool := Fin.addCases (neighborhood row j) gates

lemma assignment_input (row : Row β) (j : ℕ) (gates : Fin g → Bool)
    (i : Fin (3 * β)) : assignment row j gates (Fin.castAdd g i) = neighborhood row j i := by
  simp only [assignment, Fin.addCases_left]

lemma assignment_evaluate (row : Row β) (j : ℕ) :
    assignment row j (fun v => c.evaluate (neighborhood row j) (Fin.natAdd (3 * β) v)) =
      c.evaluate (neighborhood row j) := by
  funext i
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  · simp only [assignment_input, Circuit.evaluate_input]
  · simp only [assignment, Fin.addCases_right]

def Valid (T W : ℕ) (blank : Bits β) (initial : Row β)
    (X : ℕ → Row β) (Y : ℕ → ℕ → Fin g → Bool) : Prop :=
  (∀ j < W, X 0 j = initial j) ∧
  (∀ t, t + 1 < T → ∀ j < W, (j = 0 ∨ j + 1 = W) → X (t + 1) j = blank) ∧
  (∀ t, t + 1 < T → ∀ j, j + 2 < W →
    c.Satisfies (assignment (X t) j (Y t j))) ∧
  (∀ t, t + 1 < T → ∀ j, j + 2 < W → ∀ r,
    X (t + 1) (j + 1) r = (output r).eval (assignment (X t) j (Y t j)))

lemma valid_transition {T W : ℕ} {blank : Bits β} {initial : Row β}
    {X : ℕ → Row β} {Y : ℕ → ℕ → Fin g → Bool}
    (hv : Valid c output T W blank initial X Y) (t : ℕ) (ht : t + 1 < T)
    (j : ℕ) (hj : j < W) : X (t + 1) j = step c output W blank (X t) j := by
  by_cases hi : 0 < j ∧ j + 1 < W
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    have hk : k + 2 < W := by omega
    have he := c.assignment_unique (assignment (X t) k (Y t k))
      (neighborhood (X t) k) (hv.2.2.1 t ht k hk) (assignment_input _ _ _)
    funext r
    simpa only [step, ite_eq_left hi, localOutput, Nat.succ_eq_add_one, Nat.add_sub_cancel, he] using
      hv.2.2.2 t ht k hk r
  · rw [step, ite_eq_right hi]
    exact hv.2.1 t ht j hj (by omega)

theorem valid_run {T W : ℕ} {blank : Bits β} {initial : Row β}
    {X : ℕ → Row β} {Y : ℕ → ℕ → Fin g → Bool}
    (hv : Valid c output T W blank initial X Y) (t : ℕ) (ht : t < T)
    (j : ℕ) (hj : j < W) : X t j = run c output W blank initial t j := by
  induction t generalizing j with
  | zero => exact hv.1 j hj
  | succ t ih =>
    rw [valid_transition c output hv t ht j hj, run]
    by_cases hi : 0 < j ∧ j + 1 < W
    · have hn : neighborhood (X t) (j - 1) =
          neighborhood (run c output W blank initial t) (j - 1) := by
        funext i
        dsimp only [neighborhood]
        apply congrFun (ih (by omega) _ (by
          have hh : (finProdFinEquiv.symm i : Fin 3 × Fin β).1.val < 3 :=
            (finProdFinEquiv.symm i : Fin 3 × Fin β).1.isLt
          omega))
      simp only [step, ite_eq_left hi]
      unfold localOutput
      rw [hn]
    · simp only [step, ite_eq_right hi]

theorem run_valid (T W : ℕ) (blank : Bits β) (initial : Row β) :
    Valid c output T W blank initial (run c output W blank initial)
      (fun t j v => c.evaluate (neighborhood (run c output W blank initial t) j)
        (Fin.natAdd (3 * β) v)) := by
  refine ⟨fun _ _ => rfl, ?_, ?_, ?_⟩
  · intro t ht j hj he
    rw [run, step, ite_eq_right (by omega)]
  · intro t ht j hj
    rw [assignment_evaluate]
    exact c.evaluate_satisfies _
  · intro t ht j hj r
    rw [assignment_evaluate]
    simp only [run, step, ite_eq_left (show 0 < j + 1 ∧ j + 1 + 1 < W by omega),
      Nat.add_sub_cancel, localOutput]

theorem accepting_tableau_iff (T W origin : ℕ) (hT : 0 < T) (hO : origin < W)
    (blank accept : Bits β) (initial : Row β) :
    (∃ X Y, Valid c output T W blank initial X Y ∧ X (T - 1) origin = accept) ↔
      run c output W blank initial (T - 1) origin = accept := by
  constructor
  · rintro ⟨X, Y, hv, ha⟩
    rw [← valid_run c output hv (T - 1) (by omega) origin hO]
    exact ha
  · intro ha
    exact ⟨_, _, run_valid c output T W blank initial, ha⟩

end Rectangle

namespace Layout

def certificateCount (β g T W : ℕ) : ℕ := β * W * T + g * (W - 2) * (T - 1)

def clauseCount (β g T W : ℕ) : ℕ :=
  2 * β * W + 2 * β * (T - 1) + (3 * g + 2 * β) * (W - 2) * (T - 1) + β

def xAddress (β W t j r : ℕ) : ℕ := β * (W * t + j) + r

def yAddress (β g T W t j v : ℕ) : ℕ :=
  β * W * T + g * ((W - 2) * t + j) + v

end Layout

end SourceBurnside.Tableau

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_LocalSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.LocalSyntax

inductive Marker
  | idle | left | boundary | full | right
  deriving DecidableEq

inductive Position (q : ℕ)
  | core (p : Fin q)
  | palette (color : Fin q)
  | stop
  deriving DecidableEq

structure Metadata (k : ℕ) where
  arity : Fin k
  zeroTask : Bool
  block : Fin (arity.val + 1)
  deriving DecidableEq

structure Skeleton (q k : ℕ) where
  pos : Position q
  marker : Marker
  metadata : Metadata k
  deriving DecidableEq

namespace Skeleton
variable {q k : ℕ}

def first (c : Skeleton q k) : Prop := c.metadata.block.val = 0 ∧
  ∃ p, c.pos = .core p ∧ p.val = 0

def last (c : Skeleton q k) : Prop :=
  c.metadata.block.val = c.metadata.arity.val ∧ c.pos = .stop

def Admissible (c : Skeleton q k) : Prop :=
  (c.marker = .right → ¬ c.first) ∧ (c.marker = .left → ¬ c.last)

def leftExternal (c : Skeleton q k) : Prop :=
  c.marker = .idle ∨ (c.marker ≠ .right ∧ c.first)

def rightExternal (c : Skeleton q k) : Prop :=
  c.marker = .idle ∨ c.marker = .boundary ∨ (c.marker ≠ .left ∧ c.last)

def acceptsLeft (c : Skeleton q k) (m : Marker) : Prop :=
  if c.marker = .right then m = .full ∨ m = .right else m = .left

def acceptsRight (c : Skeleton q k) (m : Marker) : Prop :=
  if c.marker = .left then m = .left ∨ m = .boundary ∨ m = .full else m = .right

def Structural (a b : Skeleton q k) : Prop :=
  match a.pos, b.pos with
  | .core p, .core r => p.val + 1 = r.val
  | .core p, .palette _ => p.val + 1 = q
  | .palette _, .palette _ => True
  | .palette _, .stop => True
  | .stop, .core r => r.val = 0
  | _, _ => False

def Internal (a b : Skeleton q k) : Prop :=
  a.metadata.arity = b.metadata.arity ∧ a.metadata.zeroTask = b.metadata.zeroTask ∧
  (if a.pos = .stop then a.metadata.block.val + 1 = b.metadata.block.val
     else a.metadata.block.val = b.metadata.block.val) ∧ ¬ b.first ∧ ¬ a.last

def Pair (a b : Skeleton q k) : Prop :=
  Structural a b ∧
    ((a.rightExternal ∧ b.leftExternal) ∨
      (¬ a.rightExternal ∧ ¬ b.leftExternal ∧
        a.acceptsRight b.marker ∧ b.acceptsLeft a.marker ∧ Internal a b))

def mark (c : Skeleton q k) (m : Marker) : Skeleton q k := { c with marker := m }

@[simp] lemma mark_first (c : Skeleton q k) (m : Marker) : (c.mark m).first ↔ c.first := Iff.rfl
@[simp] lemma mark_last (c : Skeleton q k) (m : Marker) : (c.mark m).last ↔ c.last := Iff.rfl
@[simp] lemma mark_pos (c : Skeleton q k) (m : Marker) : (c.mark m).pos = c.pos := rfl
@[simp] lemma mark_metadata (c : Skeleton q k) (m : Marker) :
    (c.mark m).metadata = c.metadata := rfl
@[simp] lemma mark_marker (c : Skeleton q k) (m : Marker) :
    (c.mark m).marker = m := rfl

end Skeleton

namespace Skeleton
variable {q k : ℕ}

def IsHead (c : Skeleton q k) : Prop := c.marker = .boundary ∨ c.marker = .full

end Skeleton
end SourceBurnside.LocalSyntax

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_Palette
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.Palette

inductive Check (C : Type u)
  | idle
  | passed (seek : C)
  | head (seek : C)
  deriving DecidableEq

structure Cell (C : Type u) (A : Type v) where
  color : C
  check : Check C
  aux : A
  deriving DecidableEq

variable {C : Type u} {A : Type v}

variable (head : A → Prop)

inductive Pair : Check C → Check C → Prop
  | idle : Pair .idle .idle
  | passed (x : C) : Pair (.passed x) (.passed x)
  | next (x : C) : Pair (.passed x) (.head x)
  | rest (x : C) : Pair (.head x) .idle

def LastOK : Check C → Prop
  | .idle => True
  | .head _ => True
  | .passed _ => False

def Safe (w : List (Cell C A)) : Prop :=
  ∀ c ∈ w, ∀ x, c.check = .passed x → c.color ≠ x

@[simp] lemma safe_nil : Safe ([] : List (Cell C A)) := by simp [Safe]
@[simp] lemma safe_append (v w : List (Cell C A)) : Safe (v ++ w) ↔ Safe v ∧ Safe w := by
  simp only [Safe, List.forall_mem_append]
@[simp] lemma safe_cons (a : Cell C A) (w : List (Cell C A)) :
    Safe (a :: w) ↔ (∀ x, a.check = .passed x → a.color ≠ x) ∧ Safe w := by
  simp [Safe]

end SourceBurnside.Palette

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_HeadTour
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.HeadTour
open scoped BigOperators

abbrev Registers := Fin 3 → ZMod 2

variable {N : ℕ}

structure Payload (N : ℕ) where
  nonempty : 0 < N
  delta : Fin N → Registers
  last_zero : delta ⟨N - 1, by omega⟩ = 0
  gate : Registers → Prop

namespace Payload
variable (P : Payload N)

def first : Fin N := ⟨0, P.nonempty⟩
def last : Fin N := ⟨N-1, by have := P.nonempty; omega⟩

def partialSum (k : ℕ) : Registers := ∑ p : Fin N, if p.val < k then P.delta p else 0

def total : Registers := ∑ p : Fin N, P.delta p

@[simp] lemma partialSum_zero : P.partialSum 0 = 0 := by simp [partialSum]
@[simp] lemma partialSum_N : P.partialSum N = P.total := by simp [partialSum,total]

end Payload

structure Plan (m N : ℕ) where
  nonempty : 0 < m
  payload : Fin m → Payload N
  zeroTask : Bool

namespace Plan
variable {m : ℕ} (Q : Plan m N)

def Holds (j : Fin m) : Prop := (Q.payload j).gate (Q.payload j).total

end Plan
end SourceBurnside.HeadTour

namespace SourceBurnside.FiniteTable
open LocalSyntax
open LocalSyntax.Skeleton

abbrev Meta := Metadata 10
abbrev Reg := Fin 3 → ZMod 2

instance instFintypeMarker : Fintype Marker := Fintype.ofList
  [.idle,.left,.boundary,.full,.right] (by intro x; cases x <;> simp)
deriving instance Fintype for Position
deriving instance Fintype for Metadata
deriving instance Fintype for Skeleton
deriving instance Fintype for Palette.Check

inductive Phase
  | acquisition | readLeft | readRight | beforeGate | afterGate
  | undoLeft | undoRight | finish | success
  deriving DecidableEq

instance instFintypePhase : Fintype Phase := Fintype.ofList
  [.acquisition,.readLeft,.readRight,.beforeGate,.afterGate,.undoLeft,.undoRight,.finish,.success]
  (by intro x; cases x <;> simp)

structure Head (q : ℕ) where
  side : Bool
  clause : Fin q
  phase : Phase
  reg : Reg
  deriving DecidableEq, Fintype

structure Cell (q : ℕ) where
  skeleton : Skeleton q 10
  checker : Palette.Check (Fin q)
  data : Bool → ZMod 2
  certificate : ZMod 2
  head : Head q
  deriving DecidableEq, Fintype

structure Task where
  arity : Fin 10
  zeroTask : Bool
  deriving DecidableEq, Fintype

def Meta.task (m : Meta) : Task := ⟨m.arity,m.zeroTask⟩

inductive Address (q : ℕ)
  | data (side : Bool) (block : Fin 10) (position : Fin q)
  | certificate (position : Fin q)
  deriving DecidableEq, Fintype

structure Clause (q : ℕ) where
  address : Fin 3 → Address q
  truth : Reg → Bool

structure Schedule (q : ℕ) where
  count : Task → Fin (q+1)
  positive : ∀ t, 0 < (count t).val
  clause : Task → Fin q → Clause q

variable {q : ℕ} [NeZero q]

def defaultMeta : Meta := ⟨0,false,0⟩
def defaultHead : Head q := ⟨false,0,.acquisition,0⟩

namespace Cell

def pos (c : Cell q) : Position q := c.skeleton.pos
def marker (c : Cell q) : Marker := c.skeleton.marker
def metadata (c : Cell q) : Meta := c.skeleton.metadata

def wing (c : Cell q) (m : Marker) : Cell q :=
  { c with skeleton := c.skeleton.mark m, head := defaultHead }

def boundary (c : Cell q) (side : Bool) : Cell q :=
  { c with skeleton := c.skeleton.mark .boundary, head := {defaultHead with side := side} }

def full (c : Cell q) (side : Bool) (clause : Fin q) (phase : Phase) (reg : Reg) : Cell q :=
  { c with skeleton := c.skeleton.mark .full, head := ⟨side,clause,phase,reg⟩ }

def idle (c : Cell q) (side : Bool) : Cell q :=
  { c with
    skeleton := ⟨c.pos, .idle, defaultMeta⟩
    data := fun s => if s then 0 else c.data side
    certificate := 0
    head := defaultHead }

def setChecker (c : Cell q) (ch : Palette.Check (Fin q)) : Cell q :=
  { c with checker := ch }

def setColor (c : Cell q) (a : Fin q) : Cell q :=
  { c with skeleton := {c.skeleton with pos := .palette a} }

def isPalette (c : Cell q) : Prop := ∃ a, c.pos = .palette a
def isCore (c : Cell q) : Prop := ∃ p, c.pos = .core p

def endpoint (p : Phase) : Prop := p = .acquisition ∨ p = .beforeGate ∨
  p = .afterGate ∨ p = .finish ∨ p = .success

def Format (S : Schedule q) (dataSize : ℕ) (c : Cell q) : Prop :=
  c.skeleton.Admissible ∧
  (¬ c.isPalette → c.checker = .idle) ∧
  (∀ p, c.pos = .core p → dataSize ≤ p.val → c.data = 0) ∧
  (¬ c.isCore → c.data = 0 ∧ c.certificate = 0) ∧
  (c.marker = .idle → c.metadata = defaultMeta ∧ c.head = defaultHead ∧
    c.data true = 0 ∧ c.certificate = 0) ∧
  (c.marker = .left ∨ c.marker = .right → c.head = defaultHead) ∧
  (c.marker = .boundary → c.head.clause = 0 ∧ c.head.phase = .acquisition ∧ c.head.reg = 0) ∧
  (IsHead c.skeleton → (c.metadata.zeroTask = true → c.head.side = false)) ∧
  (c.marker = .full →
    (c.head.phase = .success → c.head.clause = 0) ∧
    (c.head.phase ≠ .success → c.head.clause.val < (S.count c.metadata.task).val) ∧
    (endpoint c.head.phase → c.skeleton.last))

def read (a : Address q) (c : Cell q) : ZMod 2 :=
  match a, c.pos with
  | .data s b p, .core r =>
      if c.metadata.block.val = b.val ∧ r = p then c.data s else 0
  | .certificate p, .core r =>
      if c.metadata.block.val = 0 ∧ r=p then c.certificate else 0
  | _, _ => 0

def delta (C : Clause q) (c : Cell q) : Reg := fun i => c.read (C.address i)

omit [NeZero q] in
lemma read_stop (a : Address q) (c : Cell q) (h : c.pos = .stop) : c.read a = 0 := by
  cases a <;> simp [read,h]

omit [NeZero q] in
lemma delta_stop (C : Clause q) (c : Cell q) (h : c.pos = .stop) : c.delta C = 0 := by
  funext i; exact read_stop (C.address i) c h

def HeadFree (c : Cell q) : Prop :=
  ¬ IsHead c.skeleton ∧ ∀ x, c.checker ≠ .head x

end Cell

def CheckerPair (a b : Cell q) : Prop :=
  (a.isPalette ∧ b.isPalette → Palette.Pair a.checker b.checker) ∧
  (a.isPalette ∧ b.pos = .stop → Palette.LastOK a.checker)

def Pair (a b : Cell q) : Prop := LocalSyntax.Skeleton.Pair a.skeleton b.skeleton ∧ CheckerPair a b

inductive Binary (S : Schedule q) : Cell q → Cell q → Cell q → Cell q → Prop
  | acquire (a b : Cell q) (s : Bool)
      (hp : LocalSyntax.Skeleton.Pair (a.skeleton.mark .left) (b.skeleton.mark .boundary)) :
      Binary S (a.boundary s) (b.idle s) (a.wing .left) (b.boundary s)
  | read_left (a b : Cell q) (s : Bool) (j : Fin q) (r : Reg)
      (hp : LocalSyntax.Skeleton.Pair (a.skeleton.mark .full) (b.skeleton.mark .right)) :
      Binary S (a.wing .left) (b.full s j .readLeft r)
        (a.full s j .readLeft (r+a.delta (S.clause a.metadata.task j))) (b.wing .right)
  | read_right (a b : Cell q) (s : Bool) (j : Fin q) (r : Reg)
      (hp : LocalSyntax.Skeleton.Pair (a.skeleton.mark .full) (b.skeleton.mark .right)) :
      Binary S (a.full s j .readRight r) (b.wing .right)
        (a.wing .left) (b.full s j .readRight r)
  | undo_left (a b : Cell q) (s : Bool) (j : Fin q) (r : Reg)
      (hp : LocalSyntax.Skeleton.Pair (a.skeleton.mark .full) (b.skeleton.mark .right)) :
      Binary S (a.wing .left) (b.full s j .undoLeft r)
        (a.full s j .undoLeft r) (b.wing .right)
  | undo_right (a b : Cell q) (s : Bool) (j : Fin q) (r : Reg)
      (hp : LocalSyntax.Skeleton.Pair (a.skeleton.mark .full) (b.skeleton.mark .right)) :
      Binary S (a.full s j .undoRight r) (b.wing .right)
        (a.wing .left) (b.full s j .undoRight (r+a.delta (S.clause a.metadata.task j)))
  | checker_create (a b : Cell q) (p : Fin q) (x : Fin q)
      (ha : a.pos = .core p) (hp : p.val+1=q) (hb : b.isPalette) :
      Binary S a (b.setChecker .idle) a (b.setChecker (.head x))
  | checker_advance (a b : Cell q) (v x : Fin q)
      (ha : a.pos = .palette v) (hb : b.isPalette) (hv : v ≠ x) :
      Binary S (a.setChecker (.head x)) (b.setChecker .idle)
        (a.setChecker (.passed x)) (b.setChecker (.head x))
  | swap (a b : Cell q) (x y : Fin q) (ha : a.pos = .palette x) (hb : b.pos = .palette y)
      (he : a.setColor y = b) (hf : a.HeadFree) (hf' : b.HeadFree) :
      Binary S a b b a

def SemanticZero (S : Schedule q) (c : Cell q) : Prop :=
  c.marker = .full ∧
    (((c.head.phase = .acquisition ∨ c.head.phase = .finish ∨ c.head.phase = .success) ∧
      c.head.reg ≠ 0) ∨
     (c.head.phase = .afterGate ∧ (S.clause c.metadata.task c.head.clause).truth c.head.reg = false) ∨
     (c.head.phase = .success ∧ c.metadata.zeroTask = true))

def UnaryZero (S : Schedule q) (dataSize : ℕ) (c : Cell q) : Prop :=
  ¬ c.Format S dataSize ∨ SemanticZero S c ∨
    ∃ x, c.pos = .palette x ∧ c.checker = .passed x

def BinaryZero (a b : Cell q) : Prop :=
  ¬ Pair a b ∨ (∃ x, a.pos = .palette x ∧ b.pos = .palette x) ∨
    ∃ x y, a.pos = .palette x ∧ a.checker = .head y ∧ b.pos = .stop ∧ x ≠ y

end SourceBurnside.FiniteTable

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_TableEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.Palette
variable {C : Type*}
@[simp] lemma pair_from_idle (c : Check C) : Pair .idle c ↔ c=.idle := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .idle
@[simp] lemma pair_from_head (x : C) (c : Check C) : Pair (.head x) c ↔ c=.idle := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .rest x
@[simp] lemma pair_to_head (x : C) (c : Check C) : Pair c (.head x) ↔ c=.passed x := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .next x
@[simp] lemma pair_to_passed (x : C) (c : Check C) : Pair c (.passed x) ↔ c=.passed x := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .passed x
end SourceBurnside.Palette

namespace SourceBurnside.FiniteTable.Codec
open LocalSyntax

abbrev Raw (h : ℕ) := Fin (10000*h) → Bool

lemma reserve_lt {h : ℕ} (hh : 0 < h) : 64*h+512 ≤ 10000*h := by omega

def intPosition {h : ℕ} (_hh : 0 < h) (s : Fin 32) (i : Fin (2*h)) : Fin (10000*h) :=
  ⟨s.val*(2*h)+i.val,by
    have hs : s.val≤31 := by omega
    have hm := Nat.mul_le_mul_right (2*h) hs
    have := i.isLt
    omega⟩
def flagPosition {h : ℕ} (hh : 0 < h) (i : Fin 512) : Fin (10000*h) :=
  ⟨64*h+i.val,by have := reserve_lt hh; have := i.isLt; omega⟩

def write {h : ℕ} (ints : Fin 32 → ℕ) (flags : Fin 512 → Bool) : Raw h := fun i =>
  if hi : i.val < 64*h then
    (ints ⟨i.val/(2*h),by
      have hi' : i.val < 32*(2*h) := by omega
      exact (Nat.div_lt_iff_lt_mul (by omega)).mpr hi'⟩).testBit (i.val%(2*h))
  else if hf : i.val < 64*h+512 then flags ⟨i.val-64*h,by omega⟩ else false

def readInt {h : ℕ} (hh : 0 < h) (w : Raw h) (s : Fin 32) : ℕ :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => w (intPosition hh s i)))).toNat

def readFlag {h : ℕ} (hh : 0 < h) (w : Raw h) (i : Fin 512) : Bool := w (flagPosition hh i)

lemma write_int {h : ℕ} (hh : 0 < h) (ints : Fin 32 → ℕ) (flags : Fin 512 → Bool)
    (s : Fin 32) (i : Fin (2*h)) :
    write (h:=h) ints flags (intPosition hh s i) = (ints s).testBit i.val := by
  have hi : s.val*(2*h)+i.val < 64*h := by
    have hs : s.val≤31 := by omega
    have hm := Nat.mul_le_mul_right (2*h) hs
    have := i.isLt
    omega
  have hd : (s.val*(2*h)+i.val)/(2*h)=s.val := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ (by omega)]
    simp [Nat.div_eq_of_lt i.isLt]
  have hm : (s.val*(2*h)+i.val)%(2*h)=i.val := by
    simp [Nat.add_mod,Nat.mod_eq_of_lt i.isLt]
  simp [write,intPosition,hi,hd,hm]

lemma readFlag_write {h : ℕ} (hh : 0 < h) (ints : Fin 32 → ℕ) (flags : Fin 512 → Bool)
    (i : Fin 512) : readFlag hh (write ints flags) i=flags i := by
  have hi := i.isLt
  simp [readFlag,write,flagPosition,show ¬64*h+i.val < 64*h by omega,
    show 64*h+i.val < 64*h+512 by omega]

lemma readInt_write {h : ℕ} (hh : 0 < h) (ints : Fin 32 → ℕ) (flags : Fin 512 → Bool)
    (s : Fin 32) (hs : ints s < 2^(2*h)) : readInt hh (write ints flags) s=ints s := by
  let bs := List.ofFn (fun i : Fin (2*h) => (ints s).testBit i.val)
  have he : (List.ofFn fun i => write ints flags (intPosition hh s i))=bs := by
    apply congrArg List.ofFn
    funext i
    exact write_int hh ints flags s i
  have hv : BitVec.ofBoolListLE bs = BitVec.ofNat bs.length (ints s) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hi' : i < 2*h := by simpa [bs] using hi
    rw [BitVec.getLsbD_ofBoolListLE,BitVec.getLsbD_ofNat]
    simp [bs,hi']
  unfold readInt
  rw [he,hv]
  simp [bs,Nat.mod_eq_of_lt hs]

def positionTag {q : ℕ} : Position q → ℕ
  | .core _ => 0 | .palette _ => 1 | .stop => 2
def positionIndex {q : ℕ} : Position q → ℕ
  | .core p => p.val | .palette a => a.val | .stop => 0
def markerTag : Marker → ℕ
  | .idle => 0 | .left => 1 | .boundary => 2 | .full => 3 | .right => 4
def checkerTag {q : ℕ} : Palette.Check (Fin q) → ℕ
  | .idle => 0 | .passed _ => 1 | .head _ => 2
def checkerIndex {q : ℕ} : Palette.Check (Fin q) → ℕ
  | .idle => 0 | .passed x => x.val | .head x => x.val
def phaseTag : Phase → ℕ
  | .acquisition => 0 | .readLeft => 1 | .readRight => 2 | .beforeGate => 3
  | .afterGate => 4 | .undoLeft => 5 | .undoRight => 6 | .finish => 7 | .success => 8

def bit (x : ZMod 2) : Bool := decide (x=1)
def unbit (b : Bool) : ZMod 2 := if b then 1 else 0
@[simp] lemma unbit_bit (x : ZMod 2) : unbit (bit x)=x := by
  have hx : x=0 ∨ x=1 := by
    fin_cases x
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hx with rfl | rfl <;> norm_num [unbit,SourceBurnside.FiniteTable.Codec.bit]
@[simp] lemma bit_unbit (b : Bool) : bit (unbit b)=b := by cases b <;> decide

def integers {q : ℕ} (c : Cell q) (s : Fin 32) : ℕ := match s.val with
  | 0 => positionTag c.pos
  | 1 => positionIndex c.pos
  | 2 => markerTag c.marker
  | 3 => c.metadata.arity.val
  | 4 => c.metadata.block.val
  | 5 => checkerTag c.checker
  | 6 => checkerIndex c.checker
  | 7 => c.head.clause.val
  | 8 => phaseTag c.head.phase
  | _ => 0

def flags {q : ℕ} (c : Cell q) (i : Fin 512) : Bool := match i.val with
  | 0 => c.metadata.zeroTask
  | 1 => c.head.side
  | 2 => bit (c.data false)
  | 3 => bit (c.data true)
  | 4 => bit c.certificate
  | 5 => bit (c.head.reg 0)
  | 6 => bit (c.head.reg 1)
  | 7 => bit (c.head.reg 2)
  | _ => false

def encode {h : ℕ} (c : Cell (2^h)) : Raw h := write (integers c) (flags c)

def getFin (n i : ℕ) : Option (Fin n) := if hi : i < n then some ⟨i,hi⟩ else none
@[simp] lemma getFin_val {n : ℕ} (i : Fin n) : getFin n i.val=some i := by simp [getFin,i.isLt]

def getPosition (q t i : ℕ) : Option (Position q) := match t with
  | 0 => .map Position.core (getFin q i)
  | 1 => .map Position.palette (getFin q i)
  | 2 => if i=0 then some .stop else none
  | _ => none

def getMarker : ℕ → Option Marker
  | 0 => some .idle | 1 => some .left | 2 => some .boundary
  | 3 => some .full | 4 => some .right | _ => none

def getChecker (q t i : ℕ) : Option (Palette.Check (Fin q)) := match t with
  | 0 => if i=0 then some .idle else none
  | 1 => .map Palette.Check.passed (getFin q i)
  | 2 => .map Palette.Check.head (getFin q i)
  | _ => none

def getPhase : ℕ → Option Phase
  | 0 => some .acquisition | 1 => some .readLeft | 2 => some .readRight
  | 3 => some .beforeGate | 4 => some .afterGate | 5 => some .undoLeft
  | 6 => some .undoRight | 7 => some .finish | 8 => some .success | _ => none

@[simp] lemma getPosition_encode {q : ℕ} (p : Position q) :
    getPosition q (positionTag p) (positionIndex p)=some p := by
  cases p <;> simp [getPosition,positionTag,positionIndex]
@[simp] lemma getMarker_encode (m : Marker) : getMarker (markerTag m)=some m := by cases m <;> rfl
@[simp] lemma getChecker_encode {q : ℕ} (c : Palette.Check (Fin q)) :
    getChecker q (checkerTag c) (checkerIndex c)=some c := by
  cases c <;> simp [getChecker,checkerTag,checkerIndex]
@[simp] lemma getPhase_encode (p : Phase) : getPhase (phaseTag p)=some p := by cases p <;> rfl

def parse {h : ℕ} (hh : 0 < h) (w : Raw h) : Option (Cell (2^h)) := do
  let ints := readInt hh w
  let fl := readFlag hh w
  let pos ← getPosition (2^h) (ints 0) (ints 1)
  let marker ← getMarker (ints 2)
  let arity ← getFin 10 (ints 3)
  let block ← getFin (arity.val+1) (ints 4)
  let checker ← getChecker (2^h) (ints 5) (ints 6)
  let clause ← getFin (2^h) (ints 7)
  let phase ← getPhase (ints 8)
  return ⟨⟨pos,marker,⟨arity,fl 0,block⟩⟩,checker,
    (fun s => unbit (if s then fl 3 else fl 2)),unbit (fl 4),
    ⟨fl 1,clause,phase,![unbit (fl 5),unbit (fl 6),unbit (fl 7)]⟩⟩

def decode {h : ℕ} (hh : 0 < h) (w : Raw h) : Option (Cell (2^h)) := do
  let c ← parse hh w
  if w=encode c then some c else none

lemma positionTag_lt {q : ℕ} (p : Position q) : positionTag p < 3 := by cases p <;> simp [positionTag]
lemma positionIndex_lt {q : ℕ} (hq : 0 < q) (p : Position q) : positionIndex p < q := by
  cases p with
  | core p => exact p.isLt
  | palette a => exact a.isLt
  | stop => exact hq
lemma markerTag_lt (m : Marker) : markerTag m < 5 := by cases m <;> decide
lemma checkerTag_lt {q : ℕ} (c : Palette.Check (Fin q)) : checkerTag c < 3 := by cases c <;> simp [checkerTag]
lemma checkerIndex_lt {q : ℕ} (hq : 0 < q) (c : Palette.Check (Fin q)) : checkerIndex c < q := by
  cases c with
  | idle => exact hq
  | passed x => exact x.isLt
  | head x => exact x.isLt
lemma phaseTag_lt (p : Phase) : phaseTag p < 9 := by cases p <;> decide

lemma integers_lt {q : ℕ} (hq : 10≤q) (c : Cell q) (s : Fin 32) : integers c s < q := by
  unfold integers
  split
  · exact (positionTag_lt _).trans_le (by omega)
  · exact positionIndex_lt (by omega) _
  · exact (markerTag_lt _).trans_le (by omega)
  · exact c.metadata.arity.isLt.trans_le hq
  · have ha := c.metadata.arity.isLt
    have hb := c.metadata.block.isLt
    omega
  · exact (checkerTag_lt _).trans_le (by omega)
  · exact checkerIndex_lt (by omega) _
  · exact c.head.clause.isLt
  · exact (phaseTag_lt _).trans_le (by omega)
  · omega

lemma readInt_encode {h : ℕ} (hh : 4≤h) (c : Cell (2^h)) (s : Fin 32) :
    readInt (by omega) (encode c) s=integers c s := by
  apply readInt_write
  have hq : 10≤2^h := by
    have ht := Nat.pow_le_pow_right (show 0 < 2 by omega) hh
    norm_num at ht
    omega
  have hm := Nat.pow_le_pow_right (show 0 < 2 by omega) (show h≤2*h by omega)
  exact (integers_lt hq c s).trans_le hm

lemma readFlag_encode {h : ℕ} (hh : 0 < h) (c : Cell (2^h)) (s : Fin 512) :
    readFlag hh (encode c) s=flags c s := readFlag_write hh _ _ _

lemma parse_encode {h : ℕ} (hh : 4≤h) (c : Cell (2^h)) : parse (by omega) (encode c)=some c := by
  have hi : readInt (by omega) (encode c)=integers c := funext (readInt_encode hh c)
  have hf : readFlag (by omega) (encode c)=flags c := funext (readFlag_encode (by omega) c)
  have hd : (fun s => unbit (if s then bit (c.data true) else bit (c.data false)))=c.data := by
    funext s; cases s <;> simp
  have hr : ![c.head.reg 0,c.head.reg 1,c.head.reg 2]=c.head.reg := by
    funext i; fin_cases i <;> simp
  simp [parse,hi,hf,integers,flags,hd,hr,Cell.pos,Cell.marker,Cell.metadata]

lemma decode_encode {h : ℕ} (hh : 4≤h) (c : Cell (2^h)) : decode (by omega) (encode c)=some c := by
  simp [decode,parse_encode hh]

lemma encode_injective {h : ℕ} (hh : 4≤h) : Function.Injective (encode (h:=h)) := by
  intro c d he
  have hc := decode_encode hh c
  have hd := decode_encode hh d
  rw [he,hd] at hc
  exact Option.some.inj hc.symm

end SourceBurnside.FiniteTable.Codec

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_Transactions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q : ℕ} [NeZero q] {S : Schedule q} {d : ℕ}

namespace Cell
@[simp] lemma read_wing (a : Address q) (c : Cell q) (m : Marker) : (c.wing m).read a = c.read a := rfl
@[simp] lemma read_boundary (a : Address q) (c : Cell q) (s : Bool) : (c.boundary s).read a = c.read a := rfl
omit [NeZero q] in
@[simp] lemma read_full (a : Address q) (c : Cell q) (s : Bool) (j : Fin q) (p : Phase) (r : Reg) :
    (c.full s j p r).read a = c.read a := rfl
omit [NeZero q] in
@[simp] lemma read_setChecker (a : Address q) (c : Cell q) (ch : Palette.Check (Fin q)) :
    (c.setChecker ch).read a = c.read a := rfl
end Cell

def Cell.PayloadFormat (d : ℕ) (c : Cell q) : Prop :=
  (¬ c.isPalette → c.checker = .idle) ∧
  (∀ p, c.pos = .core p → d ≤ p.val → c.data = 0) ∧
  (¬ c.isCore → c.data = 0 ∧ c.certificate = 0)

structure Region (q d : ℕ) where
  size : ℕ
  positive : 0 < size
  task : Task
  cell : Fin size → Cell q
  task_eq : ∀ i, (cell i).metadata.task = task
  first_iff : ∀ i, (cell i).skeleton.first ↔ i.val = 0
  last_iff : ∀ i, (cell i).skeleton.last ↔ i.val + 1 = size
  adjacent : ∀ i j, i.val + 1 = j.val →
    Skeleton.Structural (cell i).skeleton (cell j).skeleton ∧
      Skeleton.Internal (cell i).skeleton (cell j).skeleton
  payload_format : ∀ i, (cell i).PayloadFormat d

namespace Region
variable (R : Region q d) (S : Schedule q)
def first : Fin R.size := ⟨0,R.positive⟩
def last : Fin R.size := ⟨R.size-1,by have := R.positive; omega⟩

omit [NeZero q] in
lemma first_first : (R.cell R.first).skeleton.first := (R.first_iff _).mpr rfl
omit [NeZero q] in
lemma last_last : (R.cell R.last).skeleton.last := by
  apply (R.last_iff _).mpr
  have := R.positive
  dsimp [last]; omega

def clauseIndex (j : Fin (S.count R.task).val) : Fin q :=
  ⟨j.val,lt_of_lt_of_le j.isLt (Nat.le_of_lt_succ (S.count R.task).isLt)⟩

def plan : HeadTour.Plan (S.count R.task).val R.size where
  nonempty := S.positive R.task
  zeroTask := R.task.zeroTask
  payload j :=
    { nonempty := R.positive
      delta := fun i => (R.cell i).delta (S.clause R.task (R.clauseIndex S j))
      gate := fun r => (S.clause R.task (R.clauseIndex S j)).truth r = true
      last_zero := Cell.delta_stop _ _ R.last_last.2 }

end Region

namespace Region
variable (R : Region q d) (S : Schedule q)

omit [NeZero q] in
@[simp] lemma payload_first (j : Fin (S.count R.task).val) :
    ((R.plan S).payload j).first=R.first := rfl
omit [NeZero q] in
@[simp] lemma payload_last (j : Fin (S.count R.task).val) :
    ((R.plan S).payload j).last=R.last := rfl

end Region

end SourceBurnside.FiniteTable

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_WordComponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q N : ℕ} [NeZero q]

inductive Shape (q : ℕ)
  | core (p : Fin q) | palette | stop
  deriving DecidableEq

def Cell.shape (c : Cell q) : Shape q := match c.pos with
  | .core p => .core p | .palette _ => .palette | .stop => .stop

namespace Cell

def positionRank (c : Cell q) : ℕ := match c.pos with
  | .core p => p.val | .palette _ => q | .stop => q+1

def progress (c : Cell q) : ℕ := c.metadata.block.val*(q+2)+c.positionRank

omit [NeZero q] in
lemma rank_lt (c : Cell q) : c.positionRank < q+2 := by
  cases hp : c.pos <;> simp only [positionRank,hp]
  · rename_i p; have := p.isLt; omega
  · omega
  · omega

omit [NeZero q] in
lemma progress_mod (c : Cell q) : c.progress % (q+2)=c.positionRank := by
  simp [progress,Nat.add_mod,Nat.mod_eq_of_lt c.rank_lt]

omit [NeZero q] in
lemma progress_div (c : Cell q) : c.progress / (q+2)=c.metadata.block.val := by
  rw [progress,Nat.add_comm,Nat.add_mul_div_right _ _ (by omega)]
  simp [Nat.div_eq_of_lt c.rank_lt]

lemma progress_step {a b : Cell q} (ha : Skeleton.Structural a.skeleton b.skeleton)
    (hb : Skeleton.Internal a.skeleton b.skeleton) :
    a.progress ≤ b.progress ∧ b.progress ≤ a.progress+1 ∧
      (a.progress=b.progress → a.isPalette ∧ b.isPalette) := by
  rcases hb with ⟨_,_,hb,_,_⟩
  cases hp : a.skeleton.pos <;> cases hq : b.skeleton.pos <;>
    simp_all [Skeleton.Structural,positionRank,progress,pos,metadata,isPalette,Nat.mul_add] <;>
    try omega
  all_goals
    have hh := congrArg (fun n => n*q) hb
    simp only [Nat.add_mul,Nat.one_mul] at hh
    omega

end Cell

namespace Region
variable {d : ℕ} (R : Region q d)

lemma progress_step (a b : Fin R.size) (hab : a.val+1=b.val) :
    (R.cell a).progress ≤ (R.cell b).progress ∧
      (R.cell b).progress ≤ (R.cell a).progress+1 ∧
      ((R.cell a).progress=(R.cell b).progress → (R.cell a).isPalette ∧ (R.cell b).isPalette) := by
  exact Cell.progress_step (R.adjacent a b hab).1 (R.adjacent a b hab).2

lemma progress_mono : Monotone (fun i => (R.cell i).progress) := by
  intro i j hij
  generalize hdiff : j.val-i.val=n
  induction n generalizing j with
  | zero =>
    have he : i=j := Fin.ext (by omega)
    simp [he]
  | succ n ih =>
    let p : Fin R.size := ⟨j.val-1,by have := j.isLt; omega⟩
    have hp : p.val+1=j.val := by dsimp [p]; omega
    have hip : i≤p := by change i.val≤j.val-1; omega
    have hn : p.val-i.val=n := by dsimp [p]; omega
    exact (ih (j:=p) hip hn).trans (R.progress_step p j hp).1

omit [NeZero q] in
lemma first_progress : (R.cell R.first).progress=0 := by
  obtain ⟨hb,p,hp,hz⟩ := R.first_first
  simp [Cell.progress,Cell.positionRank,Cell.metadata,Cell.pos,hb,hp,hz]

omit [NeZero q] in
lemma last_progress : (R.cell R.last).progress=(R.task.arity.val+1)*(q+2)-1 := by
  obtain ⟨hb,hp⟩ := R.last_last
  have ht := congrArg Task.arity (R.task_eq R.last)
  change (R.cell R.last).skeleton.metadata.arity=R.task.arity at ht
  simp [Cell.progress,Cell.positionRank,Cell.metadata,Cell.pos,hp,hb,ht,Nat.add_mul]

lemma progress_surjective (r : ℕ) (hr : r≤(R.cell R.last).progress) :
    ∃ i, (R.cell i).progress=r := by
  classical
  let s := Finset.univ.filter (fun i => r≤(R.cell i).progress)
  have hs : s.Nonempty := ⟨R.last,by simp [s,hr]⟩
  let i := s.min' hs
  have hi : r≤(R.cell i).progress := (Finset.mem_filter.mp (Finset.min'_mem s hs)).2
  refine ⟨i,?_⟩
  by_cases h0 : i.val=0
  · have he : i=R.first := Fin.ext h0
    have hr0 : r=0 := by simpa [he,R.first_progress] using hi
    simp [he,R.first_progress,hr0]
  · let j : Fin R.size := ⟨i.val-1,by have := i.isLt; omega⟩
    have hj : j.val+1=i.val := by dsimp [j]; omega
    have hn : ¬r≤(R.cell j).progress := by
      intro hh
      have hm : j∈s := by simp [s,hh]
      have hle : i≤j := Finset.min'_le s _ hm
      dsimp [j] at hle
      omega
    have hu := (R.progress_step j i hj).2.1
    omega

lemma core_unique (i j : Fin R.size) (hi : (R.cell i).isCore)
    (hh : (R.cell i).progress=(R.cell j).progress) : i=j := by
  have forward (a b : Fin R.size) (hab : a.val < b.val)
      (hc : (R.cell a).progress=(R.cell b).progress) : (R.cell a).isPalette := by
    let k : Fin R.size := ⟨a.val+1,by have := b.isLt; omega⟩
    have hk := R.progress_step a k rfl
    have hm := R.progress_mono (show k≤b by change a.val+1≤b.val; omega)
    change (R.cell k).progress≤(R.cell b).progress at hm
    exact (hk.2.2 (by omega)).1
  apply Fin.ext
  by_contra hn
  have hnp : ¬(R.cell i).isPalette := by
    obtain ⟨p,hp⟩ := hi
    simp [Cell.isPalette,hp]
  by_cases hij : i.val < j.val
  · exact hnp (forward i j hij hh)
  · have hp := forward j i (by omega) hh.symm
    have hm := congrArg (fun n => n%(q+2)) hh
    rw [Cell.progress_mod,Cell.progress_mod] at hm
    obtain ⟨p,hpi⟩ := hi
    obtain ⟨x,hx⟩ := hp
    simp [Cell.positionRank,hpi,hx] at hm
    exact (Nat.ne_of_lt p.isLt) hm

omit [NeZero q] in
lemma core_rank_le (b : Fin (R.task.arity.val+1)) (p : Fin q) :
    b.val*(q+2)+p.val≤(R.cell R.last).progress := by
  rw [R.last_progress,Nat.add_mul,Nat.one_mul]
  have hb : b.val≤R.task.arity.val := by have := b.isLt; omega
  have hm := Nat.mul_le_mul_right (q+2) hb
  have := p.isLt
  omega

noncomputable def locate (b : Fin (R.task.arity.val+1)) (p : Fin q) : Fin R.size :=
  Classical.choose (R.progress_surjective (b.val*(q+2)+p.val) (R.core_rank_le b p))
lemma locate_progress (b : Fin (R.task.arity.val+1)) (p : Fin q) :
    (R.cell (R.locate b p)).progress=b.val*(q+2)+p.val :=
  Classical.choose_spec (R.progress_surjective _ (R.core_rank_le b p))
lemma locate_rank (b : Fin (R.task.arity.val+1)) (p : Fin q) :
    (R.cell (R.locate b p)).positionRank=p.val := by
  have hh := congrArg (fun n => n%(q+2)) (R.locate_progress b p)
  simpa [Cell.progress_mod,Nat.add_mod,Nat.mod_eq_of_lt (show p.val < q+2 by have := p.isLt; omega)] using hh
lemma locate_pos (b : Fin (R.task.arity.val+1)) (p : Fin q) :
    (R.cell (R.locate b p)).pos=.core p := by
  have hh := R.locate_rank b p
  cases hp : (R.cell (R.locate b p)).pos with
  | core r =>
    simp only [Cell.positionRank,hp] at hh
    exact congrArg Position.core (Fin.ext hh)
  | palette x => simp only [Cell.positionRank,hp] at hh; have := p.isLt; omega
  | stop => simp only [Cell.positionRank,hp] at hh; have := p.isLt; omega
lemma locate_block (b : Fin (R.task.arity.val+1)) (p : Fin q) :
    (R.cell (R.locate b p)).metadata.block.val=b.val := by
  have hh := congrArg (fun n => n/(q+2)) (R.locate_progress b p)
  have hx : (b.val*(q+2)+p.val)/(q+2)=b.val := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ (by omega)]
    simp [Nat.div_eq_of_lt (show p.val < q+2 by have := p.isLt; omega)]
  exact (Cell.progress_div _).symm.trans (hh.trans hx)

lemma locate_unique (b : Fin (R.task.arity.val+1)) (p : Fin q) (i : Fin R.size)
    (hb : (R.cell i).metadata.block.val=b.val) (hp : (R.cell i).pos=.core p) : i=R.locate b p := by
  apply R.core_unique i (R.locate b p) ⟨p,hp⟩
  rw [R.locate_progress]
  simp [Cell.progress,Cell.positionRank,hp,hb]

noncomputable def slot (s : Bool) (b : Fin (R.task.arity.val+1)) (p : Fin q) : ZMod 2 :=
  (R.cell (R.locate b p)).data s
noncomputable def certificate (p : Fin q) : ZMod 2 := (R.cell (R.locate 0 p)).certificate
noncomputable def read : Address q → ZMod 2
  | .data s b p => if h : b.val < R.task.arity.val+1 then R.slot s ⟨b.val,h⟩ p else 0
  | .certificate p => R.certificate p

omit [NeZero q] in
lemma block_lt (i : Fin R.size) : (R.cell i).metadata.block.val < R.task.arity.val+1 := by
  have hh := (R.cell i).metadata.block.isLt
  have ht := congrArg Task.arity (R.task_eq i)
  change (R.cell i).metadata.arity=R.task.arity at ht
  have hv := congrArg Fin.val ht
  omega

lemma sum_read (a : Address q) : (∑ i, (R.cell i).read a) = R.read a := by
  classical
  cases a with
  | data s b p =>
    by_cases hb : b.val < R.task.arity.val+1
    · let b' : Fin (R.task.arity.val+1) := ⟨b.val,hb⟩
      rw [Finset.sum_eq_single (R.locate b' p)]
      · simp [Cell.read,R.locate_pos,R.locate_block,read,hb,slot,b']
      · intro i hi hne
        cases hp : (R.cell i).pos with
        | core r =>
          simp only [Cell.read,hp]
          split
          · rename_i hh
            exact (hne (R.locate_unique b' p i hh.1 (by simpa [hh.2] using hp))).elim
          · rfl
        | palette x => simp [Cell.read,hp]
        | stop => simp [Cell.read,hp]
      · simp
    · have hi (i : Fin R.size) : (R.cell i).read (.data s b p)=0 := by
        cases hp : (R.cell i).pos with
        | core r =>
          have hh : (R.cell i).metadata.block.val≠b.val := by have := R.block_lt i; omega
          simp [Cell.read,hp,hh]
        | palette x => simp [Cell.read,hp]
        | stop => simp [Cell.read,hp]
      simp [hi,read,hb]
  | certificate p =>
    rw [Finset.sum_eq_single (R.locate 0 p)]
    · simp [Cell.read,R.locate_pos,R.locate_block,read,certificate]
    · intro i hi hne
      cases hp : (R.cell i).pos with
      | core r =>
        simp only [Cell.read,hp]
        split
        · rename_i hh
          exact (hne (R.locate_unique 0 p i hh.1 (by simpa [hh.2] using hp))).elim
        · rfl
      | palette x => simp [Cell.read,hp]
      | stop => simp [Cell.read,hp]
    · simp

lemma addressed_total (C : Clause q) : (∑ i, (R.cell i).delta C) = fun k => R.read (C.address k) := by
  funext k
  simp only [Finset.sum_apply,Cell.delta]
  exact R.sum_read (C.address k)

lemma holds_iff (S : Schedule q) (j : Fin (S.count R.task).val) :
    (R.plan S).Holds j ↔
      (S.clause R.task (R.clauseIndex S j)).truth (fun k => R.read ((S.clause R.task (R.clauseIndex S j)).address k))=true := by
  change (S.clause R.task (R.clauseIndex S j)).truth (∑ i, (R.cell i).delta _)=true ↔ _
  rw [R.addressed_total]

end Region
end SourceBurnside.FiniteTable

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Formulas_Addressable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.Addressable
open FiniteTable Tableau

variable {q : ℕ} [NeZero q]
abbrev Reading (q : ℕ) := Bool ⊕ FiniteTable.Address q

def Reading.eval (w : Reading q) (v : FiniteTable.Address q → Bool) : Bool :=
  match w with
  | .inl b => b
  | .inr a => v a

omit [NeZero q] in
lemma Reading.eval_map {n : ℕ} (m : Fin n → FiniteTable.Address q)
    (w : Wire n) (v : FiniteTable.Address q → Bool) :
    Reading.eval (w.map id m) v=w.eval (v ∘ m) := by cases w <;> rfl

def bit (b : Bool) : ZMod 2 := if b then 1 else 0
def unbit (z : ZMod 2) : Bool := decide (z=1)
@[simp] lemma unbit_bit (b : Bool) : unbit (bit b)=b := by cases b <;> decide
@[simp] lemma bit_unbit (z : ZMod 2) : bit (unbit z)=z := by
  have hz : z=0 ∨ z=1 := by
    fin_cases z
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hz with rfl|rfl <;> norm_num [bit,unbit]

structure Clause (q : ℕ) where
  wires : Fin 3 → Reading q
  truth : (Fin 3 → Bool) → Bool

def Clause.Holds (C : Clause q) (v : FiniteTable.Address q → Bool) : Prop :=
  C.truth (fun i => (C.wires i).eval v)=true

def Clause.compile (C : Clause q) : FiniteTable.Clause q where
  address i := match C.wires i with
    | .inl _ => .certificate 0
    | .inr a => a
  truth r := C.truth (fun i => match C.wires i with
    | .inl b => b
    | .inr _ => unbit (r i))

lemma Clause.compile_holds (C : Clause q) (v : FiniteTable.Address q → Bool) :
    (C.compile.truth fun i => bit (v (C.compile.address i)))=true ↔ C.Holds v := by
  have he : (fun i => match C.wires i with
      | .inl b => b
      | .inr _ => unbit (bit (v (C.compile.address i)))) = fun i => (C.wires i).eval v := by
    funext i
    cases hi : C.wires i <;> simp [compile,Reading.eval,hi]
  change (C.truth (fun i => match C.wires i with
      | .inl b => b
      | .inr _ => unbit (bit (v (C.compile.address i)))))=true ↔ C.Holds v
  rw [he]
  rfl

def unit (a : Reading q) (b : Bool) : Clause q :=
  ⟨![a,a,a],fun v => decide (v 0=b)⟩
omit [NeZero q] in
@[simp] lemma unit_holds (a : Reading q) (b : Bool) (v : FiniteTable.Address q → Bool) :
    (unit a b).Holds v ↔ a.eval v=b := by
  change decide (a.eval v=b)=true ↔ a.eval v=b
  constructor
  · exact of_decide_eq_true
  · intro h; exact decide_eq_true h

def equal (a b : Reading q) (i : Fin 2) : Clause q :=
  ⟨![a,b,a],fun v => if i.val=0 then !v 0 || v 1 else v 0 || !v 1⟩
omit [NeZero q] in
lemma equal_holds (a b : Reading q) (v : FiniteTable.Address q → Bool) :
    (∀ i, (equal a b i).Holds v) ↔ a.eval v=b.eval v := by
  simp only [Clause.Holds,equal,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [Fin.forall_fin_two]
  cases a.eval v <;> cases b.eval v <;> decide

abbrev DataAddress (q : ℕ) := Bool × Fin 10 × Fin q

def dataAddress (p : DataAddress q) : FiniteTable.Address q := .data p.1 p.2.1 p.2.2

inductive InputBit (q : ℕ)
  | fixed (value : Bool)
  | input (address : DataAddress q) (negated : Bool)

def InputBit.eval (a : InputBit q) (v : FiniteTable.Address q → Bool) : Bool :=
  match a with
  | .fixed b => b
  | .input p neg => if neg then !(v (dataAddress p)) else v (dataAddress p)

def initial (a : Reading q) : InputBit q → Fin 2 → Clause q
  | .fixed b,_ => unit a b
  | .input p neg,i =>
      ⟨![a,.inr (dataAddress p),a], fun v =>
        let x := if neg then !v 1 else v 1
        if i.val=0 then !v 0 || x else v 0 || !x⟩

omit [NeZero q] in
lemma initial_holds (a : Reading q) (b : InputBit q) (v : FiniteTable.Address q → Bool) :
    (∀ i, (initial a b i).Holds v) ↔ a.eval v=b.eval v := by
  cases b with
  | fixed b => simp [initial,InputBit.eval]
  | input p neg =>
    change (∀ i : Fin 2, (if i.val=0 then
        !a.eval v || (if neg then !(v (dataAddress p)) else v (dataAddress p))
        else a.eval v || !(if neg then !(v (dataAddress p)) else v (dataAddress p)))=true) ↔
      a.eval v=(if neg then !(v (dataAddress p)) else v (dataAddress p))
    rw [Fin.forall_fin_two]
    cases a.eval v <;> cases v (dataAddress p) <;> cases neg <;> decide

def ofCircuitClause {n : ℕ} (m : Fin n → FiniteTable.Address q)
    (C : Tableau.Circuit.Clause n) : Clause q where
  wires i := (C.wires i).map id m
  truth := C.truth
omit [NeZero q] in
lemma ofCircuitClause_holds {n : ℕ} (m : Fin n → FiniteTable.Address q)
    (C : Tableau.Circuit.Clause n) (v : FiniteTable.Address q → Bool) :
    (ofCircuitClause m C).Holds v ↔ C.Holds (v ∘ m) := by
  have he : (fun i => Reading.eval ((C.wires i).map id m) v) =
      fun i => (C.wires i).eval (v ∘ m) := by
    funext i
    cases C.wires i <;> rfl
  change (C.truth fun i => Reading.eval ((C.wires i).map id m) v)=true ↔ C.truth _=true
  rw [he]

abbrev Triple (a b c : ℕ) := (Fin a × Fin b) × Fin c

def tripleEquiv (a b c : ℕ) : Triple a b c ≃ Fin (c*b*a) :=
  (((finProdFinEquiv (m:=a) (n:=b)).prodCongr (Equiv.refl (Fin c))).trans
    finProdFinEquiv).trans (finCongr (by ring))
lemma tripleEquiv_val (a b c : ℕ) (i : Triple a b c) :
    (tripleEquiv a b c i).val=c*(b*i.1.1.val+i.1.2.val)+i.2.val := by
  simp [tripleEquiv,finProdFinEquiv]
  ring

structure Layout (q β g T W : ℕ) where
  bit_pos : 0<β
  time_pos : 0<T
  width_ge : 3≤W
  certificate_fit : Tableau.Layout.certificateCount β g T W≤q
  clause_fit : Tableau.Layout.clauseCount β g T W≤q
  origin : Fin W

namespace Layout
variable {β g T W : ℕ} (L : Layout q β g T W)

abbrev XIndex := Triple T W β
abbrev YIndex := Triple (T-1) (W-2) g
abbrev CIndex := XIndex (β:=β) (T:=T) (W:=W) ⊕ YIndex (g:=g) (T:=T) (W:=W)

def certEquiv : CIndex (β:=β) (g:=g) (T:=T) (W:=W) ≃
    Fin (Tableau.Layout.certificateCount β g T W) :=
  ((tripleEquiv T W β).sumCongr (tripleEquiv (T-1) (W-2) g)).trans finSumFinEquiv

def core (i : CIndex (β:=β) (g:=g) (T:=T) (W:=W)) : Fin q :=
  Fin.castLE L.certificate_fit (certEquiv i)

def x (t : Fin T) (j : Fin W) (r : Fin β) : FiniteTable.Address q :=
  .certificate (L.core (.inl ((t,j),r)))
def y (t : Fin (T-1)) (j : Fin (W-2)) (v : Fin g) : FiniteTable.Address q :=
  .certificate (L.core (.inr ((t,j),v)))

omit [NeZero q] in
lemma core_x_val (t : Fin T) (j : Fin W) (r : Fin β) :
    (L.core (.inl ((t,j),r))).val=Tableau.Layout.xAddress β W t.val j.val r.val := by
  change (tripleEquiv T W β ((t,j),r)).val=Tableau.Layout.xAddress β W t.val j.val r.val
  exact tripleEquiv_val T W β ((t,j),r)
omit [NeZero q] in
lemma core_y_val (t : Fin (T-1)) (j : Fin (W-2)) (v : Fin g) :
    (L.core (.inr ((t,j),v))).val=Tableau.Layout.yAddress β g T W t.val j.val v.val := by
  change β*W*T+(tripleEquiv (T-1) (W-2) g ((t,j),v)).val=Tableau.Layout.yAddress β g T W t.val j.val v.val
  rw [tripleEquiv_val]
  simp [Tableau.Layout.yAddress,Nat.add_assoc]

def certificate (_L : Layout q β g T W) (v : CIndex (β:=β) (g:=g) (T:=T) (W:=W) → Bool) (p : Fin q) : Bool :=
  if hp : p.val < Tableau.Layout.certificateCount β g T W then
    v (certEquiv.symm ⟨p.val,hp⟩) else false

omit [NeZero q] in
@[simp] lemma certificate_core (v : CIndex (β:=β) (g:=g) (T:=T) (W:=W) → Bool)
    (i : CIndex (β:=β) (g:=g) (T:=T) (W:=W)) : L.certificate v (L.core i)=v i := by
  unfold certificate
  rw [dite_eq_left (show (L.core i).val < Tableau.Layout.certificateCount β g T W from
    (certEquiv i).isLt)]
  change v (certEquiv.symm (certEquiv i))=v i
  exact congrArg v (certEquiv.symm_apply_apply i)

def payload (data : DataAddress q → Bool)
    (cert : CIndex (β:=β) (g:=g) (T:=T) (W:=W) → Bool) : FiniteTable.Address q → Bool
  | .data s b p => data (s,b,p)
  | .certificate p => L.certificate cert p
omit [NeZero q] in
@[simp] lemma payload_data (data : DataAddress q → Bool)
    (cert : CIndex (β:=β) (g:=g) (T:=T) (W:=W) → Bool) (p : DataAddress q) :
    L.payload data cert (dataAddress p)=data p := rfl
omit [NeZero q] in
@[simp] lemma payload_x (data : DataAddress q → Bool)
    (cert : CIndex (β:=β) (g:=g) (T:=T) (W:=W) → Bool)
    (t : Fin T) (j : Fin W) (r : Fin β) :
    L.payload data cert (L.x t j r)=cert (.inl ((t,j),r)) := by
  exact L.certificate_core cert _
omit [NeZero q] in
@[simp] lemma payload_y (data : DataAddress q → Bool)
    (cert : CIndex (β:=β) (g:=g) (T:=T) (W:=W) → Bool)
    (t : Fin (T-1)) (j : Fin (W-2)) (v : Fin g) :
    L.payload data cert (L.y t j v)=cert (.inr ((t,j),v)) := by
  exact L.certificate_core cert _

abbrev InitialIndex := Triple W β 2
abbrev BoundaryIndex := Triple (T-1) 2 β
abbrev LocalIndex := Triple (T-1) (W-2) (3*g+2*β)
abbrev ClauseIndex :=
  ((InitialIndex (β:=β) (W:=W) ⊕ BoundaryIndex (β:=β) (T:=T)) ⊕
    LocalIndex (β:=β) (g:=g) (T:=T) (W:=W)) ⊕ Fin β

def clauseEquiv : ClauseIndex (β:=β) (g:=g) (T:=T) (W:=W) ≃
    Fin (Tableau.Layout.clauseCount β g T W) :=
  let bound : BoundaryIndex (β:=β) (T:=T) ≃ Fin (2*β*(T-1)) :=
    (tripleEquiv (T-1) 2 β).trans (finCongr (by ring))
  let first := ((tripleEquiv W β 2).sumCongr bound).trans finSumFinEquiv
  let second := (first.sumCongr (tripleEquiv (T-1) (W-2) (3*g+2*β))).trans finSumFinEquiv
  (second.sumCongr (Equiv.refl (Fin β))).trans finSumFinEquiv

def currentTime (t : Fin (T-1)) : Fin T := ⟨t.val,by have := t.isLt; omega⟩
def nextTime (t : Fin (T-1)) : Fin T := ⟨t.val+1,by have := t.isLt; omega⟩
def interior (j : Fin (W-2)) : Fin W := ⟨j.val+1,by have := j.isLt; omega⟩
def boundary (i : Fin 2) : Fin W :=
  if i.val=0 then ⟨0,by have := L.width_ge; omega⟩ else ⟨W-1,by have := L.width_ge; omega⟩

def localRead (t : Fin (T-1)) (j : Fin (W-2)) :
    Fin (3*β+g) → FiniteTable.Address q := Fin.addCases
  (fun i => let p := finProdFinEquiv.symm i
    L.x (currentTime t) ⟨j.val+p.1.val,by
      have := j.isLt
      have : p.1.val<3 := p.1.isLt
      omega⟩ p.2)
  (L.y t j)

def localClause (c : Circuit (3*β) g) (output : Fin β → Wire (3*β+g))
    (t : Fin (T-1)) (j : Fin (W-2)) (i : Fin (3*g+2*β)) : Clause q :=
  if hi : i.val<3*g then
    ofCircuitClause (L.localRead t j) (c.clauses[ i.val ]'(by rw [c.clauses_length]; exact hi))
  else
    let r : Fin β := ⟨(i.val-3*g)/2,by have := i.isLt; omega⟩
    let k : Fin 2 := ⟨(i.val-3*g)%2,Nat.mod_lt _ (by decide)⟩
    equal (.inr (L.x (nextTime t) (interior j) r)) ((output r).map id (L.localRead t j)) k

def clause (c : Circuit (3*β) g) (output : Fin β → Wire (3*β+g))
    (init : Fin W → Fin β → InputBit q) (blank accept : Fin β → Bool) :
    ClauseIndex (β:=β) (g:=g) (T:=T) (W:=W) → Clause q
  | .inl (.inl (.inl ((j,r),k))) =>
      initial (.inr (L.x ⟨0,L.time_pos⟩ j r)) (init j r) k
  | .inl (.inl (.inr ((t,k),r))) =>
      unit (.inr (L.x (nextTime t) (L.boundary k) r)) (blank r)
  | .inl (.inr ((t,j),i)) => L.localClause c output t j i
  | .inr r => unit (.inr (L.x ⟨T-1,by have := L.time_pos; omega⟩ L.origin r)) (accept r)

def clauseAt (c : Circuit (3*β) g) (output : Fin β → Wire (3*β+g))
    (init : Fin W → Fin β → InputBit q) (blank accept : Fin β → Bool)
    (i : Fin (Tableau.Layout.clauseCount β g T W)) : Clause q :=
  L.clause c output init blank accept (clauseEquiv.symm i)

omit [NeZero q] in
lemma all_clauses_iff (c : Circuit (3*β) g) (output : Fin β → Wire (3*β+g))
    (init : Fin W → Fin β → InputBit q) (blank accept : Fin β → Bool)
    (v : FiniteTable.Address q → Bool) :
    (∀ i, (L.clauseAt c output init blank accept i).Holds v) ↔
    (∀ i, (L.clause c output init blank accept i).Holds v) := by
  constructor
  · intro h i
    have hi := h (clauseEquiv i)
    simpa only [clauseAt,Equiv.symm_apply_apply] using hi
  · intro h i
    exact h _

omit [NeZero q] in
lemma localClause_gate (c : Circuit (3*β) g) (output : Fin β → Wire (3*β+g))
    (t : Fin (T-1)) (j : Fin (W-2)) (i : Fin (3*g)) :
    L.localClause c output t j (Fin.castAdd (2*β) i) =
      ofCircuitClause (L.localRead t j) (c.clauses[i.val]'(by rw [c.clauses_length]; exact i.isLt)) := by
  simp [localClause,i.isLt]

def outputIndex (r : Fin β) (k : Fin 2) : Fin (3*g+2*β) :=
  ⟨3*g+2*r.val+k.val,by have := r.isLt; have := k.isLt; omega⟩
omit [NeZero q] in
lemma localClause_output (c : Circuit (3*β) g) (output : Fin β → Wire (3*β+g))
    (t : Fin (T-1)) (j : Fin (W-2)) (r : Fin β) (k : Fin 2) :
    L.localClause c output t j (outputIndex r k) =
      equal (.inr (L.x (nextTime t) (interior j) r)) ((output r).map id (L.localRead t j)) k := by
  have hk := k.isLt
  have hd : (3*g+2*r.val+k.val-3*g)/2 = r.val := by omega
  have hm : (3*g+2*r.val+k.val-3*g)%2 = k.val := by omega
  simp [localClause,outputIndex,show ¬3*g+2*r.val+k.val < 3*g by omega,hd,hm]

omit [NeZero q] in
lemma localClause_holds (c : Circuit (3*β) g) (output : Fin β → Wire (3*β+g))
    (t : Fin (T-1)) (j : Fin (W-2)) (v : FiniteTable.Address q → Bool) :
    (∀ i, (L.localClause c output t j i).Holds v) ↔
    c.Satisfies (v ∘ L.localRead t j) ∧
      ∀ r, v (L.x (nextTime t) (interior j) r) =
        (output r).eval (v ∘ L.localRead t j) := by
  constructor
  · intro h
    constructor
    · apply (c.clauses_iff (v ∘ L.localRead t j)).mp
      intro C hc
      obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hc
      have hi' : i<3*g := by simpa only [c.clauses_length] using hi
      have hv := h (Fin.castAdd (2*β) ⟨i,hi'⟩)
      rw [L.localClause_gate] at hv
      exact (ofCircuitClause_holds ..).mp hv
    · intro r
      have he := (equal_holds (.inr (L.x (nextTime t) (interior j) r))
        ((output r).map id (L.localRead t j)) v).mp (fun k => by
          have hk := h (outputIndex r k)
          rwa [L.localClause_output] at hk)
      change v (L.x (nextTime t) (interior j) r)=_ at he
      simpa only [Reading.eval_map] using he
  · rintro ⟨hc,ho⟩ i
    unfold localClause
    split_ifs with hi
    · apply (ofCircuitClause_holds ..).mpr
      exact (c.clauses_iff (v ∘ L.localRead t j)).mpr hc _ (List.getElem_mem _)
    · apply (equal_holds _ _ v).mpr
      change v (L.x (nextTime t) (interior j) _)=_
      have he := ho ⟨(i.val-3*g)/2,by have := i.isLt; omega⟩
      simpa only [Reading.eval_map] using he

def FiniteValid (c : Circuit (3*β) g) (output : Fin β → Wire (3*β+g))
    (init : Fin W → Fin β → InputBit q) (blank accept : Fin β → Bool)
    (v : FiniteTable.Address q → Bool) : Prop :=
  (∀ j r, v (L.x ⟨0,L.time_pos⟩ j r)=(init j r).eval v) ∧
  (∀ t k r, v (L.x (nextTime t) (L.boundary k) r)=blank r) ∧
  (∀ t j, c.Satisfies (v ∘ L.localRead t j)) ∧
  (∀ t j r, v (L.x (nextTime t) (interior j) r)=
    (output r).eval (v ∘ L.localRead t j)) ∧
  (∀ r, v (L.x ⟨T-1,by have := L.time_pos; omega⟩ L.origin r)=accept r)

omit [NeZero q] in
lemma clauseAt_holds_iff (c : Circuit (3*β) g) (output : Fin β → Wire (3*β+g))
    (init : Fin W → Fin β → InputBit q) (blank accept : Fin β → Bool)
    (v : FiniteTable.Address q → Bool) :
    (∀ i, (L.clauseAt c output init blank accept i).Holds v) ↔
      L.FiniteValid c output init blank accept v := by
  rw [L.all_clauses_iff]
  constructor
  · intro h
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro j r
      exact (initial_holds _ _ v).mp (fun k => h (.inl (.inl (.inl ((j,r),k)))))
    · intro t k r
      exact (unit_holds _ _ v).mp (h (.inl (.inl (.inr ((t,k),r)))))
    · intro t j
      exact ((L.localClause_holds c output t j v).mp (fun i => h (.inl (.inr ((t,j),i))))).1
    · intro t j r
      exact ((L.localClause_holds c output t j v).mp (fun i => h (.inl (.inr ((t,j),i))))).2 r
    · intro r
      exact (unit_holds _ _ v).mp (h (.inr r))
  · rintro ⟨hi,hb,hg,ho,ha⟩ i
    rcases i with ((i|i)|i)|i
    · rcases i with ⟨⟨j,r⟩,k⟩
      exact (initial_holds (.inr (L.x ⟨0,L.time_pos⟩ j r)) (init j r) v).mpr (hi j r) k
    · rcases i with ⟨⟨t,k⟩,r⟩
      exact (unit_holds _ _ v).mpr (hb t k r)
    · rcases i with ⟨⟨t,j⟩,k⟩
      exact (L.localClause_holds c output t j v).mpr ⟨hg t j,ho t j⟩ k
    · exact (unit_holds _ _ v).mpr (ha i)

def rows (v : FiniteTable.Address q → Bool) (t j : ℕ) (r : Fin β) : Bool :=
  if ht : t<T then if hj : j<W then v (L.x ⟨t,ht⟩ ⟨j,hj⟩ r) else false else false

def gates (v : FiniteTable.Address q → Bool) (t j : ℕ) (r : Fin g) : Bool :=
  if ht : t<T-1 then if hj : j<W-2 then v (L.y ⟨t,ht⟩ ⟨j,hj⟩ r) else false else false

omit [NeZero q] in
lemma rows_at (v : FiniteTable.Address q → Bool) {t j : ℕ} (ht : t<T) (hj : j<W) (r : Fin β) :
    L.rows v t j r=v (L.x ⟨t,ht⟩ ⟨j,hj⟩ r) := by simp [rows,ht,hj]
omit [NeZero q] in
lemma gates_at (v : FiniteTable.Address q → Bool) {t j : ℕ} (ht : t<T-1) (hj : j<W-2) (r : Fin g) :
    L.gates v t j r=v (L.y ⟨t,ht⟩ ⟨j,hj⟩ r) := by simp [gates,ht,hj]

omit [NeZero q] in
lemma localRead_rows (v : FiniteTable.Address q → Bool) (t : Fin (T-1)) (j : Fin (W-2)) :
    v ∘ L.localRead t j =
      Rectangle.assignment (L.rows v t.val) j.val (L.gates v t.val j.val) := by
  funext i
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  · simp only [Function.comp_apply,localRead,Fin.addCases_left,Rectangle.assignment,
      Rectangle.neighborhood]
    exact (L.rows_at v (show t.val<T by have := t.isLt; omega)
      (show j.val+(finProdFinEquiv.symm k : Fin 3 × Fin β).1.val<W by
        have := j.isLt
        have := (finProdFinEquiv.symm k : Fin 3 × Fin β).1.isLt
        omega) _).symm
  · simp only [Function.comp_apply,localRead,Fin.addCases_right,Rectangle.assignment]
    exact (L.gates_at v t.isLt j.isLt k).symm

def inputRow (_L : Layout q β g T W) (init : Fin W → Fin β → InputBit q) (v : FiniteTable.Address q → Bool)
    (j : ℕ) (r : Fin β) : Bool :=
  if hj : j<W then (init ⟨j,hj⟩ r).eval v else false
omit [NeZero q] in
lemma inputRow_at (init : Fin W → Fin β → InputBit q) (v : FiniteTable.Address q → Bool)
    {j : ℕ} (hj : j<W) (r : Fin β) : L.inputRow init v j r=(init ⟨j,hj⟩ r).eval v := by
  simp [inputRow,hj]

omit [NeZero q] in
lemma rectangle_of_finiteValid (c : Circuit (3*β) g) (output : Fin β → Wire (3*β+g))
    (init : Fin W → Fin β → InputBit q) (blank accept : Fin β → Bool)
    (v : FiniteTable.Address q → Bool) (hv : L.FiniteValid c output init blank accept v) :
    Rectangle.Valid c output T W blank (L.inputRow init v) (L.rows v) (L.gates v) ∧
      L.rows v (T-1) L.origin.val=accept := by
  constructor
  · refine ⟨?_,?_,?_,?_⟩
    · intro j hj
      funext r
      rw [L.rows_at v L.time_pos hj,L.inputRow_at init v hj]
      exact hv.1 _ _
    · intro t ht j hj hjb
      have ht' : t<T-1 := by omega
      funext r
      rw [L.rows_at v ht hj]
      rcases hjb with rfl|he
      · have hb := hv.2.1 ⟨t,ht'⟩ 0 r
        simpa only [nextTime,boundary,Fin.val_zero,ite_true] using hb
      · have hb := hv.2.1 ⟨t,ht'⟩ 1 r
        have hj' : j=W-1 := by omega
        subst j
        simpa only [nextTime,boundary,Fin.val_one,show ¬(1:ℕ)=0 by omega,ite_false] using hb
    · intro t ht j hj
      have ht' : t<T-1 := by omega
      have hj' : j<W-2 := by omega
      have hc := hv.2.2.1 ⟨t,ht'⟩ ⟨j,hj'⟩
      rwa [L.localRead_rows] at hc
    · intro t ht j hj r
      have ht' : t<T-1 := by omega
      have hj' : j<W-2 := by omega
      have hc := hv.2.2.2.1 ⟨t,ht'⟩ ⟨j,hj'⟩ r
      rw [L.localRead_rows] at hc
      rw [L.rows_at v ht (show j+1<W by omega)]
      exact hc
  · funext r
    rw [L.rows_at v (by have := L.time_pos; omega) L.origin.isLt]
    exact hv.2.2.2.2 r

omit [NeZero q] in
theorem clause_sound (c : Circuit (3*β) g) (output : Fin β → Wire (3*β+g))
    (init : Fin W → Fin β → InputBit q) (blank accept : Fin β → Bool)
    (v : FiniteTable.Address q → Bool)
    (hv : ∀ i, (L.clauseAt c output init blank accept i).Holds v) :
    Rectangle.run c output W blank (L.inputRow init v) (T-1) L.origin.val=accept := by
  have hh := L.rectangle_of_finiteValid c output init blank accept v
    ((L.clauseAt_holds_iff c output init blank accept v).mp hv)
  exact (Rectangle.accepting_tableau_iff c output T W L.origin.val L.time_pos L.origin.isLt
    blank accept (L.inputRow init v)).mp ⟨L.rows v,L.gates v,hh⟩

def assemble (data : DataAddress q → Bool) (cert : Fin q → Bool) : FiniteTable.Address q → Bool
  | .data s b p => data (s,b,p)
  | .certificate p => cert p

omit [NeZero q] in
lemma inputBit_assemble (b : InputBit q) (data : DataAddress q → Bool)
    (c₁ c₂ : Fin q → Bool) : b.eval (assemble data c₁)=b.eval (assemble data c₂) := by
  cases b <;> rfl

omit [NeZero q] in
lemma inputBit_payload (b : InputBit q) (data : DataAddress q → Bool)
    (cert : CIndex (β:=β) (g:=g) (T:=T) (W:=W) → Bool) :
    b.eval (L.payload data cert)=b.eval (assemble data (fun _ => false)) := by
  cases b <;> rfl

omit [NeZero q] in
lemma inputRow_assemble (init : Fin W → Fin β → InputBit q) (data : DataAddress q → Bool)
    (c₁ c₂ : Fin q → Bool) : L.inputRow init (assemble data c₁)=L.inputRow init (assemble data c₂) := by
  funext j r
  unfold inputRow
  split
  · exact inputBit_assemble _ _ _ _
  · rfl

def rectCertificate (X : ℕ → Rectangle.Row β) (Y : ℕ → ℕ → Fin g → Bool) :
    CIndex (β:=β) (g:=g) (T:=T) (W:=W) → Bool
  | .inl ((t,j),r) => X t.val j.val r
  | .inr ((t,j),v) => Y t.val j.val v

omit [NeZero q] in
lemma localRead_rect (data : DataAddress q → Bool)
    (X : ℕ → Rectangle.Row β) (Y : ℕ → ℕ → Fin g → Bool)
    (t : Fin (T-1)) (j : Fin (W-2)) :
    L.payload data (rectCertificate X Y) ∘ L.localRead t j =
      Rectangle.assignment (X t.val) j.val (Y t.val j.val) := by
  funext i
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  · simp only [Function.comp_apply,localRead,Fin.addCases_left,payload_x,rectCertificate,
      currentTime,Rectangle.assignment,Rectangle.neighborhood]
  · simp only [Function.comp_apply,localRead,Fin.addCases_right,payload_y,rectCertificate,
      Rectangle.assignment]

omit [NeZero q] in
lemma finiteValid_of_rectangle (c : Circuit (3*β) g) (output : Fin β → Wire (3*β+g))
    (init : Fin W → Fin β → InputBit q) (blank accept : Fin β → Bool)
    (data : DataAddress q → Bool)
    (X : ℕ → Rectangle.Row β) (Y : ℕ → ℕ → Fin g → Bool)
    (hv : Rectangle.Valid c output T W blank
      (L.inputRow init (assemble data (fun _ => false))) X Y)
    (ha : X (T-1) L.origin.val=accept) :
    L.FiniteValid c output init blank accept (L.payload data (rectCertificate X Y)) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro j r
    rw [L.payload_x,L.inputBit_payload]
    simpa only [rectCertificate,inputRow,dite_eq_left j.isLt] using congrFun (hv.1 j.val j.isLt) r
  · intro t k r
    rw [L.payload_x]
    exact congrFun (hv.2.1 t.val (by have := t.isLt; omega)
      (L.boundary k).val (L.boundary k).isLt (by
        unfold boundary
        split
        · exact Or.inl rfl
        · exact Or.inr (by have := L.width_ge; dsimp; omega))) r
  · intro t j
    rw [L.localRead_rect]
    exact hv.2.2.1 t.val (by have := t.isLt; omega) j.val (by have := j.isLt; omega)
  · intro t j r
    rw [L.payload_x,L.localRead_rect]
    exact hv.2.2.2 t.val (by have := t.isLt; omega) j.val (by have := j.isLt; omega) r
  · intro r
    rw [L.payload_x]
    exact congrFun ha r

omit [NeZero q] in
theorem certificate_iff (c : Circuit (3*β) g) (output : Fin β → Wire (3*β+g))
    (init : Fin W → Fin β → InputBit q) (blank accept : Fin β → Bool)
    (data : DataAddress q → Bool) :
    (∃ cert : Fin q → Bool, ∀ i,
      (L.clauseAt c output init blank accept i).Holds (assemble data cert)) ↔
      Rectangle.run c output W blank (L.inputRow init (assemble data (fun _ => false)))
        (T-1) L.origin.val=accept := by
  constructor
  · rintro ⟨cert,hc⟩
    have hh := L.clause_sound c output init blank accept (assemble data cert) hc
    rwa [L.inputRow_assemble init data cert (fun _ => false)] at hh
  · intro ha
    let X := Rectangle.run c output W blank (L.inputRow init (assemble data (fun _ => false)))
    let Y := fun t j v => c.evaluate (Rectangle.neighborhood (X t) j) (Fin.natAdd (3*β) v)
    refine ⟨L.certificate (rectCertificate X Y),?_⟩
    change ∀ i, (L.clauseAt c output init blank accept i).Holds
      (L.payload data (rectCertificate X Y))
    exact (L.clauseAt_holds_iff c output init blank accept _).mpr
      (L.finiteValid_of_rectangle c output init blank accept data X Y
        (Rectangle.run_valid c output T W blank _) ha)

omit [NeZero q] in
lemma clauseCount_pos (L : Layout q β g T W) : 0<Tableau.Layout.clauseCount β g T W := by
  have := L.bit_pos
  unfold Tableau.Layout.clauseCount
  omega

def schedule (c : Circuit (3*β) g) (output : Fin β → Wire (3*β+g))
    (init : Task → Fin W → Fin β → InputBit q) (blank accept : Fin β → Bool) : Schedule q where
  count _ := ⟨Tableau.Layout.clauseCount β g T W,by have := L.clause_fit; omega⟩
  positive _ := L.clauseCount_pos
  clause task p := if hp : p.val<Tableau.Layout.clauseCount β g T W then
    (L.clauseAt c output (init task) blank accept ⟨p.val,hp⟩).compile
    else (unit (.inl true) true).compile

lemma schedule_clause (c : Circuit (3*β) g) (output : Fin β → Wire (3*β+g))
    (init : Task → Fin W → Fin β → InputBit q) (blank accept : Fin β → Bool)
    (task : Task) (i : Fin (Tableau.Layout.clauseCount β g T W)) :
    (L.schedule c output init blank accept).clause task (Fin.castLE L.clause_fit i)=
      (L.clauseAt c output (init task) blank accept i).compile := by
  simp only [schedule,Fin.val_castLE,dite_eq_left i.isLt]

end Layout
end SourceBurnside.Addressable

namespace SourceBurnside.Addressable
open FiniteTable Tableau
variable {q β g T W d : ℕ} [NeZero q]

noncomputable def physicalBits (R : FiniteTable.Region q d) (a : FiniteTable.Address q) : Bool := unbit (R.read a)

theorem physical_clauses_iff (L : Layout q β g T W)
    (c : Circuit (3*β) g) (output : Fin β → Wire (3*β+g))
    (init : Task → Fin W → Fin β → InputBit q) (blank accept : Fin β → Bool)
    (R : FiniteTable.Region q d) :
    (∀ i, (R.plan (L.schedule c output init blank accept)).Holds i) ↔
      ∀ i, (L.clauseAt c output (init R.task) blank accept i).Holds (physicalBits R) := by
  let S := L.schedule c output init blank accept
  have he (i : Fin (Tableau.Layout.clauseCount β g T W)) :
      (R.plan S).Holds i ↔ (L.clauseAt c output (init R.task) blank accept i).Holds (physicalBits R) := by
    rw [R.holds_iff S i]
    have hi : R.clauseIndex S i=Fin.castLE L.clause_fit i := by rfl
    rw [hi,L.schedule_clause]
    have hh := Clause.compile_holds (L.clauseAt c output (init R.task) blank accept i) (physicalBits R)
    simpa only [physicalBits,bit_unbit] using hh
  exact forall_congr' he

end SourceBurnside.Addressable

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Machines_UniversalInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.Structured
noncomputable section

inductive Program (K : Type*)
  | skip
  | push (k : K) (b : Bool)
  | pop (k : K) (branch : Option Bool → Program K)
  | seq (first second : Program K)
  | loop (k : K) (body : Bool → Program K)

open Program
variable {K : Type*} [DecidableEq K]

abbrev Store (K : Type*) := K → List Bool

inductive Run : Program K → Store K → ℕ → Store K → Prop
  | skip (r) : Run .skip r 1 r
  | push (r) (k) (b) : Run (.push k b) r 1 (Function.update r k (r k++[b]))
  | pop (r : Store K) (k) (b : Option Bool → Program K) (n : ℕ) (s : Store K)
      (h : Run (b (r k).getLast?) (Function.update r k (r k).dropLast) n s) :
      Run (.pop k b) r (1+n) s
  | seq (p q : Program K) (r s t : Store K) (n m : ℕ)
      (hp : Run p r n s) (hq : Run q s m t) : Run (.seq p q) r (n+m) t
  | loop_nil (r : Store K) (k) (b : Bool → Program K) (h : r k=[]) : Run (.loop k b) r 1 r
  | loop_cons (r : Store K) (k) (b : Bool → Program K) (v : List Bool) (a : Bool)
      (s t : Store K) (n m : ℕ) (h : r k=v++[a])
      (hb : Run (b a) (Function.update r k v) n s) (ht : Run (.loop k b) s m t) :
      Run (.loop k b) r (1+(n+m)) t

end
end SourceBurnside.Structured

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Machines_BinaryRegisters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.Structured.Binary
open Program
variable {K : Type*} [DecidableEq K]

def move (src dst : K) : Program K := .loop src (fun b => .push dst b)
def spread (src left right : K) : Program K :=
  .loop src (fun b => .seq (.push left b) (.push right b))
def copy (src dst tmp : K) : Program K := .seq (move src tmp) (spread tmp src dst)

lemma move_run (src dst : K) (hne : src≠dst) (r : Store K) :
    Run (move src dst) r (2*(r src).length+1)
      (Function.update (Function.update r src []) dst (r dst++(r src).reverse)) := by
  generalize hv : r src=v
  induction v using List.reverseRecOn generalizing r with
  | nil =>
    have he : Function.update (Function.update r src []) dst (r dst++([]:List Bool).reverse)=r := by
      funext k
      by_cases h1 : k=dst
      · subst k;simp
      · by_cases h2 : k=src
        · subst k;simp [hne,hv]
        · simp [h1,h2]
    rw [he]
    exact Run.loop_nil r src _ hv
  | append_singleton v a ih =>
    let r1 := Function.update r src v
    let r2 := Function.update r1 dst (r1 dst++[a])
    have h2 : r2 src=v := by simp [r2,r1,hne]
    have ht := ih r2 h2
    have hh := Run.loop_cons r src (fun b => Program.push dst b) v a r2
      (Function.update (Function.update r2 src []) dst (r2 dst++v.reverse))
      1 (2*v.length+1) hv (Run.push r1 dst a) ht
    have he : Function.update (Function.update r2 src []) dst (r2 dst++v.reverse)=
        Function.update (Function.update r src []) dst (r dst++(v++[a]).reverse) := by
      funext k
      by_cases h1 : k=dst
      · subst k;simp [r2,r1,Ne.symm hne,List.reverse_append,List.append_assoc]
      · by_cases h2 : k=src
        · subst k;simp [h1]
        · simp [r2,r1,h1,h2]
    rw [he] at hh
    convert hh using 1 <;> simp [move]
    omega

lemma spread_run (src left right : K) (hsl : src≠left) (hsr : src≠right) (hlr : left≠right)
    (r : Store K) :
    Run (spread src left right) r (3*(r src).length+1)
      (Function.update (Function.update (Function.update r src []) left (r left++(r src).reverse))
        right (r right++(r src).reverse)) := by
  generalize hv : r src=v
  induction v using List.reverseRecOn generalizing r with
  | nil =>
    have he : Function.update (Function.update (Function.update r src []) left
        (r left++([]:List Bool).reverse)) right (r right++([]:List Bool).reverse)=r := by
      funext k
      by_cases h1 : k=right
      · subst k;simp
      · by_cases h2 : k=left
        · subst k;simp [h1]
        · by_cases h3 : k=src
          · subst k;simp [h1,h2,hv]
          · simp [h1,h2,h3]
    rw [he]
    exact Run.loop_nil r src _ hv
  | append_singleton v a ih =>
    let r1 := Function.update r src v
    let r2 := Function.update r1 left (r1 left++[a])
    let r3 := Function.update r2 right (r2 right++[a])
    have h3 : r3 src=v := by simp [r3,r2,r1,hsl,hsr]
    have ht := ih r3 h3
    have hb := Run.seq (.push left a) (.push right a) r1 r2 r3 1 1
      (Run.push r1 left a) (Run.push r2 right a)
    have hh := Run.loop_cons r src (fun b => Program.seq (.push left b) (.push right b)) v a r3
      (Function.update (Function.update (Function.update r3 src []) left (r3 left++v.reverse))
        right (r3 right++v.reverse))
      2 (3*v.length+1) hv hb ht
    have he : Function.update (Function.update (Function.update r3 src []) left (r3 left++v.reverse))
        right (r3 right++v.reverse)=
        Function.update (Function.update (Function.update r src []) left (r left++(v++[a]).reverse))
          right (r right++(v++[a]).reverse) := by
      funext k
      by_cases h1 : k=right
      · subst k;simp [r3,r2,r1,Ne.symm hlr,Ne.symm hsr,List.reverse_append,List.append_assoc]
      · by_cases h2 : k=left
        · subst k;simp [r3,r2,r1,hlr,Ne.symm hsl,List.reverse_append,List.append_assoc]
        · by_cases h3 : k=src
          · subst k;simp [h1,h2]
          · simp [r3,r2,r1,h1,h2,h3]
    rw [he] at hh
    convert hh using 1 <;> simp [spread]
    omega

lemma copy_run (src dst tmp : K) (hsd : src≠dst) (hst : src≠tmp) (hdt : dst≠tmp)
    (r : Store K) (ht : r tmp=[]) :
    Run (copy src dst tmp) r (5*(r src).length+2)
      (Function.update r dst (r dst++r src)) := by
  let s := Function.update (Function.update r src []) tmp (r src).reverse
  have h1 : Run (move src tmp) r (2*(r src).length+1) s := by
    simpa [s,ht] using move_run src tmp hst r
  have h2 := spread_run tmp src dst (Ne.symm hst) (Ne.symm hdt) hsd s
  have hlen : (s tmp).length=(r src).length := by simp [s]
  rw [hlen] at h2
  have he : Function.update (Function.update (Function.update s tmp []) src (s src++(s tmp).reverse))
      dst (s dst++(s tmp).reverse)=Function.update r dst (r dst++r src) := by
    funext k
    by_cases h1 : k=dst
    · subst k;simp [s,hdt,Ne.symm hsd]
    · by_cases h2 : k=src
      · subst k;simp [s,h1,hst]
      · by_cases h3 : k=tmp
        · subst k;simp [s,h1,h2,ht]
        · simp [s,h1,h2,h3]
  rw [he] at h2
  have hh := Run.seq (move src tmp) (spread tmp src dst) r s _ _ _ h1 h2
  simpa only [copy,show (2*(r src).length+1)+(3*(r src).length+1)=5*(r src).length+2 by omega] using hh

end SourceBurnside.Structured.Binary

namespace SourceBurnside.Structured.Binary.Add
open Program

def bit (b : Bool) : ℕ := if b then 1 else 0
def value : List Bool → ℕ
  | [] => 0 | a::w => bit a+2*value w

lemma value_append (xs ys : List Bool) : value (xs++ys)=value xs+2^xs.length*value ys := by
  induction xs with
  | nil => simp [value]
  | cons a xs ih => simp [value,ih,Nat.pow_succ];ring

end SourceBurnside.Structured.Binary.Add

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Machines_ArithmeticDevices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.Structured.Binary.Multiply
open Program
def stepCost (b : Bool) (n : ℕ) : ℕ := if b then 16*n+10 else 4*n+3

def time (n : ℕ) : List Bool → ℕ
  | [] => 1
  | b::ys => 1+stepCost b n+time n ys

end SourceBurnside.Structured.Binary.Multiply

namespace SourceBurnside.Structured.Binary
open Program

namespace Divide

def feed (N : ℕ) : List Bool → ℕ
  | [] => N
  | b::ys => feed (2*N+Add.bit b) ys

lemma feed_value (N : ℕ) (ys : List Bool) : feed N ys=2^ys.length*N+Add.value ys.reverse := by
  induction ys generalizing N with
  | nil => simp [feed,Add.value]
  | cons b ys ih => simp only [feed,ih,List.length_cons,Nat.pow_succ,List.reverse_cons,
      Add.value_append,List.length_reverse,Add.value];ring

end Divide
end SourceBurnside.Structured.Binary

namespace SourceBurnside.Structured.Device
open Program Binary

variable {ι : Type} [DecidableEq ι]

def input {W : Type} (xs : ι → List Bool) : Store (ι ⊕ W) := Sum.elim xs (fun _ => [])
def values (xs : ι → List Bool) : ι → ℕ := fun i => Add.value (xs i).reverse

def result {W : Type} [DecidableEq W] (xs : ι → List Bool) (out : W) (y : List Bool) : Store (ι ⊕ W) :=
  Function.update (input xs) (.inr out) y

structure Realizer (f : (ι → ℕ) → ℕ) (Pre : ℕ → (ι → ℕ) → Prop) where
  W : Type
  finiteW : Finite W
  eqW : DecidableEq W
  out : W
  program : Program (ι ⊕ W)
  coefficient : ℕ
  spec : ∀ (n : ℕ) (_hn : 0<n) (xs : ι → List Bool),
    (∀i,(xs i).length=n) → Pre n (values xs) →
    ∃t y,t ≤ coefficient*(n+1)^2 ∧ y.length=n ∧ Add.value y.reverse=f (values xs) ∧
      Run program (input xs) t (@result ι _ W eqW xs out y)
attribute [instance] Realizer.finiteW Realizer.eqW

end SourceBurnside.Structured.Device

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Machines_RegisterLoops
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.Structured.Device

inductive Formula (ι : Type)
  | read : ι → Formula ι
  | constant : ℕ → Formula ι
  | add : Formula ι → Formula ι → Formula ι
  | sub : Formula ι → Formula ι → Formula ι
  | mul : Formula ι → Formula ι → Formula ι
  | div : Formula ι → Formula ι → Formula ι
  | mod : Formula ι → Formula ι → Formula ι
  | le : Formula ι → Formula ι → Formula ι
  | powTwo : Formula ι → Formula ι
  | bitLength : Formula ι → Formula ι
  | branch : Formula ι → Formula ι → Formula ι → Formula ι

namespace Formula
variable {ι : Type} [DecidableEq ι]
def eval : Formula ι → (ι → ℕ) → ℕ
  | .read i,vs => vs i
  | .constant a,_ => a
  | .add x y,vs => x.eval vs+y.eval vs
  | .sub x y,vs => x.eval vs-y.eval vs
  | .mul x y,vs => x.eval vs*y.eval vs
  | .div x y,vs => x.eval vs/y.eval vs
  | .mod x y,vs => x.eval vs%y.eval vs
  | .le x y,vs => if x.eval vs≤y.eval vs then 1 else 0
  | .powTwo x,vs => 2^(x.eval vs)
  | .bitLength x,vs => if x.eval vs=0 then 1 else (x.eval vs).size
  | .branch c a b,vs => if c.eval vs=0 then b.eval vs else a.eval vs

end Formula
end SourceBurnside.Structured.Device

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_Recognizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w
namespace SourceBurnside.FiniteTable.Recognizer
open LocalSyntax Skeleton
variable {q : ℕ} [NeZero q]

def firstTest (c : Skeleton q 10) : Prop :=
  c.metadata.block.val=0 ∧ match c.pos with
  | .core p => p.val=0
  | _ => False

def paletteTest (c : Cell q) : Prop := match c.pos with
  | .palette _ => True
  | _ => False
def coreTest (c : Cell q) : Prop := match c.pos with
  | .core _ => True
  | _ => False
lemma coreTest_iff (c : Cell q) : coreTest c ↔ c.isCore := by
  cases hp : c.pos <;> simp [coreTest,Cell.isCore,hp]
instance decideCore (c : Cell q) : Decidable c.isCore := by
  haveI : Decidable (coreTest c) := by unfold coreTest; cases c.pos <;> infer_instance
  exact decidable_of_iff (coreTest c) (coreTest_iff c)

def headfreeTest (c : Cell q) : Prop :=
  ¬IsHead c.skeleton ∧ match c.checker with
  | .head _ => False
  | _ => True

def AcquireTest (a b a' b' : Cell q) : Prop :=
  Skeleton.Pair (a.skeleton.mark .left) (b'.skeleton.mark .boundary) ∧
  a=a.boundary a.head.side ∧ b=b'.idle a.head.side ∧
  a'=a.wing .left ∧ b'=b'.boundary a.head.side

def ReadLeftTest (S : Schedule q) (a b a' b' : Cell q) : Prop :=
  Skeleton.Pair (a.skeleton.mark .full) (b.skeleton.mark .right) ∧
  a=a.wing .left ∧ b=b.full b.head.side b.head.clause .readLeft b.head.reg ∧
  a'=a.full b.head.side b.head.clause .readLeft (b.head.reg+a.delta (S.clause a.metadata.task b.head.clause)) ∧
  b'=b.wing .right

def ReadRightTest (a b a' b' : Cell q) : Prop :=
  Skeleton.Pair (a.skeleton.mark .full) (b.skeleton.mark .right) ∧
  a=a.full a.head.side a.head.clause .readRight a.head.reg ∧ b=b.wing .right ∧
  a'=a.wing .left ∧ b'=b.full a.head.side a.head.clause .readRight a.head.reg

def UndoLeftTest (a b a' b' : Cell q) : Prop :=
  Skeleton.Pair (a.skeleton.mark .full) (b.skeleton.mark .right) ∧
  a=a.wing .left ∧ b=b.full b.head.side b.head.clause .undoLeft b.head.reg ∧
  a'=a.full b.head.side b.head.clause .undoLeft b.head.reg ∧ b'=b.wing .right

def UndoRightTest (S : Schedule q) (a b a' b' : Cell q) : Prop :=
  Skeleton.Pair (a.skeleton.mark .full) (b.skeleton.mark .right) ∧
  a=a.full a.head.side a.head.clause .undoRight a.head.reg ∧ b=b.wing .right ∧
  a'=a.wing .left ∧
  b'=b.full a.head.side a.head.clause .undoRight (a.head.reg+a.delta (S.clause a.metadata.task a.head.clause))

def CheckerCreateTest (a b a' b' : Cell q) : Prop :=
  a'=a ∧ b=b'.setChecker .idle ∧ match a.pos,b'.pos,b'.checker with
  | .core p,.palette _,.head _ => p.val+1=q
  | _,_,_ => False

def CheckerAdvanceTest (a b a' b' : Cell q) : Prop := match a.pos,b.pos,a.checker with
  | .palette v,.palette _,.head x => v≠x ∧ b.checker=.idle ∧
      a'=a.setChecker (.passed x) ∧ b'=b.setChecker (.head x)
  | _,_,_ => False

def SwapTest (a b a' b' : Cell q) : Prop := match a.pos,b.pos with
  | .palette _,.palette y => a'=b ∧ b'=a ∧ a.setColor y=b ∧ a.HeadFree ∧ b.HeadFree
  | _,_ => False

def BinaryTest (S : Schedule q) (a b a' b' : Cell q) : Prop :=
  AcquireTest a b a' b' ∨ ReadLeftTest S a b a' b' ∨ ReadRightTest a b a' b' ∨
  UndoLeftTest a b a' b' ∨ UndoRightTest S a b a' b' ∨ CheckerCreateTest a b a' b' ∨
  CheckerAdvanceTest a b a' b' ∨ SwapTest a b a' b'

lemma checkerCreateTest_iff (a b a' b' : Cell q) : CheckerCreateTest a b a' b' ↔
    ∃ p x, a.pos=.core p ∧ p.val+1=q ∧ b'.isPalette ∧ b'.checker=.head x ∧
      a'=a ∧ b=b'.setChecker .idle := by
  cases ha : a.pos <;> cases hb : b'.pos <;> cases hx : b'.checker <;>
    simp [CheckerCreateTest,Cell.isPalette,ha,hb,hx,and_comm,and_left_comm]
lemma checkerAdvanceTest_iff (a b a' b' : Cell q) : CheckerAdvanceTest a b a' b' ↔
    ∃ v x, a.pos=.palette v ∧ b.isPalette ∧ a.checker=.head x ∧ v≠x ∧ b.checker=.idle ∧
      a'=a.setChecker (.passed x) ∧ b'=b.setChecker (.head x) := by
  cases ha : a.pos <;> cases hb : b.pos <;> cases hx : a.checker <;>
    simp [CheckerAdvanceTest,Cell.isPalette,ha,hb,hx]
lemma swapTest_iff (a b a' b' : Cell q) : SwapTest a b a' b' ↔
    ∃ x y, a.pos=.palette x ∧ b.pos=.palette y ∧
      a'=b ∧ b'=a ∧ a.setColor y=b ∧ a.HeadFree ∧ b.HeadFree := by
  cases ha : a.pos <;> cases hb : b.pos <;> simp [SwapTest,ha,hb]

lemma binary_test {S : Schedule q} {a b a' b' : Cell q} (h : Binary S a b a' b') :
    BinaryTest S a b a' b' := by
  cases h with
  | acquire a b s hp =>
    apply Or.inl
    exact ⟨hp,rfl,rfl,rfl,rfl⟩
  | read_left a b s j r hp =>
    apply Or.inr ∘ Or.inl
    exact ⟨hp,rfl,rfl,rfl,rfl⟩
  | read_right a b s j r hp =>
    apply Or.inr ∘ Or.inr ∘ Or.inl
    exact ⟨hp,rfl,rfl,rfl,rfl⟩
  | undo_left a b s j r hp =>
    apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
    exact ⟨hp,rfl,rfl,rfl,rfl⟩
  | undo_right a b s j r hp =>
    apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
    exact ⟨hp,rfl,rfl,rfl,rfl⟩
  | checker_create a b p x ha hp hb =>
    apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
    apply (checkerCreateTest_iff ..).mpr
    exact ⟨p,x,ha,hp,hb,rfl,rfl,rfl⟩
  | checker_advance a b v x ha hb hv =>
    apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
    apply (checkerAdvanceTest_iff ..).mpr
    exact ⟨v,x,ha,hb,rfl,hv,rfl,rfl,rfl⟩
  | swap a b x y ha hb he hf hf' =>
    apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr
    exact (swapTest_iff ..).mpr ⟨x,y,ha,hb,rfl,rfl,he,hf,hf'⟩

lemma binary_of_test {S : Schedule q} {a b a' b' : Cell q} (h : BinaryTest S a b a' b') :
    Binary S a b a' b' := by
  rcases h with h | h | h | h | h | h | h | h
  · rcases h with ⟨hp,ha,hb,ha',hb'⟩
    simpa only [← ha,← hb,← ha',← hb'] using Binary.acquire (S:=S) a b' a.head.side hp
  · rcases h with ⟨hp,ha,hb,ha',hb'⟩
    simpa only [← ha,← hb,← ha',← hb'] using Binary.read_left (S:=S) a b b.head.side b.head.clause b.head.reg hp
  · rcases h with ⟨hp,ha,hb,ha',hb'⟩
    simpa only [← ha,← hb,← ha',← hb'] using Binary.read_right (S:=S) a b a.head.side a.head.clause a.head.reg hp
  · rcases h with ⟨hp,ha,hb,ha',hb'⟩
    simpa only [← ha,← hb,← ha',← hb'] using Binary.undo_left (S:=S) a b b.head.side b.head.clause b.head.reg hp
  · rcases h with ⟨hp,ha,hb,ha',hb'⟩
    simpa only [← ha,← hb,← ha',← hb'] using Binary.undo_right (S:=S) a b a.head.side a.head.clause a.head.reg hp
  · obtain ⟨p,x,hp,hq,hpal,hch,ha',hb⟩ := (checkerCreateTest_iff ..).mp h
    have hv := Binary.checker_create (S:=S) a b' p x hp hq hpal
    have he : b'.setChecker (.head x)=b' := by cases b'; simp_all [Cell.setChecker]
    simpa only [← hb,he,← ha'] using hv
  · obtain ⟨v,x,hp,hpal,hch,hne,hidle,ha',hb'⟩ := (checkerAdvanceTest_iff ..).mp h
    have hv := Binary.checker_advance (S:=S) a b v x hp hpal hne
    have he : a.setChecker (.head x)=a := by cases a; simp_all [Cell.setChecker]
    have he' : b.setChecker .idle=b := by cases b; simp_all [Cell.setChecker]
    simpa only [he,he',← ha',← hb'] using hv
  · obtain ⟨x,y,hp,hq,ha',hb',he,hf,hf'⟩ := (swapTest_iff ..).mp h
    simpa only [← ha',← hb'] using Binary.swap (S:=S) a b x y hp hq he hf hf'

end SourceBurnside.FiniteTable.Recognizer

namespace SourceBurnside.FiniteTable.Codec

section

def binaryValue (bs : List Bool) : ℕ := (BitVec.ofBoolListLE bs).toNat
@[simp] lemma binaryValue_bit (bs : List Bool) (i : ℕ) : (binaryValue bs).testBit i=bs.getD i false := by
  change (BitVec.ofBoolListLE bs).getLsbD i=_
  exact BitVec.getLsbD_ofBoolListLE

def natCode {h : ℕ} (w : Raw h) : ℕ := binaryValue (List.ofFn w)
lemma natCode_bit {h : ℕ} (w : Raw h) (i : Fin (10000*h)) : (natCode w).testBit i.val=w i := by
  simp [natCode,i.isLt]

lemma readInt_arithmetic {h : ℕ} (hh : 0<h) (w : Raw h) (s : Fin 32) :
    readInt hh w s=(natCode w/2^(s.val*(2*h)))%2^(2*h) := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (binaryValue (List.ofFn (fun j => w (intPosition hh s j)))).testBit i=_
  rw [binaryValue_bit,Nat.testBit_mod_two_pow,Nat.testBit_div_two_pow]
  by_cases hi : i<2*h
  · have hj : i+s.val*(2*h)<10000*h := by
      have hs : s.val≤31 := by omega
      have ht := Nat.mul_le_mul_right (2*h) hs
      omega
    have hb := natCode_bit w ⟨i+s.val*(2*h),hj⟩
    simp only [List.getD_eq_getElem, List.length_ofFn, hi,List.getElem_ofFn,
      decide_true,Bool.true_and]
    rw [hb]
    congr 1
    apply Fin.ext
    simp [intPosition,Nat.add_comm]
  · simp [hi]

lemma readFlag_arithmetic {h : ℕ} (hh : 0<h) (w : Raw h) (s : Fin 512) :
    readFlag hh w s=decide ((natCode w/2^(64*h+s.val))%2=1) := by
  rw [←Nat.testBit_eq_decide_div_mod_eq]
  exact (natCode_bit w (flagPosition hh s)).symm

lemma flag_as_nat {h : ℕ} (hh : 0<h) (w : Raw h) (s : Fin 512) :
    (if readFlag hh w s then 1 else 0)=(natCode w/2^(64*h+s.val))%2 := by
  rw [readFlag_arithmetic]
  have H := Nat.mod_lt (natCode w/2^(64*h+s.val)) (by omega : 0<2)
  split_ifs <;> simp_all


open LocalSyntax

lemma integers_unused {q : ℕ} (c : Cell q) (s : Fin 32) (hs : 9 ≤ s.val) : integers c s=0 := by
  unfold integers
  split <;> omega
lemma flags_unused {q : ℕ} (c : Cell q) (s : Fin 512) (hs : 8 ≤ s.val) : flags c s=false := by
  unfold flags
  split <;> first | omega | rfl

end

open LocalSyntax

end SourceBurnside.FiniteTable.Codec

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Formulas_BooleanCircuits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w

namespace SourceBurnside.Structured.Device.Formula
section
variable {ι : Type}

def equal (x y : Formula ι) : Formula ι := .branch (.le x y) (.le y x) (.constant 0)
def less (x y : Formula ι) : Formula ι := .branch (.le y x) (.constant 0) (.constant 1)
def neg (e : Formula ι) : Formula ι := .branch e (.constant 0) (.constant 1)
def and (e f : Formula ι) : Formula ι := .branch e f (.constant 0)
def or (e f : Formula ι) : Formula ι := .branch e (.constant 1) f
def all (es : List (Formula ι)) : Formula ι := es.foldr and (.constant 1)
def any (es : List (Formula ι)) : Formula ι := es.foldr or (.constant 0)

def field (x offset width : Formula ι) : Formula ι :=
  .mod (.div x (.powTwo offset)) (.powTwo width)
def bitAt (x index : Formula ι) : Formula ι := field x index (.constant 1)

@[simp] lemma equal_eval (x y : Formula ι) (vs : ι → ℕ) :
    (equal x y).eval vs=if x.eval vs=y.eval vs then 1 else 0 := by
  by_cases h : x.eval vs=y.eval vs
  · simp [equal,eval,h]
  · by_cases hxy : x.eval vs≤y.eval vs <;>
      simp [equal,eval,h,hxy]
    omega
@[simp] lemma less_eval (x y : Formula ι) (vs : ι → ℕ) :
    (less x y).eval vs=if x.eval vs<y.eval vs then 1 else 0 := by
  by_cases h : y.eval vs≤x.eval vs <;> simp [less,eval,h]
@[simp] lemma neg_eval (x : Formula ι) (vs : ι → ℕ) :
    (neg x).eval vs=if x.eval vs=0 then 1 else 0 := rfl
@[simp] lemma and_eval (x y : Formula ι) (vs : ι → ℕ) :
    (and x y).eval vs=if x.eval vs=0 then 0 else y.eval vs := rfl
@[simp] lemma or_eval (x y : Formula ι) (vs : ι → ℕ) :
    (or x y).eval vs=if x.eval vs=0 then y.eval vs else 1 := rfl
@[simp] lemma all_eval [DecidableEq ι] (es : List (Formula ι)) (vs : ι → ℕ) :
    (all es).eval vs=if ∀e∈es,e.eval vs≠0 then 1 else 0 := by
  induction es with
  | nil => simp [all,eval]
  | cons e es ih =>
    change (and e (all es)).eval vs=_
    rw [and_eval,ih]
    by_cases h : e.eval vs=0 <;> simp [h]
@[simp] lemma any_eval [DecidableEq ι] (es : List (Formula ι)) (vs : ι → ℕ) :
    (any es).eval vs=if ∃e∈es,e.eval vs≠0 then 1 else 0 := by
  induction es with
  | nil => simp [any,eval]
  | cons e es ih =>
    change (or e (any es)).eval vs=_
    rw [or_eval,ih]
    by_cases h : e.eval vs=0 <;> simp [h]
@[simp] lemma field_eval (x index width : Formula ι) (vs : ι → ℕ) :
    (field x index width).eval vs=(x.eval vs/2^(index.eval vs))%2^(width.eval vs) := rfl

end

variable {ι : Type}
def implies (x y : Formula ι) : Formula ι := .branch x y (.constant 1)
lemma implies_eval (x y : Formula ι) (v : ι → ℕ) :
    (implies x y).eval v=if x.eval v=0 then 1 else y.eval v := rfl
@[simp] lemma implies_ne_zero (x y : Formula ι) (v : ι → ℕ) :
    (implies x y).eval v≠0 ↔ (x.eval v≠0 → y.eval v≠0) := by
  by_cases h : x.eval v=0 <;> simp [implies_eval,h]
end SourceBurnside.Structured.Device.Formula

namespace SourceBurnside.RawFormula
open Structured.Device Structured.Device.Formula FiniteTable.Codec
abbrev F := Formula (Fin 2)
def height : F := .read 0
def word : F := .read 1
def scale (a : ℕ) : F := .mul (.constant a) height
def slot (s : Fin 32) : F := field word (scale (2*s.val)) (scale 2)
def bound : F := .powTwo height

def inputs (h w : ℕ) : Fin 2 → ℕ := ![h,w]
@[simp] lemma height_eval (h w : ℕ) : height.eval (inputs h w)=h := rfl
@[simp] lemma word_eval (h w : ℕ) : word.eval (inputs h w)=w := rfl
@[simp] lemma scale_eval (a h w : ℕ) : (scale a).eval (inputs h w)=a*h := rfl
@[simp] lemma slot_eval (s : Fin 32) (h w : ℕ) :
    (slot s).eval (inputs h w)=(w/2^(s.val*(2*h)))%2^(2*h) := by
  simp [slot,Nat.mul_comm,Nat.mul_left_comm]
@[simp] lemma bound_eval (h w : ℕ) : bound.eval (inputs h w)=2^h := rfl

end SourceBurnside.RawFormula

namespace SourceBurnside.CellRepr
open LocalSyntax FiniteTable FiniteTable.Codec

def boolean (b : Bool) : ℕ := if b then 1 else 0
@[simp] lemma boolean_false : boolean false=0 := rfl
@[simp] lemma boolean_true : boolean true=1 := rfl
lemma boolean_injective : Function.Injective boolean := by intro a b;cases a <;> cases b <;> simp [boolean]
@[simp] lemma boolean_eq_zero (b : Bool) : boolean b=0 ↔ b=false := by cases b <;> decide
@[simp] lemma boolean_eq_one (b : Bool) : boolean b=1 ↔ b=true := by cases b <;> decide
@[simp] lemma boolean_bit_zero : boolean (bit 0)=0 := rfl

abbrev Record (A : Type) := (Fin 9 → A) × (Fin 8 → A)
def cellRecord {q : ℕ} (c : Cell q) : Record ℕ :=
  ⟨fun s => integers c ⟨s.val,by have := s.isLt;omega⟩,
   fun s => boolean (flags c ⟨s.val,by have := s.isLt;omega⟩)⟩

lemma repr_injective {h : ℕ} (hh : 4≤h) : Function.Injective (cellRecord (q:=2^h)) := by
  intro c d H
  apply encode_injective hh
  unfold encode
  congr 1
  · funext s
    by_cases hs : s.val<9
    · have Hs := congrArg (fun r : Record ℕ => r.1 ⟨s.val,hs⟩) H
      exact Hs
    · rw [integers_unused c s (by omega),integers_unused d s (by omega)]
  · funext s
    by_cases hs : s.val<8
    · have Hs := congrArg (fun r : Record ℕ => r.2 ⟨s.val,hs⟩) H
      exact boolean_injective Hs
    · rw [flags_unused c s (by omega),flags_unused d s (by omega)]

end SourceBurnside.CellRepr

namespace SourceBurnside.CellFormula
open LocalSyntax FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} [DecidableEq ι]
abbrev Expr := Record (Formula ι)

def evaluate (a : Expr (ι:=ι)) (v : ι → ℕ) : Record ℕ :=
  ⟨fun i => (a.1 i).eval v,fun i => (a.2 i).eval v⟩

def ofRaw (height word : Formula ι) : Expr (ι:=ι) :=
  ⟨fun i => field word (.mul (.constant (2*i.val)) height) (.mul (.constant 2) height),
   fun i => bitAt word (.add (.mul (.constant 64) height) (.constant i.val))⟩

omit [DecidableEq ι] in
lemma ofRaw_represents {h : ℕ} (hh : 4≤h) (c : Cell (2^h)) (H W : Formula ι) (v : ι → ℕ)
    (hH : H.eval v=h) (hW : W.eval v=natCode (encode c)) :
    evaluate (ofRaw H W) v=cellRecord c := by
  apply Prod.ext
  · funext i
    have HR := readInt_arithmetic (show 0<h by omega) (encode c) ⟨i.val,by have := i.isLt;omega⟩
    rw [readInt_encode hh] at HR
    simpa [evaluate,ofRaw,Formula.eval,hH,hW,cellRecord,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using HR.symm
  · funext i
    have HR := flag_as_nat (show 0<h by omega) (encode c) ⟨i.val,by have := i.isLt;omega⟩
    rw [readFlag_encode] at HR
    simpa [evaluate,ofRaw,bitAt,Formula.eval,hH,hW,cellRecord,boolean] using HR.symm

def equalCells (a b : Expr (ι:=ι)) : Formula ι :=
  and (all (List.ofFn (fun i : Fin 9 => equal (a.1 i) (b.1 i))))
    (all (List.ofFn (fun i : Fin 8 => equal (a.2 i) (b.2 i))))

lemma equalCells_eval (a b : Expr (ι:=ι)) (v : ι → ℕ) :
    (equalCells a b).eval v=if evaluate a v=evaluate b v then 1 else 0 := by
  simp only [equalCells,and_eval,all_eval]
  have H (n : ℕ) (a b : Fin n → Formula ι) :
      (∀e∈List.ofFn (fun i => equal (a i) (b i)),e.eval v≠0) ↔
        (fun i => (a i).eval v)=(fun i => (b i).eval v) := by
    simp [funext_iff]
  simp only [H]
  simp only [evaluate,Prod.mk.injEq]
  split_ifs <;> simp_all

lemma equality_exact {h : ℕ} (hh : 4≤h) (a b : Expr (ι:=ι)) (v : ι → ℕ)
    (c d : Cell (2^h)) (ha : evaluate a v=cellRecord c) (hb : evaluate b v=cellRecord d) :
    (equalCells a b).eval v=1 ↔ c=d := by
  simp only [equalCells_eval,ha,hb,(repr_injective hh).eq_iff]
  split_ifs <;> simp_all

lemma equalCells_bool (a b : Expr (ι:=ι)) (v : ι → ℕ) : (equalCells a b).eval v≤1 := by
  rw [equalCells_eval];split_ifs <;> omega

def wing (a : Expr (ι:=ι)) (m : Marker) : Expr (ι:=ι) :=
  ⟨fun i => match i.val with | 2 => .constant (markerTag m) | 7 | 8 => .constant 0 | _ => a.1 i,
   fun i => match i.val with | 1 | 5 | 6 | 7 => .constant 0 | _ => a.2 i⟩
def boundary (a : Expr (ι:=ι)) (side : Formula ι) : Expr (ι:=ι) :=
  ⟨(wing a .boundary).1,
   fun i => match i.val with | 1 => side | 5 | 6 | 7 => .constant 0 | _ => a.2 i⟩
def full (a : Expr (ι:=ι)) (side clause : Formula ι) (phase : Phase)
    (reg : Fin 3 → Formula ι) : Expr (ι:=ι) :=
  ⟨fun i => match i.val with | 2 => .constant 3 | 7 => clause | 8 => .constant (phaseTag phase) | _ => a.1 i,
   fun i => match i.val with | 1 => side | 5 => reg 0 | 6 => reg 1 | 7 => reg 2 | _ => a.2 i⟩
def idle (a : Expr (ι:=ι)) (side : Formula ι) : Expr (ι:=ι) :=
  ⟨fun i => match i.val with | 2 | 3 | 4 | 7 | 8 => .constant 0 | _ => a.1 i,
   fun i => if i.val=2 then .branch side (a.2 3) (a.2 2) else .constant 0⟩
def setChecker (a : Expr (ι:=ι)) (tag index : Formula ι) : Expr (ι:=ι) :=
  ⟨fun i => match i.val with | 5 => tag | 6 => index | _ => a.1 i,a.2⟩
def setColor (a : Expr (ι:=ι)) (color : Formula ι) : Expr (ι:=ι) :=
  ⟨fun i => match i.val with | 0 => .constant 1 | 1 => color | _ => a.1 i,a.2⟩

omit [DecidableEq ι]

lemma represent_int {q : ℕ} {a : Expr (ι:=ι)} {v : ι → ℕ} {c : Cell q}
    (h : evaluate a v=cellRecord c) (i : Fin 9) : (a.1 i).eval v=(cellRecord c).1 i := congrArg (fun r => r.1 i) h
lemma represent_flag {q : ℕ} {a : Expr (ι:=ι)} {v : ι → ℕ} {c : Cell q}
    (h : evaluate a v=cellRecord c) (i : Fin 8) : (a.2 i).eval v=(cellRecord c).2 i := congrArg (fun r => r.2 i) h

variable {q : ℕ} [NeZero q] {a : Expr (ι:=ι)} {v : ι → ℕ} {c : Cell q}
variable (ha : evaluate a v=cellRecord c)
include ha

lemma wing_represents (m : Marker) : evaluate (wing a m) v=cellRecord (c.wing m) := by
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [evaluate,wing,Formula.eval,represent_int ha,represent_flag ha,cellRecord,
      integers,flags,Cell.wing,Skeleton.mark,defaultHead,Cell.pos,Cell.marker,Cell.metadata,phaseTag]

lemma boundary_represents (side : Formula ι) (s : Bool) (hs : side.eval v=boolean s) :
    evaluate (boundary a side) v=cellRecord (c.boundary s) := by
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [evaluate,boundary,wing,Formula.eval,represent_int ha,represent_flag ha,hs,cellRecord,
      integers,flags,Cell.boundary,Skeleton.mark,defaultHead,Cell.pos,Cell.marker,Cell.metadata,phaseTag]

omit [NeZero q] in
lemma full_represents (side clause : Formula ι) (phase : Phase) (reg : Fin 3 → Formula ι)
    (s : Bool) (j : Fin q) (r : Reg) (hs : side.eval v=boolean s) (hj : clause.eval v=j.val)
    (hr : ∀i,(reg i).eval v=boolean (bit (r i))) :
    evaluate (full a side clause phase reg) v=cellRecord (c.full s j phase r) := by
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [evaluate,full,Formula.eval,represent_int ha,represent_flag ha,hs,hj,hr,cellRecord,
      integers,flags,Cell.full,Skeleton.mark,Cell.pos,Cell.marker,Cell.metadata,markerTag]

lemma idle_represents (side : Formula ι) (s : Bool) (hs : side.eval v=boolean s) :
    evaluate (idle a side) v=cellRecord (c.idle s) := by
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [evaluate,idle,Formula.eval,represent_int ha,represent_flag ha,hs,cellRecord,
      integers,flags,Cell.idle,defaultHead,defaultMeta,Cell.pos,Cell.marker,Cell.metadata,
      markerTag,phaseTag,bit,boolean]
  cases s <;> simp

omit [NeZero q] in
lemma setChecker_represents (tag index : Formula ι) (ch : Palette.Check (Fin q))
    (ht : tag.eval v=checkerTag ch) (hi : index.eval v=checkerIndex ch) :
    evaluate (setChecker a tag index) v=cellRecord (c.setChecker ch) := by
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [evaluate,setChecker,represent_int ha,represent_flag ha,ht,hi,cellRecord,
      integers,flags,Cell.setChecker,Cell.pos,Cell.marker,Cell.metadata]

omit [NeZero q] in
lemma setColor_represents (color : Formula ι) (col : Fin q) (hc : color.eval v=col.val) :
    evaluate (setColor a color) v=cellRecord (c.setColor col) := by
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [evaluate,setColor,Formula.eval,represent_int ha,represent_flag ha,hc,cellRecord,
      integers,flags,Cell.setColor,Cell.pos,Cell.marker,Cell.metadata,positionTag,positionIndex]

end SourceBurnside.CellFormula

namespace SourceBurnside.Structured.Device.Formula
variable {ι : Type}
@[simp] lemma constant_eval (k : ℕ) (v : ι → ℕ) : (.constant k : Formula ι).eval v=k := rfl
@[simp] lemma add_eval (a b : Formula ι) (v : ι → ℕ) : (Formula.add a b).eval v=a.eval v+b.eval v := rfl
@[simp↓] lemma equal_ne_zero (x y : Formula ι) (v : ι → ℕ) :
    (equal x y).eval v≠0 ↔ x.eval v=y.eval v := by simp [equal_eval]
@[simp↓] lemma all_ne_zero [DecidableEq ι] (es : List (Formula ι)) (v : ι → ℕ) :
    (all es).eval v≠0 ↔ ∀e∈es,e.eval v≠0 := by simp [all_eval]
@[simp↓] lemma any_ne_zero [DecidableEq ι] (es : List (Formula ι)) (v : ι → ℕ) :
    (any es).eval v≠0 ↔ ∃e∈es,e.eval v≠0 := by simp [any_eval]
@[simp↓] lemma and_ne_zero (x y : Formula ι) (v : ι → ℕ) :
    (and x y).eval v≠0 ↔ x.eval v≠0 ∧ y.eval v≠0 := by
  rw [and_eval];split_ifs <;> simp_all
@[simp↓] lemma or_ne_zero (x y : Formula ι) (v : ι → ℕ) :
    (or x y).eval v≠0 ↔ x.eval v≠0 ∨ y.eval v≠0 := by
  rw [or_eval];split_ifs <;> simp_all
@[simp↓] lemma neg_ne_zero (x : Formula ι) (v : ι → ℕ) :
    (neg x).eval v≠0 ↔ ¬x.eval v≠0 := by simp [neg_eval]
attribute [-simp] equal_eval all_eval any_eval and_eval or_eval neg_eval
end SourceBurnside.Structured.Device.Formula

namespace SourceBurnside.CellFormula
open LocalSyntax FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} [DecidableEq ι]
def first (a : Expr (ι:=ι)) : Formula ι :=
  all [equal (a.1 4) (.constant 0),equal (a.1 0) (.constant 0),equal (a.1 1) (.constant 0)]
def last (a : Expr (ι:=ι)) : Formula ι :=
  all [equal (a.1 4) (a.1 3),equal (a.1 0) (.constant 2)]
def hasMarker (a : Expr (ι:=ι)) (m : Marker) := equal (a.1 2) (.constant (markerTag m))
def hasPhase (a : Expr (ι:=ι)) (p : Phase) := equal (a.1 8) (.constant (phaseTag p))
def isCore (a : Expr (ι:=ι)) := equal (a.1 0) (.constant 0)
def isPalette (a : Expr (ι:=ι)) := equal (a.1 0) (.constant 1)
def isStop (a : Expr (ι:=ι)) := equal (a.1 0) (.constant 2)
def hasHead (a : Expr (ι:=ι)) := or (hasMarker a .boundary) (hasMarker a .full)
def endpoint (a : Expr (ι:=ι)) := any ([Phase.acquisition,.beforeGate,.afterGate,.finish,.success].map (hasPhase a))

def admissible (a : Expr (ι:=ι)) : Formula ι :=
  and (implies (hasMarker a .right) (neg (first a)))
    (implies (hasMarker a .left) (neg (last a)))
def leftExternal (a : Expr (ι:=ι)) : Formula ι :=
  or (hasMarker a .idle) (and (neg (hasMarker a .right)) (first a))
def rightExternal (a : Expr (ι:=ι)) : Formula ι :=
  or (hasMarker a .idle) (or (hasMarker a .boundary) (and (neg (hasMarker a .left)) (last a)))
def acceptsLeft (a b : Expr (ι:=ι)) : Formula ι :=
  .branch (hasMarker a .right) (or (hasMarker b .full) (hasMarker b .right)) (hasMarker b .left)
def acceptsRight (a b : Expr (ι:=ι)) : Formula ι :=
  .branch (hasMarker a .left) (any [hasMarker b .left,hasMarker b .boundary,hasMarker b .full]) (hasMarker b .right)
def structural (a b : Expr (ι:=ι)) (Q : Formula ι) : Formula ι :=
  any [all [isCore a,isCore b,equal (.add (a.1 1) (.constant 1)) (b.1 1)],
    all [isCore a,isPalette b,equal (.add (a.1 1) (.constant 1)) Q],
    and (isPalette a) (isPalette b),and (isPalette a) (isStop b),
    all [isStop a,isCore b,equal (b.1 1) (.constant 0)]]
def internal (a b : Expr (ι:=ι)) : Formula ι :=
  all [equal (a.1 3) (b.1 3),equal (a.2 0) (b.2 0),
    .branch (isStop a) (equal (.add (a.1 4) (.constant 1)) (b.1 4)) (equal (a.1 4) (b.1 4)),
    neg (first b),neg (last a)]
def skeletonPair (a b : Expr (ι:=ι)) (Q : Formula ι) : Formula ι :=
  and (structural a b Q) (or (and (rightExternal a) (leftExternal b))
    (all [neg (rightExternal a),neg (leftExternal b),acceptsRight a b,acceptsLeft b a,internal a b]))

lemma markerTag_injective : Function.Injective markerTag := by intro a b;cases a <;> cases b <;> simp [markerTag]
lemma phaseTag_injective : Function.Injective phaseTag := by intro a b;cases a <;> cases b <;> simp [phaseTag]

variable {q : ℕ} [NeZero q] {a b : Expr (ι:=ι)} {v : ι → ℕ} {c d : Cell q}
variable (ha : evaluate a v=cellRecord c) (hb : evaluate b v=cellRecord d)
include ha
lemma first_exact : (first a).eval v≠0 ↔ c.skeleton.first := by
  cases hp : c.skeleton.pos <;>
    simp [first,represent_int ha,cellRecord,integers,Skeleton.first,Cell.pos,hp,
      positionTag,positionIndex,Cell.metadata]
omit [NeZero q] in
lemma last_exact : (last a).eval v≠0 ↔ c.skeleton.last := by
  cases hp : c.skeleton.pos <;>
    simp [last,represent_int ha,cellRecord,integers,Skeleton.last,Cell.pos,hp,
      positionTag,Cell.metadata]
omit [DecidableEq ι] [NeZero q] in
lemma marker_exact (m : Marker) : (hasMarker a m).eval v≠0 ↔ c.marker=m := by
  simp [hasMarker,represent_int ha,cellRecord,integers,markerTag_injective.eq_iff]
omit [DecidableEq ι] [NeZero q] in
lemma phase_exact (p : Phase) : (hasPhase a p).eval v≠0 ↔ c.head.phase=p := by
  simp [hasPhase,represent_int ha,cellRecord,integers,phaseTag_injective.eq_iff]
omit [DecidableEq ι] in
lemma core_exact : (isCore a).eval v≠0 ↔ c.isCore := by
  cases hp : c.skeleton.pos <;> simp [isCore,represent_int ha,cellRecord,integers,Cell.isCore,Cell.pos,hp,positionTag]
omit [DecidableEq ι] in
lemma palette_exact : (isPalette a).eval v≠0 ↔ c.isPalette := by
  cases hp : c.skeleton.pos <;> simp [isPalette,represent_int ha,cellRecord,integers,Cell.isPalette,Cell.pos,hp,positionTag]
omit [DecidableEq ι] [NeZero q] in
lemma stop_exact : (isStop a).eval v≠0 ↔ c.pos=.stop := by
  cases hp : c.skeleton.pos <;> simp [isStop,represent_int ha,cellRecord,integers,Cell.pos,hp,positionTag]
omit [DecidableEq ι] [NeZero q] in
lemma head_exact : (hasHead a).eval v≠0 ↔ Skeleton.IsHead c.skeleton := by
  simp only [hasHead,Formula.or_ne_zero,marker_exact ha,Skeleton.IsHead,Cell.marker]
omit [NeZero q] in
lemma endpoint_exact : (endpoint a).eval v≠0 ↔ Cell.endpoint c.head.phase := by
  simp only [endpoint,Formula.any_ne_zero,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false,exists_eq_or_imp,exists_eq_left,phase_exact ha,Cell.endpoint]
lemma admissible_exact : (admissible a).eval v≠0 ↔ c.skeleton.Admissible := by
  simp [admissible,first_exact ha,last_exact ha,marker_exact ha,Skeleton.Admissible,Cell.marker]
lemma leftExternal_exact : (leftExternal a).eval v≠0 ↔ c.skeleton.leftExternal := by
  simp only [leftExternal,Formula.or_ne_zero,Formula.and_ne_zero,Formula.neg_ne_zero,first_exact ha,marker_exact ha,Skeleton.leftExternal,Cell.marker]
omit [NeZero q] in
lemma rightExternal_exact : (rightExternal a).eval v≠0 ↔ c.skeleton.rightExternal := by
  simp only [rightExternal,Formula.or_ne_zero,Formula.and_ne_zero,Formula.neg_ne_zero,last_exact ha,marker_exact ha,Skeleton.rightExternal,Cell.marker]
include hb
omit [DecidableEq ι] [NeZero q] in
lemma acceptsLeft_exact : (acceptsLeft a b).eval v≠0 ↔ c.skeleton.acceptsLeft d.marker := by
  change (if (hasMarker a .right).eval v=0 then (hasMarker b .left).eval v else
    (or (hasMarker b .full) (hasMarker b .right)).eval v)≠0 ↔ _
  by_cases h : c.skeleton.marker=.right
  · have H := (marker_exact ha .right).mpr h
    simp only [H,ite_false,ite_true,Formula.or_ne_zero,marker_exact hb,Skeleton.acceptsLeft,Cell.marker,h]
  · have H : (hasMarker a .right).eval v=0 := not_not.mp (mt (marker_exact ha .right).mp h)
    simp [H,marker_exact hb,Skeleton.acceptsLeft,Cell.marker,h]
omit [NeZero q] in
lemma acceptsRight_exact : (acceptsRight a b).eval v≠0 ↔ c.skeleton.acceptsRight d.marker := by
  change (if (hasMarker a .left).eval v=0 then (hasMarker b .right).eval v else
    (any [hasMarker b .left,hasMarker b .boundary,hasMarker b .full]).eval v)≠0 ↔ _
  by_cases h : c.skeleton.marker=.left
  · have H := (marker_exact ha .left).mpr h
    simp only [H,ite_false,ite_true,marker_exact hb,Skeleton.acceptsRight,Cell.marker,h,Formula.any_ne_zero,List.mem_cons,List.not_mem_nil,or_false,exists_eq_or_imp,exists_eq_left]
  · have H : (hasMarker a .left).eval v=0 := not_not.mp (mt (marker_exact ha .left).mp h)
    simp only [H,ite_false,ite_true,marker_exact hb,Skeleton.acceptsRight,Cell.marker,h]
lemma structural_exact (Q : Formula ι) (hQ : Q.eval v=q) :
    (structural a b Q).eval v≠0 ↔ Skeleton.Structural c.skeleton d.skeleton := by
  simp only [structural,any_ne_zero,all_ne_zero,List.mem_cons,List.not_mem_nil,or_false,
    exists_eq_or_imp,exists_eq_left,forall_eq_or_imp,forall_eq,and_ne_zero,core_exact ha,core_exact hb,palette_exact ha,
    palette_exact hb,stop_exact ha,stop_exact hb,equal_ne_zero,Formula.constant_eval,Formula.add_eval,represent_int ha,
    represent_int hb,hQ,cellRecord,integers]
  cases hp : c.skeleton.pos <;> cases hr : d.skeleton.pos <;>
    simp [Cell.isCore,Cell.isPalette,hp,hr,positionIndex,Skeleton.Structural,Cell.pos]
lemma internal_exact : (internal a b).eval v≠0 ↔ Skeleton.Internal c.skeleton d.skeleton := by
  have B : (Formula.branch (isStop a)
      (equal (.add (a.1 4) (.constant 1)) (b.1 4)) (equal (a.1 4) (b.1 4))).eval v≠0 ↔
      (if c.pos=.stop then c.metadata.block.val+1=d.metadata.block.val
        else c.metadata.block.val=d.metadata.block.val) := by
    change (if (isStop a).eval v=0 then (equal (a.1 4) (b.1 4)).eval v
      else (equal (.add (a.1 4) (.constant 1)) (b.1 4)).eval v)≠0 ↔ _
    by_cases hp : c.pos=.stop
    · have HS := (stop_exact ha).mpr hp
      simp [HS,hp,represent_int ha,represent_int hb,cellRecord,integers]
    · have HS : (isStop a).eval v=0 := not_not.mp (mt (stop_exact ha).mp hp)
      simp [HS,hp,represent_int ha,represent_int hb,cellRecord,integers]
  simp only [internal,Formula.all_ne_zero,List.mem_cons,List.not_mem_nil,or_false,
    forall_eq_or_imp,forall_eq,Formula.equal_ne_zero,B,Formula.neg_ne_zero]
  simp [represent_int ha,represent_int hb,represent_flag ha,represent_flag hb,cellRecord,integers,flags,
    boolean_injective.eq_iff,first_exact hb,last_exact ha,Skeleton.Internal,Cell.metadata,Cell.pos]
  simp only [Fin.ext_iff]
  rfl
lemma skeletonPair_exact (Q : Formula ι) (hQ : Q.eval v=q) :
    (skeletonPair a b Q).eval v≠0 ↔ Skeleton.Pair c.skeleton d.skeleton := by
  simp only [skeletonPair,Formula.and_ne_zero,Formula.or_ne_zero,Formula.all_ne_zero,Formula.neg_ne_zero,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,structural_exact ha hb Q hQ,rightExternal_exact ha,leftExternal_exact hb,
    acceptsRight_exact ha hb,acceptsLeft_exact hb ha,internal_exact ha hb,Skeleton.Pair,Cell.marker]
end SourceBurnside.CellFormula

namespace SourceBurnside.CellRepr
open FiniteTable FiniteTable.Codec
@[simp] lemma bit_false_iff (x : ZMod 2) : bit x=false ↔ x=0 := by
  constructor
  · intro H
    have HH := congrArg unbit H
    rw [unbit_bit] at HH
    exact HH
  · rintro rfl;rfl
@[simp] lemma bit_true_iff (x : ZMod 2) : bit x=true ↔ x=1 := by
  constructor
  · intro H
    have HH := congrArg unbit H
    rw [unbit_bit] at HH
    exact HH
  · rintro rfl;rfl
@[simp] lemma boolean_bit_zero_iff (x : ZMod 2) : boolean (bit x)=0 ↔ x=0 := by simp
@[simp] lemma boolean_bit_one_iff (x : ZMod 2) : boolean (bit x)=1 ↔ x=1 := by simp
lemma boolean_bit_add (x y : ZMod 2) :
    boolean (bit (x+y))=(boolean (bit x)+boolean (bit y))%2 := by
  fin_cases x <;> fin_cases y <;> decide
end SourceBurnside.CellRepr

namespace SourceBurnside.Structured.Device.Formula
variable {ι : Type}
@[simp↓] lemma le_ne_zero (a b : Formula ι) (v : ι → ℕ) :
    (Formula.le a b).eval v≠0 ↔ a.eval v≤b.eval v := by simp [eval]
@[simp↓] lemma less_ne_zero (a b : Formula ι) (v : ι → ℕ) :
    (less a b).eval v≠0 ↔ a.eval v<b.eval v := by simp [less_eval]
attribute [-simp] less_eval
end SourceBurnside.Structured.Device.Formula

namespace SourceBurnside.CellFormula
section
open LocalSyntax FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} [DecidableEq ι]
def regZero (a : Expr (ι:=ι)) : Formula ι :=
  all [equal (a.2 5) (.constant 0),equal (a.2 6) (.constant 0),equal (a.2 7) (.constant 0)]
def headZero (a : Expr (ι:=ι)) : Formula ι :=
  all [equal (a.2 1) (.constant 0),equal (a.1 7) (.constant 0),hasPhase a .acquisition,regZero a]
def metaZero (a : Expr (ι:=ι)) : Formula ι :=
  and (equal (a.1 3) (.constant 0)) (equal (a.2 0) (.constant 0))
def dataZero (a : Expr (ι:=ι)) : Formula ι :=
  and (equal (a.2 2) (.constant 0)) (equal (a.2 3) (.constant 0))
def checkerIdle (a : Expr (ι:=ι)) : Formula ι := equal (a.1 5) (.constant 0)
def checkerPassed (a : Expr (ι:=ι)) : Formula ι := equal (a.1 5) (.constant 1)
def checkerHead (a : Expr (ι:=ι)) : Formula ι := equal (a.1 5) (.constant 2)
def headFree (a : Expr (ι:=ι)) : Formula ι := and (neg (hasHead a)) (neg (checkerHead a))
def coreLimit (a : Expr (ι:=ι)) (size : Formula ι) : Formula ι :=
  implies (and (isCore a) (.le size (a.1 1))) (dataZero a)
def formats (a : Expr (ι:=ι)) (size count : Formula ι) : Formula ι := all
  [admissible a,
   implies (neg (isPalette a)) (checkerIdle a),
   coreLimit a size,
   implies (neg (isCore a)) (and (dataZero a) (equal (a.2 4) (.constant 0))),
   implies (hasMarker a .idle) (all [metaZero a,headZero a,equal (a.2 3) (.constant 0),equal (a.2 4) (.constant 0)]),
   implies (or (hasMarker a .left) (hasMarker a .right)) (headZero a),
   implies (hasMarker a .boundary) (all [equal (a.1 7) (.constant 0),hasPhase a .acquisition,regZero a]),
   implies (hasHead a) (implies (equal (a.2 0) (.constant 1)) (equal (a.2 1) (.constant 0))),
   implies (hasMarker a .full) (all [implies (hasPhase a .success) (equal (a.1 7) (.constant 0)),
     implies (neg (hasPhase a .success)) (less (a.1 7) count),implies (endpoint a) (last a)])]

def palettePair (a b : Expr (ι:=ι)) : Formula ι := any
  [and (checkerIdle a) (checkerIdle b),
   all [checkerPassed a,checkerPassed b,equal (a.1 6) (b.1 6)],
   all [checkerPassed a,checkerHead b,equal (a.1 6) (b.1 6)],
   and (checkerHead a) (checkerIdle b)]
def checkerPair (a b : Expr (ι:=ι)) : Formula ι :=
  and (implies (and (isPalette a) (isPalette b)) (palettePair a b))
    (implies (and (isPalette a) (isStop b)) (neg (checkerPassed a)))
def pair (a b : Expr (ι:=ι)) (Q : Formula ι) : Formula ι := and (skeletonPair a b Q) (checkerPair a b)

lemma reg_zero_iff (r : Reg) : r=0 ↔ r 0=0 ∧ r 1=0 ∧ r 2=0 := by
  constructor
  · rintro rfl;simp
  · intro h;funext i;fin_cases i <;> simp_all
lemma data_zero_iff (f : Bool → ZMod 2) : f=0 ↔ f false=0 ∧ f true=0 := by
  constructor
  · rintro rfl;simp
  · intro h;funext i;cases i <;> simp_all
lemma meta_zero_iff (m : Meta) : m=defaultMeta ↔ m.arity=0 ∧ m.zeroTask=false := by
  constructor
  · rintro rfl;simp [defaultMeta]
  · rcases m with ⟨arity,task,block⟩;dsimp only
    rintro ⟨rfl,rfl⟩
    have H : block=0 := by
      apply Fin.ext
      have HB := block.isLt
      norm_num at HB ⊢
    subst block;rfl
lemma head_zero_iff {q : ℕ} [NeZero q] (h : Head q) : h=defaultHead ↔
    h.side=false ∧ h.clause=0 ∧ h.phase=.acquisition ∧ h.reg=0 := by
  cases h;simp [defaultHead,Head.mk.injEq]

variable {q : ℕ} [NeZero q] {a b : Expr (ι:=ι)} {v : ι → ℕ} {c d : Cell q}
variable (ha : evaluate a v=cellRecord c) (hb : evaluate b v=cellRecord d)
include ha
omit [NeZero q] in
lemma regZero_exact : (regZero a).eval v≠0 ↔ c.head.reg=0 := by
  simp only [regZero,Formula.all_ne_zero,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    Formula.equal_ne_zero,Formula.constant_eval]
  simp [represent_flag ha,cellRecord,flags,reg_zero_iff]
omit [DecidableEq ι] [NeZero q] in
lemma dataZero_exact : (dataZero a).eval v≠0 ↔ c.data=0 := by
  simp only [dataZero,Formula.and_ne_zero,Formula.equal_ne_zero,Formula.constant_eval]
  simp [represent_flag ha,cellRecord,flags,data_zero_iff]
omit [DecidableEq ι] [NeZero q] in
lemma metaZero_exact : (metaZero a).eval v≠0 ↔ c.metadata=defaultMeta := by
  simp only [metaZero,Formula.and_ne_zero,Formula.equal_ne_zero,Formula.constant_eval]
  simp [represent_int ha,represent_flag ha,cellRecord,integers,flags,meta_zero_iff]
lemma headZero_exact : (headZero a).eval v≠0 ↔ c.head=defaultHead := by
  simp only [headZero,Formula.all_ne_zero,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    Formula.equal_ne_zero,Formula.constant_eval,phase_exact ha,regZero_exact ha]
  simp [represent_int ha,represent_flag ha,cellRecord,integers,flags,head_zero_iff]
omit [DecidableEq ι] [NeZero q] in
lemma checkerIdle_exact : (checkerIdle a).eval v≠0 ↔ c.checker=.idle := by
  cases hc : c.checker <;> simp [checkerIdle,represent_int ha,cellRecord,integers,hc,checkerTag]
omit [DecidableEq ι] in
lemma checkerPassed_exact : (checkerPassed a).eval v≠0 ↔ ∃ x,c.checker=.passed x := by
  cases hc : c.checker <;> simp [checkerPassed,represent_int ha,cellRecord,integers,hc,checkerTag]
omit [DecidableEq ι] in
lemma checkerHead_exact : (checkerHead a).eval v≠0 ↔ ∃ x,c.checker=.head x := by
  cases hc : c.checker <;> simp [checkerHead,represent_int ha,cellRecord,integers,hc,checkerTag]
omit [DecidableEq ι] in
lemma headFree_exact : (headFree a).eval v≠0 ↔ c.HeadFree := by
  simp only [headFree,Formula.and_ne_zero,Formula.neg_ne_zero,head_exact ha,checkerHead_exact ha]
  simp [Cell.HeadFree]
omit [DecidableEq ι] in
lemma coreLimit_exact (size : Formula ι) (n : ℕ) (hn : size.eval v=n) :
    (coreLimit a size).eval v≠0 ↔ ∀p,c.pos=.core p → n≤p.val → c.data=0 := by
  simp only [coreLimit,implies_ne_zero,Formula.and_ne_zero,core_exact ha,le_ne_zero,hn,dataZero_exact ha]
  cases hp : c.pos <;>
    simp [represent_int ha,cellRecord,integers,Cell.isCore,hp,positionIndex]
lemma formats_exact (S : Schedule q) (size count : Formula ι) (n : ℕ)
    (hn : size.eval v=n) (hc : count.eval v=(S.count c.metadata.task).val) :
    (formats a size count).eval v≠0 ↔ c.Format S n := by
  simp only [formats,Formula.all_ne_zero,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    implies_ne_zero,Formula.and_ne_zero,Formula.or_ne_zero,Formula.neg_ne_zero,
    admissible_exact ha,checkerIdle_exact ha,core_exact ha,palette_exact ha,coreLimit_exact ha size n hn,
    dataZero_exact ha,marker_exact ha,metaZero_exact ha,headZero_exact ha,head_exact ha,
    phase_exact ha,regZero_exact ha,endpoint_exact ha,last_exact ha,Formula.equal_ne_zero,
    Formula.constant_eval,less_ne_zero,hc]
  simp [represent_int ha,represent_flag ha,cellRecord,integers,flags,Cell.Format]

end

open LocalSyntax FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} [DecidableEq ι]
lemma check_pair_iff {q : ℕ} (x y : Palette.Check (Fin q)) : Palette.Pair x y ↔
    (x=.idle ∧ y=.idle) ∨ (∃z,x=.passed z ∧ y=.passed z) ∨
      (∃z,x=.passed z ∧ y=.head z) ∨ (∃z,x=.head z ∧ y=.idle) := by
  constructor
  · intro h;cases h <;> simp
  · rintro (⟨rfl,rfl⟩ | ⟨z,rfl,rfl⟩ | ⟨z,rfl,rfl⟩ | ⟨z,rfl,rfl⟩)
    · exact .idle
    · exact .passed z
    · exact .next z
    · exact .rest z

def passedOwn (a : Expr (ι:=ι)) : Formula ι :=
  all [isPalette a,checkerPassed a,equal (a.1 1) (a.1 6)]
def duplicate (a b : Expr (ι:=ι)) : Formula ι :=
  all [isPalette a,isPalette b,equal (a.1 1) (b.1 1)]
def missing (a b : Expr (ι:=ι)) : Formula ι :=
  all [isPalette a,checkerHead a,isStop b,neg (equal (a.1 1) (a.1 6))]
def semanticZero (a : Expr (ι:=ι)) (truth : Formula ι) : Formula ι :=
  and (hasMarker a .full) (any
    [and (any [hasPhase a .acquisition,hasPhase a .finish,hasPhase a .success]) (neg (regZero a)),
     and (hasPhase a .afterGate) (equal truth (.constant 0)),
     and (hasPhase a .success) (equal (a.2 0) (.constant 1))])
def unaryZero (a : Expr (ι:=ι)) (size count truth : Formula ι) : Formula ι :=
  any [neg (formats a size count),semanticZero a truth,passedOwn a]
def binaryZero (a b : Expr (ι:=ι)) (Q : Formula ι) : Formula ι :=
  any [neg (pair a b Q),duplicate a b,missing a b]

variable {q : ℕ} [NeZero q] {a b : Expr (ι:=ι)} {v : ι → ℕ} {c d : Cell q}
variable (ha : evaluate a v=cellRecord c) (hb : evaluate b v=cellRecord d)
include ha hb
lemma palettePair_exact : (palettePair a b).eval v≠0 ↔ Palette.Pair c.checker d.checker := by
  rw [check_pair_iff]
  simp only [palettePair,Formula.any_ne_zero,Formula.all_ne_zero,Formula.and_ne_zero,
    List.mem_cons,List.not_mem_nil,or_false,exists_eq_or_imp,exists_eq_left,forall_eq_or_imp,forall_eq,
    checkerIdle_exact ha,checkerIdle_exact hb,checkerPassed_exact ha,checkerPassed_exact hb,
    checkerHead_exact ha,checkerHead_exact hb,Formula.equal_ne_zero]
  cases hc : c.checker <;> cases hd : d.checker <;>
    simp [represent_int ha,represent_int hb,cellRecord,integers,hc,hd,checkerIndex]
  all_goals simp only [Fin.ext_iff]
  all_goals exact eq_comm
lemma checkerPair_exact : (checkerPair a b).eval v≠0 ↔ CheckerPair c d := by
  have HL : (¬∃ x,c.checker=.passed x) ↔ Palette.LastOK c.checker := by
    cases c.checker <;> simp [Palette.LastOK]
  simp only [checkerPair,Formula.and_ne_zero,implies_ne_zero,Formula.neg_ne_zero,
    palette_exact ha,palette_exact hb,stop_exact hb,palettePair_exact ha hb,checkerPassed_exact ha,HL,CheckerPair]
lemma pair_exact (Q : Formula ι) (hQ : Q.eval v=q) :
    (pair a b Q).eval v≠0 ↔ Pair c d := by
  simp only [pair,Formula.and_ne_zero,skeletonPair_exact ha hb Q hQ,checkerPair_exact ha hb,Pair]
omit hb in
lemma passedOwn_exact : (passedOwn a).eval v≠0 ↔ ∃x,c.pos=.palette x ∧ c.checker=.passed x := by
  simp only [passedOwn,Formula.all_ne_zero,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    palette_exact ha,checkerPassed_exact ha,Formula.equal_ne_zero]
  cases hp : c.pos <;> cases hc : c.checker <;>
    simp [represent_int ha,cellRecord,integers,hp,hc,Cell.isPalette,checkerIndex,positionIndex]
  simp only [Fin.ext_iff]
  exact eq_comm
lemma duplicate_exact : (duplicate a b).eval v≠0 ↔ ∃x,c.pos=.palette x ∧ d.pos=.palette x := by
  simp only [duplicate,Formula.all_ne_zero,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    palette_exact ha,palette_exact hb,Formula.equal_ne_zero]
  cases hp : c.pos <;> cases hr : d.pos <;>
    simp [represent_int ha,represent_int hb,cellRecord,integers,hp,hr,Cell.isPalette,positionIndex]
  simp only [Fin.ext_iff]
  exact eq_comm
lemma missing_exact : (missing a b).eval v≠0 ↔
    ∃ x y,c.pos=.palette x ∧ c.checker=.head y ∧ d.pos=.stop ∧ x≠y := by
  simp only [missing,Formula.all_ne_zero,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    palette_exact ha,checkerHead_exact ha,stop_exact hb,Formula.neg_ne_zero,Formula.equal_ne_zero]
  cases hp : c.pos <;> cases hc : c.checker <;>
    simp [represent_int ha,cellRecord,integers,hp,hc,Cell.isPalette,checkerIndex,positionIndex]
  simp only [Fin.ext_iff]
  simp
omit hb [NeZero q] in
lemma semanticZero_exact (S : Schedule q) (truth : Formula ι)
    (ht : truth.eval v=boolean ((S.clause c.metadata.task c.head.clause).truth c.head.reg)) :
    (semanticZero a truth).eval v≠0 ↔ SemanticZero S c := by
  simp only [semanticZero,Formula.and_ne_zero,Formula.any_ne_zero,Formula.neg_ne_zero,
    List.mem_cons,List.not_mem_nil,or_false,exists_eq_or_imp,exists_eq_left,
    marker_exact ha,phase_exact ha,regZero_exact ha,Formula.equal_ne_zero,Formula.constant_eval,ht]
  simp [represent_flag ha,cellRecord,flags,SemanticZero]
lemma binaryZero_exact (Q : Formula ι) (hQ : Q.eval v=q) :
    (binaryZero a b Q).eval v≠0 ↔ BinaryZero c d := by
  simp only [binaryZero,Formula.any_ne_zero,Formula.neg_ne_zero,List.mem_cons,List.not_mem_nil,
    or_false,exists_eq_or_imp,exists_eq_left,pair_exact ha hb Q hQ,duplicate_exact ha hb,
    missing_exact ha hb,BinaryZero]
end SourceBurnside.CellFormula

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Formulas_ClauseEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w
namespace SourceBurnside.Addressable

namespace Layout
variable {β g T W : ℕ}

def family : ClauseIndex (β:=β) (g:=g) (T:=T) (W:=W) → ℕ
  | .inl (.inl (.inl _)) => 0
  | .inl (.inl (.inr _)) => 1
  | .inl (.inr _) => 2
  | .inr _ => 3

def coordinates : ClauseIndex (β:=β) (g:=g) (T:=T) (W:=W) → ℕ × ℕ × ℕ
  | .inl (.inl (.inl ((j,r),k))) => (j.val,r.val,k.val)
  | .inl (.inl (.inr ((t,k),r))) => (t.val,k.val,r.val)
  | .inl (.inr ((t,j),v)) => (t.val,j.val,v.val)
  | .inr r => (0,0,r.val)

def directIndex (β g T W i : ℕ) : ℕ × (ℕ × ℕ × ℕ) :=
  let A := 2*β*W
  let B := 2*β*(T-1)
  let C := (3*g+2*β)*(W-2)*(T-1)
  if i<A then (0,((i/2)/β,(i/2)%β,i%2))
  else if i<A+B then
    let p := i-A
    (1,((p/β)/2,(p/β)%2,p%β))
  else if i<A+B+C then
    let p := i-A-B
    (2,((p/(3*g+2*β))/(W-2),(p/(3*g+2*β))%(W-2),p%(3*g+2*β)))
  else (3,(0,0,i-A-B-C))

lemma natural_unpair (a b k l : ℕ) (hk : k<a) (hl : l<b) :
    (b*k+l)/b=k ∧ (b*k+l)%b=l ∧ b*k+l<b*a := by
  have hb : 0<b := by omega
  constructor
  · rw [Nat.add_comm,Nat.add_mul_div_left _ _ hb]
    simp [Nat.div_eq_of_lt hl]
  constructor
  · simp [Nat.add_mod,Nat.mod_eq_of_lt hl]
  · nlinarith

lemma clause_index_direct (j : ClauseIndex (β:=β) (g:=g) (T:=T) (W:=W)) :
    directIndex β g T W (clauseEquiv j).val=(family j,coordinates j) := by
  cases j with
  | inl j => cases j with
    | inl j => cases j with
      | inl j =>
        rcases j with ⟨⟨a,b⟩,c⟩
        have h1 := natural_unpair W β a.val b.val a.isLt b.isLt
        have h2 := natural_unpair (β*W) 2 (β*a.val+b.val) c.val h1.2.2 c.isLt
        have hc : (clauseEquiv (β:=β) (g:=g) (T:=T) (W:=W) (Sum.inl (Sum.inl (Sum.inl ((a,b),c))))).val=2*(β*a.val+b.val)+c.val := by
          change (tripleEquiv W β 2 ((a,b),c)).val=_
          exact tripleEquiv_val W β 2 ((a,b),c)
        rw [hc]
        have hb : 2*(β*a.val+b.val)+c.val<2*β*W := by nlinarith [h2.2.2]
        simp [directIndex,hb,h2.1,h2.2.1,h1.1,h1.2.1,family,coordinates]
      | inr j =>
        rcases j with ⟨⟨a,b⟩,c⟩
        have h1 := natural_unpair (T-1) 2 a.val b.val a.isLt b.isLt
        have h2 := natural_unpair (2*(T-1)) β (2*a.val+b.val) c.val h1.2.2 c.isLt
        have hc : (clauseEquiv (β:=β) (g:=g) (T:=T) (W:=W) (Sum.inl (Sum.inl (Sum.inr ((a,b),c))))).val=2*β*W+(β*(2*a.val+b.val)+c.val) := by
          change 2*β*W+(tripleEquiv (T-1) 2 β ((a,b),c)).val=_
          rw [tripleEquiv_val]
        rw [hc]
        have hb : β*(2*a.val+b.val)+c.val<2*β*(T-1) := by nlinarith [h2.2.2]
        simp [directIndex,show ¬2*β*W+(β*(2*a.val+b.val)+c.val)<2*β*W by omega,
          show 2*β*W+(β*(2*a.val+b.val)+c.val)<2*β*W+2*β*(T-1) by omega,
          h2.1,h2.2.1,h1.1,h1.2.1,family,coordinates]
    | inr j =>
      rcases j with ⟨⟨a,b⟩,c⟩
      have h1 := natural_unpair (T-1) (W-2) a.val b.val a.isLt b.isLt
      have h2 := natural_unpair ((W-2)*(T-1)) (3*g+2*β) ((W-2)*a.val+b.val) c.val h1.2.2 c.isLt
      have hc : (clauseEquiv (β:=β) (g:=g) (T:=T) (W:=W) (Sum.inl (Sum.inr ((a,b),c)))).val=2*β*W+2*β*(T-1)+((3*g+2*β)*((W-2)*a.val+b.val)+c.val) := by
        change 2*β*W+2*β*(T-1)+(tripleEquiv (T-1) (W-2) (3*g+2*β) ((a,b),c)).val=_
        rw [tripleEquiv_val]
      rw [hc]
      have hb : (3*g+2*β)*((W-2)*a.val+b.val)+c.val<(3*g+2*β)*(W-2)*(T-1) := by nlinarith [h2.2.2]
      have hsub : 2*β*W+2*β*(T-1)+((3*g+2*β)*((W-2)*a.val+b.val)+c.val)-2*β*W-2*β*(T-1)=
          (3*g+2*β)*((W-2)*a.val+b.val)+c.val := by omega
      simp [directIndex,show ¬2*β*W+2*β*(T-1)+((3*g+2*β)*((W-2)*a.val+b.val)+c.val)<2*β*W by omega,
        show ¬2*β*W+2*β*(T-1)+((3*g+2*β)*((W-2)*a.val+b.val)+c.val)<2*β*W+2*β*(T-1) by omega,
        show 2*β*W+2*β*(T-1)+((3*g+2*β)*((W-2)*a.val+b.val)+c.val)<2*β*W+2*β*(T-1)+(3*g+2*β)*(W-2)*(T-1) by omega,
        hsub,h2.1,h2.2.1,h1.1,h1.2.1,family,coordinates]
  | inr r =>
    have hc : (clauseEquiv (β:=β) (g:=g) (T:=T) (W:=W) (Sum.inr r)).val=2*β*W+2*β*(T-1)+(3*g+2*β)*(W-2)*(T-1)+r.val := by rfl
    rw [hc]
    simp only [directIndex,family,coordinates]
    rw [ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_right (by omega)]
    congr 3; omega

theorem clause_index_lookup (i : Fin (Tableau.Layout.clauseCount β g T W)) :
    directIndex β g T W i.val=(family (clauseEquiv.symm i),coordinates (clauseEquiv.symm i)) := by
  simpa only [Equiv.apply_symm_apply] using clause_index_direct (clauseEquiv.symm i)

end Layout
end SourceBurnside.Addressable

namespace SourceBurnside.AddressFormula
open LocalSyntax FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} [DecidableEq ι]
abbrev Expr := Fin 4 → Formula ι
def record {q : ℕ} : Address q → Fin 4 → ℕ
  | .data s b p => ![0,boolean s,b.val,p.val]
  | .certificate p => ![1,0,0,p.val]
def evaluate (a : Expr (ι:=ι)) (v : ι → ℕ) : Fin 4 → ℕ := fun i => (a i).eval v

def data (s b p : Formula ι) : Expr (ι:=ι) := ![.constant 0,s,b,p]
def certificate (p : Formula ι) : Expr (ι:=ι) := ![.constant 1,.constant 0,.constant 0,p]
omit [DecidableEq ι] in
lemma data_exact {q : ℕ} (s b p : Formula ι) (v : ι → ℕ) (S : Bool) (B : Fin 10) (P : Fin q)
    (hs : s.eval v=boolean S) (hb : b.eval v=B.val) (hp : p.eval v=P.val) :
    evaluate (data s b p) v=record (.data S B P) := by
  funext i;fin_cases i <;> simp [evaluate,data,record,hs,hb,hp]
omit [DecidableEq ι] in
lemma certificate_exact {q : ℕ} (p : Formula ι) (v : ι → ℕ) (P : Fin q) (hp : p.eval v=P.val) :
    evaluate (certificate p) v=record (.certificate P) := by
  funext i;fin_cases i <;> simp [evaluate,certificate,record,hp]

def readAt (a : Expr (ι:=ι)) (c : CellFormula.Expr (ι:=ι)) : Formula ι :=
  .branch (all [CellFormula.isCore c,equal (c.1 1) (a 3),equal (c.1 4) (a 2)])
    (.branch (a 0) (c.2 4) (.branch (a 1) (c.2 3) (c.2 2))) (.constant 0)

lemma readAt_exact {q : ℕ} [NeZero q] {a : Expr (ι:=ι)} {c : CellFormula.Expr (ι:=ι)}
    {v : ι → ℕ} {A : Address q} {C : Cell q}
    (ha : evaluate a v=record A) (hc : CellFormula.evaluate c v=cellRecord C) :
    (readAt a c).eval v=boolean (bit (C.read A)) := by
  have ha' (i : Fin 4) : (a i).eval v=record A i := congrFun ha i
  have hzero : (all [CellFormula.isCore c,equal (c.1 1) (a 3),equal (c.1 4) (a 2)]).eval v=0 ↔
      ¬(C.isCore ∧ (cellRecord C).1 1=record A 3 ∧ (cellRecord C).1 4=record A 2) := by
    rw [←not_iff_not];simp only [not_not,Formula.all_ne_zero,List.mem_cons,List.not_mem_nil,or_false,
      forall_eq_or_imp,forall_eq,CellFormula.core_exact hc,Formula.equal_ne_zero,CellFormula.represent_int hc,ha']
  simp only [readAt,Formula.eval,hzero,ha',CellFormula.represent_flag hc]
  cases A <;> cases hp : C.pos <;>
    simp [Cell.read,hp,record,cellRecord,integers,flags,Cell.isCore,positionIndex,boolean]
  all_goals simp only [Fin.ext_iff]
  all_goals split_ifs <;> simp_all
end SourceBurnside.AddressFormula

namespace SourceBurnside.InitialFormula
section
open FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} [DecidableEq ι]

def binSize (n : ℕ) := if n=0 then 1 else n.size
def bin (n : ℕ) : List Bool := List.ofFn (fun i : Fin (binSize n) => n.testBit (binSize n-1-i.val))
def enc (n : ℕ) : List Bool := List.replicate (binSize n) true ++ false::bin n
@[simp] lemma bin_length (n : ℕ) : (bin n).length=binSize n := by simp [bin]
@[simp] lemma enc_length (n : ℕ) : (enc n).length=2*binSize n+1 := by simp [enc];omega
@[simp] lemma bin_zero : bin 0=[false] := by decide

end

open FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
end SourceBurnside.InitialFormula

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Formulas_LocalPredicates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w

namespace SourceBurnside.CellFormula
section
open LocalSyntax FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} [DecidableEq ι]
def side (a : Expr (ι:=ι)) : Formula ι := a.2 1
def clause (a : Expr (ι:=ι)) : Formula ι := a.1 7
def register (a : Expr (ι:=ι)) (i : Fin 3) : Formula ι := a.2 ⟨i.val+5,by omega⟩
def zeroReg : Fin 3 → Formula ι := fun _ => .constant 0

section Accessors
variable {q : ℕ} {a : Expr (ι:=ι)} {v : ι → ℕ} {c : Cell q}
variable (ha : evaluate a v=cellRecord c)
include ha
omit [DecidableEq ι] in
lemma side_exact : (side a).eval v=boolean c.head.side := by
  simpa [side,cellRecord,flags] using represent_flag ha 1
omit [DecidableEq ι] in
lemma clause_exact : (clause a).eval v=c.head.clause.val := by
  simpa [clause,cellRecord,integers] using represent_int ha 7
omit [DecidableEq ι] in
lemma register_exact (i : Fin 3) : (register a i).eval v=boolean (bit (c.head.reg i)) := by
  fin_cases i
  · exact represent_flag ha 5
  · exact represent_flag ha 6
  · exact represent_flag ha 7
omit [DecidableEq ι] in
lemma notSide_exact : (neg (side a)).eval v=boolean (!c.head.side) := by
  simp only [neg_eval,side_exact ha];cases c.head.side <;> rfl
end Accessors

omit [DecidableEq ι] in
lemma zeroReg_exact (v : ι → ℕ) (i : Fin 3) : (zeroReg i).eval v=boolean (bit ((0:Reg) i)) := rfl
omit [DecidableEq ι] in
lemma zeroClause_exact {q : ℕ} [NeZero q] (v : ι → ℕ) :
    (.constant 0 : Formula ι).eval v=(0:Fin q).val := rfl
lemma equals_exact {h : ℕ} (hh : 4≤h) {a b : Expr (ι:=ι)} {v : ι → ℕ}
    {c d : Cell (2^h)} (ha : evaluate a v=cellRecord c) (hb : evaluate b v=cellRecord d) :
    (equalCells a b).eval v≠0 ↔ c=d := by
  have H := equalCells_bool a b v
  rw [← equality_exact hh a b v c d ha hb];omega

end

open LocalSyntax FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} [DecidableEq ι]
def addReg (r t : Fin 3 → Formula ι) : Fin 3 → Formula ι :=
  fun i => .mod (.add (r i) (t i)) (.constant 2)
omit [DecidableEq ι] in
lemma addReg_exact {r t : Fin 3 → Formula ι} {v : ι → ℕ} {R T : Reg}
    (hr : ∀i,(r i).eval v=boolean (bit (R i))) (ht : ∀i,(t i).eval v=boolean (bit (T i))) (i : Fin 3) :
    (addReg r t i).eval v=boolean (bit ((R+T) i)) := by
  simp only [addReg,Formula.eval,hr,ht,Pi.add_apply,boolean_bit_add]

def acquireMove (a b a' b' : Expr (ι:=ι)) (Q : Formula ι) : Formula ι := all
  [skeletonPair (wing a .left) (wing b' .boundary) Q,
   equalCells a (boundary a (side a)),equalCells b (idle b' (side a)),
   equalCells a' (wing a .left),equalCells b' (boundary b' (side a))]
def readLeftMove (a b a' b' : Expr (ι:=ι)) (Q : Formula ι) (delta : Fin 3 → Formula ι) : Formula ι := all
  [skeletonPair (wing a .full) (wing b .right) Q,
   equalCells a (wing a .left),equalCells b (full b (side b) (clause b) .readLeft (register b)),
   equalCells a' (full a (side b) (clause b) .readLeft (addReg (register b) delta)),equalCells b' (wing b .right)]
def readRightMove (a b a' b' : Expr (ι:=ι)) (Q : Formula ι) : Formula ι := all
  [skeletonPair (wing a .full) (wing b .right) Q,
   equalCells a (full a (side a) (clause a) .readRight (register a)),equalCells b (wing b .right),
   equalCells a' (wing a .left),equalCells b' (full b (side a) (clause a) .readRight (register a))]
def undoLeftMove (a b a' b' : Expr (ι:=ι)) (Q : Formula ι) : Formula ι := all
  [skeletonPair (wing a .full) (wing b .right) Q,
   equalCells a (wing a .left),equalCells b (full b (side b) (clause b) .undoLeft (register b)),
   equalCells a' (full a (side b) (clause b) .undoLeft (register b)),equalCells b' (wing b .right)]
def undoRightMove (a b a' b' : Expr (ι:=ι)) (Q : Formula ι) (delta : Fin 3 → Formula ι) : Formula ι := all
  [skeletonPair (wing a .full) (wing b .right) Q,
   equalCells a (full a (side a) (clause a) .undoRight (register a)),equalCells b (wing b .right),
   equalCells a' (wing a .left),equalCells b' (full b (side a) (clause a) .undoRight (addReg (register a) delta))]
def checkerCreateMove (a b a' b' : Expr (ι:=ι)) (Q : Formula ι) : Formula ι := all
  [equalCells a' a,equalCells b (setChecker b' (.constant 0) (.constant 0)),
   isCore a,isPalette b',checkerHead b',equal (.add (a.1 1) (.constant 1)) Q]
def checkerAdvanceMove (a b a' b' : Expr (ι:=ι)) : Formula ι := all
  [isPalette a,isPalette b,checkerHead a,neg (equal (a.1 1) (a.1 6)),checkerIdle b,
   equalCells a' (setChecker a (.constant 1) (a.1 6)),equalCells b' (setChecker b (.constant 2) (a.1 6))]
def swapMove (a b a' b' : Expr (ι:=ι)) : Formula ι := all
  [isPalette a,isPalette b,equalCells a' b,equalCells b' a,
   equalCells (setColor a (b.1 1)) b,headFree a,headFree b]
def binaryMove (a b a' b' : Expr (ι:=ι)) (Q : Formula ι) (readDelta undoDelta : Fin 3 → Formula ι) : Formula ι := any
  [acquireMove a b a' b' Q,readLeftMove a b a' b' Q readDelta,readRightMove a b a' b' Q,
   undoLeftMove a b a' b' Q,undoRightMove a b a' b' Q undoDelta,checkerCreateMove a b a' b' Q,
   checkerAdvanceMove a b a' b',swapMove a b a' b']

variable {h : ℕ} (hh : 4≤h) {a b a' b' : Expr (ι:=ι)} {v : ι → ℕ} {c d c' d' : Cell (2^h)}
variable (ha : evaluate a v=cellRecord c) (hb : evaluate b v=cellRecord d)
variable (ha' : evaluate a' v=cellRecord c') (hb' : evaluate b' v=cellRecord d')
variable (Q : Formula ι) (hQ : Q.eval v=2^h)
include hh ha hb ha' hb' hQ
lemma acquireMove_exact : (acquireMove a b a' b' Q).eval v≠0 ↔ Recognizer.AcquireTest c d c' d' := by
  simp only [acquireMove,Formula.all_ne_zero,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    skeletonPair_exact (wing_represents ha .left) (wing_represents hb' .boundary) Q hQ,
    equals_exact hh ha (boundary_represents ha _ _ (side_exact ha)),
    equals_exact hh hb (idle_represents hb' _ _ (side_exact ha)),
    equals_exact hh ha' (wing_represents ha .left),
    equals_exact hh hb' (boundary_represents hb' _ _ (side_exact ha)),Recognizer.AcquireTest,Cell.wing]
lemma readLeftMove_exact (S : Schedule (2^h)) (delta : Fin 3 → Formula ι)
    (hd : ∀i,(delta i).eval v=boolean (bit (c.delta (S.clause c.metadata.task d.head.clause) i))) :
    (readLeftMove a b a' b' Q delta).eval v≠0 ↔ Recognizer.ReadLeftTest S c d c' d' := by
  simp only [readLeftMove,Formula.all_ne_zero,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    skeletonPair_exact (wing_represents ha .full) (wing_represents hb .right) Q hQ,
    equals_exact hh ha (wing_represents ha .left),
    equals_exact hh hb (full_represents hb _ _ _ _ _ _ _ (side_exact hb) (clause_exact hb) (register_exact hb)),
    equals_exact hh ha' (full_represents ha _ _ _ _ _ _ _ (side_exact hb) (clause_exact hb) (addReg_exact (register_exact hb) hd)),
    equals_exact hh hb' (wing_represents hb .right),Recognizer.ReadLeftTest,Cell.wing]
lemma readRightMove_exact : (readRightMove a b a' b' Q).eval v≠0 ↔ Recognizer.ReadRightTest c d c' d' := by
  simp only [readRightMove,Formula.all_ne_zero,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    skeletonPair_exact (wing_represents ha .full) (wing_represents hb .right) Q hQ,
    equals_exact hh ha (full_represents ha _ _ _ _ _ _ _ (side_exact ha) (clause_exact ha) (register_exact ha)),
    equals_exact hh hb (wing_represents hb .right),equals_exact hh ha' (wing_represents ha .left),
    equals_exact hh hb' (full_represents hb _ _ _ _ _ _ _ (side_exact ha) (clause_exact ha) (register_exact ha)),
    Recognizer.ReadRightTest,Cell.wing]
lemma undoLeftMove_exact : (undoLeftMove a b a' b' Q).eval v≠0 ↔ Recognizer.UndoLeftTest c d c' d' := by
  simp only [undoLeftMove,Formula.all_ne_zero,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    skeletonPair_exact (wing_represents ha .full) (wing_represents hb .right) Q hQ,
    equals_exact hh ha (wing_represents ha .left),
    equals_exact hh hb (full_represents hb _ _ _ _ _ _ _ (side_exact hb) (clause_exact hb) (register_exact hb)),
    equals_exact hh ha' (full_represents ha _ _ _ _ _ _ _ (side_exact hb) (clause_exact hb) (register_exact hb)),
    equals_exact hh hb' (wing_represents hb .right),Recognizer.UndoLeftTest,Cell.wing]
lemma undoRightMove_exact (S : Schedule (2^h)) (delta : Fin 3 → Formula ι)
    (hd : ∀i,(delta i).eval v=boolean (bit (c.delta (S.clause c.metadata.task c.head.clause) i))) :
    (undoRightMove a b a' b' Q delta).eval v≠0 ↔ Recognizer.UndoRightTest S c d c' d' := by
  simp only [undoRightMove,Formula.all_ne_zero,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    skeletonPair_exact (wing_represents ha .full) (wing_represents hb .right) Q hQ,
    equals_exact hh ha (full_represents ha _ _ _ _ _ _ _ (side_exact ha) (clause_exact ha) (register_exact ha)),
    equals_exact hh hb (wing_represents hb .right),equals_exact hh ha' (wing_represents ha .left),
    equals_exact hh hb' (full_represents hb _ _ _ _ _ _ _ (side_exact ha) (clause_exact ha) (addReg_exact (register_exact ha) hd)),
    Recognizer.UndoRightTest,Cell.wing]
lemma checkerCreateMove_exact : (checkerCreateMove a b a' b' Q).eval v≠0 ↔ Recognizer.CheckerCreateTest c d c' d' := by
  have hc := setChecker_represents hb' (.constant 0) (.constant 0) Palette.Check.idle rfl rfl
  simp only [checkerCreateMove,Formula.all_ne_zero,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    equals_exact hh ha' ha,equals_exact hh hb hc,core_exact ha,palette_exact hb',checkerHead_exact hb',
    Formula.equal_ne_zero,Formula.add_eval,Formula.constant_eval,hQ]
  cases hp : c.pos <;> cases hd : d'.pos <;> cases hh' : d'.checker <;>
    simp [Recognizer.CheckerCreateTest,Cell.isCore,Cell.isPalette,hp,hd,hh',
      represent_int ha,cellRecord,integers,positionIndex]
omit hQ in
lemma checkerAdvanceMove_exact : (checkerAdvanceMove a b a' b').eval v≠0 ↔ Recognizer.CheckerAdvanceTest c d c' d' := by
  simp only [checkerAdvanceMove,Formula.all_ne_zero,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    palette_exact ha,palette_exact hb,checkerHead_exact ha,checkerIdle_exact hb,Formula.neg_ne_zero,Formula.equal_ne_zero]
  cases hp : c.pos <;> cases hd : d.pos <;> cases hk : c.checker <;>
    simp [Recognizer.CheckerAdvanceTest,Cell.isPalette,hp,hd,hk]
  rename_i x y z
  have hi : (a.1 6).eval v=z.val := by simpa [cellRecord,integers,hk,checkerIndex] using represent_int ha 6
  simp only [← ne_eq]
  rw [equals_exact hh ha' (setChecker_represents ha (.constant 1) _ (.passed z) rfl hi),
    equals_exact hh hb' (setChecker_represents hb (.constant 2) _ (.head z) rfl hi)]
  simp only [represent_int ha,cellRecord,integers,hp,hk,positionIndex,checkerIndex]
  change (x.val≠z.val ∧ _) ↔ (x≠z ∧ _)
  simp only [ne_eq,Fin.val_inj]
omit hQ in
lemma swapMove_exact : (swapMove a b a' b').eval v≠0 ↔ Recognizer.SwapTest c d c' d' := by
  simp only [swapMove,Formula.all_ne_zero,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    palette_exact ha,palette_exact hb,equals_exact hh ha' hb,equals_exact hh hb' ha,headFree_exact ha,headFree_exact hb]
  cases hp : c.pos <;> cases hd : d.pos <;> simp [Recognizer.SwapTest,Cell.isPalette,hp,hd]
  rename_i x y
  have hi : (b.1 1).eval v=y.val := by simpa [cellRecord,integers,hd,positionIndex] using represent_int hb 1
  simp only [← ne_eq]
  rw [equals_exact hh (setColor_represents ha _ _ hi) hb]
  simp
lemma binaryMove_exact (S : Schedule (2^h)) (rd ud : Fin 3 → Formula ι)
    (hrd : ∀i,(rd i).eval v=boolean (bit (c.delta (S.clause c.metadata.task d.head.clause) i)))
    (hud : ∀i,(ud i).eval v=boolean (bit (c.delta (S.clause c.metadata.task c.head.clause) i))) :
    (binaryMove a b a' b' Q rd ud).eval v≠0 ↔ Binary S c d c' d' := by
  rw [show Binary S c d c' d' ↔ Recognizer.BinaryTest S c d c' d' from
    ⟨Recognizer.binary_test,Recognizer.binary_of_test⟩]
  simp only [binaryMove,Formula.any_ne_zero,List.mem_cons,List.not_mem_nil,or_false,exists_eq_or_imp,exists_eq_left,
    acquireMove_exact hh ha hb ha' hb' Q hQ,readLeftMove_exact hh ha hb ha' hb' Q hQ S rd hrd,
    readRightMove_exact hh ha hb ha' hb' Q hQ,undoLeftMove_exact hh ha hb ha' hb' Q hQ,
    undoRightMove_exact hh ha hb ha' hb' Q hQ S ud hud,checkerCreateMove_exact hh ha hb ha' hb' Q hQ,
    checkerAdvanceMove_exact hh ha hb ha' hb',swapMove_exact hh ha hb ha' hb',Recognizer.BinaryTest]
end SourceBurnside.CellFormula

namespace SourceBurnside.Structured.Device.Formula
variable {ι κ : Type} [DecidableEq ι] [DecidableEq κ]
def bind (f : ι → Formula κ) : Formula ι → Formula κ
  | .read i => f i
  | .constant a => .constant a
  | .add x y => .add (x.bind f) (y.bind f)
  | .sub x y => .sub (x.bind f) (y.bind f)
  | .mul x y => .mul (x.bind f) (y.bind f)
  | .div x y => .div (x.bind f) (y.bind f)
  | .mod x y => .mod (x.bind f) (y.bind f)
  | .le x y => .le (x.bind f) (y.bind f)
  | .powTwo x => .powTwo (x.bind f)
  | .bitLength x => .bitLength (x.bind f)
  | .branch c a b => .branch (c.bind f) (a.bind f) (b.bind f)
omit [DecidableEq ι] [DecidableEq κ] in
@[simp] lemma bind_eval (f : ι → Formula κ) (e : Formula ι) (v : κ → ℕ) :
    (e.bind f).eval v=e.eval (fun i => (f i).eval v) := by
  induction e <;> simp_all [bind,eval]
end SourceBurnside.Structured.Device.Formula

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Formulas_PredicateCompilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w

namespace SourceBurnside.Structured.Device.Formula
section
variable {ι : Type}

def totalize : Formula ι → Formula ι
  | .read i => .read i
  | .constant a => .constant a
  | .add x y => .add x.totalize y.totalize
  | .sub x y => .branch (.le y.totalize x.totalize) (.sub x.totalize y.totalize) (.constant 0)
  | .mul x y => .mul x.totalize y.totalize
  | .div x y => .branch (.le (.constant 1) y.totalize) (.div x.totalize y.totalize) (.constant 0)
  | .mod x y => .branch (.le (.constant 1) y.totalize) (.mod x.totalize y.totalize) x.totalize
  | .le x y => .le x.totalize y.totalize
  | .powTwo x => .powTwo x.totalize
  | .bitLength x => .bitLength x.totalize
  | .branch c a b => .branch (.le (.constant 1) c.totalize) a.totalize b.totalize
@[simp] theorem totalize_eval (e : Formula ι) (v : ι → ℕ) : e.totalize.eval v=e.eval v := by
  induction e with
  | read i => rfl
  | constant a => rfl
  | add x y hx hy => simp [totalize,eval,hx,hy]
  | sub x y hx hy =>
    by_cases h : y.eval v≤x.eval v
    · simp [totalize,eval,hx,hy,h]
    · simp [totalize,eval,hx,hy,h,Nat.sub_eq_zero_of_le (show x.eval v≤y.eval v by omega)]
  | mul x y hx hy => simp [totalize,eval,hx,hy]
  | div x y hx hy =>
    by_cases h : y.eval v=0
    · simp [totalize,eval,hy,h]
    · simp [totalize,eval,hx,hy,show 1≤y.eval v by omega]
  | mod x y hx hy =>
    by_cases h : y.eval v=0
    · simp [totalize,eval,hx,hy,h]
    · simp [totalize,eval,hx,hy,show 1≤y.eval v by omega]
  | le x y hx hy => simp [totalize,eval,hx,hy]
  | powTwo x hx => simp [totalize,eval,hx]
  | bitLength x hx => simp [totalize,eval,hx]
  | branch c a b hc ha hb =>
    by_cases h : c.eval v=0
    · simp [totalize,eval,hc,hb,h]
    · simp [totalize,eval,hc,ha,h,show 1 ≤ c.eval v by omega]

end

section
variable {ι : Type}

def Exponents (M : ℕ) (v : ι → ℕ) : Formula ι → Prop
  | .read _ | .constant _ => True
  | .add x y | .sub x y | .mul x y | .div x y | .mod x y | .le x y => x.Exponents M v ∧ y.Exponents M v
  | .powTwo x => x.Exponents M v ∧ x.eval v≤M
  | .bitLength x => x.Exponents M v
  | .branch c a b => c.Exponents M v ∧ (if c.eval v=0 then b.Exponents M v else a.Exponents M v)
end

variable {ι κ : Type} {M : ℕ} {v : ι → ℕ}
@[simp] lemma exponents_constant (a : ℕ) : (constant a : Formula ι).Exponents M v := trivial
@[simp] lemma exponents_read (i : ι) : (read i : Formula ι).Exponents M v := trivial
lemma exponents_branch {c a b : Formula ι} (hc : c.Exponents M v)
    (ha : a.Exponents M v) (hb : b.Exponents M v) : (branch c a b).Exponents M v :=
  ⟨hc,by split <;> assumption⟩
lemma exponents_equal {a b : Formula ι} (ha : a.Exponents M v) (hb : b.Exponents M v) :
    (equal a b).Exponents M v := by
  exact exponents_branch ⟨ha,hb⟩ ⟨hb,ha⟩ (exponents_constant 0)
lemma exponents_neg {a : Formula ι} (ha : a.Exponents M v) : (neg a).Exponents M v :=
  exponents_branch ha (exponents_constant 0) (exponents_constant 1)
lemma exponents_and {a b : Formula ι} (ha : a.Exponents M v) (hb : b.Exponents M v) :
    (and a b).Exponents M v := exponents_branch ha hb (exponents_constant 0)
lemma exponents_all {es : List (Formula ι)} (H : ∀e∈es,e.Exponents M v) : (all es).Exponents M v := by
  induction es with
  | nil => exact exponents_constant 1
  | cons e es ih => exact exponents_and (H e (by simp)) (ih (by intro a ha;exact H a (by simp [ha])))
lemma exponents_bit {a i : Formula ι} (hM : 1≤M) (ha : a.Exponents M v) (hi : i.Exponents M v) (hv : i.eval v≤M) :
    (bitAt a i).Exponents M v := ⟨⟨ha,hi,hv⟩,trivial,hM⟩
lemma exponents_field {a i w : Formula ι} (ha : a.Exponents M v) (hi : i.Exponents M v) (hw : w.Exponents M v)
    (hiv : i.eval v≤M) (hwv : w.eval v≤M) : (field a i w).Exponents M v := ⟨⟨ha,hi,hiv⟩,hw,hwv⟩
end SourceBurnside.Structured.Device.Formula

namespace SourceBurnside.CellFormula
open Structured.Device Structured.Device.Formula
variable {ι : Type}
def Exponents (a : Expr (ι:=ι)) (M : ℕ) (v : ι → ℕ) : Prop :=
  (∀i,(a.1 i).Exponents M v) ∧ (∀i,(a.2 i).Exponents M v)
lemma ofRaw_exponents {H W : Formula ι} {M : ℕ} {v : ι → ℕ}
    (hH : H.Exponents M v) (hW : W.Exponents M v) (hM : 64*H.eval v+8≤M) :
    Exponents (ofRaw H W) M v := by
  constructor
  · intro i
    apply exponents_field
    · exact hW
    · exact ⟨trivial,hH⟩
    · exact ⟨trivial,hH⟩
    · change 2*i.val*H.eval v≤M
      have := i.isLt;nlinarith
    · change 2*H.eval v≤M;omega
  · intro i
    apply exponents_bit
    · omega
    · exact hW
    · exact ⟨⟨trivial,hH⟩,trivial⟩
    · change 64*H.eval v+i.val≤M
      have := i.isLt;omega
end SourceBurnside.CellFormula

namespace SourceBurnside.AddressFormula
open Structured.Device Structured.Device.Formula
variable {ι : Type} {M : ℕ} {v : ι → ℕ}
def Exponents (a : Expr (ι:=ι)) (M : ℕ) (v : ι → ℕ) := ∀i,(a i).Exponents M v
lemma certificate_exponents {a : Formula ι} (ha : a.Exponents M v) : Exponents (certificate a) M v := by
  intro i;fin_cases i <;> simp [certificate,ha]
lemma data_exponents {s b p : Formula ι} (hs : s.Exponents M v) (hb : b.Exponents M v) (hp : p.Exponents M v) :
    Exponents (data s b p) M v := by intro i;fin_cases i <;> simp [data,hs,hb,hp]
end SourceBurnside.AddressFormula

namespace SourceBurnside.CellFormula
open LocalSyntax Structured.Device Structured.Device.Formula
variable {ι : Type} {M : ℕ} {v : ι → ℕ}
lemma equalCells_exponents {a b : Expr (ι:=ι)} (ha : Exponents a M v) (hb : Exponents b M v) :
    (equalCells a b).Exponents M v := by
  apply exponents_and
  · apply exponents_all
    simp only [List.mem_ofFn]
    rintro e ⟨i,rfl⟩
    exact exponents_equal (ha.1 _) (hb.1 _)
  · apply exponents_all
    simp only [List.mem_ofFn]
    rintro e ⟨i,rfl⟩
    exact exponents_equal (ha.2 _) (hb.2 _)
lemma wing_exponents {a : Expr (ι:=ι)} (m : Marker) (ha : Exponents a M v) : Exponents (wing a m) M v := by
  constructor <;> intro i <;> fin_cases i <;> simp [wing,ha.1,ha.2]
lemma boundary_exponents {a : Expr (ι:=ι)} {s : Formula ι} (ha : Exponents a M v) (hs : s.Exponents M v) :
    Exponents (boundary a s) M v := by
  refine ⟨(wing_exponents .boundary ha).1,?_⟩
  intro i;fin_cases i <;> simp [boundary,ha.2,hs]
lemma full_exponents {a : Expr (ι:=ι)} {s j : Formula ι} (p : FiniteTable.Phase) {r : Fin 3 → Formula ι}
    (ha : Exponents a M v) (hs : s.Exponents M v) (hj : j.Exponents M v) (hr : ∀i,(r i).Exponents M v) :
    Exponents (full a s j p r) M v := by
  constructor <;> intro i <;> fin_cases i <;> simp [full,ha.1,ha.2,hs,hj,hr]
lemma idle_exponents {a : Expr (ι:=ι)} {s : Formula ι} (ha : Exponents a M v) (hs : s.Exponents M v) :
    Exponents (idle a s) M v := by
  constructor
  · intro i;fin_cases i <;> simp [idle,ha.1]
  · intro i;fin_cases i <;> simp [idle,Formula.Exponents,hs,ha.2]
lemma setChecker_exponents {a : Expr (ι:=ι)} {tag i : Formula ι}
    (ha : Exponents a M v) (ht : tag.Exponents M v) (hi : i.Exponents M v) : Exponents (setChecker a tag i) M v := by
  refine ⟨?_,ha.2⟩
  intro j;fin_cases j <;> simp [setChecker,ha.1,ht,hi]
lemma setColor_exponents {a : Expr (ι:=ι)} {color : Formula ι}
    (ha : Exponents a M v) (hc : color.Exponents M v) : Exponents (setColor a color) M v := by
  refine ⟨?_,ha.2⟩
  intro j;fin_cases j <;> simp [setColor,ha.1,hc]
lemma formats_exponents {a : Expr (ι:=ι)} {size count : Formula ι}
    (ha : Exponents a M v) (hs : size.Exponents M v) (hc : count.Exponents M v) :
    (formats a size count).Exponents M v := by
  simp [formats,admissible,coreLimit,headZero,metaZero,dataZero,checkerIdle,regZero,
    hasHead,endpoint,hasPhase,hasMarker,first,last,isCore,isPalette,
    all,any,Formula.and,Formula.or,neg,equal,less,implies,Formula.Exponents,ha.1,ha.2,hs,hc]
lemma pair_exponents {a b : Expr (ι:=ι)} {Q : Formula ι}
    (ha : Exponents a M v) (hb : Exponents b M v) (hQ : Q.Exponents M v) :
    (pair a b Q).Exponents M v := by
  simp [pair,skeletonPair,checkerPair,palettePair,structural,internal,acceptsLeft,acceptsRight,leftExternal,rightExternal,
    checkerIdle,checkerPassed,checkerHead,hasMarker,first,last,isCore,isPalette,isStop,
    all,any,Formula.and,Formula.or,neg,equal,implies,Formula.Exponents,ha.1,ha.2,hb.1,hb.2,hQ]
lemma unaryZero_exponents {a : Expr (ι:=ι)} {size count truth : Formula ι}
    (ha : Exponents a M v) (hs : size.Exponents M v) (hc : count.Exponents M v) (ht : truth.Exponents M v) :
    (unaryZero a size count truth).Exponents M v := by
  have hf := formats_exponents ha hs hc
  simp [unaryZero,semanticZero,passedOwn,isPalette,checkerPassed,hasMarker,hasPhase,regZero,
    Formula.or,Formula.and,any,all,neg,equal,Formula.Exponents,ha.1,ha.2,hf,ht]
lemma binaryZero_exponents {a b : Expr (ι:=ι)} {Q : Formula ι}
    (ha : Exponents a M v) (hb : Exponents b M v) (hQ : Q.Exponents M v) :
    (binaryZero a b Q).Exponents M v := by
  have hp := pair_exponents ha hb hQ
  simp [binaryZero,duplicate,missing,checkerHead,isPalette,isStop,
    Formula.or,Formula.and,any,all,neg,equal,Formula.Exponents,ha.1,hb.1,hp]
end SourceBurnside.CellFormula

namespace SourceBurnside.AddressFormula
open Structured.Device Structured.Device.Formula
variable {ι : Type} {M : ℕ} {v : ι → ℕ}
lemma readAt_exponents {a : Expr (ι:=ι)} {c : CellFormula.Expr (ι:=ι)}
    (ha : Exponents a M v) (hc : CellFormula.Exponents c M v) : (readAt a c).Exponents M v := by
  have ha' : ∀i,(a i).Exponents M v := ha
  simp [readAt,CellFormula.isCore,all,Formula.and,equal,Formula.Exponents,ha',hc.1,hc.2]
end SourceBurnside.AddressFormula

namespace SourceBurnside.CellFormula
open LocalSyntax Structured.Device Structured.Device.Formula
variable {ι : Type} {M : ℕ} {v : ι → ℕ}
lemma skeletonPair_exponents {a b : Expr (ι:=ι)} {Q : Formula ι}
    (ha : Exponents a M v) (hb : Exponents b M v) (hQ : Q.Exponents M v) :
    (skeletonPair a b Q).Exponents M v := by
  simp [skeletonPair,structural,internal,acceptsLeft,acceptsRight,leftExternal,rightExternal,
    hasMarker,first,last,isCore,isPalette,isStop,all,any,Formula.and,Formula.or,neg,equal,
    Formula.Exponents,ha.1,ha.2,hb.1,hb.2,hQ]
lemma register_exponents {a : Expr (ι:=ι)} (ha : Exponents a M v) (i : Fin 3) :
    (register a i).Exponents M v := ha.2 _
lemma zeroReg_exponents (i : Fin 3) : (zeroReg (ι:=ι) i).Exponents M v := trivial
attribute [local simp] register_exponents zeroReg_exponents equalCells_exponents wing_exponents boundary_exponents full_exponents
  idle_exponents setChecker_exponents setColor_exponents skeletonPair_exponents
lemma addReg_exponents {r t : Fin 3 → Formula ι}
    (hr : ∀i,(r i).Exponents M v) (ht : ∀i,(t i).Exponents M v) (i : Fin 3) :
    (addReg r t i).Exponents M v := by simp [addReg,Formula.Exponents,hr,ht]
attribute [local simp] addReg_exponents
lemma binaryMove_exponents {a b a' b' : Expr (ι:=ι)} {Q : Formula ι}
    {readDelta undoDelta : Fin 3 → Formula ι}
    (ha : Exponents a M v) (hb : Exponents b M v)
    (ha' : Exponents a' M v) (hb' : Exponents b' M v) (hQ : Q.Exponents M v)
    (hr : ∀i,(readDelta i).Exponents M v) (hu : ∀i,(undoDelta i).Exponents M v) :
    (binaryMove a b a' b' Q readDelta undoDelta).Exponents M v := by
  have hra := register_exponents ha
  have hrb := register_exponents hb
  have hread := addReg_exponents hrb hr
  have hundo := addReg_exponents hra hu
  have h0 (p : FiniteTable.Phase) := full_exponents p hb (hb.2 1) (hb.1 7) hrb
  have h1 (p : FiniteTable.Phase) := full_exponents p ha (hb.2 1) (hb.1 7) hread
  have h2 (p : FiniteTable.Phase) := full_exponents p ha (ha.2 1) (ha.1 7) hra
  have h3 (p : FiniteTable.Phase) := full_exponents p hb (ha.2 1) (ha.1 7) hra
  have h4 (p : FiniteTable.Phase) := full_exponents p ha (hb.2 1) (hb.1 7) hrb
  have h5 (p : FiniteTable.Phase) := full_exponents p hb (ha.2 1) (ha.1 7) hundo
  have hk0 := setChecker_exponents ha (exponents_constant 1) (ha.1 6)
  have hk1 := setChecker_exponents hb (exponents_constant 2) (ha.1 6)
  have hk2 := setChecker_exponents hb' (exponents_constant 0) (exponents_constant 0)
  simp [binaryMove,acquireMove,readLeftMove,readRightMove,undoLeftMove,undoRightMove,
    checkerCreateMove,checkerAdvanceMove,swapMove,all,any,Formula.and,Formula.or,equal,
    side,clause,isCore,isPalette,checkerHead,checkerIdle,headFree,hasHead,hasMarker,
    Formula.Exponents,ha,hb,ha',hb',ha.1,ha.2,hb.1,hb'.1,hQ,h0,h1,h2,h3,h4,h5,hk0,hk1,hk2]
  all_goals simp [neg,Formula.Exponents,ha.1,hb.1]
end SourceBurnside.CellFormula

namespace SourceBurnside.CellFormula
open Structured.Device Structured.Device.Formula
variable {ι : Type} {M : ℕ} {v : ι → ℕ}
def Ready (a : Expr (ι:=ι)) (M : ℕ) (v : ι → ℕ) : Prop :=
  Exponents a M v ∧ InitialFormula.binSize ((a.1 3).eval v+1)≤M+1
lemma ofRaw_ready {H W : Formula ι}
    (hH : H.Exponents M v) (hW : W.Exponents M v) (hM : 64*H.eval v+8≤M) :
    Ready (ofRaw H W) M v := by
  refine ⟨ofRaw_exponents hH hW hM,?_⟩
  have hlt : ((ofRaw H W).1 3).eval v<2^(2*H.eval v) := by
    change W.eval v / 2^(6*H.eval v) % 2^(2*H.eval v)<2^(2*H.eval v)
    exact Nat.mod_lt _ (by positivity)
  have hs := Nat.size_le_size (show ((ofRaw H W).1 3).eval v+1≤2^(2*H.eval v) by omega)
  rw [Nat.size_pow] at hs
  simp only [InitialFormula.binSize,Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false]
  omega
end SourceBurnside.CellFormula

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Machines_Compilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.FiniteTable.Codec
open Structured.Binary
lemma binaryValue_eq (bs : List Bool) : binaryValue bs=Add.value bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [binaryValue,BitVec.ofBoolListLE,BitVec.toNat_concat] at *
    cases b <;> simp [Add.value,Add.bit,ih] <;> omega
end SourceBurnside.FiniteTable.Codec

namespace SourceBurnside.InitialFormula
open FiniteTable.Codec Structured.Binary
lemma bin_value (n : ℕ) : Add.value (bin n).reverse=n := by
  rw [←binaryValue_eq]
  apply Nat.eq_of_testBit_eq
  intro k
  rw [binaryValue_bit]
  by_cases hk : k<binSize n
  · have hr : k<(bin n).reverse.length := by simpa using hk
    rw [List.getD_eq_getElem _ _ hr,List.getElem_reverse]
    simp only [bin,List.length_ofFn,List.getElem_ofFn]
    congr 1
    omega
  · have hz : (bin n).reverse.getD k false=false := List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hk)
    rw [hz,eq_comm]
    apply Nat.testBit_eq_false_of_lt
    have hs : n<2^(binSize n) := by
      by_cases hn : n=0
      · simp [hn,binSize]
      · simpa [binSize,hn] using Nat.lt_size_self n
    exact hs.trans_le (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_gt hk))
end SourceBurnside.InitialFormula

namespace SourceBurnside.BinaryUnary
open Structured Structured.Program Structured.Binary
abbrev K := Fin 4
def store (bits : List Bool) (n : ℕ) : Store K := ![bits.reverse,List.replicate n false,[],[]]
def lastBit (b : Bool) : Program K := if b then .push 1 false else .skip
def step (b : Bool) : Program K := .seq (copy 1 2 3) (.seq (move 2 1) (lastBit b))
def program : Program K := .loop 0 step
lemma step_run (b : Bool) (bits : List Bool) (n : ℕ) :
    Run (step b) (store bits n) (7*n+4) (store bits (2*n+Add.bit b)) := by
  let r := store bits n
  let s := Function.update r (2:K) (List.replicate n false)
  have h1 : Run (copy (1:K) 2 3) r (5*n+2) s := by
    simpa [r,s,store] using copy_run (1:K) 2 3 (by decide) (by decide) (by decide) r (by rfl)
  have h2 := move_run (2:K) 1 (by decide) s
  have he : Function.update (Function.update s 2 []) 1 (s 1++(s 2).reverse)=store bits (2*n) := by
    funext i;fin_cases i <;> simp [s,r,store,two_mul]
  rw [he] at h2
  have hl : (s 2).length=n := by simp [s]
  rw [hl] at h2
  have h3 : Run (lastBit b) (store bits (2*n)) 1 (store bits (2*n+Add.bit b)) := by
    cases b
    · simpa [lastBit,Add.bit] using Run.skip (store bits (2*n))
    · convert Run.push (store bits (2*n)) (1:K) false using 1 <;> try rfl
      funext i;fin_cases i <;> simp [store,Add.bit,List.replicate_add]
  have H := Run.seq _ _ _ _ _ _ _ h1 (Run.seq _ _ _ _ _ _ _ h2 h3)
  convert H using 1 <;> first | rfl | omega
lemma feed_ge (n : ℕ) (bits : List Bool) : n≤Divide.feed n bits := by
  rw [Divide.feed_value]
  have hp : 1≤2^bits.length := Nat.one_le_pow _ _ (by omega)
  nlinarith
lemma program_run (bits : List Bool) (n : ℕ) :
    ∃t,t≤(7*Divide.feed n bits+5)*bits.length+1 ∧
      Run program (store bits n) t (store [] (Divide.feed n bits)) := by
  induction bits generalizing n with
  | nil => exact ⟨1,by simp,Run.loop_nil _ _ _ rfl⟩
  | cons b bits ih =>
    obtain ⟨t,ht,hT⟩ := ih (2*n+Add.bit b)
    have he : Function.update (store (b::bits) n) 0 bits.reverse=store bits n := by
      funext i;fin_cases i <;> simp [store]
    have H := Run.loop_cons (store (b::bits) n) (0:K) step bits.reverse b
      (store bits (2*n+Add.bit b)) (store [] (Divide.feed (2*n+Add.bit b) bits)) (7*n+4) t
      (by simp [store]) (by rw [he];exact step_run b bits n) hT
    refine ⟨1+(7*n+4+t),?_,?_⟩
    · have hn : n≤Divide.feed (2*n+Add.bit b) bits :=
        (show n≤2*n+Add.bit b by omega).trans (feed_ge _ _)
      simp only [Divide.feed,List.length_cons]
      nlinarith
    · convert H using 1 <;> rfl

theorem numeral_run (n : ℕ) :
    ∃t,t≤(7*n+5)*InitialFormula.binSize n+1 ∧
      Run program (store (InitialFormula.bin n) 0) t (store [] n) := by
  have h : Divide.feed 0 (InitialFormula.bin n)=n := by
    simp [Divide.feed_value,InitialFormula.bin_value]
  simpa only [h,InitialFormula.bin_length] using program_run (InitialFormula.bin n) 0
end SourceBurnside.BinaryUnary

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Machines_TimedExecution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w

namespace SourceBurnside.Addressable.InputBit
variable {q : ℕ}

def mapBool (f : Bool → Bool) : InputBit q → InputBit q
  | .fixed b => .fixed (f b)
  | .input p neg => match f false,f true with
    | false,false => .fixed false
    | false,true => .input p neg
    | true,false => .input p (!neg)
    | true,true => .fixed true

lemma eval_mapBool (f : Bool → Bool) (a : InputBit q) (v : FiniteTable.Address q → Bool) :
    (a.mapBool f).eval v=f (a.eval v) := by
  cases a with
  | fixed b => rfl
  | input p neg =>
    cases h0 : f false <;> cases h1 : f true <;> cases hv : v (dataAddress p) <;> cases neg <;>
      simp [mapBool,eval,h0,h1,hv]
end SourceBurnside.Addressable.InputBit

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Algebra_WordAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.Cancellation

open scoped BigOperators

variable {K : Type u} [CommRing K] [CharP K 2]

noncomputable def alternatingSum {d m : ℕ} (X : Fin m → Matrix (Fin d) (Fin d) K) :
    Matrix (Fin d) (Fin d) K :=
  ∑ σ : Equiv.Perm (Fin m), (List.ofFn (X ∘ σ)).prod

end SourceBurnside.Cancellation

namespace SourceBurnside.Cancellation
open scoped BigOperators
open Classical
noncomputable section

variable {Γ : Type*} {K : Type*} [CommRing K] [CharP K 2]

def chunkWeight {d : ℕ} (W : Γ → Matrix (Fin d) (Fin d) K) (s : List Γ) :=
  (s.map W).prod

structure Packet (Γ : Type*) where
  before : List Γ
  inside : List Γ
  after : List Γ

def Packet.join (p : Packet Γ) : List Γ := p.before ++ p.inside ++ p.after

def Packet.key (p : Packet Γ) : List Γ × List Γ × Multiset Γ :=
  (p.before, p.after, p.inside)

def Packet.reorder (p : Packet Γ) (σ : Equiv.Perm (Fin p.inside.length)) : List Γ :=
  p.before ++ List.ofFn (p.inside.get ∘ σ) ++ p.after

end
end SourceBurnside.Cancellation

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Algebra_DirectCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.Automaton
open scoped BigOperators
noncomputable section
open Classical

variable {Γ : Type u} {S : Type v} [Semiring S]

abbrev State (Γ : Type u) (b : ℕ) := { w : List Γ // w.length < b }

def stateCode {b : ℕ} (p : State Γ b) : Σ i : Fin b, Fin i.val → Γ :=
  ⟨⟨p.val.length, p.property⟩, p.val.get⟩

lemma stateCode_injective {b : ℕ} : Function.Injective (@stateCode Γ b) := by
  intro p q h
  have hp : List.ofFn (stateCode p).2 = p.val := List.ofFn_get _
  have hq : List.ofFn (stateCode q).2 = q.val := List.ofFn_get _
  apply Subtype.ext
  calc
    p.val = List.ofFn (stateCode p).2 := hp.symm
    _ = List.ofFn (stateCode q).2 := congrArg (fun z : (Σ i : Fin b, Fin i.val → Γ) => List.ofFn z.2) h
    _ = q.val := hq

instance instFintypeState [Fintype Γ] (b : ℕ) : Fintype (State Γ b) := Fintype.ofInjective stateCode stateCode_injective

def root {b : ℕ} (hb : 0 < b) : State Γ b := ⟨[], hb⟩

def transition {b : ℕ} (W : List Γ → S) (a : Γ) : Matrix (State Γ b) (State Γ b) S :=
  fun p q => (if q.val = p.val ++ [a] then 1 else 0) +
    (if q.val = [] then W (p.val ++ [a]) else 0)

def scan (b : ℕ) (W : List Γ → S) (p : List Γ) : List Γ → S
  | [] => if p = [] then 1 else 0
  | a :: w => (if (p ++ [a]).length < b then scan b W (p ++ [a]) w else 0) +
      W (p ++ [a]) * scan b W [] w

def freeScan (W : List Γ → S) (p : List Γ) : List Γ → S
  | [] => if p = [] then 1 else 0
  | a :: w => freeScan W (p ++ [a]) w + W (p ++ [a]) * freeScan W [] w

def partitions : List Γ → List (List (List Γ))
  | [] => [[]]
  | a :: w => (partitions w).flatMap (fun vs =>
      ([a] :: vs) :: (match vs with
        | [] => []
        | v :: rest => [(a :: v) :: rest]))

def partitionWeight (W : List Γ → S) (p : List Γ) : List (List Γ) → S
  | [] => if p = [] then 1 else 0
  | v :: vs => W (p ++ v) * (vs.map W).prod

def Segments (vs : List (List Γ)) (w : List Γ) : Prop :=
  vs.flatten = w ∧ ∀ v ∈ vs, v ≠ []

def children (a : Γ) (vs : List (List Γ)) : List (List (List Γ)) :=
  ([a] :: vs) :: (match vs with | [] => [] | v :: rest => [(a :: v) :: rest])

def parent : List (List Γ) → List (List Γ)
  | [] => []
  | [] :: vs => vs
  | [_] :: vs => vs
  | (_ :: b :: v) :: vs => (b :: v) :: vs

def blockTransition {b : ℕ} [Fintype Γ] {ι : Type*} [Fintype ι]
    (W : List Γ → Matrix ι ι S) (a : Γ) :
    Matrix (State Γ b × ι) (State Γ b × ι) S :=
  Matrix.compRingEquiv _ _ _ (transition W a)

end
end SourceBurnside.Automaton

namespace SourceBurnside.Automaton
open scoped BigOperators
noncomputable section
open Classical
variable {α Γ S : Type*} [Fintype Γ] [Semiring S]

def combinedWeight (label : Γ → List α) (weight : Γ → S) (w : List α) : S :=
  ∑ c, if label c = w then weight c else 0

abbrev BoundedSequences (Γ : Type*) (n : ℕ) := Σ r : Fin (n+1), Fin r.val → Γ

def spelled (label : Γ → List α) {n : ℕ} (s : BoundedSequences Γ n) : List α :=
  (List.ofFn (label ∘ s.2)).flatten

def seqWeight (weight : Γ → S) {n : ℕ} (s : BoundedSequences Γ n) : S :=
  (List.ofFn (weight ∘ s.2)).prod

def wordCoefficient (label : Γ → List α) (weight : Γ → S) (w : List α) : S :=
  ∑ s : BoundedSequences Γ w.length,
    if spelled label s = w then seqWeight weight s else 0

end
end SourceBurnside.Automaton

end

end OAI
end


