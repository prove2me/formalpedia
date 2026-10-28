-- Prove2me | Definitions.Def_OAIQ6Wl001
-- name    : OAIQ6Wl001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T01:52:45.448106+00:00
-- url     : https://prove2.me/theorems/99be05f0-c8cc-46ba-bec9-491bfc5d881a
-- title:
--   Definitions bundle OAIQ6Wl001 of the split of OpenAI, Variable-dimension Weisfeiler–Leman equivalence on general and subcubic graphs
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.VariableWL.main`, carved from OpenAI's openai/math development (OpenAI, *Variable-dimension Weisfeiler–Leman equivalence on general and subcubic graphs*, OpenAI Math Release, September 25, 2026, result family 133, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 132 declarations of OpenAI's Lean: 99 definitions, 4 inductive types or structures, 11 instances and 18 theorems. The definitions and types are `OAI.VariableWL.Encoding.header`, `OAI.VariableWL.Encoding.integer`, `OAI.VariableWL.Encoding.value`, `OAI.VariableWL.Game.decodeSigma`, `OAI.VariableWL.Game.triangularEquiv`, `OAI.VariableWL.MachineCellular.alpha`, `OAI.VariableWL.MachineCellular.emptyLetter`, `OAI.VariableWL.MachineCellular.headLetter`, `OAI.VariableWL.MachineCellular.tailLetter`, `OAI.VariableWL.MachineOneHead.Alphabet`, `OAI.VariableWL.MachineOneHead.Control`, `OAI.VariableWL.MachineOneHead.Label0`, `OAI.VariableWL.MachineOneHead.Label1`, `OAI.VariableWL.MachineOneHead.addressBits`, `OAI.VariableWL.MachineOneHead.input`, `OAI.VariableWL.MachineOneHead.inputExponent`, `OAI.VariableWL.MachineOneHead.instructionsBound`, `OAI.VariableWL.MachineOneHead.linearConstant`, `OAI.VariableWL.MachineOneHead.oneHead`, `OAI.VariableWL.MachineOneHead.program0`, `OAI.VariableWL.MachineOneHead.program1`, `OAI.VariableWL.MachineOneHead.quadraticConstant`, `OAI.VariableWL.MachineOneHead.simulationExponent`, `OAI.VariableWL.MachineOneHead.stackTime`, `OAI.VariableWL.MachineOneHead.support0`, `OAI.VariableWL.MachineOneHead.support1`, `OAI.VariableWL.MachineOneHead.time`, `OAI.VariableWL.MachineReduction.Letter`, `OAI.VariableWL.MachineReduction.bits`, `OAI.VariableWL.MachineReduction.dimension`, `OAI.VariableWL.MachineReduction.internal`, `OAI.VariableWL.MachineReduction.marked`, `OAI.VariableWL.MultiStack.Config`, `OAI.VariableWL.MultiStack.Data`, `OAI.VariableWL.MultiStack.K`, `OAI.VariableWL.MultiStack.Label`, `OAI.VariableWL.MultiStack.Q`, `OAI.VariableWL.MultiStack.Related`, `OAI.VariableWL.MultiStack.Slot`, `OAI.VariableWL.MultiStack.Stacks` and 63 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `VariableWL_BoundedLoop`, `VariableWL_Encoding`, `VariableWL_GeneralReduction`, `VariableWL_MachineCellular`, `VariableWL_MachineReduction`, `VariableWL_MachineSimulation`, `VariableWL_MultiStack`, `VariableWL_OneHead`, `VariableWL_PortGame`, `VariableWL_Refinement`, `VariableWL_RefinementTable`, `VariableWL_StackSimulation`, `VariableWL_TypedGame`.
--
--   **Imports.** It imports the published bundle `Def_VariableWL`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ6Wl002`.
-- source:
--   OpenAI, Variable-dimension Weisfeiler–Leman equivalence on general and subcubic graphs, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 133; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Variable-dimension-Weisfeiler-Leman-equivalence-on-general-and-subcubic-graphs-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_VariableWL

section
-- module Solutions.OAIQ6_WL.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Refinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6

namespace VariableWL

def tupleEquiv {G H : Graph} (e : G.graph ≃g H.graph) (k : ℕ) :
    Tuple G k ≃ Tuple H k where
  toFun v := e ∘ v
  invFun v := e.symm ∘ v
  left_inv v := by funext i; simp
  right_inv v := by funext i; simp

end VariableWL

universe uGame1 uGame2 uGame3 uGame4 uGame5 uGame6 uGame7

namespace VariableWL.Game

theorem exists_fresh {k : ℕ} (σ : Fin k → Fin (k+1)) :
    ∃ j, ∀ i, σ i ≠ j := by
  by_contra! h
  have hsurj : Function.Surjective σ := fun j => by simpa using h j
  have hc := Fintype.card_le_of_surjective σ hsurj
  simp at hc

theorem update_injective_of_fresh {α : Type uGame1} {β : Type uGame2} [DecidableEq α]
    {f : α → β} (hf : Function.Injective f) (i : α) (b : β)
    (hb : ∀ a, f a ≠ b) : Function.Injective (Function.update f i b) := by
  intro x y hxy
  by_cases hx : x = i <;> by_cases hy : y = i
  · exact hx.trans hy.symm
  · subst x
    simp only [Function.update_self, Function.update_of_ne hy] at hxy
    exact (hb y hxy.symm).elim
  · subst y
    simp only [Function.update_self, Function.update_of_ne hx] at hxy
    exact (hb x hxy).elim
  · simp only [Function.update_of_ne hx, Function.update_of_ne hy] at hxy
    exact hf hxy

end VariableWL.Game

namespace VariableWL.Game

def triangularEquiv {A : Type uGame3} {B : Type uGame4} {C : Type uGame5} {D : Type uGame6} (e : A ≃ B) (E : A → C ≃ D) :
    (A × C) ≃ (B × D) where
  toFun a := (e a.1, E a.1 a.2)
  invFun b := (e.symm b.1, (E (e.symm b.1)).symm b.2)
  left_inv a := by simp
  right_inv b := by simp

end VariableWL.Game

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_GeneralReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10

namespace VariableWL.Game
variable {G H : Graph} {r : ℕ} {B : Type uVariable8} {Z Y : B → Type uVariable10}
variable (query : B → Fin G.order) (response : (Σ b, Z b) → Fin H.order)
variable (decode : ∀ b, Z b → Y b)

theorem sigma_eq_cast (s : Σ b, Y b) {b : B} (h : s.1 = b) : s = ⟨b,h ▸ s.2⟩ := by
  cases s
  cases h
  rfl

def decodeSigma (z : Σ b, Z b) : Σ b, Y b := ⟨z.1,decode z.1 z.2⟩

end VariableWL.Game

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_TypedGame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9

namespace VariableWL.TypedGame
attribute [local instance] Classical.propDecidable
variable {V : Type uVariable1} {W : Type uVariable2} [Fintype V] [Fintype W]

abbrev Position (V : Type uVariable3) (W : Type uVariable4) (q : ℕ) := Fin q → Option (V × W)

def keep {q : ℕ} (p : Position V W q) (s : Finset (Fin q)) : Position V W q :=
  fun i => if i ∈ s then p i else none

end VariableWL.TypedGame

namespace VariableWL.TypedGame
attribute [local instance] Classical.propDecidable
variable {V : Type uVariable5} {W : Type uVariable6} [Fintype V] [Fintype W]

def swap {q : ℕ} (p : Position V W q) : Position W V q := fun i => (p i).map Prod.swap

theorem spare {q : ℕ} (hq : 3 ≤ q) (i j : Fin q) : ∃ l : Fin q, l ≠ i ∧ l ≠ j := by
  classical
  have hc : ({i,j} : Finset (Fin q)).card < (Finset.univ : Finset (Fin q)).card := by
    have hl : ({i,j} : Finset (Fin q)).card ≤ 2 := le_trans (Finset.card_insert_le _ _) (by simp)
    simpa only [Finset.card_univ,Fintype.card_fin] using lt_of_le_of_lt hl (by omega : 2 < q)
  obtain ⟨l,_,hl⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  refine ⟨l,?_⟩
  simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hl

def Triangle (G : SimpleGraph V) (v : V) : Prop :=
  ∃ a b, G.Adj v a ∧ G.Adj a b ∧ G.Adj b v

def Tail (G : SimpleGraph V) : ℕ → V → V → Prop
  | 0,_,v => G.degree v = 1
  | n+1,u,v => G.degree v = 2 ∧ ∃ w, w ≠ u ∧ G.Adj v w ∧ Tail G n v w

end VariableWL.TypedGame

namespace VariableWL.TypedGame
attribute [local instance] Classical.propDecidable
variable {V : Type uVariable7} {W : Type uVariable8} [Fintype V] [Fintype W]

def ColorTag (G : SimpleGraph V) (t : ℕ) (v : V) : Prop :=
  0 < t ∧ Triangle G v ∧ ∃ c, G.Adj v c ∧ ¬ Triangle G c ∧
    ∃ y, G.Adj c y ∧ y ≠ v ∧ G.degree y ≤ 2 ∧ Tail G (t-1) c y

end VariableWL.TypedGame

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_PortGame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7

namespace VariableWL.TypedGame
attribute [local instance] Classical.propDecidable
variable {V : Type uVariable1} {W : Type uVariable2} [Fintype V] [Fintype W]

def Compose {A : Type uVariable3} (R S : A → A → Prop) (a b : A) : Prop := ∃ m, R a m ∧ S m b

def SameTriangle (G : SimpleGraph V) (a b : V) : Prop :=
  Triangle G a ∧ Triangle G b ∧ (a=b ∨ G.Adj a b)

def Exit (G : SimpleGraph V) (a b : V) : Prop :=
  Triangle G a ∧ ¬ Triangle G b ∧ G.Adj a b

def Access (G : SimpleGraph V) : V → V → Prop := Compose (SameTriangle G) (Exit G)

def UnderlyingEdge (G : SimpleGraph V) : V → V → Prop :=
  Compose (Access G) (Compose G.Adj (fun a b => Access G b a))

end VariableWL.TypedGame

namespace VariableWL.SubcubicRealization
attribute [local instance] Classical.propDecidable
variable {V : Type uVariable5} {W : Type uVariable6} [Fintype V] [Fintype W]
variable (color : V → ℕ)
  (color' : W → ℕ)

def SortWalk {A : Type uVariable7} (G : SimpleGraph A) (c : A → ℕ) : List ℕ → A → A → Prop
  | [], _, _ => False
  | [t], x, y => x=y ∧ c x=t
  | t::u::ts, x, y => c x=t ∧ ∃ z, G.Adj x z ∧ SortWalk G c (u::ts) z y

end VariableWL.SubcubicRealization

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_OneHead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10

namespace VariableWL.OneHead

variable {Q : Type uVariable1} {Γ : Type uVariable2} {A : Type uVariable3}

structure Program (Q : Type uVariable4) (Γ : Type uVariable5) where
  start : Q
  transition : Q → Γ → Option (Q × Γ × Motion)
  accepting : Q → Γ → Bool

structure State (Q : Type uVariable6) (Γ : Type uVariable7) (A : Type uVariable8) where
  control : Q
  head : A
  cells : A → Γ

abbrev Cell (Q : Type uVariable9) (Γ : Type uVariable10) := Γ × Option Q

def Program.action (M : Program Q Γ) (q : Q) (a : Γ) : Q × Γ × Motion :=
  (M.transition q a).getD (q,a,.stay)

def move [AddGroup A] (u : A) : Motion → A → A
  | .left, x => x-u
  | .stay, x => x
  | .right, x => x+u

def Program.next [AddGroup A] [DecidableEq A] (M : Program Q Γ) (u : A) (s : State Q Γ A) : State Q Γ A :=
  let a := M.action s.control (s.cells s.head)
  ⟨a.1, move u a.2.2 s.head, Function.update s.cells s.head a.2.1⟩

noncomputable def encode [DecidableEq A] (s : State Q Γ A) (i : A) : Cell Q Γ :=
  (s.cells i,if i=s.head then some s.control else none)

def Program.incoming (M : Program Q Γ) (m : Motion) (a : Cell Q Γ) : Option Q :=
  a.2.bind fun q => let b := M.action q a.1; if b.2.2=m then some b.1 else none

def Program.rule (M : Program Q Γ) (a b c : Cell Q Γ) : Cell Q Γ :=
  (b.2.elim b.1 (fun q => (M.action q b.1).2.1),
    (M.incoming .right a).or ((M.incoming .stay b).or (M.incoming .left c)))

noncomputable def Program.run [AddGroup A] [DecidableEq A] (M : Program Q Γ) (u : A) (s : State Q Γ A) : ℕ → State Q Γ A
  | 0 => s
  | t+1 => M.next u (M.run u s t)

def Program.acceptingCell (M : Program Q Γ) (a : Cell Q Γ) : Prop :=
  ∃ q, a.2=some q ∧ M.accepting q a.1=true

end VariableWL.OneHead

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_StackSimulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10 uVariable11 uVariable12 uVariable13 uVariable14 uVariable15 uVariable16 uVariable17 uVariable18 uVariable19

namespace VariableWL.OneHead
variable {Q : Type uVariable1} {Γ : Type uVariable2} {A : Type uVariable3} {B : Type uVariable4} [AddCommGroup A] [AddCommGroup B] [DecidableEq A] [DecidableEq B]

def Related (f : A →+ B) (S : Set A) (s : State Q Γ A) (t : State Q Γ B) : Prop :=
  t.control=s.control ∧ t.head=f s.head ∧ ∀ i ∈ S, t.cells (f i)=s.cells i

def window (T : ℕ) : Set ℤ := {i | -(T:ℤ) ≤ i ∧ i ≤ T}

variable {m : ℕ}

def lineInput (blank : Γ) (w : Fin m → Γ) (i : ℤ) : Γ :=
  if h : 0 ≤ i ∧ i < m then w ⟨i.toNat,by omega⟩ else blank

def ringInput (N : ℕ) (blank : Γ) (w : Fin m → Γ) (i : ZMod N) : Γ :=
  if h : i.val < m then w ⟨i.val,h⟩ else blank

def lineInitial (M : Program Q Γ) (blank : Γ) (w : Fin m → Γ) : State Q Γ ℤ :=
  ⟨M.start,0,lineInput blank w⟩

def ringInitial (M : Program Q Γ) (N : ℕ) (blank : Γ) (w : Fin m → Γ) : State Q Γ (ZMod N) :=
  ⟨M.start,0,ringInput N blank w⟩

end VariableWL.OneHead

namespace VariableWL.OneHead
variable {Q : Type uVariable5} {Γ : Type uVariable6} {m d : ℕ}

def markedInput (M : Program Q Γ) (w : Fin m → Γ) (j : Fin m) : Cell Q Γ :=
  (w j, if j.val=0 then some M.start else none)

end VariableWL.OneHead

namespace VariableWL.StackSimulation
open Turing TM2to1 TM2to1.Λ'
variable {K : Type uVariable16} {Γ : K → Type uVariable19} {Λ : Type uVariable17} {σ : Type uVariable18} [DecidableEq K]

def operations : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => operations q+1
  | .peek _ _ q => operations q+1
  | .pop _ _ q => operations q+1
  | .load _ q => operations q
  | .branch _ q r => max (operations q) (operations r)
  | .goto _ | .halt => 0

end VariableWL.StackSimulation

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_MultiStack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9

namespace VariableWL.UnitSimulation
open Turing
variable {Γ : Type uVariable5} {Λ : Type uVariable6} {σ : Type uVariable7} [Inhabited Γ] [Inhabited Λ] [Inhabited σ]

def instructions : TM1.Stmt Γ Λ σ → ℕ
  | .move _ q => instructions q+1
  | .write _ q => instructions q+1
  | .load _ q => instructions q
  | .branch _ q r => max (instructions q) (instructions r)
  | .goto _ | .halt => 1

end VariableWL.UnitSimulation

namespace VariableWL.MultiStack
open Turing
variable (M : Machine)
abbrev K := Fin (M.extraTapes+1)
abbrev Γ := Fin (M.workSymbols+3)
abbrev Q := Fin (M.states+1)
abbrev Slot := K M × Bool
abbrev Stacks := Slot M → List (Γ M)
abbrev Data := Q M × (K M → Γ M × Motion)

inductive Label where
  | simulate : Q M → Label
  | drain : Bool → Label
  deriving DecidableEq

instance instFintypeLabel : Fintype (Label M) := Fintype.ofEquiv (Q M ⊕ Bool)
  ⟨(fun | .inl q => .simulate q | .inr b => .drain b),
   (fun | .simulate q => .inl q | .drain b => .inr b),
   (by intro q; cases q <;> rfl),(by intro q; cases q <;> rfl)⟩
instance instInhabitedLabel : Inhabited (Label M) := ⟨.simulate 0⟩

@[ext] structure Vars where
  reads : K M → Γ M
  data : Option (Data M)
  answer : Bool

abbrev Statement := TM2.Stmt (fun _ : Slot M => Γ M) (Label M) (Vars M)
abbrev Config := TM2.Cfg (fun _ : Slot M => Γ M) (Label M) (Vars M)

instance instInhabitedVars : Inhabited (Vars M) := ⟨⟨fun _ => 0,none,false⟩⟩

def getData (v : Vars M) : Data M := v.data.getD (0,fun _ => (0,.stay))
def tape (S : Stacks M) (j : K M) : Tape (Γ M) := Tape.mk₂ (S (j,false)) (S (j,true))

def readVars (ls : List (K M)) (v : Vars M) (S : Stacks M) : Vars M :=
  {v with reads := fun j => if j ∈ ls then (S (j,true)).headI else v.reads j}

def readAll : List (K M) → Statement M → Statement M
  | [], q => q
  | j::ls, q => .peek (j,true) (fun v a => {v with reads := Function.update v.reads j (a.getD 0)})
      (readAll ls q)

noncomputable def allTapes : List (K M) := List.ofFn id

def writeVars (v : Vars M) (S : Stacks M) (j : K M) (m : Motion) : Vars M :=
  match m with
  | .left => {v with reads := Function.update v.reads j (S (j,false)).headI}
  | _ => v

def writeStacks (S : Stacks M) (j : K M) (a : Γ M) : Motion → Stacks M
  | .left => Function.update (Function.update S (j,false) (S (j,false)).tail)
      (j,true) ((S (j,false)).headI::a::(S (j,true)).tail)
  | .right => Function.update (Function.update S (j,false) (a::S (j,false)))
      (j,true) (S (j,true)).tail
  | .stay => Function.update S (j,true) (a::(S (j,true)).tail)

def writeTape (j : K M) (q : Statement M) : Statement M :=
  .pop (j,true) (fun v _ => v)
    (.branch (fun v => decide (((getData M v).2 j).2 = .left))
      (.pop (j,false) (fun v a => {v with reads := Function.update v.reads j (a.getD 0)})
        (.push (j,true) (fun v => ((getData M v).2 j).1)
          (.push (j,true) (fun v => v.reads j) q)))
      (.branch (fun v => decide (((getData M v).2 j).2 = .right))
        (.push (j,false) (fun v => ((getData M v).2 j).1) q)
        (.push (j,true) (fun v => ((getData M v).2 j).1) q)))

def applyMotion (T : Tape (Γ M)) : Motion → Tape (Γ M)
  | .left => T.move .left
  | .stay => T
  | .right => T.move .right

def writeAll : List (K M) → Statement M → Statement M
  | [],q => q
  | j::ls,q => writeTape M j (writeAll ls q)

def applyStacks : List (K M) → Data M → Stacks M → Stacks M
  | [],_,S => S
  | j::ls,d,S => applyStacks ls d (writeStacks M S j (d.2 j).1 (d.2 j).2)

noncomputable def program : Label M → Statement M
  | .simulate q => readAll M (allTapes M)
      (.load (fun v => {v with data := M.transition q v.reads})
        (.branch (fun v => v.data.isSome)
          (writeAll M (allTapes M) (.goto (fun v => .simulate (getData M v).1)))
          (.load (fun v => {v with answer := false}) (.goto (fun _ => .drain false)))))
  | .drain b => .pop (0,b) (fun v a =>
      { data := none
        answer := v.answer || decide (a=some 2)
        reads := Function.update v.reads 0 (if a.isSome then 1 else 0) })
      (.branch (fun v => decide (v.reads 0=0))
        (if b then .halt else .goto (fun _ => .drain true))
        (.goto (fun _ => .drain b)))

end VariableWL.MultiStack

namespace VariableWL.MultiStack
open Turing
variable (M : Machine)

def Related (c : Configuration M) (s : Config M) : Prop :=
  s.l=some (.simulate c.control) ∧
    ∀ j i, (tape M s.stk j).nth i=c.cells j (c.heads j+i)

end VariableWL.MultiStack

namespace VariableWL.MultiStack
open Turing
variable (M : Machine)

def inputSymbol (b : Bool) : Γ M := if b then 2 else 1

def initialStacks (w : Word) : Stacks M :=
  Function.update (fun _ => []) (0,true) (w.map (inputSymbol M))

def initialConfig (w : Word) : Config M := ⟨some (.simulate 0),default,initialStacks M w⟩

end VariableWL.MultiStack

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_MachineSimulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2

namespace VariableWL.MultiStack
open Turing
variable (M : Machine)

def found (l : List (Γ M)) : Bool := l.contains 2

def drainVars (v : Vars M) (l : List (Γ M)) : Vars M :=
  { reads := Function.update v.reads 0 0
    data := none
    answer := v.answer || found M l }

def drainLabel (b : Bool) : Option (Label M) := if b then none else some (.drain true)

end VariableWL.MultiStack

namespace VariableWL.MultiStack
open Turing
variable (M : Machine)

instance instFintypeMotion : Fintype Motion := ⟨{.left,.stay,.right},by intro m; cases m <;> simp⟩

instance instFintypeVars : Fintype (Vars M) := Fintype.ofEquiv ((K M → Γ M) × Option (Data M) × Bool)
  ⟨(fun v => ⟨v.1,v.2.1,v.2.2⟩),(fun v => (v.reads,v.data,v.answer)),
    (by rintro ⟨a,b,c⟩; rfl),(by rintro ⟨a,b,c⟩; rfl)⟩

noncomputable def operationsBound : ℕ := Finset.univ.sup (fun l : Label M => StackSimulation.operations (program M l))

end VariableWL.MultiStack

namespace VariableWL.TM0Adapter
open Turing
variable {Γ : Type uVariable1} {Λ : Type uVariable2} [Inhabited Γ] [Inhabited Λ]
variable (M : TM0.Machine Γ Λ) (S : Finset Λ) (hS : TM0.Supports M (S : Set Λ))

abbrev Control := {q : Λ // q ∈ S}

def action (a : Γ) : TM0.Stmt Γ → Γ × Motion
  | .move .left => (a,.left)
  | .move .right => (a,.right)
  | .write b => (b,.stay)

noncomputable def program (accept : Λ → Γ → Bool) : OneHead.Program (Control S) Γ where
  start := ⟨default,hS.1⟩
  transition := fun q a => match h : M q.val a with
    | none => none
    | some (q',s) => some (⟨q',hS.2 h q.property⟩,action a s)
  accepting := fun q a => accept q.val a

def Related (c : TM0.Cfg Γ Λ) (s : OneHead.State (Control S) Γ ℤ) : Prop :=
  s.control.val=c.q ∧ ∀ i, c.Tape.nth i=s.cells (s.head+i)

end VariableWL.TM0Adapter

namespace VariableWL.MachineOneHead
open Turing
variable (M : Machine)

abbrev Alphabet := TM2to1.Γ' (MultiStack.Slot M) (fun _ => MultiStack.Γ M)
abbrev Label1 := TM2to1.Λ' (MultiStack.Slot M) (fun _ => MultiStack.Γ M)
  (MultiStack.Label M) (MultiStack.Vars M)
noncomputable def program1 := TM2to1.tr (MultiStack.program M)
noncomputable def support1 : Finset (Label1 M) := TM2to1.trSupp (MultiStack.program M) Finset.univ

theorem supported2 : TM2.Supports (MultiStack.program M) Finset.univ := by
  refine ⟨Finset.mem_univ _,fun q _ => ?_⟩
  generalize MultiStack.program M q=t
  induction t <;> simp_all [TM2.SupportsStmt]

theorem supported1 : TM1.Supports (program1 M) (support1 M) :=
  TM2to1.tr_supports (MultiStack.program M) (supported2 M)

abbrev Label0 := TM1to0.Λ' (program1 M)
noncomputable def program0 := TM1to0.tr (program1 M)
noncomputable def support0 : Finset (Label0 M) := TM1to0.trStmts (program1 M) (support1 M)
theorem supported0 : TM0.Supports (program0 M) (support0 M : Set (Label0 M)) :=
  TM1to0.tr_supports (program1 M) (supported1 M)

abbrev Control := TM0Adapter.Control (support0 M)
noncomputable instance instFintypeControl : Fintype (Control M) := Fintype.ofFinite _

noncomputable def instructionsBound : ℕ := (support1 M).sup (fun l => UnitSimulation.instructions (program1 M l))

noncomputable def oneHead : OneHead.Program (Control M) (Alphabet M) :=
  TM0Adapter.program (program0 M) (support0 M) (supported0 M) (fun q _ => !q.2.answer)

noncomputable def input (w : Word) : List (Alphabet M) :=
  TM2to1.trInit (0,true) (w.map (MultiStack.inputSymbol M))

theorem input_length (w : Word) : (input M w).length ≤ w.length+1 := by
  change (((w.map (MultiStack.inputSymbol M)).reverse.map
    (fun a => (false,Function.update (fun _ : MultiStack.Slot M => none) (0,true) (some a)))).tail).length+1 ≤ w.length+1
  simp only [List.length_tail,List.length_map,List.length_reverse]
  omega

noncomputable def stackTime (m T : ℕ) : ℕ := T+2*(m+T*MultiStack.operationsBound M)+3
noncomputable def time (m T : ℕ) : ℕ :=
  stackTime M m T * (1+MultiStack.operationsBound M *
    (2*(m+stackTime M m T*MultiStack.operationsBound M+MultiStack.operationsBound M)+2)) * instructionsBound M

end VariableWL.MachineOneHead

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_MachineReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6

namespace VariableWL.MachineOneHead
variable (M : Machine)

noncomputable def linearConstant : ℕ := 2*MultiStack.operationsBound M+5
noncomputable def quadraticConstant : ℕ :=
  linearConstant M * (1+MultiStack.operationsBound M *
    (2*(1+linearConstant M*MultiStack.operationsBound M+MultiStack.operationsBound M)+2)) * instructionsBound M

def inputExponent (c d m : ℕ) : ℕ := (c+1)*(m+1)^(d+1)
noncomputable def simulationExponent (c d m : ℕ) : ℕ :=
  quadraticConstant M+3+2*inputExponent c d m
noncomputable def addressBits (c d m : ℕ) : ℕ := simulationExponent M c d m+2

theorem inputExponent_ge_length (c d m : ℕ) : m+1 ≤ inputExponent c d m := by
  unfold inputExponent
  rw [pow_succ]
  have hp : 1 ≤ (c+1)*(m+1)^d := Nat.succ_le_of_lt (Nat.mul_pos (by omega) (pow_pos (by omega) _))
  simpa only [Nat.mul_assoc,one_mul] using Nat.mul_le_mul_right (m+1) hp

theorem input_fits_budget (c d m : ℕ) : m+1 ≤ 2^simulationExponent M c d m := by
  have h : inputExponent c d m ≤ simulationExponent M c d m := by
    unfold simulationExponent; omega
  exact (inputExponent_ge_length c d m).trans ((Nat.le_of_lt Nat.lt_two_pow_self).trans
    (Nat.pow_le_pow_right (by omega) h))

theorem ring_budget (c d m : ℕ) :
    2*(2^simulationExponent M c d m) < 2^addressBits M c d m := by
  unfold addressBits
  rw [pow_add]
  have h := Nat.two_pow_pos (simulationExponent M c d m)
  norm_num
  omega

theorem addressBits_ge_four (c d m : ℕ) : 4 ≤ addressBits M c d m := by
  unfold addressBits simulationExponent
  omega

end VariableWL.MachineOneHead

namespace VariableWL.MachineReduction
open MachineOneHead
attribute [local instance] Classical.propDecidable
variable (M : Machine) (c d : ℕ)

abbrev Letter := OneHead.Cell (Control M) (Alphabet M)
noncomputable instance letterFintype : Fintype (Letter M) := inferInstance
noncomputable def bits (w : Word) : ℕ := addressBits M c d w.length
noncomputable def dimension (w : Word) : ℕ := bits M c d w+bits M c d w
noncomputable def internal (w : Word) : ℕ := 4*(dimension M c d w+1)

theorem fits (w : Word) : (input M w).length < 2^bits M c d w := by
  have hi := (input_length M w).trans (input_fits_budget M c d w.length)
  have hr := ring_budget M c d w.length
  change (input M w).length < 2^addressBits M c d w.length
  omega

theorem dimension_large (w : Word) : 8 ≤ dimension M c d w := by
  have h := addressBits_ge_four M c d w.length
  unfold dimension bits
  omega

noncomputable def marked (w : Word) : Fin (dimension M c d w) := ⟨0,by have := dimension_large M c d w; omega⟩

end VariableWL.MachineReduction

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Encoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.Encoding
attribute [local instance] Classical.propDecidable

def value : Word → ℕ := List.foldr Nat.bit 0
@[simp] theorem value_bits (n : ℕ) : value n.bits=n := by
  induction n using Nat.binaryRec' with
  | zero => simp [value]
  | bit b n hn ih => simp [Nat.bits_append_bit _ _ hn,value] at ih ⊢; exact congrArg (Nat.bit b) ih

def header : Word → Option (ℕ × Word)
  | [] => none
  | false::w => some (0,w)
  | true::w => (header w).map fun (n,v) => (n+1,v)

def integer (w : Word) : Option (ℕ × Word) :=
  match header w with
  | none => none
  | some (n,v) =>
    if n ≤ v.length then
      let bits := v.take n
      let a := value bits
      if a.bits=bits then some (a,v.drop n) else none
    else none

end VariableWL.Encoding

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_RefinementTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.RefinementTable
attribute [local instance] Classical.propDecidable

def sameCounts {α : Type} (eq : α → α → Bool) (xs ys : List α) : Bool :=
  (xs++ys).all fun a => decide ((xs.filter (eq a)).length=(ys.filter (eq a)).length)

end VariableWL.RefinementTable

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_BoundedLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.TupleAddress

def encode {n k : ℕ} (v : Fin k → Fin n) : ℕ := (finFunctionFinEquiv v).val

def digit (n a i : ℕ) : ℕ := a/n^i%n

def replace (n a i z : ℕ) : ℕ := a-digit n a i*n^i+z*n^i

end VariableWL.TupleAddress

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_MachineCellular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.MachineCellular
open MachineOneHead MachineReduction
attribute [local instance] Classical.propDecidable
variable (M : Machine)
noncomputable def alpha (first b : Bool) : Alphabet M :=
  (first,Function.update (fun _ : MultiStack.Slot M => none) (0,true) (some (MultiStack.inputSymbol M b)))
noncomputable def headLetter (b : Bool) : Letter M := (alpha M true b,some (oneHead M).start)
noncomputable def tailLetter (b : Bool) : Letter M := (alpha M false b,none)
noncomputable def emptyLetter : Letter M := ((true,fun _=>none),some (oneHead M).start)
end VariableWL.MachineCellular

end OAI
end


