-- Prove2me | Definitions.Def_MIPRE_TM_CookLevin_Tableau
-- name    : MIPRE_TM_CookLevin_Tableau
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:59:24.464983+00:00
-- url     : https://prove2.me/theorems/244a8e12-d43d-4eb5-9aa7-a8683ed2792f
-- title:
--   Definitions of Tableau: The Cook–Levin tableau of a multi-input machine The 3SAT formula `tableau M s₀ s₁ S fixed chk` of a run of `S` steps of…
-- statement:
--   The definitions of the module `MIPRE.TM.CookLevin.Tableau` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The Cook–Levin tableau of a multi-input machine. The 3SAT formula `tableau M s₀ s₁ S fixed chk` of a run of `S` steps of the machine `M` (`planning/succinct-cook-levin.md`, S1; `answer_reduction.tex` `prop:standard-succinct-sat`): * **Variables** (`TabVar`): for each time `t ≤ S`, tape and cell position, the one-hot cell values and the head bit; for each time the one-hot state; per step the emission flags `emitOne` (the accepting symbol `acc` is emitted) and `emitBad` (another symbol is), and per time the flag `emitted` (something was emitted before); and, per step and window, the gate…
--
--   **Definitions** (32): `MIPRE.TM.CookLevin.Center` (A window center, offset by two: the window of center `c` covers the cells `c ..); `MIPRE.TM.CookLevin.IsCheckCircuit` (`chk` computes local consistency of a window: its specification, the hypothesis of the correctness of the tableau (`Correct.lean`); `S3`…); `MIPRE.TM.CookLevin.Pos` (A cell position.); `MIPRE.TM.CookLevin.Pos.IsBdry` (A boundary cell: the first two and the last two.); `MIPRE.TM.CookLevin.TabVar` (The variables of the tableau.); `MIPRE.TM.CookLevin.auxOf` (The gate variables of the check circuit at a window.); `MIPRE.TM.CookLevin.baseAssign` (The assignment of the run on the non-auxiliary variables.); `MIPRE.TM.CookLevin.bdryClauses` (The boundary rows: boundary cells hold the marker and carry no head, at every time.); `MIPRE.TM.CookLevin.cellIdx` (The cell at offset `δ` of the window of center `c`.); `MIPRE.TM.CookLevin.cellValAt` (The value of cell `p` of tape `d` in a configuration.); `MIPRE.TM.CookLevin.center` (The middle cell of a window.); `MIPRE.TM.CookLevin.cfgAt` (The configuration at time `t` of the run on `input`.); `MIPRE.TM.CookLevin.emitClauses` (The emission bookkeeping: nothing emitted before time `0`, `emitted (t + 1) ↔ emitted t ∨ emitOne t`, no emission after an emission,…); `MIPRE.TM.CookLevin.finalClauses` (The acceptance row: halted at time `S`, and `acc` emitted.); and 4 more.
--
--   **Formalization Note** The bundle is the module `MIPRE.TM.CookLevin.Tableau` (`MIPRE/TM/CookLevin/Tableau.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 9 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/Tableau.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Tableau.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Computability.Language
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sign.Defs
import Mathlib.Logic.Relation
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_MIPRE_TM_MultiInput_Deterministic
import Definitions.Def_MIPRE_TM_CookLevin_Local
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin

/-!
# The Cook–Levin tableau of a multi-input machine

The 3SAT formula `tableau M s₀ s₁ S fixed chk` of a run of `S` steps of the machine `M`
(`planning/succinct-cook-levin.md`, S1; `answer_reduction.tex` `prop:standard-succinct-sat`):

* **Variables** (`TabVar`): for each time `t ≤ S`, tape and cell position, the one-hot cell
  values and the head bit; for each time the one-hot state; per step the emission flags
  `emitOne` (the accepting symbol `acc` is emitted) and `emitBad` (another symbol is), and
  per time the flag `emitted` (something was emitted before); and, per step and window, the
  gate variables of the check circuit `chk`.
* **Cells**: `2S + 7` positions per tape; cells `0, 1` and the last two hold the boundary
  marker. Input position value `k` of the machine (`0` the blank before the input, `1..L`
  the input, `L + 1` the blank after it) is cell `k + 2`; work-tape position `z ∈ ℤ` is
  cell `z + S + 3`, so that a head, which moves at most `S` cells, stays inside `2..2S+4`
  provided the inputs have length at most `2S + 1`.
* **Clauses**: the start rows (heads on their first cells, the start state, the fixed input
  tapes holding their strings, blank work tapes), the boundary rows (boundary cells and no
  heads there at every time), the free input tapes (a string over the two bit symbols `s₀`,
  `s₁` followed by blanks), the emission bookkeeping, the acceptance row (halted at time `S`,
  one emission, of `acc`), and at every step and window the circuit-to-3SAT clauses of `chk`
  on the window's variables. Windows are indexed by a center on every tape; the five cells
  of a window are the center and its two neighbors on each side.
* **The assignment of a run** (`runAssign`): the encodings of the configurations of the
  machine and the gate values of the check circuit on every window.

The check circuit is a parameter with its specification `IsCheckCircuit`: `chk.evalBits
(winBits win) = true ↔ checkPred M acc win`; the correctness of the tableau (`Correct.lean`)
is proved against the specification, and `S3` supplies the circuit.
-/

namespace MIPRE.TM.CookLevin

open Turing SAT

/-! ## Positions -/

/-- The number of cells of a tape of the tableau of `S` steps. -/
def numCells (S : ℕ) : ℕ := 2 * S + 7

/-- A cell position. -/
abbrev Pos (S : ℕ) := Fin (numCells S)

/-- A window center, offset by two: the window of center `c` covers the cells `c .. c + 4`,
its middle cell being `c + 2`. -/
abbrev Center (S : ℕ) := Fin (2 * S + 3)

/-- The cell at offset `δ` of the window of center `c`. -/
def cellIdx {S : ℕ} (c : Center S) (δ : Fin 5) : Pos S :=
  ⟨c + δ, by have := c.isLt; have := δ.isLt; unfold numCells; omega⟩

/-- The middle cell of a window. -/
def center {S : ℕ} (c : Center S) : Pos S := cellIdx c 2

/-- A boundary cell: the first two and the last two. -/
def Pos.IsBdry {S : ℕ} (p : Pos S) : Prop := (p : ℕ) < 2 ∨ numCells S ≤ (p : ℕ) + 2

instance {S : ℕ} (p : Pos S) : Decidable p.IsBdry := by unfold Pos.IsBdry; infer_instance

/-- The cell of a head at time `0`: an input head starts on the first symbol, position
value `1`, cell `3`; a work head at position `0`, cell `S + 3`. -/
def startCell {i w : ℕ} (S : ℕ) : Tape i w → Pos S
  | .inl _ => ⟨3, by unfold numCells; omega⟩
  | .inr _ => ⟨S + 3, by unfold numCells; omega⟩

/-- The value of cell `p` of an input tape holding `x`: the boundary marker on boundary
cells, the symbols of `x` on cells `3 .. |x| + 2`, blanks elsewhere. -/
def inputCellVal {Symbol : Type*} {S : ℕ} (x : List Symbol) (p : Pos S) : CellVal Symbol :=
  if p.IsBdry then .bdry
  else if h : 3 ≤ (p : ℕ) ∧ (p : ℕ) - 3 < x.length then .sym x[(p : ℕ) - 3] else .blank

/-- The value of cell `p` of a work tape at time `0`. -/
def workCellVal₀ {Symbol : Type*} {S : ℕ} (p : Pos S) : CellVal Symbol :=
  if p.IsBdry then .bdry else .blank

/-! ## Variables -/

/-- The variables of the tableau. -/
inductive TabVar (i w : ℕ) (Symbol State : Type*) (S G : ℕ) where
  | cell (t : Fin (S + 1)) (d : Tape i w) (p : Pos S) (v : CellVal Symbol)
  | head (t : Fin (S + 1)) (d : Tape i w) (p : Pos S)
  | state (t : Fin (S + 1)) (q : Option State)
  | emitOne (t : Fin S)
  | emitBad (t : Fin S)
  | emitted (t : Fin (S + 1))
  | aux (t : Fin S) (js : Tape i w → Center S) (g : Fin G)
  deriving DecidableEq

section Formula

variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S G : ℕ}

/-- The tableau variable of a window variable, at step `t` and centers `js`. -/
def winVarOf (t : Fin S) (js : Tape i w → Center S) :
    WinVar i w Symbol State → TabVar i w Symbol State S G
  | .cellPre d δ v => .cell t.castSucc d (cellIdx (js d) δ) v
  | .headPre d δ => .head t.castSucc d (cellIdx (js d) δ)
  | .cellPost d v => .cell t.succ d (center (js d)) v
  | .headPost d => .head t.succ d (center (js d))
  | .statePre q => .state t.castSucc q
  | .statePost q => .state t.succ q
  | .emitOne => .emitOne t
  | .emitBad => .emitBad t

/-- The number of window variables: the number of inputs of a check circuit. -/
abbrev winCard (i w : ℕ) (Symbol State : Type*) [Fintype Symbol] [DecidableEq Symbol]
    [Fintype State] [DecidableEq State] : ℕ :=
  Fintype.card (WinVar i w Symbol State)

/-- The bits of a window, in the canonical order. -/
noncomputable def winBits (win : WinVar i w Symbol State → Bool) : List Bool :=
  List.ofFn fun n : Fin (winCard i w Symbol State) => win ((Fintype.equivFin _).symm n)

/-- `chk` computes local consistency of a window: its specification, the hypothesis of the
correctness of the tableau (`Correct.lean`); `S3` supplies the circuit. -/
def IsCheckCircuit (M : MultiInputTM i w Symbol State) (acc : Symbol) (chk : Circuit) : Prop :=
  ∀ win : WinVar i w Symbol State → Bool, chk.evalBits (winBits win) = true ↔ checkPred M acc win

/-- The input variables of the check circuit at a window: the `n`-th window variable. -/
noncomputable def inpOf (t : Fin S) (js : Tape i w → Center S) (n : ℕ) : TabVar i w Symbol State S G :=
  if h : n < winCard i w Symbol State then winVarOf t js ((Fintype.equivFin _).symm ⟨n, h⟩)
  else .emitted 0

/-- The gate variables of the check circuit at a window. -/
def auxOf (t : Fin S) (js : Tape i w → Center S) (g : ℕ) : TabVar i w Symbol State S G :=
  if h : g < G then .aux t js ⟨g, h⟩ else .emitted 0

/-- A unit clause. -/
def unit (v : TabVar i w Symbol State S G) (b : Bool) : Clause3 (TabVar i w Symbol State S G) :=
  cl ⟨v, b⟩ ⟨v, b⟩ ⟨v, b⟩

/-- The clause `¬a ∨ b`. -/
def imp2 (a b : TabVar i w Symbol State S G) : Clause3 (TabVar i w Symbol State S G) :=
  cl ⟨a, false⟩ ⟨b, true⟩ ⟨b, true⟩

/-- The clause `¬a ∨ ¬b`. -/
def nand2 (a b : TabVar i w Symbol State S G) : Clause3 (TabVar i w Symbol State S G) :=
  cl ⟨a, false⟩ ⟨b, false⟩ ⟨b, false⟩

variable (M : MultiInputTM i w Symbol State) (acc s₀ s₁ : Symbol) (S) (G)
  (fixed : Fin i → Option (List Symbol))

/-- The start rows: heads on their first cells, the start state, the fixed input tapes
holding their strings, the work tapes blank. -/
def startClauses : Cnf3 (TabVar i w Symbol State S G) :=
  {c | ∃ d p, c = unit (.head 0 d p) (decide (p = startCell S d))} ∪
  {c | ∃ q, c = unit (.state 0 q) (decide (q = some M.q₀))} ∪
  {c | ∃ j x p v, fixed j = some x ∧ c = unit (.cell 0 (.inl j) p v) (decide (v = inputCellVal x p))} ∪
  {c | ∃ j p v, c = unit (.cell 0 (.inr j) p v) (decide (v = workCellVal₀ p))}

/-- The free input tapes at time `0`: boundary cells, the cell before the input blank, the
other cells one of `s₀`, `s₁`, blank, exactly one of them, with blanks trailing. -/
def freeClauses : Cnf3 (TabVar i w Symbol State S G) :=
  {c | ∃ j p v, fixed j = none ∧ p.IsBdry ∧ c = unit (.cell 0 (.inl j) p v) (decide (v = .bdry))} ∪
  {c | ∃ j p v, fixed j = none ∧ ¬ p.IsBdry ∧ v ≠ .sym s₀ ∧ v ≠ .sym s₁ ∧ v ≠ .blank ∧
    c = unit (.cell 0 (.inl j) p v) false} ∪
  {c | ∃ j v, fixed j = none ∧
    c = unit (.cell 0 (.inl j) ⟨2, by unfold numCells; omega⟩ v) (decide (v = .blank))} ∪
  {c | ∃ j p, fixed j = none ∧ ¬ p.IsBdry ∧
    c = cl ⟨.cell 0 (.inl j) p (.sym s₀), true⟩ ⟨.cell 0 (.inl j) p (.sym s₁), true⟩
      ⟨.cell 0 (.inl j) p .blank, true⟩} ∪
  {c | ∃ j p v v', fixed j = none ∧ ¬ p.IsBdry ∧ v ≠ v' ∧
    c = nand2 (.cell 0 (.inl j) p v) (.cell 0 (.inl j) p v')} ∪
  {c | ∃ (j : Fin i) (p p' : Pos S), fixed j = none ∧ 2 < (p : ℕ) ∧ ¬ p'.IsBdry ∧ p < p' ∧
    c = imp2 (.cell 0 (.inl j) p .blank) (.cell 0 (.inl j) p' .blank)}

/-- The boundary rows: boundary cells hold the marker and carry no head, at every time. -/
def bdryClauses : Cnf3 (TabVar i w Symbol State S G) :=
  {c | ∃ t d p v, p.IsBdry ∧ c = unit (.cell t d p v) (decide (v = .bdry))} ∪
  {c | ∃ t d p, p.IsBdry ∧ c = unit (.head t d p) false}

/-- The emission bookkeeping: nothing emitted before time `0`, `emitted (t + 1) ↔ emitted t
∨ emitOne t`, no emission after an emission, nothing but `acc` ever emitted. -/
def emitClauses : Cnf3 (TabVar i w Symbol State S G) :=
  {unit (.emitted 0) false} ∪
  {c | ∃ t : Fin S, c = cl ⟨.emitted t.succ, false⟩ ⟨.emitted t.castSucc, true⟩ ⟨.emitOne t, true⟩} ∪
  {c | ∃ t : Fin S, c = imp2 (.emitted t.castSucc) (.emitted t.succ)} ∪
  {c | ∃ t : Fin S, c = imp2 (.emitOne t) (.emitted t.succ)} ∪
  {c | ∃ t : Fin S, c = nand2 (.emitOne t) (.emitted t.castSucc)} ∪
  {c | ∃ t : Fin S, c = unit (.emitBad t) false}

/-- The acceptance row: halted at time `S`, and `acc` emitted. -/
def finalClauses : Cnf3 (TabVar i w Symbol State S G) :=
  {unit (.state (Fin.last S) none) true, unit (.emitted (Fin.last S)) true}

/-- The window clauses: the circuit-to-3SAT formula of the check circuit at every step and
window. -/
noncomputable def windowClauses (chk : Circuit) : Cnf3 (TabVar i w Symbol State S chk.gates.length) :=
  {c | ∃ (t : Fin S) (js : Tape i w → Center S), c ∈ chk.tseitin (inpOf t js) (auxOf t js)}

/-- **The tableau formula.** -/
noncomputable def tableau (M : MultiInputTM i w Symbol State) (s₀ s₁ : Symbol) (S : ℕ)
    (fixed : Fin i → Option (List Symbol)) (chk : Circuit) :
    Cnf3 (TabVar i w Symbol State S chk.gates.length) :=
  startClauses (S := S) (G := chk.gates.length) M fixed ∪
    freeClauses (S := S) (G := chk.gates.length) s₀ s₁ fixed ∪
    bdryClauses (S := S) (G := chk.gates.length) ∪ emitClauses (S := S) (G := chk.gates.length) ∪
    finalClauses (S := S) (G := chk.gates.length) ∪ windowClauses (S := S) chk

end Formula

/-! ## The assignment of a run -/

section Run

variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
  (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}

open MultiInputTM

/-- The value of cell `p` of tape `d` in a configuration. -/
def cellValAt (c : Cfg i w Symbol State input) (d : Tape i w) (p : Pos S) : CellVal Symbol :=
  match d with
  | .inl j => inputCellVal (input j) p
  | .inr j => if p.IsBdry then .bdry else .ofOpt (c.workTapes j ((p : ℤ) - (S + 3)))

/-- The cell of the head of tape `d`, as an integer. -/
def headCell (c : Cfg i w Symbol State input) : Tape i w → ℤ
  | .inl j => (c.inputPos j : ℤ) + 2
  | .inr j => c.workTapePos j + (S + 3)

/-- The configuration at time `t` of the run on `input`. -/
def cfgAt (t : ℕ) : Cfg i w Symbol State input := M.configs (M.initCfg input) t

/-- The assignment of the run on the non-auxiliary variables. -/
def baseAssign (G : ℕ) : TabVar i w Symbol State S G → Bool
  | .cell t d p v => decide (cellValAt (S := S) (cfgAt M (input := input) t) d p = v)
  | .head t d p => decide (headCell (S := S) (cfgAt M (input := input) t) d = p)
  | .state t q => decide ((cfgAt M (input := input) t).state = q)
  | .emitOne t => decide (M.outputSymbol (cfgAt M (input := input) t) = some acc)
  | .emitBad t => decide (M.outputSymbol (cfgAt M (input := input) t) ≠ none ∧
      M.outputSymbol (cfgAt M (input := input) t) ≠ some acc)
  | .emitted t => decide (M.outputString (M.initCfg input) t ≠ [])
  | .aux _ _ _ => false

/-- The assignment of the run: the encodings of its configurations, and on the auxiliary
variables the gate values of the check circuit at every window. -/
noncomputable def runAssign (chk : Circuit) : TabVar i w Symbol State S chk.gates.length → Bool
  | .aux t js g => chk.valueAt (fun n => baseAssign M acc (input := input) chk.gates.length
      (inpOf (G := chk.gates.length) t js n)) g
  | v => baseAssign M acc (input := input) chk.gates.length v

end Run

end MIPRE.TM.CookLevin


