-- Prove2me | Definitions.Def_Nintendo_game
-- name    : Nintendo_game
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-21T05:51:16.502991+00:00
-- url     : https://prove2.me/theorems/43518e87-49e7-4e38-96e9-11b92b9c29ea
-- title:
--   The game layer: reachability, the two gadget frameworks of Section 2, and the hardness predicates
-- statement:
--   The game layer of the Nintendo mission: the abstract scaffolding of the paper's Section 2. A game is a state space with a one-step reachability relation, and multi-step reachability is its reflexive-transitive closure: a configuration is reachable when some finite sequence of legal steps leads to it. The layer fixes the four hardness predicates. A framework is 3-SAT-hard when some constant bounds the size of the level built from each 3-CNF formula by the square of the formula's size, and the formula is satisfiable exactly when a goal configuration of its level is reachable from the start; the quantified variant states the same shape for quantified Boolean formulas and truth. For games with explicit levels the predicates are existential: for every formula there exists a level of at most the bounded size with the same solvability equivalence. The two frameworks of the paper's Section 2 are then defined as explicit configuration types with step relations. The 3-SAT framework of Section 2.1 runs a protocol of start, variable-setting, literal, check, and finish states: the player sets the variables one at a time, may visit clause gadgets after each choice - a visit unlocks a clause exactly when the chosen literal occurs in it - and, after the last variable, walks a check path whose gates open exactly when the corresponding clause has been unlocked. The TQBF framework of Section 2.2 runs a quantifier row in which existential quantifiers are free choices and universal quantifiers are forced truths on the forward pass, a test path over the clauses, and a back protocol that returns to the last universal quantifier, flips it to falsehood, and re-walks the suffix, so that the finish is reachable exactly when the quantified formula is true.
-- source:
--   G. Aloupis, E. D. Demaine, A. Guo, G. Viglietta, Classic Nintendo games are (computationally) hard, Theoret. Comput. Sci. 586 (2015) 135-160, Sections 2.1-2.2.

import Mathlib
import Definitions.Def_Nintendo_sat

/-!
# The game layer: reachability, the two gadget frameworks, and the hardness predicates

The game layer of the Nintendo mission: abstract games and multi-step
reachability; grid positions and list helpers; the four hardness predicates
(framework and per-game, for 3-CNF and for quantified Boolean formulas); the
3-SAT framework of Section 2.1 and the TQBF framework of Section 2.2 as
explicit configuration types with step relations.
-/

namespace Nintendo

/-- A game is a state space with a one-step reachability relation. -/
structure Game (α : Type) where
  step : α → α → Prop

/-- Multi-step reachability: the reflexive-transitive closure of the step
relation of the game. -/
inductive Reachable {α : Type} (g : Game α) : α → α → Prop
  | refl (t : α) : Reachable g t t
  | step {t u v : α} : Reachable g t u → g.step u v → Reachable g t v

/-- Positions on the grid: integer coordinates. -/
abbrev Pos := ℤ × ℤ

/-- Update a grid function at a single position. -/
def setTile {τ : Type} (g : Pos → τ) (p : Pos) (t : τ) : Pos → τ :=
  fun q => if decide (q = p) then t else g q

/-- The i-th entry of a Boolean list, or false beyond the end. -/
def getAt : List Bool → ℕ → Bool
  | [], _ => false
  | b :: _, 0 => b
  | _ :: as, i + 1 => getAt as i

/-- Replace the i-th entry of a Boolean list. -/
def updAt : List Bool → ℕ → Bool → List Bool
  | [], _, _ => []
  | _ :: as, 0, b => b :: as
  | a :: as, i + 1, b => a :: updAt as i b

/-- The i-th entry of a position list, or the origin beyond the end. -/
def nthPos (l : List Pos) (i : ℕ) : Pos := l.getD i (0, 0)

/-- Replace the i-th entry of a position list. -/
def updAtPos : List Pos → ℕ → Pos → List Pos
  | [], _, _ => []
  | _ :: ps, 0, q => q :: ps
  | p :: ps, i + 1, q => p :: updAtPos ps i q

/-- Whether a position occurs in a list. -/
def posIn (p : Pos) (l : List Pos) : Bool := l.any (fun c => decide (p = c))

/-- The i-th clause of a formula, or the empty clause beyond the end. -/
def nthClause (φ : Form) (i : ℕ) : Clause := φ.getD i []

/-- One more than the largest variable index occurring in a formula. -/
def nVar (φ : Form) : ℕ :=
  (φ.foldl (fun acc c => c.foldl (fun a l => if a < litVar l then litVar l else a) acc) 0) + 1

/-- Whether the quantifier at position i of the prefix is universal. -/
def isUniv (qs : List Quant) (i : ℕ) : Bool :=
  match qs.getD i Quant.ex with
  | Quant.univ => true
  | Quant.ex => false

/-- The largest index below b whose quantifier is universal, if any. -/
def lastUnivBelow (qs : List Quant) (b : ℕ) : Option ℕ :=
  (List.range b).foldl (fun acc i => if isUniv qs i then some i else acc) none

/-- The largest universal-quantifier index of the prefix, if any. -/
def lastUniv (qs : List Quant) : Option ℕ := lastUnivBelow qs qs.length

/-- Whether a literal holds under a finite assignment (false beyond its end). -/
def litTrueAt (as : List Bool) : Lit → Bool
  | Lit.pos v => as.getD v false
  | Lit.neg v => !(as.getD v false)

/-- Whether the k-th clause of a formula is satisfied by a finite assignment. -/
def clauseSatAt (as : List Bool) (φ : Form) (k : ℕ) : Bool :=
  (φ.getD k []).any (litTrueAt as)

/-- NP-hardness of a framework that builds one level per formula: there is a
constant such that every 3-CNF formula maps to a level of size at most the
constant times the square of the formula size, and the level is solvable
exactly when the formula is satisfiable. -/
def Hard3Sat {α : Type} (game : Form → Game α) (start : Form → α)
    (goal : Form → α → Prop) (size : Form → ℕ) : Prop :=
  ∃ C : ℕ, ∀ φ : Form, Is3Sat φ →
    size φ ≤ C * (formulaSize φ + 1) ^ 2 ∧
      (Sat φ ↔ ∃ t : α, goal φ t ∧ Reachable (game φ) (start φ) t)

/-- PSPACE-hardness of a framework that builds one level per quantified
formula. -/
def HardTqbf {α : Type} (game : QForm → Game α) (start : QForm → α)
    (goal : QForm → α → Prop) (size : QForm → ℕ) : Prop :=
  ∃ C : ℕ, ∀ ψ : QForm, IsQbf ψ →
    size ψ ≤ C * (qbfSize ψ + 1) ^ 2 ∧
      (QTrue ψ ↔ ∃ t : α, goal ψ t ∧ Reachable (game ψ) (start ψ) t)

/-- NP-hardness of a game with explicit levels: there is a constant such
that every 3-CNF formula has a level of size at most the constant times the
square of the formula size which is solvable exactly when the formula is
satisfiable. -/
def LevelHard3Sat {α : Type} {γ : Type} (gameOf : γ → Game α) (startOf : γ → α)
    (goalOf : γ → α → Prop) (sizeOf : γ → ℕ) : Prop :=
  ∃ C : ℕ, ∀ φ : Form, Is3Sat φ →
    ∃ L : γ, sizeOf L ≤ C * (formulaSize φ + 1) ^ 2 ∧
      (Sat φ ↔ ∃ t : α, goalOf L t ∧ Reachable (gameOf L) (startOf L) t)

/-- PSPACE-hardness of a game with explicit levels. -/
def LevelHardTqbf {α : Type} {γ : Type} (gameOf : γ → Game α) (startOf : γ → α)
    (goalOf : γ → α → Prop) (sizeOf : γ → ℕ) : Prop :=
  ∃ C : ℕ, ∀ ψ : QForm, IsQbf ψ →
    ∃ L : γ, sizeOf L ≤ C * (qbfSize ψ + 1) ^ 2 ∧
      (QTrue ψ ↔ ∃ t : α, goalOf L t ∧ Reachable (gameOf L) (startOf L) t)

/-- Configurations of the 3-SAT framework of Section 2.1: the start, the
variable-setting states, the literal states, the check states, and the
finish. -/
inductive FWConf where
  | start : FWConf
  | vset : ℕ → List Bool → FWConf
  | lit : ℕ → Bool → List Bool → FWConf
  | check : ℕ → List Bool → FWConf
  | finish : FWConf
  deriving Repr

/-- The step relation of the 3-SAT framework run on the formula. From the
start the player sets the variables one at a time; after each choice the
player may visit clause gadgets, and a visit unlocks a clause exactly when
the chosen literal occurs in it; after the last variable the player walks
the check path, whose clause gates open exactly when the clause was
unlocked. -/
def fwStep (φ : Form) : FWConf → FWConf → Prop
  | FWConf.start, FWConf.vset i u => i = 0 ∧ u = []
  | FWConf.vset i u, FWConf.lit i' _b u' =>
      i = i' ∧ u = u' ∧ i < nVar φ
  | FWConf.lit i b u, FWConf.lit i' b' u' =>
      i = i' ∧ b = b' ∧ ∃ c, c < φ.length ∧ u' = updAt u c true ∧
        (if b then Lit.pos i else Lit.neg i) ∈ nthClause φ c
  | FWConf.lit i _b u, FWConf.vset i' u' => i' = i + 1 ∧ u = u'
  | FWConf.vset i u, FWConf.check k u' => nVar φ ≤ i ∧ k = 0 ∧ u = u'
  | FWConf.check k u, FWConf.check k' u' =>
      u = u' ∧ k' = k + 1 ∧ k < φ.length ∧ getAt u k = true
  | FWConf.check k _u, FWConf.finish => φ.length ≤ k
  | _, _ => False

/-- The 3-SAT framework: the level built from a formula is the protocol of
the formula's gadgets. -/
def frameworkGame (φ : Form) : Game FWConf := { step := fwStep φ }

def fwStart (_φ : Form) : FWConf := FWConf.start

def fwGoal (_φ : Form) (t : FWConf) : Prop := t = FWConf.finish

/-- The size of the 3-SAT framework level: the square of the numbers of
variable and clause gadgets. -/
def fwLevelSize (φ : Form) : ℕ := (nVar φ + φ.length + 1) ^ 2

/-- Configurations of the TQBF framework of Section 2.2: the start, the row
states (the choices made so far), the test states, the back states, and the
finish. -/
inductive QFConf where
  | start : QFConf
  | row : List Bool → QFConf
  | test : List Bool → ℕ → QFConf
  | back : List Bool → ℕ → QFConf
  | finish : QFConf
  deriving Repr

/-- The step relation of the TQBF framework run on the quantified formula.
The player walks the quantifier row, appending one choice per existential
quantifier and a forced truth per universal quantifier on the forward
pass; the test path checks every clause; when a universal remains, the
player returns to the last universal position, flips it to falsehood, and
re-walks the suffix, until every universal has been tried both ways. -/
def qfStep (ψ : QForm) : QFConf → QFConf → Prop
  | QFConf.start, QFConf.row as => as = []
  | QFConf.row as, QFConf.row as' =>
      ∃ b : Bool, as' = as ++ [b] ∧ as.length < ψ.1.length ∧
        (isUniv ψ.1 as.length = true → b = true)
  | QFConf.row as, QFConf.test as' k =>
      as' = as ∧ k = 0 ∧ as.length = ψ.1.length
  | QFConf.test as k, QFConf.test as' k' =>
      as' = as ∧ k' = k + 1 ∧ k < ψ.2.length ∧ clauseSatAt as ψ.2 k = true
  | QFConf.test _as k, QFConf.finish =>
      ψ.2.length ≤ k ∧ lastUniv ψ.1 = none
  | QFConf.test as k, QFConf.back as' j =>
      as' = as ∧ ψ.2.length ≤ k ∧ lastUniv ψ.1 = some j
  | QFConf.back as j, QFConf.row as' =>
      getAt as j = true ∧ as' = updAt (List.take (j + 1) as) j false
  | QFConf.back as j, QFConf.back as' j' =>
      getAt as j = false ∧ as' = as ∧
        ∃ i, lastUnivBelow ψ.1 j = some i ∧ j' = i
  | QFConf.back as j, QFConf.finish =>
      getAt as j = false ∧ lastUnivBelow ψ.1 j = none
  | _, _ => False

/-- The TQBF framework: the level built from a quantified formula is the
protocol of its quantifier and door gadgets. -/
def qfGame (ψ : QForm) : Game QFConf := { step := qfStep ψ }

def qfStart (_ψ : QForm) : QFConf := QFConf.start

def qfGoal (_ψ : QForm) (t : QFConf) : Prop := t = QFConf.finish

/-- The size of the TQBF framework level. -/
def qfLevelSize (ψ : QForm) : ℕ := (ψ.1.length + ψ.2.length + 1) ^ 2

end Nintendo


