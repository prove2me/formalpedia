-- Prove2me | Definitions.Def_CommThresholdPR_StrongConverse_Extraction
-- name    : CommThresholdPR_StrongConverse_Extraction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:27:39.629722+00:00
-- url     : https://prove2.me/theorems/797035e2-41a7-488f-9229-48f01738ceb1
-- title:
--   Construction 4.1: successful-coordinate conditioning and coordinate extraction
-- statement:
--   After fixing the source protocol's randomness, run its deterministic binary tree on $\mu^{\otimes n}$. Let $W_i$ denote success on coordinate $i$ and $W_S=\bigcap_{i\in S}W_i$. The experiment $Q$ is the actual input law conditioned on $W_S$; transcript and outputs are deterministic functions of this input.
--
--   $$q=\mathcal L_Q\bigl(X_J,Y_J,A_J,B_J,(J,X_{<J},Y_{>J},\overline T)\bigr),\qquad \overline T=(T,A_S,B_S).$$
--   Here $J$ is sampled uniformly and independently of $Q$. Prefixes and suffixes use their exact coordinate subtypes, so empty strings are retained. Selected outputs are appended through reversible binary encodings, giving the same information as the displayed augmented transcript. The setup predicate lists only the source's input, cost, success and chosen-set conditions. A tape-fixing relation records support-compatible local choices and public seed; it includes no cost or error conclusion. No locality, divergence or information bound is assumed.
-- source:
--   Daiki Suruga, The Exact Communication Threshold for Parallel Repetition, STOC 2027 submission #304 (October 2026), §4 and Construction 4.1, pp. 12–13; (25)–(26), p. 13, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/304.pdf

import Definitions.Def_CommThresholdPR_StrongConverse_Model

noncomputable section

namespace CommThresholdPR.StrongConverse

/-- Deterministic trees obtained after fixing all random tapes in §4. -/
inductive DecisionTree (X Y A B : Type) where
  | leaf (a : X → A) (b : Y → B)
  | alice (bit : X → Bool) (zero one : DecisionTree X Y A B)
  | bob (bit : Y → Bool) (zero one : DecisionTree X Y A B)

namespace DecisionTree
variable {X Y A B : Type}

def run : DecisionTree X Y A B → X → Y → List Bool × A × B
  | .leaf a b, x, y => ([], a x, b y)
  | .alice bit l r, x, y =>
      let z := if bit x then r.run x y else l.run x y
      (bit x :: z.1, z.2)
  | .bob bit l r, x, y =>
      let z := if bit y then r.run x y else l.run x y
      (bit y :: z.1, z.2)

def randomize : DecisionTree X Y A B → BinaryTree X Y A B
  | .leaf a b => .leaf (fun x => PMF.pure (a x)) (fun y => PMF.pure (b y))
  | .alice f l r => .alice (fun x => PMF.pure (f x)) l.randomize r.randomize
  | .bob f l r => .bob (fun y => PMF.pure (f y)) l.randomize r.randomize

def protocol (t : DecisionTree X Y A B) : Protocol X Y A B :=
  Protocol.privateTree t.randomize

def sendAliceList {C : Type} [Nonempty C] (p : X → C)
    (k : C → DecisionTree X Y A B) : List C → DecisionTree X Y A B
  | [] => by classical exact k (Classical.arbitrary C)
  | c :: cs => by classical exact .alice (fun x => decide (p x = c)) (sendAliceList p k cs) (k c)

def sendBobList {C : Type} [Nonempty C] (p : Y → C)
    (k : C → DecisionTree X Y A B) : List C → DecisionTree X Y A B
  | [] => by classical exact k (Classical.arbitrary C)
  | c :: cs => by classical exact .bob (fun y => decide (p y = c)) (sendBobList p k cs) (k c)

def appendSelected {n : ℕ} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (S : Finset (Fin n)) :
    DecisionTree X Y (Fin n → A) (Fin n → B) → DecisionTree X Y (Fin n → A) (Fin n → B)
  | .leaf a b => by
      classical
      exact sendAliceList (fun x (i : S) => a x i) (fun _ =>
        sendBobList (fun y (i : S) => b y i) (fun _ => .leaf a b) Finset.univ.toList)
        Finset.univ.toList
  | .alice f l r => .alice f (appendSelected S l) (appendSelected S r)
  | .bob f l r => .bob f (appendSelected S l) (appendSelected S r)

end DecisionTree

/-- Construction 4.1, pp.12–13. The experiment is stored on its input carrier
since all transcript and output variables are actual deterministic functions.
The augmented transcript uses reversible finite binary encodings of A_S,B_S. -/
structure Extraction (X Y A B : Type) [Fintype X] [Fintype Y]
    [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] (n : ℕ) where
  μ : PMF (X × Y)
  g : TotalRelation X Y A B
  tree : DecisionTree (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B)
  selected : Finset (Fin n)

namespace Extraction
variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Nonempty A] [Nonempty B] {n : ℕ}

abbrev Inputs (X Y : Type) (n : ℕ) := (Fin n → X) × (Fin n → Y)
abbrev Prefix (X : Type) (i : Fin n) := {j : Fin n // j < i} → X
abbrev Suffix (Y : Type) (i : Fin n) := {j : Fin n // i < j} → Y

def pre (z : Inputs X Y n) (i : Fin n) : Prefix X i := fun j => z.1 j

def suf (z : Inputs X Y n) (i : Fin n) : Suffix Y i := fun j => z.2 j

def outputA (e : Extraction X Y A B n) (z : Inputs X Y n) : Fin n → A :=
  (e.tree.run z.1 z.2).2.1

def outputB (e : Extraction X Y A B n) (z : Inputs X Y n) : Fin n → B :=
  (e.tree.run z.1 z.2).2.2

def wins (e : Extraction X Y A B n) (i : Fin n) (z : Inputs X Y n) : Prop :=
  e.g.accepts (z.1 i) (z.2 i) (e.outputA z i) (e.outputB z i)

def winsSet (e : Extraction X Y A B n) (S : Finset (Fin n)) (z : Inputs X Y n) : Prop :=
  ∀ i ∈ S, e.wins i z

def P (e : Extraction X Y A B n) := inputPower e.μ n

def Q (e : Extraction X Y A B n) := condition e.P (e.winsSet e.selected)

def augmented (e : Extraction X Y A B n) := e.tree.appendSelected e.selected

abbrev AugTrace (e : Extraction X Y A B n) := e.augmented.randomize.Trace

def trace (e : Extraction X Y A B n) (z : Inputs X Y n) : e.AugTrace :=
  fun j => (e.augmented.run z.1 z.2).1[j.val]?

abbrev Auxiliary (e : Extraction X Y A B n) :=
  (i : Fin n) × (Prefix X i × Suffix Y i × e.AugTrace)

/-- The fixed-coordinate law of (X_i,Y_i,A_i,B_i,V_i). -/
def coordinate (e : Extraction X Y A B n) (i : Fin n) :
    PMF (Record X Y A B (Prefix X i × Suffix Y i × e.AugTrace)) :=
  e.Q.map fun z => ⟨z.1 i, z.2 i, e.outputA z i, e.outputB z i, (pre z i, suf z i, e.trace z)⟩

def uniformIndex (n : ℕ) (hn : 0 < n) : PMF (Fin n) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact PMF.uniformOfFintype (Fin n)

/-- J is uniform independently of Q; variable-length strings have their exact
subtype coordinate carriers, including empty strings at the boundaries. -/
def q (e : Extraction X Y A B n) (hn : 0 < n) : PMF (Record X Y A B e.Auxiliary) :=
  (uniformIndex n hn).bind fun i => (e.coordinate i).map fun z =>
    ⟨z.x, z.y, z.a, z.b, ⟨i, z.v⟩⟩

/-- Exactly the three requirements on S in Construction 4.1, with all setup
bounds. This does not include any conclusion of Lemmas 4.2–6.2. -/
def Setup (e : Extraction X Y A B n) (R p ε : ℝ) : Prop :=
  0 ≤ R ∧ 0 < p ∧ p ≤ 1 ∧ 0 < ε ∧ ε < 1 ∧
  (e.tree.protocol.cost : ℝ) ≤ n * R ∧
  p ≤ prob e.P (fun z => ∀ i, e.wins i z) ∧
  (e.selected.card : ℝ) ≤ Real.logb 2 (1 / p) / (-Real.logb 2 (1 - ε)) ∧
  p ≤ prob e.P (e.winsSet e.selected) ∧
  ∀ i, 1 - ε ≤ cprob e.P (e.wins i) (e.winsSet e.selected)

end Extraction
end CommThresholdPR.StrongConverse

namespace CommThresholdPR.StrongConverse
/-- Fix an independent finite private choice table at every node and local
input. This relation specifies only the tape fixing, never a success bound. -/
inductive IsFixing {X Y A B : Type} : DecisionTree X Y A B → BinaryTree X Y A B → Prop
  | leaf (a : X → A) (b : Y → B) (pa : X → PMF A) (pb : Y → PMF B)
      (ha : ∀ x, a x ∈ (pa x).support) (hb : ∀ y, b y ∈ (pb y).support) :
      IsFixing (.leaf a b) (.leaf pa pb)
  | alice (f : X → Bool) (pf : X → PMF Bool) (l r : DecisionTree X Y A B)
      (pl pr : BinaryTree X Y A B) (hf : ∀ x, f x ∈ (pf x).support)
      (hl : IsFixing l pl) (hr : IsFixing r pr) :
      IsFixing (.alice f l r) (.alice pf pl pr)
  | bob (f : Y → Bool) (pf : Y → PMF Bool) (l r : DecisionTree X Y A B)
      (pl pr : BinaryTree X Y A B) (hf : ∀ y, f y ∈ (pf y).support)
      (hl : IsFixing l pl) (hr : IsFixing r pr) :
      IsFixing (.bob f l r) (.bob pf pl pr)

def Protocol.fixed {X Y A B : Type} (π : Protocol X Y A B)
    (t : DecisionTree X Y A B) : Prop :=
  ∃ r, π.publicLaw r ≠ 0 ∧ IsFixing t (π.tree r)
end CommThresholdPR.StrongConverse


