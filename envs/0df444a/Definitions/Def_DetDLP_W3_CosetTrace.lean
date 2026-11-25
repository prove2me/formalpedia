-- Prove2me | Definitions.Def_DetDLP_W3_CosetTrace
-- name    : DetDLP_W3_CosetTrace
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-23T20:34:59.160265+00:00
-- url     : https://prove2.me/theorems/c9511094-fd1a-474d-95fa-1ffff485a583
-- title:
--   Stage II: exact initialization and halving traces
-- statement:
--   A trace starts at the full modular HNF and applies the normalized generator row and all coordinate-consistency rows. Each later edge carries a fixed-shift tuple pair of positive filter weight, its exact HNF intersection, and a factor-two cardinality certificate. A complete trace ends at a representative passing every fixed shift within the binary ceiling-logarithm budget.
-- source:
--   Deterministic Discrete Logarithms, §4.1–4.3, (4.1)–(4.5), proof of Theorem 1.1, pp. 13–16; referee revision R1.

import Definitions.Def_DetDLP_FilterAndCoset

set_option autoImplicit false

namespace DetDLP

abbrev w3_Label (M N : ℕ) := Fin N → ZMod M
abbrev w3_Rep (M N : ℕ) := w3_Label M N × Matrix (Fin N) (Fin N) ℤ
abbrev w3_Row (M N : ℕ) := w3_Label M N × ZMod M

def w3_holds {M N : ℕ} (r : w3_Row M N) (x : w3_Label M N) : Prop :=
  ∑ i, r.1 i * x i = r.2

def w3_coset {M N : ℕ} [NeZero M] (s : w3_Rep M N) := affineCoset M s.1 s.2

def w3_full (M N : ℕ) : w3_Rep M N := (0, 1)

def w3_update {M N : ℕ} [NeZero M] (r : w3_Row M N) (s t : w3_Rep M N) : Prop :=
  IsModularLatticeBasis M t.2 ∧ w3_coset t = {x ∈ w3_coset s | w3_holds r x}

inductive w3_InitTrace {M N : ℕ} [NeZero M] : List (w3_Row M N) → w3_Rep M N → w3_Rep M N → Prop
  | nil (s) : w3_InitTrace [] s s
  | cons {r rs s t u} : w3_update r s t → w3_InitTrace rs t u → w3_InitTrace (r::rs) s u

variable {G : Type*} {m : ℕ} (FB : IndexedFactorBase G m) (M : ℕ) [NeZero M]

def w3_unitRow (j : Fin FB.totalCoords) : w3_Label M FB.totalCoords := fun i => if i = j then 1 else 0

def w3_initRows (U : Fin FB.totalCoords → FB.BlockTuple) : List (w3_Row M FB.totalCoords) :=
  (w3_unitRow FB M FB.genCoord, 1) :: (List.finRange FB.totalCoords).map fun j =>
    (fun i => w3_unitRow FB M j i - (FB.tupleCnt (U j) i : ZMod M), 0)

def w3_shiftRow (X Y : FB.BlockTuple) : w3_Row M FB.totalCoords :=
  (fun i => (FB.tupleCnt Y i : ZMod M) - (FB.tupleCnt X i : ZMod M), 1)

def w3_delta (y : w3_Label M FB.totalCoords) (X Y : FB.BlockTuple) : ℤ :=
  FB.tupleLabelSum M y Y - FB.tupleLabelSum M y X

variable [AddCommGroup G] (P : G)

def w3_pass (y : w3_Label M FB.totalCoords) : Prop := ∀ X Y : FB.BlockTuple,
  FB.tupleVal Y = FB.tupleVal X + P → w3_holds (w3_shiftRow FB M X Y) y

/-- A proper separator step records the pair, its positive filter weight, the exact HNF intersection,
    and the factor-of-two bound. No halving is required in an initialization trace. -/
def w3_cut (s t : w3_Rep M FB.totalCoords) : Prop := ∃ X Y : FB.BlockTuple,
  FB.tupleVal Y = FB.tupleVal X + P ∧
  0 < (filterPoly (2*m) M).eval (w3_delta FB M s.1 X Y) ∧
  ¬ w3_holds (w3_shiftRow FB M X Y) s.1 ∧
  w3_update (w3_shiftRow FB M X Y) s t ∧ 2 * Nat.card (w3_coset t) ≤ Nat.card (w3_coset s)

inductive w3_Cuts : ℕ → w3_Rep M FB.totalCoords → w3_Rep M FB.totalCoords → Prop
  | nil (s) : w3_Cuts 0 s s
  | cons {n s t u} : w3_cut FB M P s t → w3_Cuts n t u → w3_Cuts (n+1) s u

/-- Complete run certificate: initialize from the full HNF, take a bounded sequence of genuine
    separator cuts, and finish with a representative passing every fixed shift. -/
def w3_Outcome (U : Fin FB.totalCoords → FB.BlockTuple) (y : w3_Label M FB.totalCoords) : Prop :=
  ∃ (s t : w3_Rep M FB.totalCoords) (n : ℕ),
    w3_InitTrace (w3_initRows FB M U) (w3_full M FB.totalCoords) s ∧
    w3_Cuts FB M P n s t ∧ n ≤ Nat.clog 2 (M ^ FB.totalCoords) ∧ t.1 = y ∧ w3_pass FB M P y

end DetDLP


