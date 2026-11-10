-- Prove2me | Definitions.Def_NogoodColoring1137_Main_Folds
-- name    : NogoodColoring1137_Main_Folds
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T17:01:30.274932+00:00
-- url     : https://prove2.me/theorems/1e7e10ee-c999-434d-99b0-902c8402db77
-- title:
--   Connector chains and all fold-pattern cases
-- statement:
--   The fold of different colors is the third color; equal colors give an undefined fold. A connector has $z_1=q_1$ and edges $z_{i-1}z_i,q_iz_i$ for $2\le i\le t$.
--   $$F_1=c(q_1),\quad F_i=F_{i-1}*c(q_i),\qquad \ell(n)=5\lceil\log_4(n+1)\rceil-2.$$
--   PatternA and PatternB encode all the source equalities and inequalities, including the four displayed cases and the exceptional $p=r=2$ case. Variable positions are 1 and every even position. Empty ranges impose nothing.
--
--   These objects expose the forcing constraints for the nogood theorem. **Formalization Note** Fold positions are one-based, bounded natural indices. Physical roots may repeat. Nat.clog computes the ceiling exactly on the theorem's positive range.
-- source:
--   Philip Whittington, STOC 2027 submission #1137 (October 2026), §§5.1–5.2, pp.14–16

import Mathlib
import Definitions.Def_NogoodColoring1137_Main_Instances

namespace NogoodColoring1137.Main

/-- Undefined exactly on equal inputs. -/
def Fold (a b : Color) : Option Color :=
  if a = b then none else
    (List.finRange 3).find? (fun c => c ≠ a ∧ c ≠ b)

/-- One-based paper indices; values outside a stated prefix have no role. -/
def FoldPrefix (c : ℕ → Color) : ℕ → Option Color
  | 0 => none
  | 1 => some (c 1)
  | k+2 => (FoldPrefix c (k+1)).bind (fun b => Fold b (c (k+2)))

def Connector {n : ℕ} (G : SimpleGraph (Fin n)) (t : ℕ)
    (q z : ℕ → Fin n) : Prop :=
  1 ≤ t ∧ z 1 = q 1 ∧ ∀ i, 2 ≤ i → i ≤ t → G.Adj (z (i-1)) (z i) ∧ G.Adj (q i) (z i)

def PatternA (r : ℕ) (c : ℕ → Color) : Prop :=
  (∀ i, 1 ≤ i → i ≤ r → c i ≠ 0) ∧ c 1 ≠ c 2 ∧
    ∀ j, 1 ≤ j → 2*j+2 ≤ r → c (2*j+1) = c (2*j+2)

def VariablePosition (r p : ℕ) : Prop :=
  1 ≤ p ∧ p ≤ r ∧ (p = 1 ∨ Even p)

/-- All four displayed cases, including p=r=2, with empty ranges literally empty. -/
def PatternB (r p : ℕ) (c : ℕ → Color) : Prop :=
  VariablePosition r p ∧ c p = 0 ∧
  (∀ i, 1 ≤ i → i ≤ r → i ≠ p → c i ≠ 0) ∧
  (p = 1 → ∀ j, 1 ≤ j → 2*j+1 ≤ r-1 → c (2*j) = c (2*j+1)) ∧
  (p = 2 → p < r → c 1 = c 3 ∧
    ∀ j, 2 ≤ j → 2*j+1 ≤ r-1 → c (2*j) = c (2*j+1)) ∧
  (4 ≤ p → p < r → c 1 ≠ c 2 ∧
    (∀ j, 1 ≤ j → 2*j+2 ≤ p-2 → c (2*j+1) = c (2*j+2)) ∧
    c (p-1) ≠ c (p+1) ∧
    ∀ j, p+2 ≤ 2*j → 2*j+1 ≤ r-1 → c (2*j) = c (2*j+1)) ∧
  (4 ≤ p → p = r → c 1 ≠ c 2 ∧
    ∀ j, 1 ≤ j → 2*j+2 ≤ r-2 → c (2*j+1) = c (2*j+2))

def NogoodLength (n : ℕ) : ℕ := 5 * Nat.clog 4 (n+1) - 2

end NogoodColoring1137.Main


