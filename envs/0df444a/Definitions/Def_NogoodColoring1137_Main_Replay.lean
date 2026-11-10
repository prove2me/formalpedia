-- Prove2me | Definitions.Def_NogoodColoring1137_Main_Replay
-- name    : NogoodColoring1137_Main_Replay
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T17:01:14.886185+00:00
-- url     : https://prove2.me/theorems/e319331a-279c-467d-915f-e2a70a2419e2
-- title:
--   Algorithm 1: deterministic minimum-potential replay
-- statement:
--   Initialize with exactly one supplied certificate on every $\ell$-scope, and no smaller entries. Scan coordinates and labels in increasing order, choosing the first minimum-potential slice label. Retain that singleton and slice at an exceptional position; otherwise delete the label and project.
--   $$B_A=\prod_vM_v^A,\qquad A\subseteq V,\quad |A|\le\min(K,n).$$
--   Every replay starts afresh from the same initial table. All choices use only that table and previous exception decisions. These are the specific boxes of Lemma 4.3.
--
--   **Formalization Note** Positivity allows the finite label scan; theorems supply $d_v\ge2$. Certificate values away from exact-$\ell$ scopes are unused.
-- source:
--   Philip Whittington, STOC 2027 submission #1137 (October 2026), §4.2, p.12

import Mathlib
import Definitions.Def_NogoodColoring1137_Main_Codes

namespace NogoodColoring1137.Main

/-- Smallest ordered label attaining the minimum, using only the table. -/
def MinimumLabel {n : ℕ} {d : Fin n → ℕ} (hd : ∀ v, 0 < d v)
    (ell : ℕ) (U : Finset (Fin n)) (W : Table d) (v : Fin n) : Fin (d v) :=
  (List.finRange (d v)).foldl (fun best b =>
    if Potential ell (U.erase v) (SliceTable v b W) <
       Potential ell (U.erase v) (SliceTable v best W) then b else best) ⟨0, hd v⟩

structure ReplayState {n : ℕ} (d : Fin n → ℕ) where
  active : Finset (Fin n)
  table : Table d
  sides : Box d

def ReplayStep {n : ℕ} {d : Fin n → ℕ} (hd : ∀ v, 0 < d v)
    (ell : ℕ) (A : Finset (Fin n)) (state : ReplayState d) (v : Fin n) : ReplayState d :=
  let b := MinimumLabel hd ell state.active state.table v
  {active := state.active.erase v
   table := if v ∈ A then SliceTable v b state.table else ProjectTable v state.table
   sides := Function.update state.sides v (if v ∈ A then {b} else Finset.univ.erase b)}

/-- Algorithm 1: every run starts afresh from exactly W0. -/
def Replay {n : ℕ} {d : Fin n → ℕ} (hd : ∀ v, 0 < d v)
    (ell : ℕ) (W0 : Table d) (A : Finset (Fin n)) : Box d :=
  ((List.finRange n).foldl (ReplayStep hd ell A)
    {active := Finset.univ, table := W0, sides := fun _ => Finset.univ}).sides

/-- Exactly one supplied certificate on ell-scopes, no smaller entries. -/
def InitialTable {n : ℕ} {d : Fin n → ℕ} (ell : ℕ)
    (cert : (T : Finset (Fin n)) → Word d T) : Table d :=
  fun T => if T.card = ell then some (cert T) else none

def ExceptionSets (n K : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.powerset.filter (fun A => A.card ≤ min K n)

end NogoodColoring1137.Main


