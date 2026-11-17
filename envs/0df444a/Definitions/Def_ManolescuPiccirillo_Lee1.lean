-- Prove2me | Definitions.Def_ManolescuPiccirillo_Lee1
-- name    : ManolescuPiccirillo_Lee1
-- status  : Definition
-- author  : @Lucas
-- created : 2026-11-16T18:51:26.694134+00:00
-- url     : https://prove2.me/theorems/f951a567-faab-4b3e-b448-046307b5fe02
-- title:
--   Manolescu–Piccirillo: Lee generators
-- statement:
--   Kauffman states, resolution circles, Lee generators and their homological/quantum gradings; normal-form convention and crossing signs.
-- source:
--   Rasmussen, https://doi.org/10.1007/s00222-010-0275-6 ; Lee, https://arxiv.org/abs/math/0210213

import Mathlib
import Definitions.Def_ManolescuPiccirillo_PD

open Classical
noncomputable section

namespace ManolescuPiccirillo
namespace PD

variable (D : PD)

def NormalForm : Prop :=
  D.labels = Finset.range (2 * D.numCrossings) ∧
  ∀ c ∈ D.crossings, c 2 = (c 0 + 1) % (2 * D.numCrossings)

def crossingSign (c : Fin 4 → ℕ) : ℤ :=
  if c 3 = (c 1 + 1) % (2 * D.numCrossings) then 1 else -1

def nPlus : ℕ := (D.crossings.filter (fun c => D.crossingSign c = 1)).length
def nMinus : ℕ := (D.crossings.filter (fun c => D.crossingSign c = -1)).length

def State := Fin D.numCrossings → Bool

def statePairs (s : D.State) : List (ℕ × ℕ) :=
  (D.crossings.zip (List.ofFn s)).flatMap (fun cb =>
    let c := cb.1; let b := cb.2
    if b then [(c 0, c 1), (c 2, c 3)] else [(c 0, c 3), (c 1, c 2)])

def statePaired (s : D.State) (x y : ℕ) : Prop :=
  (x, y) ∈ D.statePairs s ∨ (y, x) ∈ D.statePairs s

def stateGraph (s : D.State) : SimpleGraph D.labels :=
  SimpleGraph.fromRel (fun x y => D.statePaired s x.val y.val ∧ x ≠ y)

def stateConnected (s : D.State) (x y : ℕ) : Prop :=
  Relation.ReflTransGen (D.statePaired s) x y

def numTrue (s : D.State) : ℕ := ((List.ofFn s).filter (fun b => b)).length

/-- A Lee generator: a state with a `{1, X}`-labelling constant on each circle.
`.1` is the state, `.2` the labelling (`0` = `1`, `1` = `X`). -/
def LeeGen : Type :=
  { p : D.State × (D.labels → Fin 2) //
    ∀ x y : D.labels, D.statePaired p.1 x.val y.val → p.2 x = p.2 y }

def homDeg (g : D.LeeGen) : ℤ := (D.numTrue g.val.1 : ℤ) - D.nMinus

def sgn (l : Fin 2) : ℤ := if l = 0 then 1 else -1

def minReps (s : D.State) : Finset ℕ :=
  D.labels.filter (fun x => ∀ y ∈ D.labels, D.stateConnected s x y → x ≤ y)

def qDeg (g : D.LeeGen) : ℤ :=
  (D.numTrue g.val.1 : ℤ) + D.nPlus - 2 * D.nMinus +
    ∑ x : ↥(D.minReps g.val.1),
      sgn (g.val.2 (⟨x.val, (Finset.mem_filter.mp x.property).1⟩ : D.labels))

end PD
end ManolescuPiccirillo


