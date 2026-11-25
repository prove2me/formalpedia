-- Prove2me | Definitions.Def_IntMul_Kappa_R8_OppbankRankCheck
-- name    : IntMul_Kappa_R8_OppbankRankCheck
-- status  : Definition
-- author  : @immiq
-- created : 2026-11-25T06:42:54.356776+00:00
-- url     : https://prove2.me/theorems/9043eb1b-4565-4d0a-b238-4dfbd748f867
-- title:
--   Sparse rank checker for R8 opp-bank node supports
-- statement:
--   The checker decodes each node support using its recorded centre. Deleting the centre gives rows with two unit entries. Sparse elimination over the rationals maintains rows with at most two nonzero entries and returns the number of pivots. The checker compares that number with the published dimension entry.
-- source:
--   Rank-table verification for IntMul.Kappa.R8.Bit.Oppbank.Pc_rank_ND, https://prove2.me/theorems/590a9ee0-cecb-41be-b425-cdf41014939d

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCent

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 4000

namespace IntMul.Kappa.R8.Bit.Oppbank.RankCheck

open Module Submodule
open Pnd SupG Cent

abbrev V := Fin 23 → ℚ

def unit (i : Fin 23) : V := Pi.single i 1

def sign (neg : Bool) : ℚ := if neg then -1 else 1

inductive Row where
  | zero
  | one (i : Fin 23)
  | two (i j : Fin 23) (neg : Bool)
  deriving Inhabited

def Row.vec : Row → V
  | .zero => 0
  | .one i => unit i
  | .two i j b => unit i + sign b • unit j

def Row.valid : Row → Prop
  | .two i j _ => i ≠ j
  | _ => True

/-- Normalize the coefficient at the pivot to 1 and return the other term. -/
def Row.atPivot (p : Fin 23) : Row → Option (Bool × Option (Fin 23 × Bool))
  | .zero => none
  | .one i => if p = i then some (false, none) else none
  | .two i j b =>
    if p = i then some (false, some (j,b))
    else if p = j then some (b, some (i,b)) else none

def term : Option (Fin 23 × Bool) → V
  | none => 0
  | some (i,b) => sign b • unit i

/-- The difference of two signed atoms is a nonzero scalar times a normalized row,
or zero. -/
def diff : Option (Fin 23 × Bool) → Option (Fin 23 × Bool) → Row × ℚ
  | none, none => (.zero, 1)
  | some (a,b), none => (.one a, sign b)
  | none, some (c,d) => (.one c, -sign d)
  | some (a,b), some (c,d) =>
    if a = c then
      if b = d then (.zero, 1) else (.one a, 2 * sign b)
    else (.two a c (!(b ^^ d)), sign b)

def clear (p : Fin 23) (tail : Option (Fin 23 × Bool)) (r : Row) : Row :=
  match r.atPivot p with
  | none => r
  | some (_, t) => (diff t tail).1

def spanRows (rs : List Row) : Submodule ℚ V :=
  span ℚ {v | ∃ r ∈ rs, v = r.vec}

inductive Echelon where
  | nil
  | cons (p : Fin 23) (r : Row) (b : Bool) (t : Option (Fin 23 × Bool)) (rest : Echelon)

def Echelon.size : Echelon → ℕ
  | .nil => 0
  | .cons _ _ _ _ rest => rest.size + 1

def Echelon.space : Echelon → Submodule ℚ V
  | .nil => ⊥
  | .cons _ r _ _ rest => rest.space ⊔ span ℚ {r.vec}

def Echelon.good : Echelon → Prop
  | .nil => True
  | .cons p r b t rest =>
    r.valid ∧ r.atPivot p = some (b,t) ∧ rest.good ∧
    ∀ v ∈ rest.space, v p = 0

def Echelon.insert (r : Row) : Echelon → Echelon
  | .nil =>
    match r with
    | .zero => .nil
    | .one i => .cons i r false none .nil
    | .two i j b => .cons i r false (some (j,b)) .nil
  | .cons p pivot b tail rest =>
    .cons p pivot b tail (rest.insert (clear p tail r))

def rankRows (rs : List Row) : ℕ :=
  (rs.foldl (fun e r => e.insert r) Echelon.nil).size

/-- Locate the greatest bit by halving the search interval. -/
def hiBit : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, w =>
    let q := 1 <<< k
    let r := w >>> q
    if r = 0 then hiBit k w else q + hiBit k r

/-- Enumerate set bits, clearing the greatest bit at each step. -/
def bitIndices : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, w =>
    if w = 0 then [] else
      let hi := hiBit 11 w
      hi :: bitIndices fuel (w % (1 <<< hi))

def drop (c : Fin 23) : V →ₗ[ℚ] V where
  toFun v i := if i = c then 0 else v i
  map_add' x y := by funext i; by_cases h : i = c <;> simp [h]
  map_smul' a v := by funext i; by_cases h : i = c <;> simp [h]

def decode (c : Fin 23) (i : ℕ) : Option Row :=
  let a := ptsL i 0
  let b := ptsL i 1
  let d := ptsL i 2
  if h : a < b ∧ b < d ∧ d < 23 then
    let a' : Fin 23 := ⟨a, by omega⟩
    let b' : Fin 23 := ⟨b, by omega⟩
    let d' : Fin 23 := ⟨d, h.2.2⟩
    if c = a' then some (.two b' d' false)
    else if c = b' then some (.two a' d' false)
    else if c = d' then some (.two a' b' false)
    else none
  else none

/-- Decode every edge, rejecting the input if even one triple fails the check. -/
def rowsOf (c : Fin 23) : List ℕ → Option (List Row)
  | [] => some []
  | i :: is => do
      let r ← decode c i
      let rs ← rowsOf c is
      return r :: rs

noncomputable def nodeCheck (n : ℕ) : Bool :=
  if hc : centF n < 23 then
    match rowsOf ⟨centF n, hc⟩ (bitIndices 1771 (densSupG n)) with
    | none => false
    | some rs => Nat.beq (rankRows rs) (dimF n)
  else false

def pass (check : ℕ → Bool) (lo width : ℕ) : Bool :=
  (List.range width).all fun k => check (lo + k)

end IntMul.Kappa.R8.Bit.Oppbank.RankCheck


