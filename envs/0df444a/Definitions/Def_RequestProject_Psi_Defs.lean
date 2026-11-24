-- Prove2me | Definitions.Def_RequestProject_Psi_Defs
-- name    : RequestProject_Psi_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T22:48:59.640801+00:00
-- url     : https://prove2.me/theorems/3c6fcd00-cc7c-4472-8a4b-57b8515a3c54
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from SashaIr/leaving-the-hall contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Dyck-path algebra and decorated-Dyck-path bijection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Defs.lean

import Mathlib
set_option autoImplicit true
namespace Psi
def IsDyckAux : List Bool → Int → Prop
  | [], h => h = 0
  | true :: r, h => IsDyckAux r (h + 1)
  | false :: r, h => 0 < h ∧ IsDyckAux r (h - 1)
def IsDyck (p : List Bool) : Prop := IsDyckAux p 0
def numN (p : List Bool) : ℕ := (p.filter id).length
def noDescent : List Bool → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => (!a || b) && noDescent (b :: rest)
def cLead0 : List Bool → ℕ
  | false :: r => 1 + cLead0 r
  | _ => 0
def cLead1 : List Bool → ℕ
  | true :: r => 1 + cLead1 r
  | _ => 0
def splitAtRow : List Bool → ℕ → List Bool × List Bool
  | p, 0 => ([], p)
  | [], _ => ([], [])
  | true :: rest, 1 =>
      match rest with
      | false :: rest' => ([true, false], rest')
      | _ => ([true], rest)
  | true :: rest, (h + 2) =>
      let (ρ, ρ') := splitAtRow rest (h + 1)
      (true :: ρ, ρ')
  | false :: rest, (h + 1) =>
      let (ρ, ρ') := splitAtRow rest (h + 1)
      (false :: ρ, ρ')
def phiPath (w : List Bool) (av : List ℕ) : List Bool :=
  if noDescent w then
    let l := (w.filter (· = false)).length
    let k := (w.filter id).length
    (List.replicate l [true, false]).flatten ++
      List.replicate (k + 1) true ++ List.replicate (k + 1) false
  else
    let a := cLead0 w
    let after0 := w.drop a
    let b := cLead1 after0
    let w' := after0.drop (b + 1)
    let h := av.headD 0
    let av' := av.tail
    let π' := phiPath w' av'
    let (ρ, ρ') := splitAtRow π' h
    (List.replicate a [true, false]).flatten ++ [true] ++ ρ ++
      List.replicate b true ++ List.replicate (b + 1) false ++ ρ'
  termination_by w.length
  decreasing_by
    · -- `w` has a descent, hence is nonempty, and we drop `a + (b+1) ≥ 1` letters.
      simp only [List.length_drop]
      have hw : w ≠ [] := by
        intro h; subst h; simp [noDescent] at *
      have : 1 ≤ w.length := List.length_pos_of_ne_nil hw
      omega
def areaAux : List Bool → ℕ → ℕ → Bool → ℕ
  | [], _, _, _ => 0
  | true :: r, i, e, le => (if le then i - e else 0) + areaAux r (i + 1) e false
  | false :: r, i, e, _ => areaAux r i (e + 1) true
def area (p : List Bool) : ℕ := areaAux p 0 0 false
def countValleys : List Bool → Bool → ℕ
  | [], _ => 0
  | true :: r, le => (if le then 1 else 0) + countValleys r false
  | false :: r, _ => countValleys r true
def numValleys (p : List Bool) : ℕ := countValleys p false
def countRises : List Bool → Bool → Bool → ℕ
  | [], _, _ => 0
  | true :: r, le, sn => (if (!le && sn) then 1 else 0) + countRises r false true
  | false :: r, _, sn => countRises r true sn
def numRises (p : List Bool) : ℕ := countRises p false false
def cc : List Bool → List Bool
  | [] => []
  | true :: r => true :: cc r
  | false :: rest =>
      match rest with
      | true :: _ => cc rest      -- east before a North: contracted away (all valleys decorated)
      | _ => false :: cc rest
def northRunsAux : List Bool → ℕ → List ℕ
  | [], cur => if cur > 0 then [cur] else []
  | true :: r, cur => northRunsAux r (cur + 1)
  | false :: r, cur => (if cur > 0 then [cur] else []) ++ northRunsAux r 0
def northRuns (p : List Bool) : List ℕ := northRunsAux p 0
def desCompAux : List Bool → ℕ → List ℕ
  | [], cur => [cur]
  | [_], cur => [cur + 1]
  | a :: b :: rest, cur =>
      if a && !b then (cur + 1) :: desCompAux (b :: rest) 0
      else desCompAux (b :: rest) (cur + 1)
def desComp (word : List Bool) : List ℕ := desCompAux word 0
def deltaAux : List ℕ → ℕ → List ℕ
  | [], _ => []
  | x :: r, acc => (acc + x) :: deltaAux r (acc + x)
def deltaOf (γ : List ℕ) : List ℕ := deltaAux γ 0
def muVecAux : List ℕ → ℕ → List ℕ
  | [], _ => []
  | x :: r, prev => (if x - prev > 0 then [x - prev] else []) ++ muVecAux r x
def muVec (τ : List ℕ) : List ℕ := muVecAux τ 0
def tauOf (w : List Bool) (av : List ℕ) : List ℕ :=
  List.zipWith (· + ·) (deltaOf (desComp (false :: w))) av
def IsValid (w : List Bool) (av : List ℕ) : Prop :=
  av.length = (desComp (false :: w)).length ∧
    (tauOf w av).IsChain (· ≤ ·) ∧
    (tauOf w av).getLast? = some (w.length + 1)
end Psi


