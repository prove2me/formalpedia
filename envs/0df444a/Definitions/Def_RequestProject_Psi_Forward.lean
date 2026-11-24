-- Prove2me | Definitions.Def_RequestProject_Psi_Forward
-- name    : RequestProject_Psi_Forward
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T22:53:28.396739+00:00
-- url     : https://prove2.me/theorems/fdf51362-c5e5-44df-8160-93ea9741e3ad
-- title:
--   Forward
-- statement:
--   Definitions and structural lemmas for Forward, from SashaIr/leaving-the-hall contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Dyck-path algebra and decorated-Dyck-path bijection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean

import Definitions.Def_RequestProject_Psi_RiseComp
set_option autoImplicit true
namespace Psi
def Dom (n : ℕ) : Set (List Bool × List ℕ) :=
  {p | p.1.length + 1 = n ∧ IsValid p.1 p.2}
def Cod (n : ℕ) : Set (List Bool) :=
  {p | IsDyck p ∧ p.length = 2 * n}
theorem take_drop_len_le {α} (l : List α) (m n : ℕ) (h : m ≤ n) :
    (l.take m ++ l.drop n).length ≤ l.length := by
  rw [List.length_append, List.length_take, List.length_drop]; omega
def cUDraw : List Bool → ℕ
  | true :: false :: r => 1 + cUDraw r
  | _ => 0
def cUD (π : List Bool) : ℕ :=
  let c := cUDraw π
  if 2 * c = π.length then c - 1 else c
def firstDDidx : List Bool → Option ℕ
  | false :: false :: _ => some 0
  | _ :: r => (firstDDidx r).map (· + 1)
  | [] => none
def psiPath (π : List Bool) : List Bool × List ℕ :=
  let a := cUD π
  let rest := π.drop (2 * a + 1)
  match _h : firstDDidx rest with
  | none => (List.replicate a false, [0])
  | some i =>
     let b := min (((rest.take i).reverse.takeWhile id).length)
                  (((rest.drop i).takeWhile (· = false)).length - 1)
     let ρ := rest.take (i - b)
     let ρ' := rest.drop (i + b + 1)
     if _he : ρ ++ ρ' = [] then (List.replicate a false ++ List.replicate b true, [0])
     else
       let r := psiPath (ρ ++ ρ')
       (List.replicate a false ++ List.replicate b true ++ [false] ++ r.1, numN ρ :: r.2)
  termination_by π.length
  decreasing_by
    have hrest : rest ≠ [] := by
      intro hc; rw [hc] at _h; simp [firstDDidx] at _h
    have hpos : 0 < rest.length := List.length_pos_of_ne_nil hrest
    have hrl : rest.length = π.length - (2 * a + 1) := by simp [rest, List.length_drop]
    have hle : (ρ ++ ρ').length ≤ rest.length :=
      take_drop_len_le rest (i - b) (i + b + 1) (by omega)
    exact lt_of_le_of_lt hle (by omega)
end Psi


