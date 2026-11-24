-- Prove2me | Definitions.Def_ULHC_TwoFactor
-- name    : ULHC_TwoFactor
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:18:53.753666+00:00
-- url     : https://prove2.me/theorems/5f112c1e-015d-42db-b847-9a5038fc68ca
-- title:
--   Two Factor
-- statement:
--   Definitions and structural lemmas for Two Factor, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TwoFactor.lean

import Definitions.Def_ULHC_StripCount
set_option autoImplicit true
namespace ULHC
open Finset
namespace TF
def Black (z : Pt) : Prop := (z.1 + z.2) % 2 = 0
instance (z : Pt) : Decidable (Black z) := by unfold Black; infer_instance
def inc4 (z : Pt) : List Edge := [eR z, eL z, eU z, eD z]
def Fwd (V : Finset Pt) (F : Finset Edge) (u : Pt) (e : Edge) : Prop :=
  IsEdge V e ∧ (Black u → e ∉ F) ∧ (¬ Black u → e ∈ F)
instance (V : Finset Pt) (F : Finset Edge) (u : Pt) (e : Edge) : Decidable (Fwd V F u e) := by
  unfold Fwd; infer_instance
def nbr (V : Finset Pt) (F : Finset Edge) (u : Pt) : Finset Pt :=
  (((inc4 u).filter (fun e => decide (Fwd V F u e))).map (fun e => other e u)).toFinset
def layer (V : Finset Pt) (F : Finset Edge) : ℕ → Finset Pt
  | 0 => V.filter (fun z => Black z ∧ deg F z < 2)
  | k + 1 =>
    let L := layer V F k
    L ∪ L.biUnion (nbr V F)
def Bwd (V : Finset Pt) (F : Finset Edge) (L : Finset Pt) (v : Pt) (e : Edge) : Prop :=
  IsEdge V e ∧ other e v ∈ L ∧ (Black v → e ∈ F) ∧ (¬ Black v → e ∉ F)
instance (V : Finset Pt) (F : Finset Edge) (L : Finset Pt) (v : Pt) (e : Edge) :
    Decidable (Bwd V F L v e) := by
  unfold Bwd; infer_instance
def pred (V : Finset Pt) (F : Finset Edge) (L : Finset Pt) (v : Pt) : Option Edge :=
  (inc4 v).find? (fun e => decide (Bwd V F L v e))
def layersBelow (V : Finset Pt) (F : Finset Edge) : ℕ → List (Finset Pt)
  | 0 => []
  | k + 1 => layer V F k :: layersBelow V F k
def layerAcc (V : Finset Pt) (F : Finset Edge) : ℕ → List (Finset Pt)
  | 0 => [V.filter (fun z => Black z ∧ deg F z < 2)]
  | k + 1 =>
    match layerAcc V F k with
    | [] => []
    | L :: Ls => (L ∪ L.biUnion (nbr V F)) :: L :: Ls
def walk (V : Finset Pt) (F0 : Finset Edge) :
    List (Finset Pt) → Pt → Finset Edge → Finset Edge
  | [], _, F => F
  | L :: Ls, v, F =>
    if v ∈ L then walk V F0 Ls v F
    else
      match pred V F0 L v with
      | none => F
      | some e => walk V F0 Ls (other e v) (if Black v then F.erase e else insert e F)
def pick (S : Finset Pt) : Option Pt :=
  match (S.image toLex).min with
  | ⊤ => none
  | (x : Lex (ℤ × ℤ)) => some (ofLex x)
def augStep (V : Finset Pt) (F : Finset Edge) : Option (Finset Edge) :=
  match layerAcc V F V.card with
  | [] => none
  | L :: Ls =>
    match pick (L.filter (fun w => ¬ Black w ∧ deg F w < 2)) with
    | none => none
    | some w => some (walk V F Ls w F)
def augLoop (V : Finset Pt) : ℕ → Finset Edge → Finset Edge
  | 0, F => F
  | n + 1, F =>
    match augStep V F with
    | none => F
    | some F' => augLoop V n F'
def Good (V : Finset Pt) (F : Finset Edge) : Prop := Inside V F ∧ ∀ z, deg F z ≤ 2
def WInv (V : Finset Pt) (F0 : Finset Edge) (k : ℕ) (v : Pt) (F : Finset Edge) : Prop :=
  v ∈ layer V F0 k ∧ Inside V F ∧ (∀ z, z ≠ v → deg F z ≤ 2) ∧
  (¬ Black v → deg F v < 2 ∧ F.card = F0.card) ∧
  (Black v → deg F v = deg F0 v + 1 ∧ F.card = F0.card + 1) ∧
  (∀ z ∈ layer V F0 k, z ≠ v → deg F z = deg F0 z) ∧
  (∀ e, (e ∈ F ↔ e ∈ F0) ∨ e.p ∉ layer V F0 k ∨ e.q ∉ layer V F0 k)
end TF
open TF
def twoFactor (V : Finset Pt) : Option (Finset Edge) :=
  let F := augLoop V (V.card + 1) ∅
  if ∀ z ∈ V, deg F z = 2 then some F else none
end ULHC


