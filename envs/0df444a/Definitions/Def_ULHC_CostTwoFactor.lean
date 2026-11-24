-- Prove2me | Definitions.Def_ULHC_CostTwoFactor
-- name    : ULHC_CostTwoFactor
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T03:07:55.488103+00:00
-- url     : https://prove2.me/theorems/46afcb54-ba71-4800-82e2-02f236bee2c0
-- title:
--   Cost Two Factor
-- statement:
--   Definitions and structural lemmas for Cost Two Factor, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/CostTwoFactor.lean

import Definitions.Def_ULHC_CostConn
set_option autoImplicit true
namespace ULHC
open Finset TF
def nbrCost : ℕ := 45
def degCost : ℕ := 8
def predCost : ℕ := 40
def layerAccCost (V : Finset Pt) (F : Finset Edge) : ℕ → ℕ
  | 0 => 13 * V.card
  | k + 1 =>
    layerAccCost V F k +
      match layerAcc V F k with
      | [] => 1
      | L :: _ => ∑ u ∈ L, (nbrCost + (nbr V F u).card) + L.card + (L.biUnion (nbr V F)).card + 1
def walkCost (V : Finset Pt) (F0 : Finset Edge) : List (Finset Pt) → Pt → Finset Edge → ℕ
  | [], _, _ => 1
  | L :: Ls, v, F =>
    2 + if v ∈ L then walkCost V F0 Ls v F
    else predCost +
      match pred V F0 L v with
      | none => 0
      | some e => 2 + walkCost V F0 Ls (other e v) (if Black v then F.erase e else insert e F)
def pickCost (S : Finset Pt) : ℕ := 2 * S.card + 2
def augStepCost (V : Finset Pt) (F : Finset Edge) : ℕ :=
  V.card + 1 + layerAccCost V F V.card +
    match layerAcc V F V.card with
    | [] => 1
    | L :: Ls =>
      ∑ _w ∈ L, (degCost + 3) + pickCost (L.filter (fun w => ¬ Black w ∧ deg F w < 2)) +
        match pick (L.filter (fun w => ¬ Black w ∧ deg F w < 2)) with
        | none => 0
        | some w => walkCost V F Ls w F
def augLoopCost (V : Finset Pt) : ℕ → Finset Edge → ℕ
  | 0, _ => 1
  | n + 1, F =>
    augStepCost V F + 1 +
      match augStep V F with
      | none => 0
      | some F' => augLoopCost V n F'
def twoFactorCost (V : Finset Pt) : ℕ :=
  V.card + 1 + augLoopCost V (V.card + 1) ∅ + V.card * (degCost + 3) + 1
end ULHC


