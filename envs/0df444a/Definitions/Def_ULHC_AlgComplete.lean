-- Prove2me | Definitions.Def_ULHC_AlgComplete
-- name    : ULHC_AlgComplete
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T03:05:14.69043+00:00
-- url     : https://prove2.me/theorems/3d0f504e-f789-41bd-ae3d-a24954441146
-- title:
--   Alg Complete
-- statement:
--   Definitions and structural lemmas for Alg Complete, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/AlgComplete.lean

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_Counts
import Definitions.Def_ULHC_NearCA
set_option autoImplicit true
namespace ULHC
open Finset
def PathComplete (V : Finset Pt) : Prop :=
  ∀ G, Deg2 V G → NoTypeIII V G → 2 ≤ ncomp V G → ∃ σ L, CRPathCA V G σ L
section bounds
variable {V : Finset Pt}
end bounds
def dval (V : Finset Pt) (G : Finset Edge) : ℕ :=
  match findPath V G with
  | some (σ, L) => wt σ L
  | none => 0
open Classical in
noncomputable def Mz (V : Finset Pt) (G : Finset Edge) : ℕ :=
  ncomp V G * (2 * Dm V + 4) + (if NoTypeIII V G then 2 * dval V G + 2 else 1)
section potential
variable {V : Finset Pt}
end potential
section round
variable {V : Finset Pt} (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z)
  (hPC : PathComplete V)
include hs x0 hconn hPC
end round
end ULHC


