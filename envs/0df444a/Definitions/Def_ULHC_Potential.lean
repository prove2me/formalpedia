-- Prove2me | Definitions.Def_ULHC_Potential
-- name    : ULHC_Potential
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:36:30.849093+00:00
-- url     : https://prove2.me/theorems/b58a4409-d252-433f-8339-55dda6697b9d
-- title:
--   Potential
-- statement:
--   Definitions and structural lemmas for Potential, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Potential.lean

import Definitions.Def_ULHC_Grid
set_option autoImplicit true
namespace ULHC
open Finset
def RowSel (c : Pt) (e : Edge) : Prop := e.d = .v ∧ e.p.2 = c.2 ∧ e.p.1 ≤ c.1
instance (c : Pt) : DecidablePred (RowSel c) := by
  intro e; unfold RowSel; infer_instance
def pot (E : Finset Edge) (w : Edge → ℤ) (c : Pt) : ℤ :=
  ∑ e ∈ E.filter (RowSel c), w e
def Supp (E : Finset Edge) (w : Edge → ℤ) : Prop := ∀ e, e ∉ E → w e = 0
def Balanced (w : Edge → ℤ) : Prop := ∀ p, w (eD p) + w (eR p) = w (eL p) + w (eU p)
variable {E : Finset Edge} {w : Edge → ℤ}
end ULHC


