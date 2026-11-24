-- Prove2me | Definitions.Def_StableMSR_RegionalGeometryTables
-- name    : StableMSR_RegionalGeometryTables
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-24T20:45:18.54095+00:00
-- url     : https://prove2.me/theorems/71fcc37a-9693-4a2c-9859-cc09e2349ef4
-- title:
--   Five integer geometry tables for a regional separator computation
-- statement:
--   For a regional piece $W$, this contract describes the net and region indicators, nearest eligible centre with its fallback, window-membership matrix, and loop-free adjacency matrix. It records preservation of the input controls, output, and heap beyond the five arrays. The two source commands identify precisely where geometry ends and where menu and separator enumeration resumes.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, https://arxiv.org/abs/2611.03547. Execution interface for the mission’s canonical integer separator program.

import Definitions.Def_StableMSR_InitializedSeparatorTraversal

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene
open StableMSR.Recovery
set_option autoImplicit false

/-- The first 24 geometry commands end after the sweep that fills the two square matrices. -/
def geometryPrefix : Program := chain ((listOf src_build_geometry).take 24)

/-- Compute the window menus, then execute the cut and separator-row commands. -/
def menuAndRows : Program := .seq (chain ((listOf src_build_geometry).drop 24)) (chain ((middleList.take 3).drop 1))

/-- State of the five geometry arrays before window-menu generation. The first
matrix address uses the window centre as row and the tested point as column.
The second uses the two vertex indices as row and column, respectively. -/
structure GeometryImage {n : ℕ} (m : ℤ → ℤ) (W : Cluster n) (h : ℕ) (s t : State) : Prop where
  controls : ∀ j, (j=6 ∨ j=7 ∨ j=8 ∨ (64≤j ∧ j≤82)) → t.reg j=s.reg j
  scale : t.reg 195=(unit n:ℤ)
  active : ∀ p : Fin n, t.heap (cursorAt (offsets n (sizes n h)) 0+p.val) = if p∈Bits.net m W then 1 else 0
  owner : ∀ p : Fin n, t.heap (cursorAt (offsets n (sizes n h)) 1+p.val) = ((Bits.owner m (Bits.net m W) p).val:ℤ)
  piece : ∀ p : Fin n, t.heap (cursorAt (offsets n (sizes n h)) 2+p.val) = if p∈W then 1 else 0
  window : ∀ a p : Fin n, t.heap (cursorAt (offsets n (sizes n h)) 3+(a.val*n+p.val)) = if p∈Bits.win m W a then 1 else 0
  edge : ∀ p a : Fin n, t.heap (cursorAt (offsets n (sizes n h)) 4+(p.val*n+a.val)) =
    if p≠a ∧ m (address p a) ≤ 8*(unit n:ℤ) ∧ m (address a p) ≤ 8*(unit n:ℤ) then 1 else 0
  frame : ∀ q, cursorAt (offsets n (sizes n h)) 5 ≤ q → t.heap q=s.heap q
  output : t.output=s.output
  closed : t.closed=s.closed

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene


