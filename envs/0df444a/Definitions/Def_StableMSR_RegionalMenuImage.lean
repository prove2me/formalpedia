-- Prove2me | Definitions.Def_StableMSR_RegionalMenuImage
-- name    : StableMSR_RegionalMenuImage
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-25T04:49:21.7035+00:00
-- url     : https://prove2.me/theorems/991338f7-56fc-5b77-824c-57b90268bfde
-- title:
--   Physical candidate tables at entry to separator enumeration
-- statement:
--   After enumerating the candidate words and before visiting any cuts, the machine stores the word order, one representative per distinct block, its least point when nonempty, its ownership-intersection flag, its membership row, and the window feasibility bit. This interface also records the geometry prefix of the heap and the control registers needed for the cut traversal.
-- source:
--   Implementation of the root-component and boundary requests in Appendix A.6 of Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, https://arxiv.org/abs/2611.03547.

import Definitions.Def_StableMSR_RegionalGeometryTables
import Definitions.Def_StableMSR_VertexBlockRows

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene
open StableMSR.Recovery
open scoped Classical
set_option autoImplicit false

/-- The last geometry command visits every candidate word at every vertex. -/
def buildMenus := chain ((listOf src_build_geometry).drop 24)

/-- The following commands enumerate cuts and emit their separator rows. -/
def writeCuts := chain ((middleList.take 3).drop 1)

/-- Representation of the candidate tables read by the separator code. Each word slot
uses the paper's enumeration order. Representatives are indexed by their least seed. -/
structure RegionalMenus {n : ℕ} (m : ℤ → ℤ) (W : Cluster n) (h : ℕ) (v t : State) : Prop where
  controls : ∀ j, (j=6 ∨ j=7 ∨ (64 ≤ j ∧ j ≤ 82)) → t.reg j=v.reg j
  cursor : (cursorAt (offsets n (sizes n h)) 11 : ℤ) ≤ t.reg 8
  geometry : ∀ z < cursorAt (offsets n (sizes n h)) 5, t.heap z=v.heap z
  words : ∀ i < sizes n h, t.heap (cursorAt (offsets n (sizes n h)) 5+i) =
    (((SingleCodes.words n h)[i]?.getD 0 : ℕ) : ℤ)
  tables : ∀ (a : Fin n), ∀ i < sizes n h,
    let M := sizes n h
    let o := offsets n M
    let c := (SingleCodes.words n h)[i]?.getD 0
    let U := Bits.win m W a
    let C := BlockRows.rowBlock m U h c
    let R := BlockRows.representatives U C
    let slot := a.val*M+i
    let row := fun j => slot*n+j
    (∀ j : Fin n, t.heap (cursorAt o 6+row j.val) = if j.val∈R then 1 else 0) ∧
    (∀ j ∈ R, ∀ e : (C j).Nonempty,
      t.heap (cursorAt o 7+row j) = (((C j).min' e).val : ℤ)) ∧
    (∀ j ∈ R, t.heap (cursorAt o 8+row j) =
      if Bits.touchesB (Bits.owner m (Bits.net m W)) a (C j) then 1 else 0) ∧
    (∀ j ∈ R, ∀ p : Fin n, t.heap (cursorAt o 9+(row j*n+p.val)) = if p∈C j then 1 else 0) ∧
    (t.heap (cursorAt o 10+slot) = if Bits.feasible U (Bits.blocks m U h c) then 1 else 0)
  output : t.output=v.output
  closed : t.closed=v.closed

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene


