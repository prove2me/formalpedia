-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UMatUpper
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UMatUpper
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:59.903175+00:00
-- url     : https://prove2.me/theorems/12a4bba4-8861-402f-b8ea-c920f08f1612
-- title:
--   UMat Upper
-- statement:
--   Definitions and structural lemmas for UMat Upper, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UMatUpper.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DetSubUpper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open NumberField Complex Matrix
open scoped ComplexConjugate
noncomputable section
variable {n : ℕ}
def blk (G : Matrix (Fin n) (Fin n) ℂ) (c : Fin n) : Matrix (Fin c) (Fin c) ℂ :=
  G.submatrix (Fin.castLE c.isLt.le) (Fin.castLE c.isLt.le)
def rowc (G : Matrix (Fin n) (Fin n) ℂ) (c : Fin n) : Fin c → ℂ := fun m => G c (Fin.castLE c.isLt.le m)
def uMat (G : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun j c => if j = c then 1 else
    if h : j < c then -(Matrix.vecMul (rowc G c) (blk G c)⁻¹) ⟨j, h⟩ else 0
end
end ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData


