-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfA
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:34:38.542658+00:00
-- url     : https://prove2.me/theorems/94bdd28c-8848-43de-9c07-88905c8ad07e
-- title:
--   LUStatement Pf A
-- statement:
--   Definitions and structural lemmas for LUStatement Pf A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/LUStatementPfA.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DetSubUpper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
open Matrix ReciprocityTheory.ChartRestriction.G.FD
noncomputable section
variable {n : ℕ}
abbrev lb (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : Matrix (Fin i) (Fin i) ℂ :=
  M.submatrix (Fin.castLE i.isLt.le) (Fin.castLE i.isLt.le)
def wv (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : Fin i → ℂ :=
  vecMul (fun j : Fin i => M i (Fin.castLE i.isLt.le j)) (lb M i)⁻¹
def Lm (M : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i k => if h : (k : ℕ) < i then -wv M i ⟨k, h⟩ else if k = i then 1 else 0
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf


