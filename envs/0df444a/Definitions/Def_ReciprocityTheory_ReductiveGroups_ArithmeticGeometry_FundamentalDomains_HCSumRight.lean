-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HCSumRight
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HCSumRight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:15:09.805261+00:00
-- url     : https://prove2.me/theorems/0af326cb-fe45-402a-89a1-bcb7f22d7969
-- title:
--   HCSum Right
-- statement:
--   Definitions and structural lemmas for HCSum Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HCSumRight.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OnbPerp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PosCoordNe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis
open NumberField Complex Matrix
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
variable {r : ℕ} (X : Data E r)
def extP (g : Fin X.p0 → ℂ) : Fin r → ℂ := fun a => if h : (a : ℕ) < X.p0 then g ⟨a, h⟩ else 0
def extN (g : Fin (r - X.p0) → ℂ) : Fin r → ℂ :=
  fun a => if h : X.p0 ≤ (a : ℕ) then g ⟨a - X.p0, by have := a.isLt; omega⟩ else 0
end
end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis


