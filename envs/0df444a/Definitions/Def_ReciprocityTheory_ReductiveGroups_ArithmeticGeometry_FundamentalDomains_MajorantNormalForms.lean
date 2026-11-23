-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantNormalForms
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantNormalForms
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:07.710138+00:00
-- url     : https://prove2.me/theorems/8800f0b1-f95a-45a5-a574-771960a6283a
-- title:
--   Majorant Normal Forms
-- statement:
--   Definitions and structural lemmas for Majorant Normal Forms, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajorantNormalForms.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentCoefficientShift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_jp_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_jp_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_smul_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD
namespace MajorantNormalForms
open Matrix NumberField Complex
open scoped ComplexConjugate ComplexOrder
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
noncomputable def jpL (x : Frame X.Ψ r) (τ : X.Ψ) : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) where
  toFun := X.jp x τ
  map_add' := X.jp_add x τ
  map_smul' := X.jp_smul x τ
noncomputable def pposL (x : Frame X.Ψ r) (τ : X.Ψ) : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) where
  toFun := X.ppos x τ
  map_add' := X.ppos_add x τ
  map_smul' := X.ppos_smul_eq x τ
end MajorantNormalForms
end ReciprocityTheory.ChartRestriction.G.FD


