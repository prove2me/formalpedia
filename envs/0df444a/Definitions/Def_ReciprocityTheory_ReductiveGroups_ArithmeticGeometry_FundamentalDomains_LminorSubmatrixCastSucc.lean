-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:31:45.594801+00:00
-- url     : https://prove2.me/theorems/ad946209-4a5d-4712-bc78-7ac5bf38dc1a
-- title:
--   Lminor Submatrix Cast Succ
-- statement:
--   Definitions and structural lemmas for Lminor Submatrix Cast Succ, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LminorSubmatrixCastSucc.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD
open Matrix NumberField
open scoped ComplexOrder ComplexConjugate
section Herm
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
end Herm
section Quad
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
end Quad
namespace Data
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
def colP (x : Frame X.Ψ r) (τ : X.Ψ) (a : Fin X.p0) : Fin r → ℂ :=
  col (mat x τ) (Fin.castLE X.p0_le a)
noncomputable def jp (x : Frame X.Ψ r) (τ : X.Ψ) (v : Fin r → ℂ) : Fin r → ℂ := (2 : ℂ) • X.ppos x τ v - v
end Data
end ReciprocityTheory.ChartRestriction.G.FD


