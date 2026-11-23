-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantOperators
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantOperators
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:42.153391+00:00
-- url     : https://prove2.me/theorems/a4cf6758-0e6d-41f9-9ccc-aa148b3fae5f
-- title:
--   Majorant Operators
-- statement:
--   Definitions and structural lemmas for Majorant Operators, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajorantOperators.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentCoefficientShift
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalLatticeDecomposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD
namespace MajorantOperators
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
noncomputable def gI (z : Frame X.Ψ r) (u v : X.Ψ → Fin r → ℂ) : ℝ := ∑ τ, (X.Hf z τ (u τ) (v τ)).re
noncomputable def Bop (z : Frame X.Ψ r) (u : X.Ψ → Fin r → ℂ) : X.Ψ → Fin r → ℂ :=
  fun τ => (2 * τ.1 (-X.ξ0)) • X.jp z τ (u τ)
section dataX
variable {Y : DataX E r}
end dataX
end MajorantOperators
end ReciprocityTheory.ChartRestriction.G.FD


