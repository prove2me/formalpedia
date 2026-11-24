-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagOffMinor
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagOffMinor
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:50.222812+00:00
-- url     : https://prove2.me/theorems/82db74e4-c85f-45e0-ba95-de800a50d521
-- title:
--   PDiag Off Minor
-- statement:
--   Definitions and structural lemmas for PDiag Off Minor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagOffMinor.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagOffPair
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagForms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
namespace DiagonalOffMinor
variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E]
  [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]
def lineSubst (ι ν κ : Type) : (Σ b, T.wwIdx ι ν κ b) → Polynomial (MRing (T.wwIdx ι ν κ))
  | ⟨.base, i⟩ => Polynomial.C (X ⟨.base, i⟩)
  | ⟨.det, l⟩ => Polynomial.C (X ⟨.det, l⟩)
  | ⟨.line0, p⟩ => Polynomial.C (X ⟨.line0, p⟩)
  | ⟨.line1, p⟩ => Polynomial.C (X ⟨.line0, p⟩) * Polynomial.X
def blockSubst : T.WBlk → Polynomial (MvPolynomial T.WBlk Φ)
  | .line1 => Polynomial.C (X .line0) * Polynomial.X
  | b => Polynomial.C (X b)
end DiagonalOffMinor
end
end GroundTheory.Heights₂.Heights.Inter


