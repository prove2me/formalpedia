-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:26:34.795857+00:00
-- url     : https://prove2.me/theorems/69abd4f7-a3a0-4ae8-bc00-156bc05905a0
-- title:
--   Torus At
-- statement:
--   Definitions and structural lemmas for Torus At, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TorusAt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
def IsTorusAt (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) (T : PT E) : Prop :=
  ∃ φ : (Fin r → E) →+ Vsp T.dim, ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
    (∀ y, y ∈ T.L ↔ ∃ v ∈ X.Λ, φ v = y) ∧
    (∀ (α : 𝓞 E) (v : Fin r → E), φ ((α : E) • v) = act α (φ v)) ∧
    (∀ v ∈ X.Λ, ‖φ v‖ ^ 2 = ∑ τ : X.Ψ, X.c τ * X.maj x τ (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v)) ∧
    (∀ u ∈ X.Λ, ∀ v ∈ X.Λ, (Hf (φ u) (φ v)).im =
      s * ((Algebra.trace ℚ E (X.ξ0 * ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u v) : ℚ) : ℝ))
def phiFD (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (th : ℝ) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) : ℝ :=
  if X.la1 x < th then 2 * PT.f E / (PT.rd E ^ 2 * X.la1 x ^ 2) else 0
def TorusAtLa1Statement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r)
    (x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), x ∈ X.dom → ∀ T : PT E, IsTorusAt X x T →
      T.la1 = X.la1 x ∧ ∀ th : ℝ, T.ph th = phiFD X th x
end
end ReciprocityTheory.ChartRestriction.G.I2


