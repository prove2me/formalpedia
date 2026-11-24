-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfI
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfI
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:02:14.611326+00:00
-- url     : https://prove2.me/theorems/a8edadd6-1ab3-466d-b3b4-85381adae622
-- title:
--   Meas Inv Statement Pf I
-- statement:
--   Definitions and structural lemmas for Meas Inv Statement Pf I, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfI.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalFrameDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ComplexConjugate
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
def Jd : Matrix (Fin r) (Fin r) ℂ := diagonal fun a => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)
def gramT (β : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ := βᵀ * Jd X * β.map (starRingEnd ℂ)
def CmatSet : Set (Frame X.Ψ r) :=
  {β | ∀ τ a b, (b < a → β τ a b = 0) ∧ (a = b → 1 ≤ ‖β τ a b‖ ∧ ‖β τ a b‖ ≤ 2) ∧ (a < b → ‖β τ a b‖ ≤ 1)}
def SW : Set (Frame X.Ψ r) :=
  {y | y ∈ X.dom ∧ ∃ β ∈ CmatSet X, ∀ τ, gram τ.1 X.Gm (mat y τ) = gramT X (mat β τ)}
def Wf (y : Frame X.Ψ r) : ENNReal := (SW X).indicator 1 y
def uf (v : Ix X.Ψ r → ℂ) : Frame X.Ψ r := fun τ a b => v (τ, a, b)
def UF (y : UpI X.Ψ r → ℂ) : Frame X.Ψ r := fun τ => Umat y τ
def β0 (y : Frame X.Ψ r) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ := (mat (bOf X y) τ)⁻¹
def invF (b : Frame X.Ψ r) : Frame X.Ψ r := fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)
def gramF (y : Frame X.Ψ r) : Frame X.Ψ r := fun τ => gram τ.1 X.Gm (mat y τ)
def gramTF (β : Frame X.Ψ r) : Frame X.Ψ r := fun τ => gramT X (mat β τ)
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI


