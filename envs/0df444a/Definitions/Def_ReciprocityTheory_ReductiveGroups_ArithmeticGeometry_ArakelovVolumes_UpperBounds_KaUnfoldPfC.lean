-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfC
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:13:15.747178+00:00
-- url     : https://prove2.me/theorems/e6a9f91c-ba9e-4ed5-a8ef-f9e04d252886
-- title:
--   Ka Unfold Pf C
-- statement:
--   Definitions and structural lemmas for Ka Unfold Pf C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/KaUnfoldPfC.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.KU
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Matrix
open scoped ENNReal ComplexOrder
noncomputable section
local instance instMSMat {m n : Type*} : MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))
local instance instBorelMat {m n : Type*} [Fintype m] [Fintype n] : BorelSpace (Matrix m n ℂ) :=
  inferInstanceAs (BorelSpace (m → n → ℂ))
local instance instSCMat {m n : Type*} [Fintype m] [Fintype n] : SecondCountableTopology (Matrix m n ℂ) :=
  inferInstanceAs (SecondCountableTopology (m → n → ℂ))
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
local instance instPolishFrame (X : Data E r) : PolishSpace (Frame X.Ψ r) where
def Sset (X : Data E r) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))) : Set (Frame X.Ψ r) :=
  (fun pr : V (nd X) × Frame X.Ψ r => rmul (cpt X x0 pr.1) pr.2) '' (FF ×ˢ Bor X.Ψ r)
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.KU


