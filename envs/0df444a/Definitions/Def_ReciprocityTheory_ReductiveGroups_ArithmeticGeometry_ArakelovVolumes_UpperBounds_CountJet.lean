-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_CountJet
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_CountJet
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T01:23:05.482516+00:00
-- url     : https://prove2.me/theorems/ee8f7859-4b42-4b84-a6ff-c691dbc95115
-- title:
--   Count Jet
-- statement:
--   Definitions and structural lemmas for Count Jet, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/CountJet.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
def JetInjAt {r : ℕ} (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) : Prop :=
  ∀ f ∈ X.SS (Xa.Fp + Xa.T • Xa.L), VanS X Fl.xs Fl.s (Xa.T + nd X + 7) f → ∀ x ∈ X.dom, f x = 0
def CuspFormsJetInjectiveCount : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), JetInjAt X Xa Fl →
    ∀ (rr : ℕ) (f : Fin rr → Frame X.Ψ r → ℂ), (∀ q, f q ∈ X.SS (Xa.Fp + Xa.T • Xa.L)) →
      (∀ a : Fin rr → ℂ, (∀ x ∈ X.dom, ∑ q, a q * f q x = 0) → a = 0) →
      rr ≤ Fl.δ * (Xa.T + 2 * nd X + 6).choose (nd X)
end ReciprocityTheory.ChartRestriction.G.AR.Up


