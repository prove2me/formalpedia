-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_HeightSurvey_NotOverAndTriv
-- name    : Development_AbelianVarietyTheory_Counterexamples_HeightSurvey_NotOverAndTriv
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T01:12:01.571508+00:00
-- url     : https://prove2.me/theorems/7b2fd76a-8e2d-48a1-9035-a57c434b42a6
-- title:
--   Not Over And Triv
-- statement:
--   Definitions and structural lemmas for Not Over And Triv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/HeightSurvey/NotOverAndTriv.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompOrd
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegQFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Height.OrderTieGuards
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 Formalism.L2.Pj
section Unit
variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  {v : AddValuation Ω (WithTop ℤ)} {la : HeightOneSpectrum (𝓞 K)}
end Unit
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
def Clause (h : GenFrEx Xo c) (Z : Comp Xo c) (δ : Ix Dw → ℤ) (v : AddValuation (Om Z) (WithTop ℤ)) (e : ℤ)
    (val : Rul Xo c → EReal) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → evC h Z f ≠ 0 →
    (((ordC δ v (wtZ a n) (valC h a n f Z) : ℤ) : ℝ) : EReal) = ((e : ℝ) : EReal) * val f
variable {h : GenFrEx Xo c} {Z : Comp Xo c} {δ δ' : Ix Dw → ℤ} {v : AddValuation (Om Z) (WithTop ℤ)} {e : ℤ}
  {val : Rul Xo c → EReal}
end GlobalTheory.Height.OrderTieGuards


