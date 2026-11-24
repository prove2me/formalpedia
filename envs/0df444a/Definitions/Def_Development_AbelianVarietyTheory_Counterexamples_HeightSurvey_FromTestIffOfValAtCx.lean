-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_HeightSurvey_FromTestIffOfValAtCx
-- name    : Development_AbelianVarietyTheory_Counterexamples_HeightSurvey_FromTestIffOfValAtCx
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T11:21:18.758022+00:00
-- url     : https://prove2.me/theorems/00e438c6-77ed-4b7a-878e-2d62ebf106c0
-- title:
--   From Test Iff Of Val At Cx
-- statement:
--   Definitions and structural lemmas for From Test Iff Of Val At Cx, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/HeightSurvey/FromTestIffOfValAtCx.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AxHSup
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ChosenEqOfAllRules
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.SupLawProbe
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
abbrev FT {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) : Prop :=
  FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y
abbrev pn (σ : c.F →+* ℂ) (fσ : FrPt Xo c (CAt σ) → Ix Dw → ℝ) (e : Ix Dw → ℕ) (f : Rul Xo c)
    (y : FrPt Xo c (CAt σ)) : ℝ :=
  ptNorm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) σ fσ e f y
variable {h : GenFrEx Xo c} {fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ}
  {yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))}
section Conj
variable (hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z))
  (σ : c.F →+* ℂ) (cj : FrPt Xo c (CAt σ) → FrPt Xo c (CAt ((starRingEnd ℂ).comp σ)))
  (hcj : ∀ y, FrMap (SupNormExample.conjAt σ) y (cj y))
  (htr : ∀ y i, |fn _ (cj y) i| = |fn σ y i|) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c}
  (hS : f ∈ sec Xo c a n)
end Conj
end GlobalTheory.SupLawProbe


