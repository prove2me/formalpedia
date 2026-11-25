-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_HarmonicValueCopiesGaugeIndependent
-- name    : Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_HarmonicValueCopiesGaugeIndependent
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T14:43:10.536266+00:00
-- url     : https://prove2.me/theorems/ab1e1dd7-c34c-5b6a-95a6-6b214ab04ff1
-- title:
--   Harmonic Value Copies Gauge Independent
-- statement:
--   Definitions and structural lemmas for Harmonic Value Copies Gauge Independent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/HarmonicValueCopiesGaugeIndependent.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumSupportRename
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonNCongr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonGaugeIndependenceHarmonic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
namespace GlobalTheory.HarmCopies
open GlobalTheory.PowGerm
def letterEquiv (T : Type) (r : T → ℕ) (n : ℕ) : (Σ τ : T, Fin (r τ)) × Fin n ≃ Formalism.L2.Pj.Letter T r n where
  toFun p := ⟨p.1.1, p.1.2, p.2⟩
  invFun l := (⟨l.1, l.2.1⟩, l.2.2)
  left_inv _ := rfl
  right_inv _ := rfl
end GlobalTheory.HarmCopies
namespace GlobalTheory
end GlobalTheory


