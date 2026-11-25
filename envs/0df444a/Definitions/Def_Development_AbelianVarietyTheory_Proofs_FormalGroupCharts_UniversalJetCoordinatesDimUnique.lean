-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_UniversalJetCoordinatesDimUnique
-- name    : Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_UniversalJetCoordinatesDimUnique
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:50:47.223924+00:00
-- url     : https://prove2.me/theorems/c4688949-5af1-4525-8560-1326cb2eb84c
-- title:
--   Universal Jet Coordinates Dim Unique
-- statement:
--   Definitions and structural lemmas for Universal Jet Coordinates Dim Unique, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/UniversalJetCoordinatesDimUnique.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
namespace GlobalTheory.ChartCmp.JetDim
variable {V : Type} [CommRing V]
def tanAll (κ : Type) [DecidableEq κ] : Jet V κ 1 →ₐ[V] TrivSqZeroExt V (κ → V) :=
  liftJet (MvPolynomial.aeval fun i => TrivSqZeroExt.inr (Pi.single i (1 : V))) (by
    have h1 : Ideal.span (Set.range fun i => (MvPolynomial.aeval fun i : κ =>
        (TrivSqZeroExt.inr (Pi.single i (1 : V)) : TrivSqZeroExt V (κ → V))) (MvPolynomial.X i : MvPolynomial κ V))
        ≤ RingHom.ker (TrivSqZeroExt.fstHom V V (κ → V)) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp [RingHom.mem_ker]
    refine le_bot_iff.1 ((Ideal.pow_right_mono h1 _).trans ?_)
    rw [show 1 + 1 = 2 from rfl, pow_two, Ideal.mul_le]
    intro a ha b hb
    have ha' : a.fst = 0 := ha
    have hb' : b.fst = 0 := hb
    refine (Submodule.mem_bot _).2 (TrivSqZeroExt.ext ?_ ?_) <;> simp [ha', hb'])
end GlobalTheory.ChartCmp.JetDim


