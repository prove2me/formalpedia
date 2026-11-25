-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_MemOfPowEqInt
-- name    : Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_MemOfPowEqInt
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T17:46:44.283396+00:00
-- url     : https://prove2.me/theorems/67960409-a56d-5153-b9ab-d940d4b885d3
-- title:
--   Mem Of Pow Eq Int
-- statement:
--   Definitions and structural lemmas for Mem Of Pow Eq Int, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/MemOfPowEqInt.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsPrimitiveRootArcRoot
import Theorems.Thm_GlobalTheory_HostModel_host_d
import Theorems.Thm_GlobalTheory_HostModel_host_rt
import Theorems.Thm_GlobalTheory_HostModel_host_rt0_eq_I_mul_sqrt_seven
import Theorems.Thm_GlobalTheory_HostModel_host_w0_eq_halfSqrtNegSeven
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_p
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_q
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HostModel.host_d
attribute [local simp] GlobalTheory.HostModel.host_rt
attribute [local simp] GlobalTheory.HostModel.host_rt0_eq_I_mul_sqrt_seven
attribute [local simp] GlobalTheory.HostModel.host_w0_eq_halfSqrtNegSeven
attribute [local simp] GlobalTheory.HostModel.hypDatum_p
attribute [local simp] GlobalTheory.HostModel.hypDatum_q


set_option autoImplicit false
noncomputable section
open NumberField ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.ArcInTest
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
open Classical in

def changeOff {D : Datum H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {O' : Type} [CommRing O']
    [IsDomain O'] {b : O →+* O'} (a : ArcIn D l β O' b) (e : D.La → QkPt a.D₀ (FractionRing O') l.M) :
    ArcIn D l β O' b :=
  { a with
    eta := fun v => if v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) then a.eta v else e v
    geom := fun F _ _ _ r z hr hz f hf => by
      obtain ⟨h₁, I, h₂, h₃, h₄⟩ := a.geom F r z hr hz f hf
      refine ⟨h₁, I, h₂, h₃, fun v hv q hq => h₄ v hv q ?_⟩
      simpa only [if_pos hv] using hq }
example {D : Datum H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {O' : Type} [CommRing O']
    [IsDomain O'] {b : O →+* O'} (a : ArcIn D l β O' b) :
    D.La → @QkPt O' _ _ a.D₀ (FractionRing O') _ (Algebra.id _) l.M := a.eta
end GlobalTheory.ArcInTest


