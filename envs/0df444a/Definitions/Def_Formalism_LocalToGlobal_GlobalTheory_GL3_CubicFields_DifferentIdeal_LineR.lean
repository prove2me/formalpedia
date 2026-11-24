-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_LineR
-- name    : Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_LineR
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T21:25:48.924432+00:00
-- url     : https://prove2.me/theorems/ea4db279-4ac1-4813-85f4-ae8e4e1a557c
-- title:
--   Line R
-- statement:
--   Definitions and structural lemmas for Line R, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/DifferentIdeal/LineR.lean

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_DedekindFactorK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
open NumberField Classical
open scoped Pointwise
def mmR {E : Type} [Field E] [NumberField E] (M : IntermediateField ℚ ℂ) [NumberField M] {ι : Type}
    (emb : ι → E →+* ℂ) (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 M) (ι → M) :=
  Submodule.span (𝓞 M) {v | ∃ a ∈ (I : Submodule (𝓞 E) E), v = fun i => liftM M (emb i a)}
def lineR {E : Type} [Field E] [NumberField E] (M : IntermediateField ℚ ℂ) [NumberField M] {ι : Type}
    [DecidableEq ι] (emb : ι → E →+* ℂ) (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (i : ι) : Submodule (𝓞 M) M :=
  (mmR M emb I).comap (LinearMap.single (𝓞 M) (fun _ : ι => (M : Type)) i)
def imI {E : Type} [Field E] [NumberField E] (M : IntermediateField ℚ ℂ) [NumberField M]
    (σ : E →+* ℂ) (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 M) M :=
  Submodule.span (𝓞 M) {y | ∃ a ∈ (J : Submodule (𝓞 E) E), y = liftM M (σ a)}
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5


