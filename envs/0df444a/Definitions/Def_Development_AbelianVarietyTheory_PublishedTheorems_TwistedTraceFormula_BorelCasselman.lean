-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BorelCasselman
-- name    : Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BorelCasselman
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:53.690559+00:00
-- url     : https://prove2.me/theorems/ca85b225-fe34-4a91-a3c6-098d855e4cf8
-- title:
--   Borel Casselman
-- statement:
--   Definitions and structural lemmas for Borel Casselman, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/BorelCasselman.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_ofChar_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
namespace GlobalTheory.Published
def BorelCasselman : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V),
    IsAdmissible π → Function.Bijective (iwahoriProj π)
example (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : Type) [Fintype n] [DecidableEq n] {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    IsAdmissible (detRep n χ) :=
  ⟨(isSmooth_ofChar_iff _).2 hχ.detChar, fun _ _ _ => inferInstance⟩
end GlobalTheory.Published


