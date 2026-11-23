-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorRepApply
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorRepApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:31.695076+00:00
-- url     : https://prove2.me/theorems/cbdef521-56a7-43de-a38d-ad76c9e896c3
-- title:
--   Tensor Rep Apply
-- statement:
--   Definitions and structural lemmas for Tensor Rep Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TensorRepApply.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.JR.WeilProd
def tensorRep {G H X Y : Type} (W₁ : G → (X → ℂ) → X → ℂ) (W₂ : H → (Y → ℂ) → Y → ℂ) :
    G × H → (X × Y → ℂ) → X × Y → ℂ :=
  fun g f p => W₁ g.1 (fun u => W₂ g.2 (fun v => f (u, v)) p.2) p.1
end GlobalTheory.JR.WeilProd


