-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_InvIdealIdxPi
-- name    : Formalism_PeriodIntegrals_InvIdealIdxPi
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:38:32.172812+00:00
-- url     : https://prove2.me/theorems/ef2d73c8-cf19-45d8-bb76-bb191e984b9c
-- title:
--   Inv Ideal Idx Pi
-- statement:
--   Definitions and structural lemmas for Inv Ideal Idx Pi, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/InvIdealIdxPi.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI
open NumberField nonZeroDivisors
def InvIdealIdxPi : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (ι : Type) [Fintype ι] (J : ι → Ideal (𝓞 E)), (∀ i, J i ≠ ⊥) →
    (Submodule.pi Set.univ (fun _ : ι => (1 : Submodule (𝓞 E) E))).toAddSubgroup.relIndex
      (Submodule.pi Set.univ (fun i =>
        (((J i : FractionalIdeal (𝓞 E)⁰ E)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E))).toAddSubgroup =
      ∏ i, Ideal.absNorm (J i)
end PI
end


