-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperHyperplaneMid
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperHyperplaneMid
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T07:01:48.742671+00:00
-- url     : https://prove2.me/theorems/ed2cbbcf-41df-44f8-9d4f-8e41ae1c52ba
-- title:
--   PSnapper Hyperplane Mid
-- statement:
--   Definitions and structural lemmas for PSnapper Hyperplane Mid, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperHyperplaneMid.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperHyperplane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperDevissage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
namespace SnapperHyperplaneMid
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
section Quot
def mulQ (F₁ G₁ G₂ : SubSystem k x Ω) (u : Ω) (hmap : ∀ I, ∀ y ∈ F₁.sub I, u * y ∈ G₁.sub I) (I : Chart x) :
    F₁.sub I →ₗ[k] G₁.sub I ⧸ SubSystem.quotSub G₁ G₂ I :=
  (SubSystem.quotSub G₁ G₂ I).mkQ ∘ₗ
    { toFun := fun y => ⟨u * y, hmap I y y.2⟩
      map_add' := fun y y' => Subtype.ext (mul_add u (y : Ω) y')
      map_smul' := fun c y => Subtype.ext (mul_smul_comm c u (y : Ω)) }
end Quot
section Chart
end Chart
end SnapperHyperplaneMid
end
end GroundTheory.Heights₂.Heights.Kleiman


