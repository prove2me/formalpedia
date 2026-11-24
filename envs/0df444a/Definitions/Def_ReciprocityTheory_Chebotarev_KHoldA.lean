-- Prove2me | Definitions.Def_ReciprocityTheory_Chebotarev_KHoldA
-- name    : ReciprocityTheory_Chebotarev_KHoldA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:03.767268+00:00
-- url     : https://prove2.me/theorems/427a45cb-ff8b-43e6-90bb-668c2c9f2da6
-- title:
--   KHold A
-- statement:
--   Definitions and structural lemmas for KHold A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/KHoldA.lean

import Definitions.Def_ReciprocityTheory_Chebotarev_NormGsEmbZLe
import Definitions.Def_ReciprocityTheory_Chebotarev_RpowNegFinrankSubOne
import Definitions.Def_ReciprocityTheory_Chebotarev_IdealLat
import Definitions.Def_ReciprocityTheory_Chebotarev_MeanZero
import Definitions.Def_ReciprocityTheory_Chebotarev_LatSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units Set
open scoped Classical
namespace ReciprocityTheory.Cheb
noncomputable section
variable {E : Type} [Field E] [NumberField E]
def gfun {l : ℕ} (χ : DirichletCharacter ℂ l) (c : NZIdeal E) (s : ℝ) (a : NZIdeal E) : ℂ :=
  χ ((Ideal.absNorm a.1 : ℕ) : ZMod l) * (1 - (Ideal.absNorm c.1 : ℂ) * (if c.1 ∣ a.1 then 1 else 0)) *
    ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ))
def Hfun {l : ℕ} (χ : DirichletCharacter ℂ l) (b c : NZIdeal E) (s : ℝ) (I : Ideal (𝓞 E)) : ℂ :=
  ((Ideal.absNorm b.1 : ℕ) : ℂ) ^ (s : ℂ) * (χ (((Ideal.absNorm I / Ideal.absNorm b.1 : ℕ)) : ZMod l) *
    (1 - (Ideal.absNorm c.1 : ℂ) * (if b.1 * c.1 ∣ I then 1 else 0)) * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-(s : ℂ)))
end
end ReciprocityTheory.Cheb


