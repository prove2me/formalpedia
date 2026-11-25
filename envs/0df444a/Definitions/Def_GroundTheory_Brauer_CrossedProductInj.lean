-- Prove2me | Definitions.Def_GroundTheory_Brauer_CrossedProductInj
-- name    : GroundTheory_Brauer_CrossedProductInj
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T06:01:27.23415+00:00
-- url     : https://prove2.me/theorems/066c0c9d-8aef-4a37-a483-3cae9e2c60a8
-- title:
--   Crossed Product Inj
-- statement:
--   Definitions and structural lemmas for Crossed Product Inj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProductInj.lean

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Definitions.Def_GroundTheory_Brauer_CrossedProductSimple
import Definitions.Def_GroundTheory_Brauer_CrossedProductMaps
import Definitions.Def_GroundTheory_Brauer_SkolemNoether
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints
import Theorems.Thm_GroundTheory_Brauer_H2mul_mk_eq_mk_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Brauer
open groupCohomology
universe u v
namespace CrossedProduct
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} {hf : IsMulCocycle₂ f}
variable [FiniteDimensional K L] [IsGalois K L]
end CrossedProduct
namespace CrossedProduct
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ}
end CrossedProduct
theorem isMulCocycle₂_of_mem {G M : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M]
    (c : mulCocycles₂ G M) : IsMulCocycle₂ (c : G × G → M) := c.2
namespace H2mul
variable (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
def toBrauer : H2mul (L ≃ₐ[K] L) Lˣ → BrauerGroup.{u, u} K :=
  Quotient.lift (fun c : mulCocycles₂ (L ≃ₐ[K] L) Lˣ => ⟦csaOf K (CrossedProduct (isMulCocycle₂_of_mem c))⟧)
    (fun c c' h => by
      have h' : mk _ _ c = mk _ _ c' := Quotient.sound h
      rw [mk_eq_mk_iff] at h'
      exact Quotient.sound (isBrauerEquivalent_of_algEquiv
        (A := csaOf K (CrossedProduct (isMulCocycle₂_of_mem c))) (B := csaOf K (CrossedProduct (isMulCocycle₂_of_mem c')))
        (CrossedProduct.equivOfIsMulCoboundary₂ (isMulCocycle₂_of_mem c') (isMulCocycle₂_of_mem c) h').symm))
variable {K L}
end H2mul
end GroundTheory.Brauer
end


