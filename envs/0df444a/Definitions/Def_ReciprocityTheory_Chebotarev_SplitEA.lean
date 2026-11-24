-- Prove2me | Definitions.Def_ReciprocityTheory_Chebotarev_SplitEA
-- name    : ReciprocityTheory_Chebotarev_SplitEA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:33.178833+00:00
-- url     : https://prove2.me/theorems/39b4c0b0-f742-4d9b-a6f0-3350767743a5
-- title:
--   Split EA
-- statement:
--   Definitions and structural lemmas for Split EA, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitEA.lean

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitA
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
namespace ReciprocityTheory.Cheb
noncomputable section
variable {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]
def splitEH (hirr : Irreducible (Polynomial.cyclotomic l E)) (χ : DirichletCharacter ℂ l) :
    Subgroup (CyclotomicField l E ≃ₐ[E] CyclotomicField l E) :=
  (χ.toUnitHom.comp (IsCyclotomicExtension.autEquivPow (CyclotomicField l E) hirr).toMonoidHom).ker
end
end ReciprocityTheory.Cheb


