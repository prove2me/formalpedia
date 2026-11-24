-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OmLiftOfMultilinearTprod
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_OmLiftOfMultilinearTprod
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:51.815657+00:00
-- url     : https://prove2.me/theorems/3ec1e283-0034-467a-967e-bea4d66f6eaa
-- title:
--   Om Lift Of Multilinear Tprod
-- statement:
--   Definitions and structural lemmas for Om Lift Of Multilinear Tprod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/OmLiftOfMultilinearTprod.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_MinorOrderedEntries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.RowReal
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : Sizes} (P : ι → Entries S)
def omLiftOfMultilinear
    (Φ : MultilinearMap ℂ (fun j : Fin S.m => Pol ι (S.nR j.castSucc) (S.nR j.succ))
      (MultilinearMap ℂ (fun i : Fin S.m => Pol ι (S.nC i.castSucc) (S.nC i.succ))
        (weylSub (S.nR (0 : Fin (S.m + 1))) (psiWt P) →ₗ[ℂ]
          Module.Dual ℂ (weylSub (S.nC (0 : Fin (S.m + 1))) (baseWt P)) →ₗ[ℂ] ℂ))) : OM P →ₗ[ℂ] ℂ :=
  TensorProduct.lift
    ((TensorProduct.uncurry (RingHom.id ℂ) _ _ ℂ).comp
      (((LinearMap.llcomp ℂ _ _ _ (TensorProduct.uncurry (RingHom.id ℂ) _ _ ℂ)).comp
        PiTensorProduct.lift.toLinearMap).comp (PiTensorProduct.lift Φ)))
end GlobalTheory.RowReal
end


