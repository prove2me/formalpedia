-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S16_G0Coprime
-- name    : OddOrder_Peterfalvi_S16_G0Coprime
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T16:26:41.26221+00:00
-- url     : https://prove2.me/theorems/fef1e5bc-27f0-4c6b-96fd-971b91aefcfd
-- title:
--   Peterfalvi (14.11.3), support half: generic elements have order prime to $pq$
-- statement:
--   Proves the support-analysis half of Peterfalvi (14.11.3) (Peterfalvi, *Character Theory for the Odd Order Theorem*, §14, pp. 87-92): generic elements have order prime to $pq$. It introduces the concrete $T$-side Frobenius group $F_{q^p}\rtimes V^*$.
--
--   Main declarations: `tFieldFrobeniusGroup` (The concrete T-side Frobenius group `F_{q^p} ⋊ V` (BG Appendix C model with the T-side…); `tFieldKernel` (The additive kernel `F_{q^p} ≤ F_{q^p} ⋊ V` of the T-side model); `tFieldComplement` (The norm-one complement `V ≤ F_{q^p} ⋊ V` of the T-side model); `TFieldModelData` (Minimal T-side (14.4)/(9.7.b) field-model carrier).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_G0Coprime.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S16_G0Coprime.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_BridgeCharacter
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs
import Definitions.Def_OddOrder_Peterfalvi_S15_SSideGaloisFieldModel
import Definitions.Def_OddOrder_Peterfalvi_S16_PairingCoherence
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ColumnOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S16_GridExpansion
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTGrid
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_Step4Capstone
import Definitions.Def_OddOrder_Peterfalvi_S16_CoreLemmas
import Definitions.Def_OddOrder_GroupTheory_ConjClassSet
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SemilinearFieldModel

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open scoped Pointwise

variable {G : Type*} [Group G]

/-- The concrete T-side Frobenius group `F_{q^p} ⋊ V*` (BG Appendix C model with the T-side
parameters: kernel prime `q`, exponent `p`). -/
abbrev tFieldFrobeniusGroup (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) : Type _ :=
  letI : Fact hyp.q.Prime := ⟨hyp.q_prime⟩
  OddOrder.BG.AppC.NormSet.normOneFrobeniusGroup hyp.q hyp.p

/-- The additive kernel `F_{q^p} ≤ F_{q^p} ⋊ V*` of the T-side model. -/
noncomputable def tFieldKernel (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) :
    Subgroup (tFieldFrobeniusGroup hyp) :=
  letI : Fact hyp.q.Prime := ⟨hyp.q_prime⟩
  (SemidirectProduct.inl :
      OddOrder.BG.AppC.NormSet.additiveFieldGroup hyp.q hyp.p →*
        tFieldFrobeniusGroup hyp).range

/-- The norm-one complement `V* ≤ F_{q^p} ⋊ V*` of the T-side model. -/
noncomputable def tFieldComplement (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) :
    Subgroup (tFieldFrobeniusGroup hyp) :=
  letI : Fact hyp.q.Prime := ⟨hyp.q_prime⟩
  (SemidirectProduct.inr :
      OddOrder.BG.AppC.NormSet.normOneUnits hyp.q hyp.p →*
        tFieldFrobeniusGroup hyp).range

/-- **Minimal T-side (14.4)/(9.7.b) field-model carrier** — the T-side dual of the (14.2.a)
`FieldNormalizerData`: an injective realization of `T' = Q ⋊ V` as the concrete Frobenius
group `F_{q^p} ⋊ V*`, with the additive kernel matching `Q` and the norm-one complement
matching `V`.  Its supply is the (14.4)-case (9.7.b) resolution for `T` (`v = (q^p−1)/(q−1)`,
`D = 1` — the `T_side_caseB_facts`/issue-9000 sphere); its payoff is the transport
`TFieldModelData.derived_inf_centralizer_le_Q`, the `hfrobT` input of the (14.11.3) chain. -/
structure TFieldModelData (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) where
  sigma : tFieldFrobeniusGroup hyp →* G
  sigma_injective : Function.Injective sigma
  sigma_Q_eq_Q : (tFieldKernel hyp).map sigma = hyp.Q
  sigma_V_eq_V : (tFieldComplement hyp).map sigma = hyp.V

end OddOrder.Peterfalvi.S16


