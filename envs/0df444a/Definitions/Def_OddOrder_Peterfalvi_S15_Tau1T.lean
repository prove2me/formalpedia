-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S15_Tau1T
-- name    : OddOrder_Peterfalvi_S15_Tau1T
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T16:48:03.018941+00:00
-- url     : https://prove2.me/theorems/6876d474-d537-4842-bf4e-3c0dc8ff9e83
-- title:
--   The bundled coherent extension $\tau_1^T$ (Peterfalvi (13.2.d)/(13.3.c) at $T$)
-- statement:
--   The $T$-side mirror of the bundling of the coherent extension for the $S$-instance, pinning the (9.11)-$T$ coherence carrier.
--
--   Main declarations: `Hypothesis.coherentIndT_pinned` (The pinned (9.11)-`T` coherence carrier); `Hypothesis.tau1T_ofHonest` (The coherent extension `τ₁T` for the honest `T`-instance).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_Tau1T.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_Tau1T.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_NuRowPin
import Definitions.Def_OddOrder_Peterfalvi_S15_CaseACoherence

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The pinned (9.11)-`T` coherence carrier** (mirror of `coherent_H0Cprime_S`): the
`.choose` of `sSet_coherent_indT_A_pinned`.  Its `.extension` is `tau1T_ofHonest`; the pin
formula is `tau1T_ofHonest_nuRow_formula`. -/
noncomputable def Hypothesis.coherentIndT_pinned [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.indT
      (sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T) :=
  (hyp.sSet_coherent_indT_A_pinned hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief).choose

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The coherent extension `τ₁T` for the honest `T`-instance** (mirror of `tau1S_ofHonest`):
the `.extension` of the pinned (9.11)-`T` coherence.  This is the (13.2.d)
`τ₁T : IntegralCharacterMap ↥T G` that the `T`-side (13.4) θ-package threads. -/
noncomputable def Hypothesis.tau1T_ofHonest [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd)) :
    OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥hyp.T G :=
  (hyp.coherentIndT_pinned hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief).extension

end OddOrder.Peterfalvi.S15


