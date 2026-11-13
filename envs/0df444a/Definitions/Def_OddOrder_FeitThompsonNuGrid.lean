-- Prove2me | Definitions.Def_OddOrder_FeitThompsonNuGrid
-- name    : OddOrder_FeitThompsonNuGrid
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T17:52:14.462144+00:00
-- url     : https://prove2.me/theorems/546ae34e-dd91-4b6a-89db-8d2688a51946
-- title:
--   Peterfalvi: the certain-type $T$ $\nu$-grid
-- statement:
--   Constructs the canonical $T$-side grid used in Peterfalvi (4.3)–(4.9) and (13.1), mirroring the $S$-side supply from the certain-type hypothesis on the partner maximal subgroup.
--
--   Main declarations: `eTS` (The `G`-element-preserving equiv `↥certainTypeT.sdiff.W ≃ ↥certainTypeS.sdiff.W` through…); `colT` (T-side column dual on `W₂_T = mp.K`); `rowDualT` (T-side row dual on `W₁_T = mp.Kstar`); `rowT` (T-side row index corresponding to `rowDualT`).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/FeitThompsonNuGrid.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/FeitThompsonNuGrid.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_FeitThompsonSetup
import Definitions.Def_OddOrder_Peterfalvi_S15_HonestTypeP2A0

namespace OddOrder

open OddOrder.BG

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.RepresentationTheory

open scoped Pointwise

section

open scoped OddOrder.Peterfalvi.S15.FiniteInduce

namespace Section16CharacterData

variable {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimpleOdd G)
  (mp : Section16MaximalPair G)

variable (tp : Section16TypePStructure mp)

variable [NeZero (Nat.card ↥(mp.certainTypeS hG).W1)]

/-- The `G`-element-preserving equiv
`↥certainTypeT.sdiff.W ≃* ↥certainTypeS.sdiff.W` through `↥tp.W`. -/
noncomputable def eTS :
    ↥(mp.certainTypeT hG).sdiffTICyclicHypothesis.W ≃*
      ↥(mp.certainTypeS hG).sdiffTICyclicHypothesis.W :=
  (gridEquivE_T hG mp tp).symm.trans (gridEquivE hG mp tp)

/-- T-side column dual on `W₂_T = mp.K`. -/
noncomputable def colT (i : Fin tp.q) :
    ((mp.certainTypeT hG).sdiffTICyclicHypothesis.W2.subgroupOf
      (mp.certainTypeT hG).sdiffTICyclicHypothesis.W) →* ℂˣ :=
  (((mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar
        ((mp.certainTypeS hG).w1CharEquiv (eqQ hG mp tp i)) 1).comp
      (eTS hG mp tp).toMonoidHom).comp
    ((mp.certainTypeT hG).sdiffTICyclicHypothesis.W2.subgroupOf
      (mp.certainTypeT hG).sdiffTICyclicHypothesis.W).subtype

/-- T-side row dual on `W₁_T = mp.Kstar`. -/
noncomputable def rowDualT (j : Fin tp.p) :
    ((mp.certainTypeT hG).sdiffTICyclicHypothesis.W1.subgroupOf
      (mp.certainTypeT hG).sdiffTICyclicHypothesis.W) →* ℂˣ :=
  (((mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar
      1 (chi2enum hG mp tp j)).comp (eTS hG mp tp).toMonoidHom).comp
    ((mp.certainTypeT hG).sdiffTICyclicHypothesis.W1.subgroupOf
      (mp.certainTypeT hG).sdiffTICyclicHypothesis.W).subtype

variable [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)]

/-- T-side row index corresponding to `rowDualT`. -/
noncomputable def rowT (j : Fin tp.p) : Fin (Nat.card ↥(mp.certainTypeT hG).W1) :=
  (mp.certainTypeT hG).w1CharEquiv.symm (rowDualT hG mp tp j)

/-- The shared `ω`-grid expressed through `certainTypeT`. -/
noncomputable def omegaT (i : Fin tp.q) (j : Fin tp.p) : ClassFunction ↥tp.W ℂ :=
  ClassFunction.compHom (gridEquivE_T hG mp tp).toMonoidHom
    ((mp.certainTypeT hG).chiColumn (colT hG mp tp i) (rowT hG mp tp j) :
      ClassFunction ↥(mp.certainTypeT hG).sdiffTICyclicHypothesis.W ℂ)

/-- T-side `ν`-grid from the certain-type characters of `mp.T`. -/
noncomputable def nuT (i : Fin tp.q) (j : Fin tp.p) : ClassFunction ↥mp.T ℂ :=
  (((mp.certainTypeT hG).columnFamily (colT hG mp tp i)).mu
      (rowT hG mp tp j) : ClassFunction ↥mp.T ℂ)

/-- T-side signs `δ'`. -/
noncomputable def deltaPrimeT (i : Fin tp.q) : ℤ :=
  ((mp.certainTypeT hG).columnFamily (colT hG mp tp i)).sign

end Section16CharacterData

end

end OddOrder


