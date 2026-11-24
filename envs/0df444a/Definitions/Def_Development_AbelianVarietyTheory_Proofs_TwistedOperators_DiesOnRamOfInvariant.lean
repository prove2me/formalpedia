-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DiesOnRamOfInvariant
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_DiesOnRamOfInvariant
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T22:11:38.491823+00:00
-- url     : https://prove2.me/theorems/0f64d6cc-c2c7-46cd-a5e3-b1243668c531
-- title:
--   Dies On Ram Of Invariant
-- statement:
--   Definitions and structural lemmas for Dies On Ram Of Invariant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DiesOnRamOfInvariant.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemSmulOfMemFlagSubOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OpEOmTargetUnipotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLatticeExchange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLatticeChainLatAndComap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlagVolumeOpenFiniteNonzero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsSelfDualOfHasConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NabsDetEqOfActEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsCOPrXCgrp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralTranslateIndicator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsQuotIntCosetFn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingAffPtUncurry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures
import Theorems.Thm_GlobalTheory_RootEx_ChainLattice_exists_smul_mem
import Theorems.Thm_GlobalTheory_RootEx_ChainLattice_span_eq_top_of_smul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise ENNReal
noncomputable section
namespace GlobalTheory.LevelUnfold
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} {q : Unif k}
instance isLattice_interX (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) [hL : L.IsLattice k] : (interX L).IsLattice k := by
  refine ⟨Submodule.fg_of_fg_map_injective (inX k n c) (fun x y h => funext fun r => congrFun h (Sum.inl r))
    (hL.fg.of_le (Submodule.map_comap_le _ _)), ChainLattice.span_eq_top_of_smul_mem _ fun v => ?_⟩
  obtain ⟨a, ha, hav⟩ := ChainLattice.exists_smul_mem (K := k) L (v := inX k n c v) (by rw [hL.span_eq_top]; trivial)
  exact ⟨a, ha, by rw [interX, Submodule.mem_comap, map_smul]; exact hav⟩
variable [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} {ν : Measure k} [ν.IsAddHaarMeasure]
end GlobalTheory.LevelUnfold


