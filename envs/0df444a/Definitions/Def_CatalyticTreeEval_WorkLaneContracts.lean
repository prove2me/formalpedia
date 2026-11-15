-- Prove2me | Definitions.Def_CatalyticTreeEval_WorkLaneContracts
-- name    : CatalyticTreeEval_WorkLaneContracts
-- status  : Definition
-- author  : @sragavan
-- created : 2026-11-14T06:39:32.727967+00:00
-- url     : https://prove2.me/theorems/e9235101-886c-46df-b72c-8ad64f43c44b
-- title:
--   Lifted footprints and envelopes for native work lanes
-- statement:
--   For the native K-lane compiler, map each writable logical work cell p into physical address b+(K+1)p+j. Keep the source catalyst footprint and bounds. A source work envelope with upper bound B becomes the charged physical prefix $$[b,b+(K+1)B).$$ Preservation of inactive lanes means exact equality at every physical cell outside the selected lane. These contracts separate all-prefix head costs, writable cells and other retained lane data.
-- source:
--   Infrastructure for Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, uniform finite-control composition and arithmetic work banks.

import Definitions.Def_CatalyticTreeEval_WorkLanes

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.WorkLanes

/-- The source's writable work cells, mapped into its physical lane. -/
def liftedFootprint {lanes : ℕ} (lane : Fin lanes) (base : ℕ) (F : Footprint) : Footprint :=
  ⟨(address lane base) '' F.work, F.catalyst⟩

/-- Charge the entire addressed physical prefix, including origin-marker cells. -/
def liftedEnvelope (lanes base : ℕ) (E : Envelope) : Envelope :=
  ⟨base, base + (lanes + 1) * E.workHi, E.catalystLo, E.catalystHi⟩

/-- Every physical cell outside the active work lane is preserved. -/
def Inactive {lanes : ℕ} (lane : Fin lanes) (base : ℕ)
    (initial current : ℕ → Bool) : Prop :=
  ∀ p, p ∉ Set.range (address lane base) → current p = initial p

end CatalyticTreeEval.Contracts.WorkLanes


