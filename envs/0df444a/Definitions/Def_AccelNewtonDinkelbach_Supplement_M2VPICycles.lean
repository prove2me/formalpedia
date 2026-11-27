-- Prove2me | Definitions.Def_AccelNewtonDinkelbach_Supplement_M2VPICycles
-- name    : AccelNewtonDinkelbach_Supplement_M2VPICycles
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:59:36.24262+00:00
-- url     : https://prove2.me/theorems/3a9eb4d6-e8c1-45ad-a6fa-a915e8b4674f
-- title:
--   Flow-generating, unit-gain, flow-absorbing cycles and negative bicycles
-- statement:
--   Cycles are classified by gain as flow-generating ($\gamma(C)>1$), unit-gain ($=1$), or flow-absorbing ($<1$). A unit-gain cycle is negative when $c(C)<0$. A bicycle consists of a flow-generating cycle $C$, a path $P$, and a flow-absorbing cycle $D$ and is negative when
--
--   $$c(P)+\gamma(P)\frac{c(D)}{1-\gamma(D)}<-\frac{c(C)}{\gamma(C)-1}.$$
--
--   The module also records $(\delta,u)$-negative generating cycles and restriction to a selected subgraph.
-- source:
--   Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, Definitions 4.1–4.2, p.11, and Definition 4.5, p.13

import Mathlib
import Definitions.Def_AccelNewtonDinkelbach_Supplement_M2VPI

namespace AccelNewtonDinkelbach.Supplement

set_option autoImplicit false

namespace M2VPI

variable {n m : ℕ} (M : M2VPI n m)

def Walk.UsesOnly (P : M.Walk) (A : Fin m → Prop) : Prop := ∀ e ∈ P.edges, A e
def Walk.FlowGenerating (P : M.Walk) : Prop := 1 < P.walkGain
def Walk.UnitGain (P : M.Walk) : Prop := P.walkGain = 1
def Walk.FlowAbsorbing (P : M.Walk) : Prop := P.walkGain < 1
def Walk.NegativeUnitGain (P : M.Walk) : Prop := P.UnitGain ∧ P.walkCost < 0

/-- A negative bicycle `CPD` in the allowed subgraph. -/
def HasNegativeBicycle (A : Fin m → Prop) : Prop :=
  ∃ (u v : Fin n) (C D P : M.Walk), C.IsCycleAt u ∧ D.IsCycleAt v ∧
    P.start = u ∧ P.finish = v ∧ P.IsPath ∧ C.UsesOnly M A ∧ D.UsesOnly M A ∧ P.UsesOnly M A ∧
    C.FlowGenerating ∧ D.FlowAbsorbing ∧
      P.walkCost + P.walkGain * (D.walkCost / (1 - D.walkGain)) <
        -C.walkCost / (C.walkGain - 1)

def HasNegativeUnitGainCycle (A : Fin m → Prop) : Prop :=
  ∃ (u : Fin n) (C : M.Walk), C.IsCycleAt u ∧ C.UsesOnly M A ∧ C.NegativeUnitGain

/-- A `(δ,u)`-negative flow-generating cycle in the allowed subgraph. -/
def HasDeltaNegativeGeneratingCycle (A : Fin m → Prop) (δ : ℝ) (u : Fin n) : Prop :=
  ∃ (v : Fin n) (C P : M.Walk), C.IsCycleAt v ∧ P.start = v ∧ P.finish = u ∧ P.IsPath ∧
    C.UsesOnly M A ∧ P.UsesOnly M A ∧ C.FlowGenerating ∧
      C.walkCost + (C.walkGain - 1) * (P.walkCost + P.walkGain * δ) < 0

def HasAbsorbingCycleAt (A : Fin m → Prop) (u : Fin n) : Prop :=
  ∃ C : M.Walk, C.IsCycleAt u ∧ C.UsesOnly M A ∧ C.FlowAbsorbing

end M2VPI

end AccelNewtonDinkelbach.Supplement


