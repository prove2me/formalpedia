-- Prove2me | Definitions.Def_OptStopC1_SpaceDeriv_BoundaryRegularity
-- name    : OptStopC1_SpaceDeriv_BoundaryRegularity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:34.830418+00:00
-- url     : https://prove2.me/theorems/0ae2ab4c-4f54-4560-a5bb-478fa2a713c2
-- title:
--   Probabilistic and Green regularity of a boundary point
-- statement:
--   For a state set $A$ and a point $z$, **probabilistic regularity** is the immediate-hitting condition
--
--   $$P_z(\sigma_A=0)=1.$$
--
--   Given an approach set $C$, **Green regularity** means that for every $\varepsilon>0$,
--
--   $$\lim_{C\ni x\to z}P_x(\tau_A\ge\varepsilon)=0.$$
--
--   The definitions are parameterized by $A$ because the paper applies them to both the stopping set $D$ and its interior $D^\circ$. Probabilities under $P_x$ are represented by the law of the flow $X^x$ under the common measure $P$.
-- source:
--   De Angelis & Peskir, Global C¹ Regularity of the Value Function in Optimal Stopping Problems, arXiv:1812.04564v2, p. 4, equations (2.7)–(2.8); p. 5, continuation of §2.3

import Definitions.Def_OptStopC1_SpaceDeriv_FlowBasics

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace OptStopC1.SpaceDeriv

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- Probabilistic regularity for a set A, equation (2.7). -/
noncomputable def IsProbRegular (X : Flow d Ω) (P : Measure Ω)
    (A : Set (State d)) (z : State d) : Prop :=
  P {ω | hittingTime X z A ω = 0} = 1

/-- Green regularity approaching z through C, equation (2.8). -/
noncomputable def IsGreenRegular (X : Flow d Ω) (P : Measure Ω)
    (C A : Set (State d)) (z : State d) : Prop :=
  ∀ ε : ℝ≥0, 0 < ε →
    Tendsto (fun x => P {ω | (ε : ℝ≥0∞) ≤ entryTime X x A ω})
      (𝓝[C] z) (𝓝 0)

end OptStopC1.SpaceDeriv


