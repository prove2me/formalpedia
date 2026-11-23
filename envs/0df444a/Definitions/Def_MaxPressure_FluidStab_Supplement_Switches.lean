-- Prove2me | Definitions.Def_MaxPressure_FluidStab_Supplement_Switches
-- name    : MaxPressure_FluidStab_Supplement_Switches
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T08:09:56.070229+00:00
-- url     : https://prove2.me/theorems/54b37d06-a22d-4968-bf35-bfd5f7d25ef4
-- title:
--   §9.2, pp. 210–212 — finite per-flow switch networks with local slot clocks
-- statement:
--   A finite switch network has arbitrary finite sets of switches, input ports, output ports and flows. Each flow has a nonempty finite ordered route of input-output port pairs at their respective switches; its route never repeats a pair. Different flows may share a pair, and a route may return to a switch through another pair. Every flow and route position has its own queue. Empty flow families are permitted.
--
--   The stochastic processing network is constructed from these data. One input processor and activity per flow generate packets with mean interarrival requirement $m_c$. A service activity at each route position holds its input and output ports and routes deterministically to the next queue or outside. Each switch has a positive local slot duration $d_s$ and an arbitrary phase, expressed in common wall time. Its transmissions take exactly one local slot.
--
--   With $H_{c,(u,v)}$ the indicator that flow $c$ traverses pair $(u,v)$ and $\alpha_c=1/m_c$, the traffic constraints in common wall time are
--
--   $$d_{s(u)}\sum_{c,v}\alpha_cH_{c,(u,v)}\le1,\qquad d_{s(v)}\sum_{c,u}\alpha_cH_{c,(u,v)}\le1.$$
--
--   For $d_s=1$ these are exactly (33)–(34). A switch chooses any physically feasible matching maximizing the sum of the own-queue minus immediate-downstream queue lengths and retains it for its slot. Initial transmissions retain their compatible port commitments, deterministic destinations and remaining slot duration. Different switches have independent phases and durations; there is no synchronized global slot. Inputs satisfy only (3), with arbitrary dependence. Transmission and routing primitives are computed deterministically, not assumed to obey extra strong laws or moment conditions.
--
--   **Formalization Note** The duration factors express arrival rates in local slot units. The source explicitly sets service means to one; the duration-two example in TIME_UNITS.md is outside that normalized model and does not refute Theorem 10. The unit-duration statement is recovered without changing either non-strict inequality.
-- source:
--   Dai & Lin, Maximum pressure policies in stochastic processing networks, Oper. Res. 53(2) (2005), §9.2, pp. 210–212 — finite per-flow switch networks with local slot clocks

import Mathlib
import Definitions.Def_MaxPressure_FluidStab_Supplement_Histories

namespace MaxPressure.FluidStab.Supplement

open MeasureTheory Filter Topology

/-- A finite network of switches and per-flow finite routes. Ports are globally named;
inputSwitch/outputSwitch identify their switch. A route may return to a switch and
several flows may use a port pair. Each route position has its own queue.
Durations and phases are in a common wall-clock unit, allowing different local slots. -/
structure SwitchData (S U V C : ℕ) where
  inputSwitch : Fin U → Fin S
  outputSwitch : Fin V → Fin S
  length : Fin C → ℕ
  route : (c : Fin C) → Fin (length c) → Fin U × Fin V
  meanInput : Fin C → ℝ
  duration : Fin S → ℝ
  phase : Fin S → ℝ

variable {S U V C : ℕ}

abbrev Positions (D : SwitchData S U V C) := (c : Fin C) × Fin (D.length c)
abbrev queueCount (D : SwitchData S U V C) := Fintype.card (Positions D)

noncomputable def position (D : SwitchData S U V C) : Fin (queueCount D) ≃ Positions D :=
  (Fintype.equivFin (Positions D)).symm

noncomputable def ports (D : SwitchData S U V C) (q : Fin (queueCount D)) : Fin U × Fin V :=
  D.route (position D q).1 (position D q).2

noncomputable def switchOf (D : SwitchData S U V C) (q : Fin (queueCount D)) : Fin S :=
  D.inputSwitch (ports D q).1

/-- Physical route and timing assumptions of §9.2. Empty flow families are allowed;
every actual flow has a nonempty route. Different local slots need not synchronize. -/
def SwitchData.Valid (D : SwitchData S U V C) : Prop :=
  (∀ c, 0 < D.length c ∧ 0 < D.meanInput c) ∧
  (∀ c, Function.Injective (D.route c)) ∧
  (∀ c p, D.inputSwitch (D.route c p).1 = D.outputSwitch (D.route c p).2) ∧
  ∀ s, 0 < D.duration s ∧ -D.duration s < D.phase s ∧ D.phase s ≤ 0

noncomputable def nextQueue (D : SwitchData S U V C) (q : Fin (queueCount D)) :
    Option (Fin (queueCount D)) := by
  classical
  let p := position D q
  exact if ht : p.2.val + 1 < D.length p.1 then
    some ((position D).symm ⟨p.1, ⟨p.2.val + 1, ht⟩⟩) else none

noncomputable def firstQueue (D : SwitchData S U V C) (c : Fin C) : Option (Fin (queueCount D)) := by
  classical
  exact if ht : 0 < D.length c then some ((position D).symm ⟨c, ⟨0, ht⟩⟩) else none

/-- The network is constructed from routes, ports and processing times, not supplied
independently. Input activity c uses input processor c; service activity q uses its
input and output ports. The outside-buffer shift is Fin.succ, as in the base module. -/
noncomputable def switchNetwork (D : SwitchData S U V C) :
    FluidStab.Network (queueCount D) (C + queueCount D) (C + (U + V)) where
  A k j := Fin.addCases
    (fun c => Fin.addCases (fun c' => if c = c' then 1 else 0) (fun _ => 0) j)
    (fun port => Fin.addCases (fun _ => 0)
      (fun q => Fin.addCases (fun u => if u = (ports D q).1 then 1 else 0)
        (fun v => if v = (ports D q).2 then 1 else 0) port) j) k
  B j i := Fin.addCases (fun _ => if i = 0 then 1 else 0)
    (fun q => if i = q.succ then 1 else 0) j
  inputProc k := ∃ c : Fin C, k = c.castAdd (U + V)
  m j := Fin.addCases D.meanInput (fun q => D.duration (switchOf D q)) j
  P j i i' := Fin.addCases
    (fun c => if i = 0 ∧ (firstQueue D c).map Fin.succ = some i' then 1 else 0)
    (fun q => if i = q.succ ∧
      (match nextQueue D q with
        | none => (0 : Fin (queueCount D + 1))
        | some q' => q'.succ) = i' then 1 else 0) j

/-- H of (32); route injectivity ensures each pair is counted once per flow. -/
noncomputable def H (D : SwitchData S U V C) (c : Fin C) (u : Fin U) (v : Fin V) : ℝ :=
  if ∃ p, D.route c p = (u, v) then 1 else 0

/-- Traffic in common wall time. For unit-duration switches these are exactly
(33),(34). For unequal local durations the factors convert each load to its local
slot unit; omitting them would make the printed extension to unequal units false. -/
noncomputable def SwitchTraffic (D : SwitchData S U V C) : Prop :=
  (∀ u, (∑ c : Fin C, ∑ v : Fin V,
    (1 / D.meanInput c) * H D c u v * D.duration (D.inputSwitch u)) ≤ 1) ∧
  (∀ v, (∑ c : Fin C, ∑ u : Fin U,
    (1 / D.meanInput c) * H D c u v * D.duration (D.outputSwitch v)) ≤ 1)

/-- Input primitives are arbitrary; all transmission durations and routing are
constructed deterministically. Thus no moment or routing law is assumed on service. -/
noncomputable def switchPrimitives {Ω : Type*} (D : SwitchData S U V C)
    (η : Fin C → ℕ → Ω → ℝ) :
    Throughput.Primitives (queueCount D) (C + queueCount D) Ω where
  eta j n ω := Fin.addCases (fun c => η c n ω)
    (fun q => D.duration (switchOf D q)) j
  Phi j i i' n _ := if (switchNetwork D).P j i i' = 1 then n else 0

/-- Only the input strong law (3); all input sequences may be dependent and non-iid. -/
def SwitchInputs {Ω : Type*} [MeasurableSpace Ω] (D : SwitchData S U V C)
    (η : Fin C → ℕ → Ω → ℝ) (Pr : Measure Ω) : Prop :=
  (∀ c n, Measurable (η c n)) ∧ (∀ c n ω, 0 ≤ η c n ω) ∧
  ∀ᵐ ω ∂Pr, ∀ c, Tendsto (fun n : ℕ =>
    BellWilliams2001.ThresholdPolicy.partialSum (fun l => η c l ω) n / n)
    atTop (𝓝 (D.meanInput c))

/-- Initial transmissions have the residual duration of the slot already in progress.
Arbitrary queue contents, input residuals, and compatible held jobs remain allowed. -/
def SwitchInitial (D : SwitchData S U V C)
    (s : InitialState (queueCount D) (C + queueCount D)) : Prop :=
  s.Legal (switchNetwork D) true ∧
  (∀ j r, s.residual j = some r → ∀ i, (switchNetwork D).B j i = 1 →
    (switchNetwork D).P j i (s.destination j i) = 1) ∧
  ∀ q r, s.residual (Fin.natAdd C q) = some r →
    r = D.phase (switchOf D q) + D.duration (switchOf D q)

/-- A matching at one switch, with one per-flow queue for every route position. -/
noncomputable def LocalMatching (D : SwitchData S U V C) (s : Fin S)
    (z : Fin (queueCount D) → ℝ) (a : Fin (queueCount D) → ℝ) : Prop :=
  (∀ q, a q = 0 ∨ a q = 1) ∧
  (∀ q, switchOf D q ≠ s → a q = 0) ∧
  (∀ u, (∑ q : Fin (queueCount D), if (ports D q).1 = u then a q else 0) ≤ 1) ∧
  (∀ v, (∑ q : Fin (queueCount D), if (ports D q).2 = v then a q else 0) ≤ 1) ∧
  ∀ q, a q = 1 → 1 ≤ z q

noncomputable def localPressure (D : SwitchData S U V C)
    (a : Fin (queueCount D) → ℝ) (z : Fin (queueCount D) → ℝ) : ℝ :=
  ∑ q, a q * (z q - (match nextQueue D q with | none => 0 | some q' => z q'))

/-- Each switch selects an arbitrary maximizing matching at its own slot boundaries
and holds it for the slot. Initial transmissions retain their commitments. Inputs
run continuously; input completions do not create synchronized service decisions. -/
noncomputable def SwitchMaximumPressure (D : SwitchData S U V C)
    (s0 : InitialState (queueCount D) (C + queueCount D))
    (h : History (queueCount D) (C + queueCount D)) : Prop :=
  (∀ t c, 0 ≤ t → h.rate t (Fin.castAdd (queueCount D) c) = 1) ∧
  (∀ q t, 0 ≤ t → h.rate t (Fin.natAdd C q) = 0 ∨ h.rate t (Fin.natAdd C q) = 1) ∧
  ∀ s n : ℕ, ∀ hs : s < S,
    let sw : Fin S := ⟨s, hs⟩
    let b := D.phase sw + n * D.duration sw
    let chosen := fun q => if switchOf D q = sw then h.rate b (Fin.natAdd C q) else 0
    (0 ≤ b → LocalMatching D sw (h.Z b) chosen ∧
      (∀ a, LocalMatching D sw (h.Z b) a →
        (∀ q, switchOf D q = sw → Fin.natAdd C q ∈ before s0 h b → a q = 1) →
        localPressure D a (h.Z b) ≤ localPressure D chosen (h.Z b))) ∧
    (∀ t, max 0 b ≤ t → t < b + D.duration sw → ∀ q, switchOf D q = sw →
      h.rate t (Fin.natAdd C q) = h.rate (max 0 b) (Fin.natAdd C q))

/-- The Definition 2 conclusion for every switch initial state. -/
def SwitchStable {Ω : Type*} [MeasurableSpace Ω] (D : SwitchData S U V C)
    (Pr : Measure Ω) (p : Policy (queueCount D) (C + queueCount D) Ω) : Prop :=
  ∀ s, SwitchInitial D s → Throughput.PathwiseStable Pr (fun ω => (p s ω).Z)

end MaxPressure.FluidStab.Supplement


