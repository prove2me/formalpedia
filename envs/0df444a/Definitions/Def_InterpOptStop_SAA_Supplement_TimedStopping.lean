-- Prove2me | Definitions.Def_InterpOptStop_SAA_Supplement_TimedStopping
-- name    : InterpOptStop_SAA_Supplement_TimedStopping
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T22:43:33.811796+00:00
-- url     : https://prove2.me/theorems/67562ce3-11b7-4434-863f-e5e8f163ce46
-- title:
--   Time-dependent stopping policies, clock augmentation and unrestricted optimal value
-- statement:
--   A time-dependent policy prescribes stop or go at each period and physical state. Admissibility means that each stopping region is measurable. With the first stop at period $t$, its reward is $\beta^{t-1}g(t,x(t))$, and never stopping earns zero. The physical path is lifted to $(t/T,x(t))$, and the published stationary reward and value evaluate the corresponding policy on this lift. Define
--   $$J^*(\bar x)=\sup_{\pi\text{ admissible}}J^\pi(\bar x).$$
--   This is the optimum over all time-dependent policies, rather than over trees. Trees use the same clock-augmented path law. In the theorems, finite horizon and bounded rewards make this nonempty supremum finite: the always-go policy is admissible and earns zero. The clock lift is measurable and has distinct time values whenever $T>0$.
-- source:
--   Ciocan & Mišić, Interpretable Optimal Stopping, arXiv:1812.07211v2, §3.1, (1)–(2), pp. 5–6; Assumption 4, pp. 12–13

import Mathlib
import Definitions.Def_InterpOptStop_SAA_StoppingModel
import Definitions.Def_InterpOptStop_SAA_TreePolicy

open MeasureTheory

namespace InterpOptStop.SAA.Supplement

abbrev TimedPolicy (n T : ℕ) := Fin T → (Fin n → ℝ) → Act

/-- Measurable stopping regions: the convention needed for expected payoffs. -/
def Admissible {n T : ℕ} (π : TimedPolicy n T) : Prop :=
  ∀ k, MeasurableSet {x | π k x = Act.stop}

/-- The physical state is augmented by the paper's clock t/T, at coordinate zero. -/
noncomputable def clockState {n T : ℕ} (k : Fin T) (x : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.cons (((k.val + 1 : ℕ) : ℝ) / T) x

noncomputable def clockPath {n T : ℕ} (x : Fin T → Fin n → ℝ) : Fin T → Fin (n + 1) → ℝ :=
  fun k => clockState k (x k)

/-- Only the finite set of actual clock values is used; elsewhere the action is go. -/
noncomputable def stationaryLift {n T : ℕ} (π : TimedPolicy n T)
    (z : Fin (n + 1) → ℝ) : Act :=
  if h : ∃ k : Fin T, z 0 = ((k.val + 1 : ℕ) : ℝ) / T then
    π (Classical.choose h) (fun i => z i.succ)
  else Act.go

def clockReward {n T : ℕ} (g : Fin T → (Fin n → ℝ) → ℝ)
    (k : Fin T) (z : Fin (n + 1) → ℝ) : ℝ := g k (fun i => z i.succ)

noncomputable def timedValue {n T : ℕ} (μ : Measure (Fin T → Fin n → ℝ)) (β : ℝ)
    (g : Fin T → (Fin n → ℝ) → ℝ) (π : TimedPolicy n T) : ℝ :=
  J (μ.map clockPath) β (clockReward g) (stationaryLift π)

/-- The supremum is over all admissible time-dependent policies, not over trees. -/
noncomputable def optimalValue {n T : ℕ} (μ : Measure (Fin T → Fin n → ℝ)) (β : ℝ)
    (g : Fin T → (Fin n → ℝ) → ℝ) : ℝ :=
  ⨆ π : {π : TimedPolicy n T // Admissible π}, timedValue μ β g π.val

noncomputable def treeValue {n T : ℕ} (μ : Measure (Fin T → Fin n → ℝ)) (β : ℝ)
    (g : Fin T → (Fin n → ℝ) → ℝ) (S : Tree (n + 1)) (θ : Thresholds) : ℝ :=
  J (μ.map clockPath) β (clockReward g) (policy S θ)

end InterpOptStop.SAA.Supplement


