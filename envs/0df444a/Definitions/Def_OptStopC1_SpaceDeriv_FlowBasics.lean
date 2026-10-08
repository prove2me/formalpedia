-- Prove2me | Definitions.Def_OptStopC1_SpaceDeriv_FlowBasics
-- name    : OptStopC1_SpaceDeriv_FlowBasics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:23.900336+00:00
-- url     : https://prove2.me/theorems/e0b6d964-67f2-4651-9a77-79fe75cfba6b
-- title:
--   Stochastic flow, entry and hitting times, and coordinate derivatives
-- statement:
--   A **stochastic flow** starts a process at each state $x\in\mathbb R^d$ on one probability space. Its path from $x$ is $X^x_t$, for $t\ge0$. For a set $A$, the first entry time and the first strictly positive hitting time are
--
--   $$\tau_A^x=\inf\{t\ge0:X_t^x\in A\},\qquad \sigma_A^x=\inf\{t>0:X_t^x\in A\}.$$
--
--   Both take the value $+\infty$ if their defining set is empty. The coordinate derivative $\partial_iX_t^{j,x}$ is the derivative of the $j$th component of $X_t^x$ in its $i$th initial-state direction. Path right continuity and left limits are recorded separately.
--
--   These objects are used by both branches of the boundary regularity argument.
--
--   **Formalization Note** The state space is EuclideanSpace over `Fin d`, time is nonnegative real, and hitting times are extended nonnegative real. Coordinate indices start at zero in Lean.
-- source:
--   De Angelis & Peskir, Global C¹ Regularity of the Value Function in Optimal Stopping Problems, arXiv:1812.04564v2, pp. 3–4, equations (2.4)–(2.5); p. 6, §2.4

import Mathlib

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace OptStopC1.SpaceDeriv

abbrev State (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Flow (d : ℕ) (Ω : Type*) := State d → ℝ≥0 → Ω → State d

noncomputable def entryTime {d : ℕ} {Ω : Type*} (X : Flow d Ω) (x : State d)
    (A : Set (State d)) (ω : Ω) : ℝ≥0∞ :=
  sInf ((fun t : ℝ≥0 => (t : ℝ≥0∞)) '' {t | X x t ω ∈ A})

noncomputable def hittingTime {d : ℕ} {Ω : Type*} (X : Flow d Ω) (x : State d)
    (A : Set (State d)) (ω : Ω) : ℝ≥0∞ :=
  sInf ((fun t : ℝ≥0 => (t : ℝ≥0∞)) '' {t | 0 < t ∧ X x t ω ∈ A})

noncomputable def finiteEntryTime {d : ℕ} {Ω : Type*} (X : Flow d Ω) (x : State d)
    (A : Set (State d)) (ω : Ω) : ℝ≥0 := (entryTime X x A ω).untopD 0

noncomputable def flowPartial {d : ℕ} {Ω : Type*} (X : Flow d Ω) (i j : Fin d)
    (x : State d) (t : ℝ≥0) (ω : Ω) : ℝ :=
  (fderiv ℝ (fun y : State d => X y t ω) x) (EuclideanSpace.single i (1 : ℝ)) j

def IsRightContinuousPath {α : Type*} [TopologicalSpace α] (f : ℝ≥0 → α) : Prop :=
  ∀ t : ℝ≥0, ContinuousWithinAt f (Set.Ici t) t

def HasLeftLimits {α : Type*} [TopologicalSpace α] (f : ℝ≥0 → α) : Prop :=
  ∀ t : ℝ≥0, 0 < t → ∃ l : α, Tendsto f (𝓝[Set.Iio t] t) (𝓝 l)

end OptStopC1.SpaceDeriv


