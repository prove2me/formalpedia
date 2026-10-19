-- Prove2me | Definitions.Def_DynSetValue_DPP_Setting
-- name    : DynSetValue_DPP_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:18:39.047423+00:00
-- url     : https://prove2.me/theorems/069916fd-7604-4326-bce3-ce9fe4d6ebec
-- title:
--   Canonical Wiener game setting and Assumptions 3.1 and 3.6
-- statement:
--   Fix $T>0$, positive dimensions $d$ and $N$, and the canonical continuous-path space $\Omega$ starting at zero. The coordinate process $B$, finite-horizon Wiener law $\mathbb P_0$, and its Borel-null-augmented natural filtration $\mathcal F$ are represented explicitly. For paths $\omega,\widetilde\omega$, concatenation is
--
--   $$
--   (\omega\otimes_t\widetilde\omega)_s=
--   \begin{cases}\omega_s,&s\le t,\\
--   \omega_t+\widetilde\omega_{s-t},&s>t.\end{cases}
--   $$
--
--   The setting also defines the stopped-path metric $\mathbf d$, nonempty convex player action sets, the drift $b$, own-action running costs $f_i$, terminal cost $\xi$, and the paper's boundedness, progressive-measurability and uniform-continuity assumptions. These shared objects fix the model used by every theorem in the mission.
--
--   **Formalization Note** Coordinates and payoff vectors use Euclidean norms. Wiener measure is pinned by Brownian finite-dimensional laws through $T$ and independence of coordinate processes. The augmentation contains Borel null events, and the moduli are uniform as used in the paper.
-- source:
--   Feinstein, Rudloff, Zhang, Dynamic set values for nonzero sum games with multiple equilibriums, arXiv:2002.00449v2, pp. 20–23, §3.1–§3.2, Assumptions 3.1 and 3.6

import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace DynSetValue.DPP

abbrev State (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Payoff (N : ℕ) := EuclideanSpace ℝ (Fin N)
abbrev Interval (T : ℝ) := Set.Icc (0 : ℝ) T

/-- Continuous canonical paths starting at the origin. -/
abbrev Ω (T : ℝ) (d : ℕ) :=
  {ω : C(Interval T, State d) // ∀ s : Interval T, s.1 = 0 → ω s = 0}

instance instMeasurableSpaceΩ (T : ℝ) (d : ℕ) :
    MeasurableSpace (Ω T d) := borel _

/-- Clamp a real time to the game's horizon. -/
noncomputable def clamp (T : ℝ) (hT : 0 < T) (s : ℝ) : Interval T :=
  Set.projIcc 0 T hT.le s

/-- Canonical coordinate process, extended by clamping outside [0,T]. -/
noncomputable def B {T : ℝ} (hT : 0 < T) {d : ℕ} (s : ℝ) (ω : Ω T d) : State d :=
  ω.1 (clamp T hT s)

/-- A finite-horizon Wiener law: every finite collection of coordinate observations
up to T has the standard Brownian finite-dimensional distribution. -/
def IsWiener {T : ℝ} (hT : 0 < T) {d : ℕ} (P0 : Measure (Ω T d)) : Prop :=
  0 < d ∧ IsProbabilityMeasure P0 ∧
  ∀ (k : Fin d) (I : Finset ℝ≥0),
    (∀ s ∈ I, (s : ℝ) ≤ T) →
    HasLaw (fun ω : Ω T d => I.restrict (fun s => B hT (s : ℝ) ω k))
      (BrownianReal.projectiveFamily I) P0 ∧
  iIndepFun (fun k (ω : Ω T d) (s : ℝ≥0) => B hT (s : ℝ) ω k) P0

/-- The Borel null events available at every time in the augmented filtration. -/
def nullBorel {T : ℝ} {d : ℕ}
    (P0 : Measure (Ω T d)) : MeasurableSpace (Ω T d) :=
  MeasurableSpace.generateFrom {s | MeasurableSet s ∧ P0 s = 0}

/-- The raw canonical σ-algebra at time t. -/
noncomputable def rawPast {T : ℝ} (hT : 0 < T) {d : ℕ} (t : ℝ) :
    MeasurableSpace (Ω T d) :=
  ⨆ (s : ℝ) (_ : s ≤ t), MeasurableSpace.comap (B hT (d := d) s) (borel (State d))

/-- Canonical filtration augmented by Borel P₀-null events. -/
noncomputable def 𝓕 {T : ℝ} (hT : 0 < T) {d : ℕ}
    (P0 : Measure (Ω T d)) : Filtration ℝ (borel (Ω T d)) where
  seq t := rawPast hT t ⊔ nullBorel P0
  mono' := by
    intro s t hst
    apply sup_le_sup_right
    unfold rawPast
    refine iSup_le fun u => iSup_le fun hu => ?_
    exact le_iSup_of_le u (le_iSup_of_le (le_trans hu hst) le_rfl)
  le' := by
    intro t
    apply sup_le
    · unfold rawPast
      refine iSup_le fun s => iSup_le fun hs => ?_
      have hc : Continuous (fun ω : Ω T d => B hT s ω) := by
        unfold B
        exact (continuous_eval_const (clamp T hT s)).comp continuous_subtype_val
      exact hc.borel_measurable.comap_le
    · unfold nullBorel
      exact MeasurableSpace.generateFrom_le (fun s hs => hs.1)

/-- The same augmented filtration indexed only by the paper's time interval. -/
noncomputable def 𝓕Interval {T : ℝ} (hT : 0 < T) {d : ℕ}
    (P0 : Measure (Ω T d)) : Filtration (Interval T) (borel (Ω T d)) where
  seq t := 𝓕 hT P0 t.1
  mono' := by
    intro s t hst
    exact (𝓕 hT P0).mono hst
  le' := by
    intro t
    exact (𝓕 hT P0).le t.1

/-- Stopped path ω_{t∧·}. -/
noncomputable def stopped {T : ℝ} (hT : 0 < T) {d : ℕ}
    (t : ℝ) (ω : Ω T d) : Ω T d := by
  let c : C(Interval T, State d) :=
    ⟨fun s => ω.1 (clamp T hT (min s.1 t)), by
      apply ω.1.continuous.comp
      apply continuous_projIcc.comp
      fun_prop⟩
  refine ⟨c, ?_⟩
  intro s hs
  simp [c, clamp, Set.projIcc, hs, ω.2]

/-- Path concatenation: the second path starts immediately after t. -/
noncomputable def concat {T : ℝ} (hT : 0 < T) {d : ℕ}
    (t : ℝ) (ω ω' : Ω T d) : Ω T d := by
  let tc : ℝ := (clamp T hT t).1
  let c : C(Interval T, State d) :=
    ⟨fun s => ω.1 (clamp T hT (min s.1 tc)) +
      ω'.1 (clamp T hT (max (s.1 - tc) 0)), by
      apply Continuous.add
      · apply ω.1.continuous.comp
        apply continuous_projIcc.comp
        fun_prop
      · apply ω'.1.continuous.comp
        apply continuous_projIcc.comp
        fun_prop⟩
  refine ⟨c, ?_⟩
  intro s hs
  simp [c, tc, clamp, Set.projIcc, hs, ω.2, ω'.2]

/-- The zero history in canonical path space. -/
def zeroPath (T : ℝ) (d : ℕ) : Ω T d :=
  ⟨0, by intro s hs; simp⟩

/-- The pseudometric used for continuity of the game data. -/
noncomputable def distD {T : ℝ} (hT : 0 < T) {d : ℕ}
    (t : ℝ) (ω : Ω T d) (t' : ℝ) (ω' : Ω T d) : ℝ :=
  Real.sqrt |t - t'| + dist (stopped hT t ω) (stopped hT t' ω')

/-- A modulus of continuity on nonnegative arguments. -/
def IsModulus (ρ : ℝ → ℝ) : Prop :=
  ρ 0 = 0 ∧ Monotone ρ ∧ Tendsto ρ (𝓝[>] (0 : ℝ)) (𝓝 0)

/-- An admissible action is one component of a profile. -/
structure ActionSpace (N : ℕ) where
  m : Fin N → ℕ
  A : (i : Fin N) → Set (State (m i))
  nonempty : ∀ i, (A i).Nonempty
  convex : ∀ i, Convex ℝ (A i)

abbrev Action {N : ℕ} (a : ActionSpace N) := (i : Fin N) → State (a.m i)

def IsAction {N : ℕ} (a : ActionSpace N) (x : Action a) : Prop := ∀ i, x i ∈ a.A i

abbrev ActionDomain {N : ℕ} (a : ActionSpace N) :=
  {x : Action a // IsAction a x}

abbrev OwnAction {N : ℕ} (a : ActionSpace N) (i : Fin N) :=
  {x : State (a.m i) // x ∈ a.A i}

/-- Euclidean distance in the product of the players' action spaces. -/
noncomputable def actionDist {N : ℕ} (a : ActionSpace N)
    (x y : Action a) : ℝ :=
  Real.sqrt (∑ i : Fin N, ‖x i - y i‖ ^ 2)

/-- Game coefficients and terminal costs, without regularity assumptions. -/
structure Game (T : ℝ) (hT : 0 < T) (d N : ℕ) where
  dimension_pos : 0 < d
  players_pos : 0 < N
  actions : ActionSpace N
  b : ℝ → Ω T d → Action actions → State d
  f : (i : Fin N) → ℝ → Ω T d → State (actions.m i) → ℝ
  ξ : Ω T d → Payoff N

/-- Assumption 3.1: bounded coefficients, progressive measurability, and
terminal payoff measurable at T. -/
def Assumption31 {T : ℝ} {hT : 0 < T} {d N : ℕ}
    (G : Game T hT d N) (P0 : Measure (Ω T d)) : Prop :=
  (∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ ω x, IsAction G.actions x →
    ‖G.b t ω x‖ ≤ C ∧ (∀ i, |G.f i t ω (x i)| ≤ C) ∧ ‖G.ξ ω‖ ≤ C) ∧
  (∀ t ∈ Set.Icc (0 : ℝ) T,
    Measurable[MeasurableSpace.prod (borel (Interval t))
      (MeasurableSpace.prod (𝓕 hT P0 t) (borel (ActionDomain G.actions)))]
      (fun p : Interval t × (Ω T d × ActionDomain G.actions) =>
        G.b p.1.1 p.2.1 p.2.2.1)) ∧
  (∀ i t, t ∈ Set.Icc (0 : ℝ) T →
    Measurable[MeasurableSpace.prod (borel (Interval t))
      (MeasurableSpace.prod (𝓕 hT P0 t) (borel (OwnAction G.actions i)))]
      (fun p : Interval t × (Ω T d × OwnAction G.actions i) =>
        G.f i p.1.1 p.2.1 p.2.2.1)) ∧
  Measurable[𝓕 hT P0 T] G.ξ

/-- Assumption 3.6(i), with one modulus for coefficients and terminal costs. -/
def Assumption36i {T : ℝ} {hT : 0 < T} {d N : ℕ}
    (G : Game T hT d N) : Prop :=
  ∃ ρ : ℝ → ℝ, IsModulus ρ ∧
    (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ t' ∈ Set.Icc (0 : ℝ) T,
      ∀ ω ω' x, IsAction G.actions x →
      ‖G.b t ω x - G.b t' ω' x‖ ≤ ρ (distD hT t ω t' ω') ∧
      ∀ i, |G.f i t ω (x i) - G.f i t' ω' (x i)| ≤ ρ (distD hT t ω t' ω')) ∧
    (∀ ω ω', ‖G.ξ ω - G.ξ ω'‖ ≤ ρ (dist ω ω'))

/-- Assumption 3.6(ii), uniform in time and the path. -/
def Assumption36ii {T : ℝ} {hT : 0 < T} {d N : ℕ}
    (G : Game T hT d N) : Prop :=
  ∃ ρ : ℝ → ℝ, IsModulus ρ ∧
    (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ ω x x',
      IsAction G.actions x → IsAction G.actions x' →
      ‖G.b t ω x - G.b t ω x'‖ ≤ ρ (actionDist G.actions x x')) ∧
    (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ ω, ∀ a ∈ G.actions.A i, ∀ a' ∈ G.actions.A i,
      |G.f i t ω a - G.f i t ω a'| ≤ ρ (dist a a'))

end DynSetValue.DPP


