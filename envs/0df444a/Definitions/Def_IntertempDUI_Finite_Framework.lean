-- Prove2me | Definitions.Def_IntertempDUI_Finite_Framework
-- name    : IntertempDUI_Finite_Framework
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:48:36.311313+00:00
-- url     : https://prove2.me/theorems/fb60eb16-6141-48d9-86d6-38f590887d93
-- title:
--   §2 — finite time, spans, and preference structure
-- statement:
--   Let $T>0$ and $\mathcal T=[0,T]$. A time interval $\lfloor r,s\rceil$ contains an endpoint precisely when that endpoint is $0$ or $T$. A time span is a finite disjoint union of such intervals with distinct endpoints; the empty span is included. Interior, closure and connected components are relative to $\mathcal T$. A feasible trajectory is a continuous map $\mathcal T\to\mathcal X$.
--
--   $$\neg\mathcal S=\operatorname{int}(\mathcal S^{\mathrm c}),\qquad \mathcal Q\vee\mathcal R=\operatorname{int}\operatorname{cl}(\mathcal Q\cup\mathcal R).$$
--
--   The primitive preference orders compare restrictions of feasible trajectories to intervals. The induced order on a span compares full feasible representatives that agree on that span and are indifferent on every component of its complement. This framework is shared by every result of the mission.
--
--   **Formalization Note** Restricted trajectories are represented by their feasible full extensions, and the induced comparison is existential.
-- source:
--   Pivato, Intertemporal choice with continuity constraints, SSRN 3232014 (August 10, 2018), pp. 4–7, §2; https://ssrn.com/abstract=3232014

import Mathlib

namespace IntertempDUI.Finite

/-- The relative time domain [0,T]. -/
abbrev Time (T : ℝ) := Set.Icc (0 : ℝ) T

/-- Feasible continuous trajectories are drawn from this type. -/
abbrev Traj (T : ℝ) (X : Type*) [TopologicalSpace X] := C(Time T, X)

/-- The relative interval ⌊r,s⌉: an endpoint belongs exactly when it is an endpoint of time. -/
def bracket (T r s : ℝ) : Set (Time T) :=
  {t | (r < t.1 ∨ (r = 0 ∧ t.1 = 0)) ∧ (t.1 < s ∨ (s = T ∧ t.1 = T))}

def IsTimeInterval {T : ℝ} (I : Set (Time T)) : Prop :=
  ∃ r s : ℝ, 0 ≤ r ∧ r < s ∧ s ≤ T ∧ I = bracket T r s

/-- Formula (4), including the empty span when N=0. -/
def IsTimeSpan {T : ℝ} (S : Set (Time T)) : Prop :=
  ∃ (N : ℕ) (s t : Fin N → ℝ),
    (∀ i, 0 ≤ s i ∧ s i < t i ∧ t i ≤ T) ∧
    (∀ i j : Fin N, i < j → t i < s j) ∧
    S = ⋃ i, bracket T (s i) (t i)

def neg {T : ℝ} (S : Set (Time T)) : Set (Time T) := interior Sᶜ
def join {T : ℝ} (S R : Set (Time T)) : Set (Time T) := interior (closure (S ∪ R))
def IsComponent {T : ℝ} (S I : Set (Time T)) : Prop :=
  ∃ t ∈ S, I = connectedComponentIn S t

/-- Adjacent intervals are presented by their three endpoints. -/
def AreAdjacent {T : ℝ} (I J H : Set (Time T)) : Prop :=
  ∃ r s t : ℝ, 0 ≤ r ∧ r < s ∧ s < t ∧ t ≤ T ∧
    ((I = bracket T r s ∧ J = bracket T s t) ∨
     (J = bracket T r s ∧ I = bracket T s t)) ∧ H = bracket T r t

abbrev Pref (T : ℝ) (X : Type*) [TopologicalSpace X] :=
  Set (Time T) → Traj T X → Traj T X → Prop

def indiff {T : ℝ} {X : Type*} [TopologicalSpace X] (pref : Pref T X)
    (S : Set (Time T)) (a b : Traj T X) : Prop := pref S a b ∧ pref S b a

def strict {T : ℝ} {X : Type*} [TopologicalSpace X] (pref : Pref T X)
    (S : Set (Time T)) (a b : Traj T X) : Prop := pref S a b ∧ ¬ pref S b a

/-- §3's standing completeness, transitivity and nontriviality, with the order on restrictions. -/
def Standing {T : ℝ} {X : Type*} [TopologicalSpace X]
    (A : Set (Traj T X)) (pref : Pref T X) : Prop :=
  ∀ I, IsTimeInterval I →
    (∀ a ∈ A, ∀ b ∈ A, pref I a b ∨ pref I b a) ∧
    (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, pref I a b → pref I b c → pref I a c) ∧
    (∃ a ∈ A, ∃ b ∈ A, strict pref I a b) ∧
    (∀ a ∈ A, ∀ b ∈ A, ∀ a' ∈ A, ∀ b' ∈ A,
       Set.EqOn a a' I → Set.EqOn b b' I → (pref I a b ↔ pref I a' b'))

/-- Equation (6), the preference between constant trajectories. -/
def sy {T : ℝ} {X : Type*} [TopologicalSpace X] (pref : Pref T X) (x y : X) : Prop :=
  pref Set.univ (ContinuousMap.const (Time T) x) (ContinuousMap.const (Time T) y)

/-- The intermittent order constructed from whole-trajectory comparisons, as in Lemma A4. -/
def induced {T : ℝ} {X : Type*} [TopologicalSpace X]
    (A : Set (Traj T X)) (pref : Pref T X) (S : Set (Time T))
    (a b : Traj T X) : Prop :=
  ∃ a' ∈ A, ∃ b' ∈ A, Set.EqOn a' a S ∧ Set.EqOn b' b S ∧
    (∀ I, IsComponent (neg S) I → indiff pref I a' b') ∧ pref Set.univ a' b'

def inducedIndiff {T : ℝ} {X : Type*} [TopologicalSpace X]
    (A : Set (Traj T X)) (pref : Pref T X) (S : Set (Time T))
    (a b : Traj T X) : Prop := induced A pref S a b ∧ induced A pref S b a

def inducedStrict {T : ℝ} {X : Type*} [TopologicalSpace X]
    (A : Set (Traj T X)) (pref : Pref T X) (S : Set (Time T))
    (a b : Traj T X) : Prop := induced A pref S a b ∧ ¬ induced A pref S b a

end IntertempDUI.Finite


