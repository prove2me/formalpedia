-- Prove2me | Definitions.Def_ReentrantScheduling_FBFS_Supplement_MultipleLines
-- name    : ReentrantScheduling_FBFS_Supplement_MultipleLines
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T13:14:02.446022+00:00
-- url     : https://prove2.me/theorems/7b70f343-6b5e-4773-8fe9-5a94767ec131
-- title:
--   §VII — multiple published routes, combined capacity, arrivals (18), load (19) and delay stability
-- statement:
--   There are finitely many part types $p$ and centers $\sigma$, with $m_\sigma\ge1$ identical machines at each center. Every type follows a finite nonempty route of buffers, with processing time $\tau_{p,i}$ at stage $i$. Each route is an instance of the published single-line object, sharing the same centers and machine counts. One raw published run is supplied per type.
--
--   The work per machine brought by a type-$p$ part is
--
--   $$w_{p,\sigma}=\sum_{i:\,\sigma_{p,i}=\sigma}\frac{\tau_{p,i}}{m_\sigma}.$$
--
--   The arrival predicate is (18) separately for every type; the aggregate load predicate is $\sum_p\lambda_p w_{p,\sigma}<1$ at every center. Capacity and nonidling count the union of all types' in-service operations at a center. A buffer follows its own type's published head and line order, and every service choice respects a single global buffer rank. A run is stable when one finite $\Gamma\ge0$ bounds the delay of every part of every type, including initial parts.
--
--   This is a shared-resource extension of the existing Line and Run, rather than a separate replacement for either object. No delay or population bound is included in admissibility.
--
--   **Formalization Note** Types and stages are 0-based; a dependent pair identifies a buffer. Processing times inherit the published strictly positive pin, so zero processing times are excluded. Starts and exits may be $+\infty$, and all capacity counts use encard. Each route allows an arbitrary finite initial population with residual service at time zero. The empty family of types is also allowed and has vacuous stability.
-- source:
--   Lu & Kumar, Distributed Scheduling Based on Due Dates and Buffer Priorities, IEEE TAC 36(12), 1991, pp. 1413–1414, §VII, (18), work per machine, (19); p. 1408, §II; p. 1409, (4)

import Mathlib
import Definitions.Def_ReentrantScheduling_FBFS_Model

namespace ReentrantScheduling.FBFS.Supplement

/-- A finite family of routes sharing S centers and their machines (§VII, pp. 1413–1414).
Each route is converted to the published Line, with exactly the same common S and m.
Part types and route stages are 0-based. Positive service times are inherited from Line. -/
structure MultipleLines where
  P : ℕ
  S : ℕ
  m : Fin S → ℕ
  m_pos : ∀ σ, 0 < m σ
  l : Fin P → ℕ
  l_pos : ∀ p, 0 < l p
  center : (p : Fin P) → Fin (l p) → Fin S
  τ : (p : Fin P) → Fin (l p) → ℝ
  τ_pos : ∀ p i, 0 < τ p i

namespace MultipleLines

variable (N : MultipleLines)

/-- A route is an instance of the immutable published single-line object. -/
def line (p : Fin N.P) : Line where
  S := N.S
  m := N.m
  m_pos := N.m_pos
  l := N.l p
  l_pos := N.l_pos p
  center := N.center p
  τ := N.τ p
  τ_pos := N.τ_pos p

/-- All buffers, identified by their type and route stage. -/
abbrev Buffer := (p : Fin N.P) × Fin (N.l p)

/-- The work w_{p,σ} uses the published per-route work definition and the shared m_σ. -/
noncomputable def work (p : Fin N.P) (σ : Fin N.S) : ℝ := (N.line p).w σ

/-- Capacity condition (19): sum of all type loads at each center, strictly below one. -/
def BelowCapacity (lam : Fin N.P → ℝ) : Prop :=
  ∀ σ, (∑ p : Fin N.P, lam p * N.work p σ) < 1

end MultipleLines

/-- One raw published run for each type, before any shared-resource or dispatch constraints. -/
structure MultipleRun (N : MultipleLines) where
  route : (p : Fin N.P) → Run (N.line p)

namespace MultipleRun

variable {N : MultipleLines} (R : MultipleRun N)

/-- All in-service operations, tagged by type, using the same pool of machines. -/
def busySlots (σ : Fin N.S) (t : ℝ) :
    Set ((p : Fin N.P) × ((R.route p).Part × Fin (N.l p))) :=
  {a | N.center a.1 a.2.2 = σ ∧ (R.route a.1).InService a.2.1 a.2.2 t}

/-- Multitype arrivals (18), with the immutable per-route counting convention. -/
def Arrivals (lam γ : Fin N.P → ℝ) : Prop :=
  ∀ p, (R.route p).Arrivals (lam p) (γ p)

/-- Every type's parts, including initial parts, have one finite uniform delay bound (4).
The bound can depend on this run and its initial condition. -/
def Stable : Prop :=
  ∃ Γ : ℝ, 0 ≤ Γ ∧ ∀ p (a : (R.route p).Part),
    (R.route p).exit a ≤ (((R.route p).α a + Γ : ℝ) : WithTop ℝ)

/-- Nonidling nonpreemptive FIFO buffer-priority dispatch with shared capacity.
A smaller global rank means higher priority. Capacity and nonidling count the union of types,
not separate copies of the machine pool. No stability estimate is part of admissibility. -/
structure Admissible (rank : N.Buffer → ℕ) : Prop where
  precedence : ∀ p (a : (R.route p).Part) i, (R.route p).entry a ≤ i →
    ((R.route p).arrive a i ≤ (R.route p).start a i ∨
      ((R.route p).initial a ∧ i = (R.route p).entry a ∧
        ((-(N.τ p i) : ℝ) : WithTop ℝ) < (R.route p).start a i ∧
        (R.route p).start a i ≤ ((0 : ℝ) : WithTop ℝ)))
  capacity : ∀ σ (t : ℝ), 0 ≤ t → (R.busySlots σ t).encard ≤ N.m σ
  nonidling : ∀ σ (t : ℝ), 0 ≤ t →
    (∃ p, ∃ a : (R.route p).Part, ∃ i, N.center p i = σ ∧ (R.route p).Waiting a i t) →
    (R.busySlots σ t).encard = N.m σ
  head : ∀ p (a : (R.route p).Part) i (t : ℝ), 0 ≤ t →
    (R.route p).entry a ≤ i → (R.route p).start a i = (t : WithTop ℝ) →
    ∀ b, (R.route p).ord b < (R.route p).ord a → ¬ (R.route p).Waiting b i t
  ord_initial : ∀ p (a b : (R.route p).Part), (R.route p).initial a →
    ¬ (R.route p).initial b → (R.route p).ord a < (R.route p).ord b
  ord_deeper : ∀ p (a b : (R.route p).Part), (R.route p).initial a →
    (R.route p).initial b → (R.route p).entry b < (R.route p).entry a →
    (R.route p).ord a < (R.route p).ord b
  ord_release : ∀ p (a b : (R.route p).Part), ¬ (R.route p).initial a →
    ¬ (R.route p).initial b → (R.route p).α a < (R.route p).α b →
    (R.route p).ord a < (R.route p).ord b
  priority : ∀ p (a : (R.route p).Part) i (t : ℝ), 0 ≤ t →
    (R.route p).entry a ≤ i → (R.route p).start a i = (t : WithTop ℝ) →
    ∀ q (b : (R.route q).Part) j, N.center q j = N.center p i →
      rank ⟨q, j⟩ < rank ⟨p, i⟩ → ¬ (R.route q).Waiting b j t

end MultipleRun

end ReentrantScheduling.FBFS.Supplement


