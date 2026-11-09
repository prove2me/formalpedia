-- Prove2me | Definitions.Def_UniversalNonstochastic_Main_UniversalMeasure
-- name    : UniversalNonstochastic_Main_UniversalMeasure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:00:29.596786+00:00
-- url     : https://prove2.me/theorems/619e06eb-905d-497e-9245-bc710373caf3
-- title:
--   Universal semimeasure $\mathbf m$, the universal measure $\mathbf m(A)$ and its tail $\tau$
-- statement:
--   Let $\mathbb N=\{1,2,\dots\}$. A **semimeasure** on $\mathbb N$ is a function $\nu:\mathbb N\to[0,\infty)$ with $\sum_{n}\nu(n)\le1$ (every finite partial sum is at most $1$). A **universal semimeasure** $\mathbf m$ is a lower semicomputable semimeasure that multiplicatively dominates every lower semicomputable semimeasure: for each such $\nu$ there is $a_\nu>0$ with
--   $$a_\nu\,\nu(n)\le\mathbf m(n)\qquad\text{for all }n\in\mathbb N.$$
--   Its total mass need not equal $1$.
--
--   For an arbitrary subset $A\subseteq\mathbb N$ (not necessarily decidable) the **universal measure** of $A$ is $\mathbf m(A)=\sum_{n\in A}\mathbf m(n)$; this is a finite measure on all subsets of $\mathbb N$. The **tail** of $\mathbf m$ is
--   $$\tau(t)=\mathbf m(\{n\in\mathbb N : n>t\}),\qquad t\ge0 .$$
--
--   Universal semimeasures exist (Levin; see [16, Sect. 4.2], the reference the source cites for $\mathbf m$). Every result of the mission is stated for an arbitrary universal semimeasure, which the paper fixes once.
--
--   **Formalization Note** The weights are real numbers, nonnegative with partial sums at most $1$, so the series defining $\mathbf m(A)$ converges and Lean's sum is the true sum. The tail is defined for every real $t$; only $t\ge0$ is used. The extended tail explicitly sets $\tau(\infty)=0$. The function `massOn` transports the measure to any object space with a fixed computable bijection to the positive integers; no measurability restriction is needed on a discrete space.
-- source:
--   Vladimir Vovk, The universal measure of nonstochastic objects, STOC 2027 submission #11 (October 2026), SHA-256 1ca25c4b7c38d8f49718c9fecbc2a434a7592886b44992c4fbef31ab3f480078, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/11.pdf, Sect. 1 p.4 (m a fixed universal semimeasure on ℕ, m(A) := Σ_{a∈A} m(a)), Sect. 2 p.5 (τ(t) := m({n ∈ ℕ | n > t}))

import Mathlib
import Definitions.Def_UniversalNonstochastic_Main_Effective

open scoped ENNReal

namespace UniversalNonstochastic.Main

/-- A (discrete) semimeasure on the positive integers `ℕ = {1, 2, …}`: nonnegative weights
whose total sum is at most `1` (every finite partial sum is at most `1`). -/
def IsSemimeasure (ν : ℕ+ → ℝ) : Prop :=
  (∀ n, 0 ≤ ν n) ∧ ∀ s : Finset ℕ+, ∑ n ∈ s, ν n ≤ 1

/-- A universal semimeasure on `ℕ = {1, 2, …}`: a lower semicomputable semimeasure `w`
that multiplicatively dominates every lower semicomputable semimeasure `ν`
(there is `a_ν > 0` with `a_ν ν(n) ≤ w(n)` for all `n`). Total mass `1` is not required. -/
structure UniversalSemimeasure where
  w : ℕ+ → ℝ
  isSemimeasure : IsSemimeasure w
  lowerSemicomputable : IsLowerSemicomputable w
  universal : ∀ ν : ℕ+ → ℝ, IsSemimeasure ν → IsLowerSemicomputable ν →
    ∃ a : ℝ, 0 < a ∧ ∀ n, a * ν n ≤ w n

/-- The universal measure of an arbitrary set `A ⊆ ℕ`: `m(A) = ∑_{n ∈ A} m(n)`.
The family is nonnegative with partial sums at most `1`, so the sum converges. -/
noncomputable def mass (m : UniversalSemimeasure) (A : Set ℕ+) : ℝ :=
  ∑' n : ℕ+, A.indicator m.w n

/-- The tail of the universal measure, `τ(t) = m({n ∈ ℕ | n > t})`, for real `t`
(the source uses `t ≥ 0`). -/
noncomputable def tail (m : UniversalSemimeasure) (t : ℝ) : ℝ :=
  mass m {n : ℕ+ | t < ((n : ℕ) : ℝ)}

/-- The source's convention `τ(∞) = 0`, together with its finite nonnegative tail. -/
noncomputable def tailExtended (m : UniversalSemimeasure) (t : ℝ≥0∞) : ℝ :=
  if t = ⊤ then 0 else tail m t.toReal

/-- Universal mass on another computably encoded object space, exactly as in S, p.5. -/
noncomputable def massOn {X : Type*} [Primcodable X] (e : ObjectEncoding X)
    (m : UniversalSemimeasure) (A : Set X) : ℝ := mass m (e.transportSet A)

end UniversalNonstochastic.Main


