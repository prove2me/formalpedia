-- Prove2me | Definitions.Def_BorelRobustMDP_DecisionModel
-- name    : BorelRobustMDP_DecisionModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:10:16.395949+00:00
-- url     : https://prove2.me/theorems/5da8a995-5b0d-470e-9550-61ddb29b5826
-- title:
--   The finite-horizon decision model $(E,A,D_n,Z,T_n,c_n,c_N)$
-- statement:
--   The decision part of the model: for each stage $n=0,\dots,N-1$, a measurable set $D_n\subseteq E\times A$ of admissible state-action pairs which contains the graph of a measurable map $E\to A$, so that each section $D_n(x)=\{a:(x,a)\in D_n\}$ is non-empty; a measurable transition function $T_n$ giving the next state $x_{n+1}=T_n(x_n,a_n,z_{n+1})$; a one-stage cost $c_n(x,a,x')$; and a terminal cost $c_N(x)$.
--
--   Every other object of the mission is built on this data.
--
--   **Formalization Note.** $T_n$ and $c_n$ are total measurable functions; the paper's functions on $D_n\times Z$ and $D_n\times E$ extend because $D_n$ is measurable, and only their values on $D_n$ matter. Measurability of the costs is the field's standing convention. $E$ and $A$ share a universe because the platform's history space does.
-- source:
--   Bäuerle & Glauner, arXiv:2007.13103v1, §2, p.3

import Mathlib

open MeasureTheory

namespace BorelRobustMDP

universe u v

/-- The finite-horizon decision model of Bäuerle & Glauner, arXiv:2007.13103v1, §2, p.3: admissible
pairs `D_n ⊆ E × A`, measurable and containing the graph of a measurable map `E → A`; measurable
transition functions `T_n(x, a, z)`; one-stage costs `c_n(x, a, x′)`; terminal cost `c_N`.

**Formalization Note.** The time index is `ℕ`, and only `n < N` is meaningful. `T n` and `c n` are
total measurable functions on `(E × A) × Z` and `(E × A) × E`. The paper's are defined on `D_n × Z`
and `D_n × E`; since `D_n` is measurable, each extends (constant off `D_n`), and only values on `D_n`
enter any statement. The measurability of `c n`, `c_N` is the field's convention (the paper's
semicontinuity assumption gives it on `D_n × E`). `E` and `A` share a universe because the
platform's `Hist E A n` does. -/
structure DecisionModel (E A : Type u) (Z : Type v) [MeasurableSpace E] [MeasurableSpace A]
    [MeasurableSpace Z] (N : ℕ) where
  /-- The admissible state-action pairs `D_n` at time `n`. -/
  D : ℕ → Set (E × A)
  measurableSet_D : ∀ n < N, MeasurableSet (D n)
  /-- `D_n` contains the graph of a measurable mapping `E → A`. -/
  exists_graph : ∀ n < N, ∃ f : E → A, Measurable f ∧ ∀ x, (x, f x) ∈ D n
  /-- The transition function: `T n (x, a) z` is `T_n(x, a, z)`. -/
  T : ℕ → E × A → Z → E
  measurable_T : ∀ n < N, Measurable fun w : (E × A) × Z => T n w.1 w.2
  /-- The one-stage cost: `c n (x, a) x'` is `c_n(x, a, x′)`. -/
  c : ℕ → E × A → E → ℝ
  measurable_c : ∀ n < N, Measurable fun w : (E × A) × E => c n w.1 w.2
  /-- The terminal cost `c_N`. -/
  cN : E → ℝ
  measurable_cN : Measurable cN

namespace DecisionModel

variable {E A : Type u} {Z : Type v} [MeasurableSpace E] [MeasurableSpace A] [MeasurableSpace Z]
  {N : ℕ}

/-- The `x`-section `D_n(x) = {a ∈ A : (x, a) ∈ D_n}`, the admissible actions in state `x` at time
`n` (Bäuerle & Glauner, arXiv:2007.13103v1, p.3). -/
def sec (M : DecisionModel E A Z N) (n : ℕ) (x : E) : Set A :=
  {a | (x, a) ∈ M.D n}

end DecisionModel

end BorelRobustMDP


