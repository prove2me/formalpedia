-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P47
-- name    : QAlgorithms_Papers_Independent_Support50_P47
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-23T23:59:31.33768+00:00
-- url     : https://prove2.me/theorems/433f81c0-72f5-44b2-bf35-5474bd277b19
-- title:
--   Definitions for Capacities of repeater-assisted quantum communications
-- statement:
--   The objects the formalized statements of *Capacities of repeater-assisted quantum communications* (arXiv:1601.00966) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `WeightedNetwork`: PDF pp.16,23–24: an undirected weighted network with individually labelled edges. Endpoint ordering is only a representation; routes may traverse either way. Distinct labels may have the same endpoints, retaining parallel edges. Finiteness and connectedness are imposed in the proposition, not by this data.
--   - `Route`: PDF pp.16,23–24: a nonempty simple route, including its actual edge labels. Injectivity forbids repeated vertices. The first and last vertices are fixed; there is no independently supplied collection that could omit legal routes.
--   - `IsConnected`: PDF pp.23–24: every pair of distinct vertices has a simple route. On a singleton graph this is vacuous, but the proposition requires a ≠ b.
--   - `routeWeight`: PDF pp.23–24, Eq.(131): minimum of the weights of the actual route edges. The finite range is nonempty by Route.positive, so real sInf is a genuine minimum.
--   - `cutWeight`: PDF pp.20,23–24, Eqs.(107),(131): maximum weight over labelled edges crossing A and its complement, counted once regardless of endpoint ordering. For finite connected networks and an endpoint-separating A this set is finite and nonempty. Outside that domain real sSup assigns 0 to the empty cut.
-- source:
--   Capacities of repeater-assisted quantum communications, arXiv:1601.00966v4, https://arxiv.org/abs/1601.00966v4

import Mathlib

/-! Pirandola, arXiv:1601.00966v4. Only the standalone graph proposition is
stated here. Operational and source-ambiguity deferrals are individually recorded
in the unit's HARD.md and GAPS.json. Compilation is pending batch handoff. -/

namespace QAlgorithms.Papers.Independent.Support50.P47

noncomputable section

universe u v

/-- PDF pp.16,23–24: an undirected weighted network with individually labelled
edges. Endpoint ordering is only a representation; routes may traverse either
way. Distinct labels may have the same endpoints, retaining parallel edges.
Finiteness and connectedness are imposed in the proposition, not by this data. -/
structure WeightedNetwork (V : Type u) (E : Type v) where
  left : E → V
  right : E → V
  separated : ∀ e, left e ≠ right e
  weight : E → ℝ

/-- PDF pp.16,23–24: a nonempty simple route, including its actual edge labels.
Injectivity forbids repeated vertices. The first and last vertices are fixed;
there is no independently supplied collection that could omit legal routes. -/
structure Route {V : Type u} {E : Type v} (G : WeightedNetwork V E) (a b : V) where
  length : ℕ
  positive : 0 < length
  vertex : Fin (length + 1) → V
  edge : Fin length → E
  start : vertex ⟨0, Nat.zero_lt_succ length⟩ = a
  finish : vertex (Fin.last length) = b
  simple : Function.Injective vertex
  follows : ∀ i : Fin length,
    (G.left (edge i) = vertex i.castSucc ∧ G.right (edge i) = vertex i.succ) ∨
    (G.right (edge i) = vertex i.castSucc ∧ G.left (edge i) = vertex i.succ)

/-- PDF pp.23–24: every pair of distinct vertices has a simple route.
On a singleton graph this is vacuous, but the proposition requires a ≠ b. -/
def IsConnected {V : Type u} {E : Type v} (G : WeightedNetwork V E) : Prop :=
  ∀ a b : V, a ≠ b → Nonempty (Route G a b)

/-- PDF pp.23–24, Eq.(131): minimum of the weights of the actual route edges.
The finite range is nonempty by Route.positive, so real sInf is a genuine minimum. -/
def routeWeight {V : Type u} {E : Type v} (G : WeightedNetwork V E)
    {a b : V} (p : Route G a b) : ℝ :=
  sInf (Set.range (fun i : Fin p.length => G.weight (p.edge i)))

/-- PDF pp.20,23–24, Eqs.(107),(131): maximum weight over labelled edges
crossing A and its complement, counted once regardless of endpoint ordering.
For finite connected networks and an endpoint-separating A this set is finite
and nonempty. Outside that domain real sSup assigns 0 to the empty cut. -/
def cutWeight {V : Type u} {E : Type v} (G : WeightedNetwork V E) (A : Set V) : ℝ :=
  sSup {w : ℝ | ∃ e : E,
    ((G.left e ∈ A ∧ G.right e ∉ A) ∨ (G.right e ∈ A ∧ G.left e ∉ A)) ∧
    w = G.weight e}

/-- A constant-weight nonempty route has that weight, even when it is negative. -/
example {V : Type u} {E : Type v} (G : WeightedNetwork V E)
    {a b : V} (p : Route G a b) (w : ℝ) (hw : ∀ e, G.weight e = w) :
    routeWeight G p = w := by
  letI : Nonempty (Fin p.length) := ⟨⟨0, p.positive⟩⟩
  simp [routeWeight, hw]

/-- The empty crossing set has the documented off-domain value 0. -/
example {V : Type u} {E : Type v} (G : WeightedNetwork V E) :
    cutWeight G Set.univ = 0 := by
  simp [cutWeight]

end

end QAlgorithms.Papers.Independent.Support50.P47


