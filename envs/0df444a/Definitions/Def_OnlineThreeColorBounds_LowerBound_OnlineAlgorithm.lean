-- Prove2me | Definitions.Def_OnlineThreeColorBounds_LowerBound_OnlineAlgorithm
-- name    : OnlineThreeColorBounds_LowerBound_OnlineAlgorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:42:45.995437+00:00
-- url     : https://prove2.me/theorems/466e967d-6760-4da5-866a-abf05f770bd2
-- title:
--   Deterministic online rules, public horizons, and graph runs
-- statement:
--   A deterministic online rule receives the chronological revealed history $h$ and the earlier-neighbor set $S$ of the next vertex, and returns a finite color set $A(h,S)$. An algorithm with public horizon is a family $A_n$ of such rules, indexed by the known vertex count $n$. No computation or memory bound is imposed.
--
--   The run on an ordered graph feeds its earlier-neighbor sets to the rule in arrival order:
--   $$
--   h_0=\varnothing,\qquad h_{i+1}=h_i\mathbin{\|}(S_i,A_n(h_i,S_i)).
--   $$
--   Properness at horizon $n$ means that the resulting history is a legal exact-$t$-fold coloring for every $k$-colorable graph on exactly $n$ vertices. Properness across all sizes is used for the local construction lemmas. The offline coloring witness is never supplied to the rule, and there is no requirement on counterfactual histories the rule never reaches.
--
--   This interface includes stateful and computationally unbounded deterministic algorithms, and supports the exact-size, known-horizon lower bound.
--
--   Differences from the source:
--   - encoding: immediate irrevocable decisions from revealed information, optionally knowing n → a function of past neighbor/color records and the new earlier neighbors, with a separate public horizon argument; reason: the complete past represents any deterministic internal state, with no future adjacency or offline certificate supplied
-- source:
--   Yaqiao Li, New bounds for online coloring three-colorable graphs, STOC 2027 submission #425 (October 2026), pinned submission PDF SHA256 ca491d3191fa544c55ed3f45022e4cb14e5570bbd8b8bfb36e98205a8a5c518a, §1 and Remark 1.3(1), printed p. 1 / PDF p. 2; §2, printed p. 5 / PDF p. 6

import Definitions.Def_OnlineThreeColorBounds_LowerBound_History
set_option autoImplicit false

namespace OnlineThreeColorBounds.LowerBound

/-- A deterministic response sees only past records and the new vertex's earlier neighbors. -/
abbrev OnlineRule := History → Finset ℕ → Finset ℕ

/-- The public horizon is separate from the revealed history. -/
abbrev OnlineAlgorithm := ℕ → OnlineRule

/-- Feed the next neighbor sets in arrival order, retaining every irrevocable output. -/
def feed (A : OnlineRule) : History → List (Finset ℕ) → History
  | h, [] => h
  | h, s :: ss => feed A (h ++ [(s, A h s)]) ss

noncomputable def earlierNeighbors {n : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n) : Finset ℕ := by
  classical
  exact (Finset.univ.filter (fun w : Fin n => w.val < v.val ∧ G.Adj w v)).image Fin.val

noncomputable def run {n : ℕ} (A : OnlineRule) (G : SimpleGraph (Fin n)) : History :=
  feed A [] (List.ofFn (earlierNeighbors G))

/-- Properness is required only on promised inputs of this exact public size.
There is no condition on counterfactual histories that A never reaches. -/
def ProperAt (t k n : ℕ) (A : OnlineRule) : Prop :=
  ∀ G : SimpleGraph (Fin n), G.Colorable k → LegalHistory t (run A G)

/-- A local construction may face any proper rule, with arbitrary fixed advice/state. -/
def ProperOn (t k : ℕ) (A : OnlineRule) : Prop :=
  ∀ n : ℕ, ProperAt t k n A

end OnlineThreeColorBounds.LowerBound


