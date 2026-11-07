-- Prove2me | Definitions.Def_ShadowBootstrap_select
-- name    : ShadowBootstrap_select
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:22:16.859194+00:00
-- url     : https://prove2.me/theorems/24cc36fd-f793-4aeb-878f-f2489c359c20
-- title:
--   Selection by pairwise distances (Lemma 7.2)
-- statement:
--   Given $R+1$ outputs $X_0, \dots, X_R$ of an estimator in a (pseudo)metric space and a radius $r$, the **selection rule** returns the first $X_i$ such that more than half of all outputs (itself included) lie within distance $2r$ of $X_i$, and $X_0$ if there is no such output.
--
--   This is the rule "selecting one output using pairwise distances" of the confidence amplification Lemma 7.2 ([HKOT23, Proposition 2.4]).
--
--   **Formalization Note** The rule uses only pairwise distances and $r$.
-- source:
--   Cho, Kim, Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow Clifford measurements, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…), Lemma 7.2, p.28

import Mathlib

namespace ShadowBootstrap

open Classical in
/-- Cho, Kim, *Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow
Clifford measurements*, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…),
Lemma 7.2, p.28 ([HKOT23, Proposition 2.4]): "selecting one output using pairwise distances".
Among the `R + 1` outputs `X_0, …, X_R`, return the first `X_i` such that more than half of all
outputs (itself included) lie within distance `2r` of it, and `X_0` if there is none.

**Formalization Note** Only pairwise distances and the radius `r` are used. The space is a
pseudometric space: the trace distance between pure states, applied to unit vectors, ignores a
global phase. -/
noncomputable def select {X : Type} [PseudoMetricSpace X] {R : ℕ} (r : ℝ) (v : Fin (R + 1) → X) :
    X :=
  match (List.finRange (R + 1)).find? (fun i =>
      decide (R + 1 < 2 * (Finset.univ.filter fun j => dist (v i) (v j) ≤ 2 * r).card)) with
  | some i => v i
  | none => v 0

end ShadowBootstrap


