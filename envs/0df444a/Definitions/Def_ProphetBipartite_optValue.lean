-- Prove2me | Definitions.Def_ProphetBipartite_optValue
-- name    : ProphetBipartite_optValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:50:15.734404+00:00
-- url     : https://prove2.me/theorems/bb7fca8e-0d63-4d3b-81b6-09ac795613b2
-- title:
--   The prophet's value $\mathrm{opt}(v)$: the maximum value of a matching
-- statement:
--   For a profile of edge values $v=(v_e)_{e\in E}$ with $v_e\in\mathbb R_+$, $\mathrm{opt}(v)$ is the value of the maximum-weight (offline) matching of $G$ with edge values $v$:
--
--   $$
--   \mathrm{opt}(v)=\max\Big\{\sum_{e\in S}v_e\ :\ S\subseteq E \text{ a matching}\Big\}.
--   $$
--
--   This is the prophet's benchmark: a prophet who sees all values in advance selects an optimal matching.
--
--   **Formalization Note** Values are in $\mathbb R_{\ge0}$ and the maximum is a finite supremum over the nonempty set of matchings (the empty set is one), so it is attained.
-- source:
--   Gravin, Wang, Prophet inequality for bipartite matching: merits of being simple and non adaptive, arXiv:1902.06243v1, §2, p.4

import Mathlib
import Definitions.Def_ProphetBipartite_IsMatching

open scoped NNReal

namespace ProphetBipartite

/-- **The prophet's value `opt(v)`.** Gravin & Wang, arXiv:1902.06243v1, §2, p.4: "For a given
profile of values `v = {v_e}_{e∈E}`, we let `opt(v)` to denote the value of the maximal (offline)
matching in the graph `G` with edge values `v`."

`optValue left right v` is the maximum of `∑_{e∈S} v_e` over all matchings `S` of the multigraph.

**Formalization Note.** Values are in `ℝ≥0` (the paper's `ℝ₊`). The maximum is a `Finset.sup` in
`ℝ≥0` over the finite, nonempty set of matchings (the empty set is a matching), so it is attained
and equals the paper's maximum; the bottom element `0` of `ℝ≥0` is never a junk value here. -/
noncomputable def optValue {L R E : Type*} [Fintype E] [DecidableEq E]
    (left : E → L) (right : E → R) (v : E → ℝ≥0) : ℝ≥0 := by
  classical
  exact (Finset.univ.filter (fun S : Finset E => IsMatching left right S)).sup
    (fun S => ∑ e ∈ S, v e)

end ProphetBipartite


