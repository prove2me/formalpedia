-- Prove2me | Definitions.Def_ProphetBipartite_IsOptSelector
-- name    : ProphetBipartite_IsOptSelector
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:50:58.903537+00:00
-- url     : https://prove2.me/theorems/8ec9eca3-1698-4f54-b70e-9982a6b7a109
-- title:
--   Measurable optimal matching selectors
-- statement:
--   The analysis compares the policy with "the optimal matching selected by the prophet", a random optimal matching $\mathrm{opt}(\hat v)$ of a value profile $\hat v$. A **selector** $\mathrm{opt}$ assigns to every value profile $v$ a set of edges $\mathrm{opt}(v)$; it is an **optimal matching selector** when
--
--   1. $\mathrm{opt}(v)$ is a matching and $\sum_{e\in\mathrm{opt}(v)}v_e=\mathrm{opt}(v)$ (the maximum value) for every $v$, and
--   2. every level set $\{v:\mathrm{opt}(v)=S\}$ is measurable.
--
--   Condition 2 makes $\Pr_v[(i,j)\in\mathrm{opt}(v)]$ and $\mathbb E_v[\chi^{(i,j)}_{\mathrm{opt}}(v)]$ well defined.
--
--   **Formalization Note** The paper does not specify how ties between optimal matchings are broken; the milestones are stated for every selector of this kind.
-- source:
--   Gravin, Wang, Prophet inequality for bipartite matching: merits of being simple and non adaptive, arXiv:1902.06243v1, §3.1, p.6 (opt(v̂), (4))

import Mathlib
import Definitions.Def_ProphetBipartite_IsMatching
import Definitions.Def_ProphetBipartite_optValue

open scoped NNReal

namespace ProphetBipartite

/-- **A (measurable) optimal matching `opt(v)`.** Gravin & Wang, arXiv:1902.06243v1, §3.1, p.6:
the analysis uses "the optimal matching selected by the prophet", a random optimal matching
`opt(v̂)` of the value profile. `opt` is a selector: for every profile `v`, `opt v` is a matching
whose value `∑_{e ∈ opt v} v_e` equals `opt(v)`, and every level set `{v | opt v = S}` is
measurable, so that `Pr[(i, j) ∈ opt(v)]` and `E[χ^{(i,j)}_opt(v)]` of (4) and (10) are defined.

**Formalization Note.** The paper does not fix how ties between optimal matchings are broken. Every
milestone that mentions `opt` is stated for every selector with this property. One exists for every
finite multigraph (the first maximizer in a fixed enumeration of the matchings). -/
def IsOptSelector {L R E : Type*} [Fintype E] [DecidableEq E]
    (left : E → L) (right : E → R) (opt : (E → ℝ≥0) → Finset E) : Prop :=
  (∀ v, IsMatching left right (opt v) ∧ ∑ e ∈ opt v, v e = optValue left right v) ∧
    ∀ S : Finset E, MeasurableSet {v : E → ℝ≥0 | opt v = S}

end ProphetBipartite


