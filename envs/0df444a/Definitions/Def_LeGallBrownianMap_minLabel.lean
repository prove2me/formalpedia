-- Prove2me | Definitions.Def_LeGallBrownianMap_minLabel
-- name    : LeGallBrownianMap_minLabel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:36:13.071105+00:00
-- url     : https://prove2.me/theorems/77b53f91-ff7b-4b2f-9521-e1c2f5731381
-- title:
--   The minimal label $\min\{\ell_v : v\in\tau^\circ\}$
-- statement:
--   For a labeled $p$-tree $\theta=(\tau,\ell)$, the minimal label over white vertices, $\min\{\ell_v: v\in\tau^\circ\}$. It is the label of the vertices adjacent to the distinguished vertex $\partial$ in the BDG construction, and $\ell_v-\min\ell+1$ is the distance from $\partial$ to $v$.
--
--   **Formalization Note** Written as the infimum (in $\mathbb Z$) of the finite nonempty set of white labels.
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, §2.2, pp.10–12

import Mathlib

namespace LeGallBrownianMap

/-- Le Gall, *Uniqueness and universality of the Brownian map*, arXiv:1105.4842v2, §2.2,
pp.10–12: the minimal label `min{ℓ_v : v ∈ τ°}` of a labeled p-tree `θ = (τ, ℓ)`, used in the
BDG construction and in eq. (3).

**Formalization Note.** Written `sInf` over the (finite, nonempty: it contains `∅`) set of
labels of white vertices, which in `ℤ` is its minimum. -/
noncomputable def minLabel (θ : Finset (List ℕ+) × (List ℕ+ → ℤ)) : ℤ :=
  sInf (θ.2 '' {v | v ∈ θ.1 ∧ Even v.length})

end LeGallBrownianMap


