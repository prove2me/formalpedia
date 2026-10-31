-- Prove2me | Definitions.Def_LeGallBrownianMap_bdgGH
-- name    : LeGallBrownianMap_bdgGH
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:41:29.991765+00:00
-- url     : https://prove2.me/theorems/ec8dde38-1d8d-4b47-aea1-10b6dd1fd7e9
-- title:
--   The rescaled vertex set $(m_n, c\,d_{gr})$ of the BDG map
-- statement:
--   For $\theta\in\mathbb T^p_n$ and $c>0$, the point of $\mathbb K$ given by the vertex set $m=\tau^\circ\cup\{\partial\}$ of the BDG map of $\theta$ with $c$ times its graph distance. With $c=\kappa_p n^{-1/4}$ and $\theta=\theta_n$ uniform, this is $(m_n,\kappa_p n^{-1/4}d_{gr})$ of Theorem 2.3.
--
--   **Formalization Note** The carrier is the finite subtype $\{\partial\}\cup\tau^\circ$ of `Option` words; distances are those of `bdgGraph`, which has no edges outside this set.
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, §2.5, p.16; Theorem 2.3, p.17

import Mathlib
import Definitions.Def_LeGallBrownianMap_bdgGraph
import Definitions.Def_LeGallBrownianMap_pseudoQuotientGH

open GromovHausdorff

namespace LeGallBrownianMap

/-- Le Gall, *Uniqueness and universality of the Brownian map*, arXiv:1105.4842v2, §2.5, p.16:
"Thanks to the BDG bijection, we have the identification m_n = τ°_n ∪ {∂}", and Theorem 2.3,
p.17: "the random compact metric spaces (m_n, κ_p n^{−1/4} d_gr)".

`bdgGH c θ` is the isometry class of the vertex set `τ° ∪ {∂}` of the map built from `θ`, with `c`
times its graph distance (the graph distance of `bdgGraph θ`).

**Formalization Note.** The carrier is the subtype `{none} ∪ some '' τ°` of `Option (List ℕ+)`
(`none` = `∂`). `bdgGraph θ` has no edge leaving this set, so distances computed in it are those of
the map. -/
noncomputable def bdgGH (c : ℝ) (θ : Finset (List ℕ+) × (List ℕ+ → ℤ)) : GHSpace :=
  pseudoQuotientGH
    ↥(insert (none : Option (List ℕ+)) (some '' {v | v ∈ θ.1 ∧ Even v.length}))
    (fun x y => c * ((bdgGraph θ).dist x.1 y.1 : ℝ))

end LeGallBrownianMap


