-- Prove2me | Definitions.Def_LeGallBrownianMap_uniformTreeExpectation
-- name    : LeGallBrownianMap_uniformTreeExpectation
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:38:58.929192+00:00
-- url     : https://prove2.me/theorems/621ba487-cc1b-41bc-9a27-92f0feb4c2a5
-- title:
--   Expectation under the uniform law on $\mathbb T^p_n$
-- statement:
--   For $g$ a real function of labeled $p$-trees and $\theta_n$ uniform on $\mathbb T^p_n$, $\mathbb E[g(\theta_n)]=\frac{1}{\#\mathbb T^p_n}\sum_{\theta\in\mathbb T^p_n}g(\theta)$. A uniform rooted pointed $2p$-angulation with $n$ faces is the BDG image of $\theta_n$ and a uniform independent bit, so all its laws used in the mission are of this form.
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, §2.5, p.15

import Mathlib
import Definitions.Def_LeGallBrownianMap_labeledPTrees

namespace LeGallBrownianMap

/-- Le Gall, *Uniqueness and universality of the Brownian map*, arXiv:1105.4842v2, §2.5, p.15:
"Clearly, θ_n is uniformly distributed over the set T^p_n".

`uniformTreeExpectation p n g = E[g(θ_n)]` for `θ_n` uniform on `T^p_n`: the average of `g` over
the finite set `labeledPTrees p n`.

**Formalization Note.** `Nat.card` and `finsum` over the finite set `T^p_n`. (The rooted pointed
map `M_n` uniform on `M^p_n` is the BDG image of `(θ_n, ε_n)` with `θ_n` uniform on `T^p_n`; every
quantity of the mission's statements depends on `M_n` only through `θ_n`.) -/
noncomputable def uniformTreeExpectation (p n : ℕ)
    (g : Finset (List ℕ+) × (List ℕ+ → ℤ) → ℝ) : ℝ :=
  (Nat.card (labeledPTrees p n) : ℝ)⁻¹ * ∑ᶠ (θ) (_ : θ ∈ labeledPTrees p n), g θ

end LeGallBrownianMap


