-- Prove2me | Definitions.Def_NondetConn_W
-- name    : NondetConn_W
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:23:56.011352+00:00
-- url     : https://prove2.me/theorems/7e1ac794-8194-4484-b82d-f67354309837
-- title:
--   The set $\mathcal W_{(x,y)}(b)$
-- statement:
--   Let $\mathcal A$ be a set of permutations of $[n]$, $b$ a permutation of $[n]$ and $x \ne y \in [n]$. Then $\mathcal W_{(x,y)}(b)$ is the set of $w \in [n]\setminus\{x,y\}$ such that $(w\,x\,y)$ is compatible with the cycle $b^{-1}a$ for every $a \in \mathcal A$:
--   $$
--   \mathcal W_{(x,y)}(b) = \{ w \in [n]\setminus\{x,y\} : w, x, y \text{ follow the cyclic order } (w\,x\,y) \text{ along } b^{-1}a \text{ for all } a \in \mathcal A\}.
--   $$
--   Lemmas 4.5 and 4.6 bound the multiplicity of the shortcut maps through $|\mathcal W_{(x,y)}(b)|$.
--
--   **Formalization Note** The paper leaves the dependence on $\mathcal A$ implicit; here $\mathcal A$ is an explicit argument. The definition is total in $x, y$; every use has $x \ne y$.
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), §4.1, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_NondetConn_cyclicOrder

namespace NondetConn

/-- **The set `𝒲_(x,y)(b)`** (Zhang, *Settling Nondeterministic Communication Complexity of Graph Connectivity*, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), §4.1,
p.11): for a set `𝒜` of permutations of `[n]`, a permutation `b` and `x ≠ y ∈ [n]`, the set of
`w ∈ [n] \ {x, y}` such that `(w x y)` is compatible with the cycle `b⁻¹a` for every `a ∈ 𝒜`,
i.e. `w, x, y` follow the cyclic order `(w x y)` (not `(w y x)`) along `b⁻¹a`.

**Formalization Note** The paper leaves the dependence on `𝒜` implicit; here `𝒜` is an explicit
argument and "for every `a ∈ 𝒜`" is inside the defining condition. `b⁻¹a` is `b⁻¹ * a`. The
definition is total in `x, y`; every use has `x ≠ y`. Membership is decided classically. -/
noncomputable def W {n : ℕ} (𝒜 : Finset (Equiv.Perm (Fin n))) (b : Equiv.Perm (Fin n))
    (x y : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter
    (fun w => w ≠ x ∧ w ≠ y ∧ ∀ a ∈ 𝒜, cyclicOrder (b⁻¹ * a) w x y)

end NondetConn


