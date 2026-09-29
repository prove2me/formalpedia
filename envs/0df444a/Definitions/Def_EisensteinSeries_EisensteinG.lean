-- Prove2me | Definitions.Def_EisensteinSeries_EisensteinG
-- name    : EisensteinSeries_EisensteinG
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/8b5efe3e-b5da-56f6-ad35-38b1fc8e8b51
-- title:
--   Non-normalised level-N Eisenstein series over a congruence class
-- statement:
--   For a natural number $N$, an integer $k$, a vector $a \in (\mathbb{Z}/N\mathbb{Z})^2$ (i.e. $a : \mathrm{Fin}\,2 \to \mathbb{Z}/N\mathbb{Z}$) and a point $z$ of the upper half-plane, [`EisensteinSeries.eisensteinG N k a z`](../def/EisensteinSeries_EisensteinG.html#L5) is defined as the unconditional sum
--   $$\sum_{\substack{v \in \mathbb{Z}^2 \\ v \equiv a \ (N)}} \mathrm{eisSummand}\,k\,v\,z,$$
--   the index set being the subtype of those $v : \mathrm{Fin}\,2 \to \mathbb{Z}$ whose componentwise reduction map $\mathbb{Z} \to \mathbb{Z}/N\mathbb{Z}$ composed with $v$ equals $a$, and the summand being Mathlib's Eisenstein summand, $\mathrm{eisSummand}\,k\,v\,z = (v_0 z + v_1)^{-k}$ (a complex zpow). Thus, for $k \ge 3$, this is the classical non-normalised Eisenstein series $G_k^{a}(z) = \sum (v_0 z + v_1)^{-k}$ of weight $k$ for $\Gamma(N)$ attached to the residue class $a$, the sum running over the entire congruence class and not only over its vectors with coprime entries.
--
--   Two points about the shape of the definition deserve note. First, the sum is a `tsum`, so the value is defined for every integer $k$ and every $N$, and equals $0$ by convention when the family fails to be summable; no convergence hypothesis is part of the definition. Second, when $a = 0$ the zero vector belongs to the index set, and it contributes $0^{-k}$, which for $k > 0$ is $0$ under the conventions for complex zpow, so that no term has to be removed by hand. The definition is made for arbitrary $N : \mathbb{N}$, the case $N = 0$ reading as the single vector $v$ with $\mathbb{Z}$-coordinates prescribed by $a$ under $\mathbb{Z}/0\mathbb{Z} = \mathbb{Z}$.
--
--   **Relation to Mathlib.** Mathlib's `eisensteinSeries a k` sums `eisSummand` only over the vectors of the class $a$ with coprime entries (the `gammaSet`); [`EisensteinSeries.eisensteinG`](../def/EisensteinSeries_EisensteinG.html#L5) is the non-normalised variant, built from the same Mathlib summand `eisSummand`, summing over the whole congruence class modulo $N$.
--
--   **Where it is used.** This series is the project's concrete model of a weight-$k$ level-$\Gamma(N)$ Eisenstein series, with an explicit Fourier expansion at infinity, and is used in the modular-forms part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_EisensteinSeries_EisensteinG.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace EisensteinSeries

noncomputable def eisensteinG (N : ℕ) (k : ℤ) (a : Fin 2 → ZMod N) (z : UpperHalfPlane) : ℂ :=
  ∑' v : {v : Fin 2 → ℤ // ((↑) : ℤ → ZMod N) ∘ v = a}, eisSummand k v.1 z

end EisensteinSeries


