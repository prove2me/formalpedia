-- Prove2me | Definitions.Def_NatureSLT_GrowthFunction_growthFunction
-- name    : NatureSLT_GrowthFunction_growthFunction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:50:45.024369+00:00
-- url     : https://prove2.me/theorems/3f3d9b4b-7ec9-4ba6-b3fd-3ba0eb6fca7a
-- title:
--   Growth function $G^\Lambda(\ell) = \ln \sup_{z_1, \dots, z_\ell} N^\Lambda(z_1, \dots, z_\ell)$
-- statement:
--   Let $Q(z, \alpha)$, $\alpha \in \Lambda$, be a set of indicator functions on a set $Z$, and for a sample $z_1, \dots, z_\ell$ let $N^\Lambda(z_1, \dots, z_\ell)$ be the number of different binary vectors $(Q(z_1, \alpha), \dots, Q(z_\ell, \alpha))$, $\alpha \in \Lambda$. The **growth function** of the set is
--
--   $$G^\Lambda(\ell) = \ln \sup_{z_1, \dots, z_\ell} N^\Lambda(z_1, \dots, z_\ell), \qquad \ell = 0, 1, 2, \dots,$$
--
--   the supremum being over all samples of $\ell$ points of $Z$ (repetitions allowed) and $\ln$ the natural logarithm. Since $N^\Lambda \le 2^\ell$, the supremum is a maximum and $G^\Lambda(\ell) \le \ell \ln 2$.
--
--   Unlike the entropy and the annealed entropy, the growth function does not depend on a probability measure; it is the quantity through which distribution-free bounds are stated.
--
--   **Formalization Note** The supremum is taken in $\mathbb N$ over all maps `Fin ℓ → Z`; it is bounded by $2^\ell$, hence attained when $Z$ is nonempty. For empty $Z$ and $\ell \ge 1$ there is no sample, the supremum is $0$, and $\ln 0$ is evaluated as $0$; the same value arises for empty $\Lambda$. The theorems of this mission assume $Z$ and $\Lambda$ nonempty, so these values never enter.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 55, Section 2.7, (ii)

import Mathlib
import Definitions.Def_NatureSLT_GrowthFunction_numSeparations

namespace NatureSLT.GrowthFunction

/-- `sup_{z₁, …, z_ℓ} N^Λ(z₁, …, z_ℓ)`: the largest number of different separations of a sample of
size `ℓ` by the indicator functions `Q(z, α)`, `α ∈ Λ`, over all samples `z₁, …, z_ℓ ∈ Z`
(repeated points allowed). Every value is at most `2^ℓ`, so the supremum is a maximum whenever
`Z` is nonempty or `ℓ = 0`; for empty `Z` and `ℓ ≥ 1` there is no sample and the value is `0`. -/
noncomputable def maxSeparations {Z Λ : Type*} (Q : Λ → Z → Bool) (ℓ : ℕ) : ℕ :=
  ⨆ z : Fin ℓ → Z, numSeparations Q z

/-- The **growth function** (Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed., §2.7,
p. 55, (ii)):
`G^Λ(ℓ) = ln sup_{z₁, …, z_ℓ} N^Λ(z₁, …, z_ℓ)`, with `ln` the natural logarithm.
(`Real.log 0 = 0`: the argument is `≥ 1` exactly when `Λ` is nonempty and a sample of size `ℓ`
exists; the theorems of this mission assume `Λ` and `Z` nonempty.) -/
noncomputable def growthFunction {Z Λ : Type*} (Q : Λ → Z → Bool) (ℓ : ℕ) : ℝ :=
  Real.log (maxSeparations Q ℓ)

end NatureSLT.GrowthFunction


