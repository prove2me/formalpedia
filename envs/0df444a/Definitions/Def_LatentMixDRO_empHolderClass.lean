-- Prove2me | Definitions.Def_LatentMixDRO_empHolderClass
-- name    : LatentMixDRO_empHolderClass
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:23:40.552851+00:00
-- url     : https://prove2.me/theorems/5a3eacb2-eeb0-44bb-81d0-cd707f3e2cd5
-- title:
--   Empirical Hölder class $\widehat{\mathcal H}_{L,p}$
-- statement:
--   For a sample $(X_1,Y_1),\dots,(X_n,Y_n)$,
--
--   $$
--   \widehat{\mathcal H}_{L,p}=\big\{h\in\mathbb R^n:\ h(X_i)-h(X_j)\le L^{p-1}\|X_i-X_j\|^{p-1}\ \text{for all }i,j\in[n]\big\}.
--   $$
--
--   It is the finite-dimensional set of test vectors in the empirical plug-in (14).
-- source:
--   Duchi, Hashimoto & Namkoong, Distributionally Robust Losses for Latent Covariate Mixtures, arXiv:2007.13982v2, display (13), p.10

import Mathlib

namespace LatentMixDRO

/-- The empirical Hölder class
`Ĥ_{L,p} = {h ∈ ℝⁿ : h(X_i) - h(X_j) ≤ L^{p-1} ‖X_i - X_j‖^{p-1} for all i, j ∈ [n]}`.

Duchi, Hashimoto & Namkoong, arXiv:2007.13982v2, display (13), p.10. -/
def empHolderClass {d n : ℕ} (ω : Fin n → EuclideanSpace ℝ (Fin d) × ℝ) (p L : ℝ) :
    Set (Fin n → ℝ) :=
  {h | ∀ i j, h i - h j ≤ L ^ (p - 1) * ‖(ω i).1 - (ω j).1‖ ^ (p - 1)}

end LatentMixDRO


