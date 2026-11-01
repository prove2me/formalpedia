-- Prove2me | Definitions.Def_LatentMixDRO_holderClass
-- name    : LatentMixDRO_holderClass
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:23:42.450652+00:00
-- url     : https://prove2.me/theorems/14b374d0-1d08-47fe-a00d-581fab21acff
-- title:
--   Hölder class $\mathcal H_{L,p}$
-- statement:
--   For $\mathcal X\subset\mathbb R^d$, $p\in(1,2]$ and $L\ge0$, the class $\mathcal H_{L,p}$ consists of the $(p-1,L^{p-1})$-Hölder functions on $\mathcal X$:
--
--   $$
--   \mathcal H_{L,p}=\big\{h:\ |h(x)-h(x')|\le L^{p-1}\|x-x'\|^{p-1}\ \text{for all }x,x'\in\mathcal X\big\}.
--   $$
--
--   It is the class of test functions in the variational objective (12).
--
--   **Formalization Note** The functions are total on $\mathbb R^d$ and constrained on $\mathcal X$ only, so the source's functions on $\mathcal X$ are exactly the restrictions.
-- source:
--   Duchi, Hashimoto & Namkoong, Distributionally Robust Losses for Latent Covariate Mixtures, arXiv:2007.13982v2, display (11), p.9

import Mathlib

namespace LatentMixDRO

/-- The Hölder class `H_{L,p} = {h : 𝒳 → ℝ, (p - 1, L^{p-1})-Hölder continuous}`:
`|h x - h x'| ≤ L^{p-1} ‖x - x'‖^{p-1}` for all `x, x' ∈ 𝒳`.

Duchi, Hashimoto & Namkoong, arXiv:2007.13982v2, display (11), p.9.

**Formalization Note.** `h` is a total function on `ℝ^d`, constrained on `𝒳` only; the source's
functions on `𝒳` are exactly the restrictions. -/
def holderClass {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d))) (p L : ℝ) :
    Set (EuclideanSpace ℝ (Fin d) → ℝ) :=
  {h | ∀ x ∈ X, ∀ x' ∈ X, |h x - h x'| ≤ L ^ (p - 1) * ‖x - x'‖ ^ (p - 1)}

end LatentMixDRO


