-- Prove2me | Definitions.Def_HighDimProbAudit_Grothendieck_TensorPowers
-- name    : HighDimProbAudit_Grothendieck_TensorPowers
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:35:03.174901+00:00
-- url     : https://prove2.me/theorems/f1257bf2-d56b-4db6-bbe9-5d73da1a121b
-- title:
--   Tensor arrays and tensor powers (Definition 3.7.1; Example 3.7.3)
-- statement:
--   For natural numbers $n,k$, a real tensor array of order $k$ has a real entry for every tuple $(i_1,\ldots,i_k)$ of coordinates in $\{0,\ldots,n-1\}$. It carries the Euclidean inner product
--   $$\langle T,S\rangle=\sum_{i_1,\ldots,i_k}T_{i_1\cdots i_k}S_{i_1\cdots i_k}.$$
--   For $u\in\mathbb R^n$, its tensor power is the actual array
--   $$(u^{\otimes k})_{i_1\cdots i_k}=\prod_{r=1}^k u_{i_r}.$$
--   At order zero the sole entry is the empty product, equal to one. This array model supplies the common tensor object for the feature-map milestones. The inner product is Mathlib’s Euclidean inner product; its value on tensor powers is a subsequent theorem, rather than part of this definition.
-- source:
--   Vershynin, High-Dimensional Probability: An Introduction with Applications in Data Science, Cambridge University Press, 2018, author-corrected electronic copy dated June 9, 2020, https://doi.org/10.1017/9781108231596, Definition 3.7.1, Eq. (3.28), printed p. 70 (PDF p. 78); Example 3.7.3, printed p. 71 (PDF p. 79).

import Mathlib

set_option autoImplicit false

namespace HighDimProbAudit.Grothendieck

/-- Real k-dimensional arrays, with the Euclidean inner product (3.28). -/
abbrev TensorArray (n k : ℕ) := EuclideanSpace ℝ (Fin k → Fin n)

/-- The entries of the tensor power in Example 3.7.3; order zero is the scalar one. -/
noncomputable def tensorPower {n : ℕ} (k : ℕ) (u : EuclideanSpace ℝ (Fin n)) :
    TensorArray n k :=
  WithLp.toLp 2 (fun t : Fin k → Fin n => ∏ r : Fin k, u (t r))

end HighDimProbAudit.Grothendieck


