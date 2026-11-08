-- Prove2me | Definitions.Def_AffDisp4n_IsAffineFn
-- name    : AffDisp4n_IsAffineFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:55:32.421448+00:00
-- url     : https://prove2.me/theorems/8631237a-b96d-4970-88ee-d0f818c26058
-- title:
--   Affine function of the parameters
-- statement:
--   A function $\ell : \mathbb F_2^m \to \mathbb F_2$ is an **affine function of the parameters** $u = (u_1, \dots, u_m)$ if
--   $$
--   \ell(u) = \sum_{j=1}^m \lambda_j u_j + \kappa
--   $$
--   for some $\lambda_1, \dots, \lambda_m, \kappa \in \mathbb F_2$.
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), proof of Lemma 2.2, p.17

import Mathlib

namespace AffDisp4n

/-- An **affine function of the parameters** `u = (u₁, …, uₘ)` (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), proof of Lemma 2.2, p.17):
`ℓ(u) = ∑ⱼ λⱼ uⱼ + κ` with `λⱼ, κ ∈ 𝔽₂`. -/
def IsAffineFn {m : ℕ} (ℓ : (Fin m → ZMod 2) → ZMod 2) : Prop :=
  ∃ (coef : Fin m → ZMod 2) (κ : ZMod 2), ∀ u, ℓ u = ∑ j, coef j * u j + κ

end AffDisp4n


