-- Prove2me | Definitions.Def_PermLimits_Cauchy_SupDist
-- name    : PermLimits_Cauchy_SupDist
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:21:24.186505+00:00
-- url     : https://prove2.me/theorems/706b704b-a777-474f-ad0e-ddbb7326ada9
-- title:
--   The distance $d_\infty(Z_1,Z_2)$ between joint distribution functions
-- statement:
--   For $Z_1,Z_2\in\mathcal Z$ let $F_i$ be the joint distribution function of the random point $(X_i,Y_i)$ associated with $Z_i$. By Eq. (21) of the source,
--   $$F_i(x,y)=\mathbf P(X_i\le x,\,Y_i\le y)=\int_0^x Z_i(t,y)\,dt,\qquad x,y\in[0,1].$$
--   The **sup-norm distance** of $Z_1$ and $Z_2$ is
--   $$d_\infty(Z_1,Z_2)=\|F_1-F_2\|_\infty=\sup_{x,y\in[0,1]}\big|F_1(x,y)-F_2(x,y)\big| .$$
--
--   The distance $d_\infty$ is comparable to the rectangular distance $d_\square$ (Eq. (34) of the source) and is simpler to work with, since it involves one corner point instead of a rectangle.
--
--   **Formalization Note** The joint distribution function is written directly by the integral $\int_0^x Z_i(t,y)\,dt$ (Lebesgue integral over $[0,x]$), not through a construction of the random point. The supremum is the real supremum of the set of values; for limit permutations every value lies in $[0,1]$, so the set is nonempty and bounded and the supremum is genuine. The distance is applied only to limit permutations.
-- source:
--   Hoppen, Kohayakawa, Moreira, Ráth, Sampaio, Limits of permutation sequences, arXiv:1103.5844v2, https://arxiv.org/abs/1103.5844v2, p. 12, Eq. (33), with the joint distribution function of p. 9, Eq. (21)

import Mathlib

/-!
# The sup-norm distance between the distribution functions of two limit permutations

C. Hoppen, Y. Kohayakawa, C. G. Moreira, B. Ráth, R. M. Sampaio, *Limits of permutation
sequences*, arXiv:1103.5844v2, p. 12, Eq. (33), with the joint distribution function written
through Eq. (21), p. 9.
-/

namespace PermLimits.Cauchy

open MeasureTheory unitInterval

/-- **The distance `d∞(Z₁, Z₂)`** (Hoppen et al., arXiv:1103.5844v2, Eq. (33), p. 12):
`d∞(Z₁, Z₂) = ‖F₁ − F₂‖_∞ = sup_{x, y ∈ [0,1]} |F₁(x, y) − F₂(x, y)|`, where `Fᵢ` is the joint
distribution function of the random point `(Xᵢ, Yᵢ)` associated with `Zᵢ` (Definition 2.3).

**Formalization Note.** The joint distribution function is written by the right side of Eq. (21)
(p. 9), `Fᵢ(x, y) = ∫₀ˣ Zᵢ(t, y) dt`, the Lebesgue integral over `[0, x] = Set.Iic x` in
`I = [0, 1]`; this avoids any dependence on a construction of the random point `(Xᵢ, Yᵢ)`. The
supremum is the real `sSup` of the set of values. For `Z₁, Z₂ ∈ 𝒵` both `Fᵢ` take values in
`[0, 1]`, so every value lies in `[0, 1]`: the set is nonempty and bounded and `sSup` is the true
supremum. Statements apply `supDist` only to limit permutations. -/
noncomputable def supDist (Z₁ Z₂ : I → I → ℝ) : ℝ :=
  sSup {r : ℝ | ∃ x y : I,
    r = |(∫ t in Set.Iic x, Z₁ t y) - (∫ t in Set.Iic x, Z₂ t y)|}

end PermLimits.Cauchy


