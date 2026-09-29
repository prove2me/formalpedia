-- Prove2me | Definitions.Def_PermLimits_Shared_RectDist
-- name    : PermLimits_Shared_RectDist
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:57:10.154729+00:00
-- url     : https://prove2.me/theorems/f54a9519-9c92-481f-b719-d147f02c23c3
-- title:
--   Rectangular distance $d_\square(Z_1,Z_2)$ between limit permutations
-- statement:
--   For $Z_1,Z_2\in\mathcal Z$ the **rectangular distance** is
--   $$d_\square(Z_1,Z_2)=\sup_{\substack{x_1<x_2\in[0,1]\\ y_1<y_2\in[0,1]}}\left|\int_{x_1}^{x_2}\big(Z_1(x,y_2)-Z_1(x,y_1)\big)\,dx-\int_{x_1}^{x_2}\big(Z_2(x,y_2)-Z_2(x,y_1)\big)\,dx\right| .$$
--   Each integral is the probability that the random point associated with $Z_i$ falls in the rectangle $[x_1,x_2]\times[y_1,y_2]$, so $d_\square$ is the largest discrepancy of the two laws on a rectangle. For a permutation $\sigma$ and $Z\in\mathcal Z$ one sets $d_\square(\sigma,Z):=d_\square(Z_\sigma,Z)$.
--
--   **Formalization Note** The supremum is the real supremum of the set of values. For limit permutations every value lies in $[0,1]$, so the set is nonempty and bounded and the supremum is genuine; the distance is applied only to limit permutations. The distance of a permutation to a limit permutation is written with the step limit permutation $Z_\sigma$.
--
--   This definition is shared by both missions of this series: mission 1 (`01-limit-existence`, existence and uniqueness of the limit permutation) (Lemma 4.2, p. 13; Definition 5.2, p. 16) and mission 2 (`02-cauchy-rectangular`, convergent sequences are Cauchy for the rectangular distance) (Eq. (34), p. 12; the Cauchy condition of Theorem 1.8, p. 5 and Sect. 4.1, pp. 12–13; Definition 5.2, p. 16).
-- source:
--   Hoppen, Kohayakawa, Moreira, Ráth, Sampaio, Limits of permutation sequences, arXiv:1103.5844v2, https://arxiv.org/abs/1103.5844v2, p. 12, Eq. (32) (first line), and p. 13, Eq. (36)

import Mathlib

/-!
# The rectangular distance between limit permutations

C. Hoppen, Y. Kohayakawa, C. G. Moreira, B. Ráth, R. M. Sampaio, *Limits of permutation
sequences*, arXiv:1103.5844v2, p. 12, Eq. (32) (first line), and Eq. (36), p. 13.
-/

namespace PermLimits.Shared

open MeasureTheory unitInterval

/-- **Rectangular distance** `d□(Z₁, Z₂)` (Hoppen et al., arXiv:1103.5844v2, Eq. (32), first
line, p. 12):
`d□(Z₁, Z₂) = sup_{x₁ < x₂, y₁ < y₂ ∈ [0,1]} | ∫_{x₁}^{x₂} (Z₁(x,y₂) − Z₁(x,y₁)) dx
− ∫_{x₁}^{x₂} (Z₂(x,y₂) − Z₂(x,y₁)) dx |`.

**Formalization Note.** The supremum is the real `sSup` of the set of values. For
`Z₁, Z₂ ∈ 𝒵` every value lies in `[0, 2]` (in fact in `[0, 1]`), so the set is nonempty and
bounded and `sSup` is the true supremum; statements apply `rectDist` only to limit permutations.
`∫_{x₁}^{x₂}` is the Lebesgue integral over `[x₁, x₂] ⊆ [0, 1]`. The rectangular distance
between a permutation `σ` and `Z` is `d□(σ, Z) := d□(Z_σ, Z)` (Eq. (36), p. 13), written
`rectDist (stepLimit σ) Z`. -/
noncomputable def rectDist (Z₁ Z₂ : I → I → ℝ) : ℝ :=
  sSup {r : ℝ | ∃ x₁ x₂ y₁ y₂ : I, x₁ < x₂ ∧ y₁ < y₂ ∧
    r = |(∫ x in Set.Icc x₁ x₂, (Z₁ x y₂ - Z₁ x y₁)) -
          (∫ x in Set.Icc x₁ x₂, (Z₂ x y₂ - Z₂ x y₁))|}

end PermLimits.Shared


