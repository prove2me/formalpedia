-- Prove2me | Definitions.Def_DerandSq_Supplement_rotTree
-- name    : DerandSq_Supplement_rotTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T20:03:11.50158+00:00
-- url     : https://prove2.me/theorems/f9d04b4c-f3b1-4285-a7fc-c90503a729f8
-- title:
--   Infinite rotating tree $a$ (3.4)
-- statement:
--   Let $g_1, \dots, g_r, h_1, \dots, h_{k-1}$ freely generate the free group $F_{r+k-1}$, let $\lambda$ be its left-regular representation on $\ell^2(F_{r+k-1})$, and put $u_j = \lambda(g_j)$, $v_i = \lambda(h_i)$ and
--
--   $$
--   t = u_1 + u_1^* + \cdots + u_r + u_r^*,
--   $$
--
--   the adjacency operator of the $d = 2r$-regular infinite tree $T_d$. The **infinite rotating tree** is the operator
--
--   $$
--   a = t v_1 t v_2 t \cdots v_{k-1} t^2 v_{k-1}^* \cdots v_2^* t v_1^* t
--   $$
--
--   on $\ell^2(F_{r+k-1})$. It is the limit object of the rotating walk on a random permutation-model graph with random rotations; for $k = 1$ it is $t^2$.
--
--   **Formalization Note** $F_{r+k-1}$ is `FreeGroup (Fin r ⊕ Fin m)` with $m = k - 1$; $^*$ is the Hilbert adjoint.
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), (3.4), p.14

import Mathlib
import Definitions.Def_DerandSq_leftReg

namespace DerandSq.Supplement

/-- The infinite rotating tree `a` of (3.4), Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), p.14:
in `F_{r+k−1}` with free generators `g_1, …, g_r, h_1, …, h_{k−1}`, `u_j = λ(g_j)`,
`v_i = λ(h_i)`, `t = u_1 + u_1^* + ⋯ + u_r + u_r^*` (the `d = 2r`-regular infinite tree) and
`a = t v_1 t v_2 t ⋯ v_{k−1} t² v_{k−1}^* ⋯ v_2^* t v_1^* t`,
an operator on `ℓ²(F_{r+k−1})`.

**Formalization Note** `F_{r+k−1}` is `FreeGroup (Fin r ⊕ Fin m)` with `m = k − 1`:
`g_j = of (inl j)`, `h_i = of (inr i)`; `λ` is `DerandSq.leftReg` (`λ(g)δ_h = δ_{gh}`) and
`^*` is the Hilbert adjoint `star`. The operator is written as `M · M'` with
`M = t · ∏_i (v_i t)` (increasing `i`) and `M' = ∏_i (t v_{k−1−i}^*) · t` (decreasing), which
is (3.4) letter by letter; for `m = 0` it is `t²`. -/
noncomputable def rotTree (r m : ℕ) :
    DerandSq.L2 (FreeGroup (Fin r ⊕ Fin m)) →L[ℂ] DerandSq.L2 (FreeGroup (Fin r ⊕ Fin m)) :=
  let t := ∑ j : Fin r, (DerandSq.leftReg (FreeGroup.of (Sum.inl j)) +
    star (DerandSq.leftReg (FreeGroup.of (Sum.inl j) : FreeGroup (Fin r ⊕ Fin m))))
  let v : Fin m → DerandSq.L2 (FreeGroup (Fin r ⊕ Fin m)) →L[ℂ]
      DerandSq.L2 (FreeGroup (Fin r ⊕ Fin m)) := fun i => DerandSq.leftReg (FreeGroup.of (Sum.inr i))
  (t * (List.ofFn fun i : Fin m => v i * t).prod) *
    ((List.ofFn fun i : Fin m => t * star (v (Fin.rev i))).prod * t)

end DerandSq.Supplement


