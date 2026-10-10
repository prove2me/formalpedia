-- Prove2me | Definitions.Def_LuoSunLiu_PLBLower_TwoPoint
-- name    : LuoSunLiu_PLBLower_TwoPoint
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T19:14:08.285149+00:00
-- url     : https://prove2.me/theorems/533cf504-9f3f-4b9c-ae64-74b80cb7e312
-- title:
--   Proof of Proposition 2, p. 44 — the two actions U, V and the two parameters ξ_u, ξ_v
-- statement:
--   Fix a central parameter $\tilde\xi\in\mathbb R^d$, two distinct coordinates $j_u\neq j_v$, and a number $C$ (in the proof, $C=C_p/2$). Write $u=\tilde\xi_{j_u}$ and $v=\tilde\xi_{j_v}$, and let $e_j$ be the $j$-th standard basis vector. Define the two actions
--   $$U=\frac{1}{u+C}\,e_{j_u},\qquad V=\frac{1}{v+C}\,e_{j_v},$$
--   each with a single nonzero entry, and the two parameters $\xi_u,\xi_v\in\mathbb R^d$ that agree with $\tilde\xi$ off $\{j_u,j_v\}$ and satisfy
--   $$(\xi_u)_{j_u}=u-C,\quad(\xi_u)_{j_v}=v+C,\qquad(\xi_v)_{j_u}=u+C,\quad(\xi_v)_{j_v}=v-C.$$
--
--   In the proof of Proposition 2, $u$ and $v$ are the smallest and second smallest entries of $\tilde\xi$, every action set is $\{U,V\}$, and in each period the adversary sets $\xi_t$ to $\xi_u$ or $\xi_v$ so that the action the algorithm favours is the wrong one.
--
--   **Formalization Note** $U$ and $V$ are `Pi.single` vectors; $\xi_u,\xi_v$ are built with `Function.update`, first at $j_u$ then at $j_v$ (the order is immaterial since $j_u\neq j_v$ in every statement). The choice of $j_u,j_v$ as the indices of the two smallest entries is not part of the definitions.
-- source:
--   Luo, Sun and Liu, arXiv:2109.07340v2, App. A, proof of Proposition 2, p. 44

import Mathlib

namespace LuoSunLiu.PLBLower

/-! The two-point construction of the proof of Proposition 2 (p. 44). Throughout, `ξc` is the
central parameter `ξ̃`, `ju ≠ jv` are two coordinates with `u = ξ̃_{ju}`, `v = ξ̃_{jv}`, and
`C = C_p / 2`. -/

/-- The action `U`: its only nonzero entry is `1 / (u + C)`, at index `ju`, where `u = ξ̃_{ju}`. -/
noncomputable def actU {d : ℕ} (ξc : Fin d → ℝ) (C : ℝ) (ju : Fin d) : Fin d → ℝ :=
  Pi.single ju (1 / (ξc ju + C))

/-- The action `V`: its only nonzero entry is `1 / (v + C)`, at index `jv`, where `v = ξ̃_{jv}`. -/
noncomputable def actV {d : ℕ} (ξc : Fin d → ℝ) (C : ℝ) (jv : Fin d) : Fin d → ℝ :=
  Pi.single jv (1 / (ξc jv + C))

/-- The parameter `ξ_u`: equal to `ξ̃` off `{ju, jv}`, with `(ξ_u)_{ju} = u − C` and
`(ξ_u)_{jv} = v + C`. -/
noncomputable def xiU {d : ℕ} (ξc : Fin d → ℝ) (C : ℝ) (ju jv : Fin d) : Fin d → ℝ :=
  Function.update (Function.update ξc ju (ξc ju - C)) jv (ξc jv + C)

/-- The parameter `ξ_v`: equal to `ξ̃` off `{ju, jv}`, with `(ξ_v)_{ju} = u + C` and
`(ξ_v)_{jv} = v − C`. -/
noncomputable def xiV {d : ℕ} (ξc : Fin d → ℝ) (C : ℝ) (ju jv : Fin d) : Fin d → ℝ :=
  Function.update (Function.update ξc ju (ξc ju + C)) jv (ξc jv - C)

end LuoSunLiu.PLBLower


