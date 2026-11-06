-- Prove2me | Definitions.Def_MatchedUCLB_slope
-- name    : MatchedUCLB_slope
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:30:50.0536+00:00
-- url     : https://prove2.me/theorems/61c30f9e-a1e7-4b7b-98cc-6d815d09b3e0
-- title:
--   The starting slope $s_j=\Gamma_j+G_jt^\star_j/R_j$
-- statement:
--   For a phase with parameters $\lambda,\tau,G$ and directions $v,u$, with $R=\|h\|$ the length of the center increment, the **starting slope** is
--
--   $$
--   s=\Gamma+\frac{G\,t^\star}{R}.
--   $$
--
--   **Formalization Note** A phase is described by $m$ (the length of the family $u$), $\lambda$ (`lam`), $\tau=\tau_j$, $G=G_j$, $s'=s_{j+1}$ (`sN`), the center $c=c_j$, the starting direction $v=v_j$, the next direction $v'=v_{j+1}$ (`vN`) and the chain directions $u_0,\dots,u_{m-1}$ ($=u_{j,1},\dots,u_{j,m}$, indexed from $0$). The terminal phase $j=L-1$ is the case $v'=0$, $s'=0$, which is the page's convention $s_Lv_L:=0$.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Eq. (4.11), p.8; Definition E.1, p.83

import Mathlib
import Definitions.Def_MatchedUCLB_Gam
import Definitions.Def_MatchedUCLB_phaseH

namespace MatchedUCLB

/-- **The starting slope `s_j = Γ_j + G_j t⋆_j / R_j`.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Eq. (4.11), p.8, with
`R_j = ‖h_j‖` (4.10); Definition E.1, p.83.

**Formalization Note.** One phase is described by its chain length `m` (through `u : Fin m → ℝ^d`),
the reals `lam` (= λ), `τ` (= τ_j), `G` (= G_j), `sN` (= s_{j+1}), and the points `c` (= c_j), `v`
(= v_j), `vN` (= v_{j+1}) and the chain directions `u i` (= u_{j,i+1}, 0-based). The terminal phase
`j = L − 1` ("we omit t_L, v_L and set s_L = t⋆_L = 0, with s_L v_L := 0", p.9) is the case
`vN = 0`, `sN = 0`. -/
noncomputable def slope (q : ℝ) {d m : ℕ} (lam τ G : ℝ) (v : EuclideanSpace ℝ (Fin d)) (u : Fin m → EuclideanSpace ℝ (Fin d)) : ℝ :=
  Gam q m lam τ + G * tStar m τ / ‖phaseH τ v u‖

end MatchedUCLB


