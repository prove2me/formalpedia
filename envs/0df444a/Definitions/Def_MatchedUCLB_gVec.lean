-- Prove2me | Definitions.Def_MatchedUCLB_gVec
-- name    : MatchedUCLB_gVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:32:05.802769+00:00
-- url     : https://prove2.me/theorems/99dd40f3-2c14-445f-adff-3e24bd67a33b
-- title:
--   The completed-phase gradient $g_j=s_jv_j-s_{j+1}v_{j+1}-b_j$
-- statement:
--   For a phase with slope $s$, next slope $s'$, next direction $v'$ and base increment $b=(G/R)\,h$, the **completed-phase gradient** is
--
--   $$
--   g=s\,v-s'\,v'-b .
--   $$
--
--   It is the gradient the phase function must contribute after the phase is completed, so that the total gradient at the next center is $-s'v'$.
--
--   **Formalization Note** A phase is described by $m$ (the length of the family $u$), $\lambda$ (`lam`), $\tau=\tau_j$, $G=G_j$, $s'=s_{j+1}$ (`sN`), the center $c=c_j$, the starting direction $v=v_j$, the next direction $v'=v_{j+1}$ (`vN`) and the chain directions $u_0,\dots,u_{m-1}$ ($=u_{j,1},\dots,u_{j,m}$, indexed from $0$). The terminal phase $j=L-1$ is the case $v'=0$, $s'=0$, which is the page's convention $s_Lv_L:=0$.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Eq. (4.11), p.8; Lemma 4.4, p.9

import Mathlib
import Definitions.Def_MatchedUCLB_slope

namespace MatchedUCLB

/-- **The completed-phase gradient `g_j = s_j v_j − s_{j+1} v_{j+1} − b_j`.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527,
Eq. (4.11), p.8, with `b_j = (G_j/R_j) h_j` (Lemma 4.4, p.9).

**Formalization Note.** One phase is described by its chain length `m` (through `u : Fin m → ℝ^d`),
the reals `lam` (= λ), `τ` (= τ_j), `G` (= G_j), `sN` (= s_{j+1}), and the points `c` (= c_j), `v`
(= v_j), `vN` (= v_{j+1}) and the chain directions `u i` (= u_{j,i+1}, 0-based). The terminal phase
`j = L − 1` ("we omit t_L, v_L and set s_L = t⋆_L = 0, with s_L v_L := 0", p.9) is the case
`vN = 0`, `sN = 0`. -/
noncomputable def gVec (q : ℝ) {d m : ℕ} (lam τ G sN : ℝ) (v vN : EuclideanSpace ℝ (Fin d)) (u : Fin m → EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  slope q lam τ G v u • v - sN • vN - (G / ‖phaseH τ v u‖) • phaseH τ v u

end MatchedUCLB


