-- Prove2me | Definitions.Def_MatchedUCLB_phaseI
-- name    : MatchedUCLB_phaseI
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:33:38.082213+00:00
-- url     : https://prove2.me/theorems/82397db0-5748-4948-ba77-8565c79ba0c2
-- title:
--   The affine continuation $I_j(x)=\langle g_j,x-c_{j+1}\rangle$
-- statement:
--   With the completed-phase gradient $g$ and the phase endpoint $c+h$ (the next center), the **affine continuation** is
--
--   $$
--   I(x)=\langle g,\,x-(c+h)\rangle .
--   $$
--
--   **Formalization Note** A phase is described by $m$ (the length of the family $u$), $\lambda$ (`lam`), $\tau=\tau_j$, $G=G_j$, $s'=s_{j+1}$ (`sN`), the center $c=c_j$, the starting direction $v=v_j$, the next direction $v'=v_{j+1}$ (`vN`) and the chain directions $u_0,\dots,u_{m-1}$ ($=u_{j,1},\dots,u_{j,m}$, indexed from $0$). The terminal phase $j=L-1$ is the case $v'=0$, $s'=0$, which is the page's convention $s_Lv_L:=0$.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Eq. (4.12a), p.8; Definition E.8, p.89

import Mathlib
import Definitions.Def_MatchedUCLB_gVec

namespace MatchedUCLB

/-- **The affine continuation `I_j`, ambient form.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Eq. (4.12a), p.8:
"`I_j(w, t_{j+1}) = ⟨g_j, w − h_j + t_{j+1} v_{j+1}⟩`"; Definition E.8, p.89:
"`I_j(x) := ⟨g_j, x − c_{j+1}⟩`", where `c_{j+1} = c_j + h_j`.

**Formalization Note.** One phase is described by its chain length `m` (through `u : Fin m → ℝ^d`),
the reals `lam` (= λ), `τ` (= τ_j), `G` (= G_j), `sN` (= s_{j+1}), and the points `c` (= c_j), `v`
(= v_j), `vN` (= v_{j+1}) and the chain directions `u i` (= u_{j,i+1}, 0-based). The terminal phase
`j = L − 1` ("we omit t_L, v_L and set s_L = t⋆_L = 0, with s_L v_L := 0", p.9) is the case
`vN = 0`, `sN = 0`. -/
noncomputable def phaseI (q lam τ G sN : ℝ) {d m : ℕ} (c v vN : EuclideanSpace ℝ (Fin d)) (u : Fin m → EuclideanSpace ℝ (Fin d)) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  inner ℝ (gVec q lam τ G sN v vN u) (x - (c + phaseH τ v u))

end MatchedUCLB


