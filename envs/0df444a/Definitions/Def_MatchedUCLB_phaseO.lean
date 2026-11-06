-- Prove2me | Definitions.Def_MatchedUCLB_phaseO
-- name    : MatchedUCLB_phaseO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:30:42.817523+00:00
-- url     : https://prove2.me/theorems/f4da86dc-b563-4767-be92-0a6cbbe6b3b0
-- title:
--   The shifted chain $O_j=P_j-P_j(c_{j+1})-4\delta_j$
-- statement:
--   With the regularized chain $P$, the endpoint $c+h$ and the smoothing width $\delta$, the **shifted chain** is
--
--   $$
--   O(x)=P(x)-P(c+h)-4\delta .
--   $$
--
--   It agrees with the affine continuation up to a margin: $I(c+h)=0$ and $O(c+h)=-4\delta$.
--
--   **Formalization Note** A phase is described by $m$ (the length of the family $u$), $\lambda$ (`lam`), $\tau=\tau_j$, $G=G_j$, $s'=s_{j+1}$ (`sN`), the center $c=c_j$, the starting direction $v=v_j$, the next direction $v'=v_{j+1}$ (`vN`) and the chain directions $u_0,\dots,u_{m-1}$ ($=u_{j,1},\dots,u_{j,m}$, indexed from $0$). The terminal phase $j=L-1$ is the case $v'=0$, $s'=0$, which is the page's convention $s_Lv_L:=0$.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Eq. (4.12c), p.8; Definition E.8, p.89

import Mathlib
import Definitions.Def_MatchedUCLB_phaseP
import Definitions.Def_MatchedUCLB_phaseH
import Definitions.Def_MatchedUCLB_deltaC

namespace MatchedUCLB

/-- **The shifted chain `O_j`, ambient form.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Eq. (4.12c), p.8:
"`O_j(w, t_{j+1}) = P_j(w, t_{j+1}) − P_j(h_j, 0) − 4δ_j`"; Definition E.8, p.89:
"`O_j(x) := P_j(x) − P_j(c_{j+1}) − 4δ_j`", with `δ_j = c_1 λ m τ_j^q`.

**Formalization Note.** One phase is described by its chain length `m` (through `u : Fin m → ℝ^d`),
the reals `lam` (= λ), `τ` (= τ_j), `G` (= G_j), `sN` (= s_{j+1}), and the points `c` (= c_j), `v`
(= v_j), `vN` (= v_{j+1}) and the chain directions `u i` (= u_{j,i+1}, 0-based). The terminal phase
`j = L − 1` ("we omit t_L, v_L and set s_L = t⋆_L = 0, with s_L v_L := 0", p.9) is the case
`vN = 0`, `sN = 0`. -/
noncomputable def phaseO (q lam τ : ℝ) {d m : ℕ} (c v vN : EuclideanSpace ℝ (Fin d)) (u : Fin m → EuclideanSpace ℝ (Fin d)) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  phaseP q lam c v vN u x - phaseP q lam c v vN u (c + phaseH τ v u) - 4 * deltaC q m lam τ

end MatchedUCLB


