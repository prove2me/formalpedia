-- Prove2me | Definitions.Def_MatchedUCLB_phaseA
-- name    : MatchedUCLB_phaseA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:35:05.233288+00:00
-- url     : https://prove2.me/theorems/1531fb2e-2e73-4ded-99cf-df06c04341a3
-- title:
--   The phase function $A_j=M_{\delta_j}(I_j,O_j)$
-- statement:
--   The **phase function** is the smooth maximum of the affine continuation and the shifted chain,
--
--   $$
--   A(x)=M_{\delta}\bigl(I(x),\,O(x)\bigr),
--   $$
--
--   evaluated on $\mathbb R^d$ through the local coordinates $(P_{E_j}(x-c_j),\langle v_{j+1},x-c_j\rangle)$ as in (4.13). It follows the chain on short prefixes and the affine function near the completed segment.
--
--   **Formalization Note** A phase is described by $m$ (the length of the family $u$), $\lambda$ (`lam`), $\tau=\tau_j$, $G=G_j$, $s'=s_{j+1}$ (`sN`), the center $c=c_j$, the starting direction $v=v_j$, the next direction $v'=v_{j+1}$ (`vN`) and the chain directions $u_0,\dots,u_{m-1}$ ($=u_{j,1},\dots,u_{j,m}$, indexed from $0$). The terminal phase $j=L-1$ is the case $v'=0$, $s'=0$, which is the page's convention $s_Lv_L:=0$. Then the next coordinate vanishes identically and the $\alpha$-term drops, which is the printed terminal formula.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Eqs. (4.12d), (4.13), p.9; Definition E.8, pp.89–90

import Mathlib
import Definitions.Def_MatchedUCLB_phaseI
import Definitions.Def_MatchedUCLB_phaseO
import Definitions.Def_MatchedUCLB_smoothMax

namespace MatchedUCLB

/-- **The phase function `A_j`, ambient form.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Eq. (4.12d), p.9:
"`A_j(w, t_{j+1}) = M_{δ_j}(I_j, O_j)`", extended to `ℝ^d` by Eq. (4.13),
`T_j(x) := T_j(P_{E_j}(x − c_j), ⟨v_{j+1}, x − c_j⟩)`; Definition E.8, pp.89–90.

**Formalization Note.** One phase is described by its chain length `m` (through `u : Fin m → ℝ^d`),
the reals `lam` (= λ), `τ` (= τ_j), `G` (= G_j), `sN` (= s_{j+1}), and the points `c` (= c_j), `v`
(= v_j), `vN` (= v_{j+1}) and the chain directions `u i` (= u_{j,i+1}, 0-based). The terminal phase
`j = L − 1` ("we omit t_L, v_L and set s_L = t⋆_L = 0, with s_L v_L := 0", p.9) is the case
`vN = 0`, `sN = 0`.
Then `⟨v_{j+1}, x − c⟩ ≡ 0` and the `α`-term vanishes, which is the printed terminal formula. -/
noncomputable def phaseA (q lam τ G sN : ℝ) {d m : ℕ} (c v vN : EuclideanSpace ℝ (Fin d)) (u : Fin m → EuclideanSpace ℝ (Fin d)) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  smoothMax (deltaC q m lam τ) (phaseI q lam τ G sN c v vN u x) (phaseO q lam τ c v vN u x)

end MatchedUCLB


