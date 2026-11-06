-- Prove2me | Definitions.Def_MatchedUCLB_phaseP
-- name    : MatchedUCLB_phaseP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:34.183502+00:00
-- url     : https://prove2.me/theorems/297d7b1c-54c7-4128-bc31-7bf707101416
-- title:
--   The regularized chain $P_j$
-- statement:
--   With the chain $Q$ and the next-phase coordinate $t'(x)=\langle v',x-c\rangle$, the **regularized chain** is
--
--   $$
--   P(x)=Q(x)+\frac{\alpha}{q}\,|t'(x)|^{q},\qquad \alpha=\lambda m^{1-3q/2}.
--   $$
--
--   The regularizer controls the chain from below along the next direction.
--
--   **Formalization Note** A phase is described by $m$ (the length of the family $u$), $\lambda$ (`lam`), $\tau=\tau_j$, $G=G_j$, $s'=s_{j+1}$ (`sN`), the center $c=c_j$, the starting direction $v=v_j$, the next direction $v'=v_{j+1}$ (`vN`) and the chain directions $u_0,\dots,u_{m-1}$ ($=u_{j,1},\dots,u_{j,m}$, indexed from $0$). The terminal phase $j=L-1$ is the case $v'=0$, $s'=0$, which is the page's convention $s_Lv_L:=0$.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Eq. (4.12b), p.8; Definition E.8, p.89

import Mathlib
import Definitions.Def_MatchedUCLB_chainQ
import Definitions.Def_MatchedUCLB_alphaC

namespace MatchedUCLB

/-- **The regularized chain `P_j`, ambient form.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Eq. (4.12b), p.8:
"`P_j(w, t_{j+1}) = Q_j(w) + (α/q)|t_{j+1}|^q`, `α = λm^{1−3q/2}`"; Definition E.8, p.89, with
`t_{j+1}(x) = ⟨v_{j+1}, x − c_j⟩`.

**Formalization Note.** One phase is described by its chain length `m` (through `u : Fin m → ℝ^d`),
the reals `lam` (= λ), `τ` (= τ_j), `G` (= G_j), `sN` (= s_{j+1}), and the points `c` (= c_j), `v`
(= v_j), `vN` (= v_{j+1}) and the chain directions `u i` (= u_{j,i+1}, 0-based). The terminal phase
`j = L − 1` ("we omit t_L, v_L and set s_L = t⋆_L = 0, with s_L v_L := 0", p.9) is the case
`vN = 0`, `sN = 0`. -/
noncomputable def phaseP (q lam : ℝ) {d m : ℕ} (c v vN : EuclideanSpace ℝ (Fin d)) (u : Fin m → EuclideanSpace ℝ (Fin d)) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  chainQ q lam c v u x + alphaC q m lam / q * |inner ℝ vN (x - c)| ^ q

end MatchedUCLB


