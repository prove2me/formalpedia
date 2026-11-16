-- Prove2me | Definitions.Def_FasterExactColoring_ThreeColor_Supplement_Measure
-- name    : FasterExactColoring_ThreeColor_Supplement_Measure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:48:31.191582+00:00
-- url     : https://prove2.me/theorems/4c517ce2-8b60-4389-a23a-ada1054b9fde
-- title:
--   The full measure and every Appendix D constraint
-- statement:
--   The five stored real weights are $\omega_1,\omega_2,\omega_{c3},\omega_{k3},\omega_{k4}$; the remaining degree weights are $\omega_0=0$ and $\omega_i=1$ for $i\ge3$. All weights are nonnegative. If $\mathcal C(P)$ comprises components of $G[U]$ other than complete triangles and four-cliques, the measure is
--   $$\mu(P)=\omega_{c3}|S|+\omega_{k3}n_{K_3}+\omega_{k4}n_{K_4}
--    +\sum_{C\in\mathcal C(P)}\sum_{v\in C}\omega_{\deg_C(v)}.$$
--
--   The linear constraints are $0\le\omega_{c3}\le\omega_1\le\omega_2\le1$, $1-\omega_2\le\omega_2-\omega_1\le\omega_1$, $\omega_{k3}\le3\omega_2$, and $\omega_{k4}\le4$. Every multiset $D$ in Table 1 imposes
--   $$\sum_{(\alpha,\beta)\in D}\alpha r^{-\beta}\le1.$$
--   All five instances $j=4,\ldots,8$ of row (7a) are included, using $(M_4,\ldots,M_8)=(2,5,5,7,10)$ and $\delta_\omega=\omega_2-\omega_{c3}$. Identical rows (13)/(14) and (17a)/(18b) share a constraint. These are conditional premises for the branching and composition lemmas, with no feasibility assumption in any headline theorem.
-- source:
--   Ryosuke Yamano, Tetsuo Shibuya, STOC 2027 submission #727 (October 2026), Section 5.7, Appendix D, Eqs. (10)–(11), Table 1, pp. 14–15, 23–24 (PDF pp. 16–17, 25–26)

import Mathlib
import Definitions.Def_FasterExactColoring_ThreeColor_Supplement_Restricted

set_option autoImplicit false

namespace FasterExactColoring.ThreeColor.Supplement

structure Weights where
  one : ℝ
  two : ℝ
  c3 : ℝ
  k3 : ℝ
  k4 : ℝ

def Weights.vertex (w : Weights) (i : ℕ) : ℝ :=
  if i = 0 then 0 else if i = 1 then w.one else if i = 2 then w.two else 1

def Weights.linearConstraints (w : Weights) : Prop :=
  0 ≤ w.c3 ∧ w.c3 ≤ w.one ∧ w.one ≤ w.two ∧ w.two ≤ 1 ∧
  1-w.two ≤ w.two-w.one ∧ w.two-w.one ≤ w.one ∧
  0 ≤ w.k3 ∧ 0 ≤ w.k4 ∧ w.k3 ≤ 3*w.two ∧ w.k4 ≤ 4

/-- Every Table 1 row, including all five j instances of (7a).
Repeated identical rows (13)/(14) and (17a)/(18b) share one constraint. -/
def branchingRows (w : Weights) : List (List (ℝ × ℝ)) :=
  let δ := w.two-w.c3
  [[(2,2*w.one-w.c3)],
   [(2,4*δ+2*w.c3)], [(5,5*δ+2*w.c3)], [(5,6*δ+2*w.c3)],
   [(7,7*δ+3*w.c3)], [(10,8*δ+3*w.c3)],
   [(1,3*δ+w.c3),(1,4*δ+w.c3),(1,5*δ+w.c3)],
   [(1,1+2*δ),(2,1+3*δ)],
   [(2,1+2*δ),(1,1+4*δ)],
   [(1,2+δ-w.c3),(1,1+3*δ),(1,2+3*δ-w.c3)],
   [(1,2+δ-w.c3),(1,1+3*δ),(1,2+2*δ-w.c3)],
   [(1,2+5*δ+w.c3-2*w.one),(1,2+2*δ+w.c3-w.k3)],
   [(1,2+4*δ+w.c3-2*w.one),(2,2+4*δ+2*w.c3-w.k3)],
   [(1,4+2*δ-w.c3-2*w.one),(1,2+2*δ-w.c3),(2,3+4*δ-2*w.one)],
   [(1,1+5*δ),(1,1-w.c3)],
   [(1,4-3*w.c3),(3,5-4*w.c3)],
   [(1,4-3*w.c3),(1,5-w.c3-w.k4)],
   [(2,5-4*w.c3),(1,6-2*w.c3-w.k4)],
   [(2,4-3*w.c3),(1,5-4*w.c3),(1,6-4*w.c3)],
   [(2,4-3*w.c3),(1,5-4*w.c3),(2,8-6*w.c3)],
   [(3,4-3*w.c3)],
   [(3,4-3*w.c3),(1,7-5*w.c3)],
   [(2,4-3*w.c3+6*(1-w.two)),(1,5-4*w.c3+3*(1-w.two)),(1,6-5*w.c3)],
   [(3,5-4*w.c3),(1,6-5*w.c3),(1,7-5*w.c3)],
   [(2,5-4*w.c3),(2,6-5*w.c3),(1,7-6*w.c3)]]

noncomputable def appendixD (r : ℝ) (w : Weights) : Prop :=
  w.linearConstraints ∧
  ∀ D ∈ branchingRows w, (D.map (fun p => p.1*r^(-p.2))).sum ≤ 1

noncomputable def measure {n : ℕ} (w : Weights) (P : Restricted n) : ℝ := by
  classical
  exact w.c3*P.S.card + w.k3*P.nClique 3 + w.k4*P.nClique 4 +
    ∑ C ∈ P.components.filter (fun C => ¬ clique P.G C 3 ∧ ¬ clique P.G C 4),
      ∑ v ∈ C, w.vertex (degreeIn P.G C v)

end FasterExactColoring.ThreeColor.Supplement


