-- Prove2me | Definitions.Def_FasterExactColoring_ThreeColor_FinalCertificate
-- name    : FasterExactColoring_ThreeColor_FinalCertificate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:11:51.977365+00:00
-- url     : https://prove2.me/theorems/d01038e0-edbf-45b2-977b-1c4da7ca1d75
-- title:
--   Appendix C matrices and exact deterministic dual data
-- statement:
--   The final deterministic analysis fixes $\varepsilon=10^{-9}$ and uses parameter order $(p,q,r,s,t,d,c,m)$. The structural matrix $A$, normalization vector $u$, exponent matrix $B_3$, and offset $b_3$ are the concrete matrices and vectors printed in Appendix C. Normalization is available only when $n>0$.
--
--   The exact rational dual data are
--   $$z=0.277893717,\qquad\eta=(0.872081561,0.108128455,0.019789984),$$
--   $$\xi=(0.006293660,0.207626932,0,0.001223624,0.000305899,0.000000010,0.016951940).$$
--   Real logarithms are applied only to the positive source bases $2,3,\Lambda$ and $3\Lambda^{-4}$. The tree and path rows include the logarithm multiplying the entire exponent, as the rendered PDF specifies.
--
--   These definitions expose the exact data for a future certified arithmetic proof. They assert neither feasibility nor optimality; the goal does not assume a certificate or an optimizer guarantee. The empty graph is handled without normalization.
-- source:
--   Ryosuke Yamano, Tetsuo Shibuya, STOC 2027 submission #727 (October 2026), Appendix C, pp. 21–23 (PDF pp. 23–25)

import Mathlib
import Definitions.Def_FasterExactColoring_ThreeColor_RuntimeBounds

namespace FasterExactColoring.ThreeColor

/-- Appendix C fixes epsilon only for the final bound. -/
noncomputable def finalEpsilon : ℝ := 1 / 10^9

noncomputable def normalizedCounts (n : ℕ) (_hn : 0 < n) (a : Counts) : Fin 8 → ℝ :=
  fun i => ![(a.p:ℝ),a.q,a.r,a.s,a.t,a.d,a.c,a.m] i / n

noncomputable def constraintMatrix : Matrix (Fin 7) (Fin 8) ℝ :=
  !![0,0,0,-1,0,1,0,0;
     4,2,-1,0,0,0,0,0;
     0,0,-2,1,0,0,0,0;
     -8,0,0,0,0,1,0,0;
     0,0,0,-2,1,-1,0,0;
     0,0,0,0,-1,-1,1,0;
     0,0,-1,0,0,0,0,2]

noncomputable def normalizationRow : Fin 8 → ℝ := ![1,1,1,1,1,0,0,0]

noncomputable def exponentMatrix : Matrix (Fin 3) (Fin 8) ℝ :=
  let l := Real.log cspBase
  let h := Real.log (3*cspBase^(-4:ℤ))
  !![Real.log 3,Real.log 2,0,l,l+h/10,h/10,19*h/660,0;
     Real.log 3,Real.log 2,Real.log 3/3,0,Real.log 3/6,Real.log 3/6,0,Real.log 3/3;
     Real.log 3,Real.log 2,Real.log 2,0,0,0,Real.log 3/6,Real.log 3-2*Real.log 2]

noncomputable def exponentOffset : Fin 3 → ℝ :=
  ![0,finalEpsilon*Real.log 3,finalEpsilon*Real.log 3]

noncomputable def dualZ : ℝ := 277893717 / 10^9
noncomputable def dualEta : Fin 3 → ℝ :=
  ![872081561/10^9,108128455/10^9,19789984/10^9]
noncomputable def dualXi : Fin 7 → ℝ :=
  ![6293660/10^9,207626932/10^9,0,1223624/10^9,305899/10^9,10/10^9,16951940/10^9]

end FasterExactColoring.ThreeColor


