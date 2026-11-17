-- Prove2me | Definitions.Def_TiltedCvx_Supplement_classZeroPlus
-- name    : TiltedCvx_Supplement_classZeroPlus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:23:01.067621+00:00
-- url     : https://prove2.me/theorems/0dc1aa48-456e-4e1a-b204-64f6606acff0
-- title:
--   The class $\mathcal F^{0^+}$ (Definition 12)
-- statement:
--   $\mathcal F^{0^+}$ is the class of proper lower semicontinuous $0^+$–tilted convex functions $f:\mathbb R^d\to\overline{\mathbb R}$. It sits between the positive-parameter classes and $\mathcal F^0$:
--
--   $$
--   \bigcup_{0<\theta\le1}\mathcal F^\theta\ \subseteq\ \mathcal F^{0^+}\ \subseteq\ \mathcal F^0 ,
--   $$
--
--   and among radially continuous functions it is the class of pseudoconvex functions (Theorem 3).
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Definition 12, p.17

import Mathlib
import Definitions.Def_TiltedCvx_IsProper
import Definitions.Def_TiltedCvx_Supplement_TiltedConvexZeroPlus

namespace TiltedCvx.Supplement

/-- **The class `F^{0+}`.** Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472, Definition 12,
p.17: `F^{0+}` is the class of proper lsc 0⁺–tilted convex functions `f : ℝ^d → ℝ̄`. -/
def classZeroPlus {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    Set (E → EReal) :=
  {f | TiltedCvx.IsProper f ∧ LowerSemicontinuous f ∧ TiltedConvexZeroPlus f}

end TiltedCvx.Supplement


