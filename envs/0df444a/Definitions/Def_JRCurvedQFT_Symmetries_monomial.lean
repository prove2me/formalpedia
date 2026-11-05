-- Prove2me | Definitions.Def_JRCurvedQFT_Symmetries_monomial
-- name    : JRCurvedQFT_Symmetries_monomial
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:02:41.897583+00:00
-- url     : https://prove2.me/theorems/c098e4dc-5efd-4e73-ac35-7cb2c9dd2e94
-- title:
--   Monomial $\Phi(f_1)\cdots\Phi(f_n)$ in the complex $L^2$
-- statement:
--   The monomial $A(\Phi)=\Phi(f_1)\cdots\Phi(f_n)$ as an element of the complex space $L^2(P;\mathbb C)$. For $n=0$ it is the constant function $1$.
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries, arXiv:0704.0052v1, §2.1, p. 3

import Mathlib
import Definitions.Def_JRCurvedQFT_Symmetries_EuclideanField

open scoped Manifold ContDiff ENNReal Topology InnerProductSpace
open Bundle MeasureTheory

namespace JRCurvedQFT.Symmetries

variable {d : ℕ} {M : Type} [EMetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) M]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The **monomial** `A(Φ) = Φ(f₁)…Φ(f_n)` as a vector of the complex `L²(P)`; the empty product
(`n = 0`) is the constant `1`.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries*, arXiv:0704.0052v1, §2.1, p. 3. -/
noncomputable def monomial (Φ : EuclideanField (d := d) M P) {n : ℕ}
    (f : Fin n → testFunctions (d := d) M) : Lp ℂ 2 P :=
  MemLp.toLp (fun w => ((∏ i, Φ.toFun (f i) w : ℝ) : ℂ)) (Φ.memLp_prod n f).ofReal

end JRCurvedQFT.Symmetries


