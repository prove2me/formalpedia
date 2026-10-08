-- Prove2me | Definitions.Def_BERicci_Tensor_Product
-- name    : BERicci_Tensor_Product
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T03:32:56.984931+00:00
-- url     : https://prove2.me/theorems/97685869-d1ef-4100-b3d4-25a4aade2528
-- title:
--   (5.1)–(5.2), p. 59 — the product space Z = X × Y with the ℓ² distance, m = m_X × m_Y, and the Cartesian Dirichlet form
-- statement:
--   Let $(X,\mathsf d_X,\mathfrak m_X)$ and $(Y,\mathsf d_Y,\mathfrak m_Y)$ be measure spaces carrying forms $\mathcal E^X$ on functions on $X$ and $\mathcal E^Y$ on functions on $Y$. The **product space** (5.1) is
--   $$Z:=X\times Y,\qquad \mathsf d((x,y),(x',y'))=\sqrt{\mathsf d_X^2(x,x')+\mathsf d_Y^2(y,y')},\qquad \mathfrak m:=\mathfrak m_X\times\mathfrak m_Y .$$
--   For a function $f$ on $Z$ and $z=(x,y)$ the **sections** are $f^y=f(\cdot,y)$, a function on $X$, and $f^x=f(x,\cdot)$, a function on $Y$. The **Cartesian Dirichlet form** (5.2) is
--   $$\mathcal E(f):=\int_Y\mathcal E^X(f^y)\,d\mathfrak m_Y(y)+\int_X\mathcal E^Y(f^x)\,d\mathfrak m_X(x),\qquad f\in L^2(Z,\mathfrak m),$$
--   and $\mathcal E(f)=+\infty$ for $f\notin L^2(Z,\mathfrak m)$.
--
--   These are the objects of the tensorization results of §5.1: the product of two $\mathrm{RCD}(K,\infty)$ spaces (Theorem 5.1), and the product of two Riemannian Energy measure spaces with $\mathrm{BE}(K,N_X)$, $\mathrm{BE}(K,N_Y)$ (Theorem 5.2).
--
--   **Formalization Note** The page prints the second term of (5.2) as $\mathcal E^X(f^x)$; since $f^x$ is a function on $Y$, and the proof of Lemma 5.3 writes $\mathcal E^Y(f^x,\varphi^x)$, the form here uses $\mathcal E^Y$. The carrier of $Z$ is `WithLp 2 (X × Y)`, whose metric is exactly the $\ell^2$ product distance of (5.1) (not the max-metric of `X × Y`), with its product topology and product σ-algebra; the measure is $\mathfrak m_X\times\mathfrak m_Y$ transported along `toLp`. The integrals are lower Lebesgue integrals of $[0,\infty]$-valued functions; the measurability of $y\mapsto\mathcal E^X(f^y)$, which the paper takes for granted, is not asserted.
-- source:
--   arXiv:1209.5786v4, §5.1, (5.1)–(5.2), p. 59; proof of Lemma 5.3, p. 62

import Mathlib
import Definitions.Def_BERicci_Gamma_Setting

namespace BERicci.Tensor

open MeasureTheory
open scoped ENNReal

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- The product measure `m = m_X × m_Y` of (5.1), p. 59, carried by `Z = WithLp 2 (X × Y)`, the
product `X × Y` whose metric is the `ℓ²` product distance `√(d_X² + d_Y²)` of (5.1). -/
noncomputable def prodMeasure (mX : Measure X) (mY : Measure Y) : Measure (WithLp 2 (X × Y)) :=
  (mX.prod mY).map (MeasurableEquiv.toLp 2 (X × Y))

/-- The section `f^y = f(·, y) : X → ℝ` of a function `f` on `Z = X × Y` (p. 59). -/
def secAtY (f : WithLp 2 (X × Y) → ℝ) (y : Y) : X → ℝ :=
  fun x => f (WithLp.toLp 2 (x, y))

/-- The section `f^x = f(x, ·) : Y → ℝ` of a function `f` on `Z = X × Y` (p. 59). -/
def secAtX (f : WithLp 2 (X × Y) → ℝ) (x : X) : Y → ℝ :=
  fun y => f (WithLp.toLp 2 (x, y))

open Classical in
/-- The Cartesian Dirichlet form (5.2), p. 59, on `L²(Z, m)`:
`E(f) = ∫_Y E_X(f^y) dm_Y(y) + ∫_X E_Y(f^x) dm_X(x)`, and `E(f) = +∞` for `f ∉ L²(Z, m)`.
The second term carries `E_Y` (the page prints `E_X(f^x)`; `f^x` is a function on `Y`, and the
proof of Lemma 5.3 uses `E_Y(f^x, φ^x)`). -/
noncomputable def cartesianForm (mX : Measure X) (mY : Measure Y)
    (EX : (X → ℝ) → ℝ≥0∞) (EY : (Y → ℝ) → ℝ≥0∞) (f : WithLp 2 (X × Y) → ℝ) : ℝ≥0∞ :=
  if MemLp f 2 (prodMeasure mX mY) then
    (∫⁻ y, EX (secAtY f y) ∂mY) + ∫⁻ x, EY (secAtX f x) ∂mX
  else ⊤

end BERicci.Tensor


