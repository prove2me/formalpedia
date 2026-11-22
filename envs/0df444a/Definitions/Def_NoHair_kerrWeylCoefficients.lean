-- Prove2me | Definitions.Def_NoHair_kerrWeylCoefficients
-- name    : NoHair_kerrWeylCoefficients
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-22T22:17:32.658417+00:00
-- url     : https://prove2.me/theorems/246153e8-5d85-4d39-8620-8e4a3a4466e6
-- title:
--   Explicit Kerr coefficients for radial Weyl reconstruction
-- statement:
--   Let $r=m+u$ and $c=z/u$ be the Boyer–Lindquist radius and polar cosine of a logarithmic Weyl point. Write $S=1-c^2$, $\Sigma=r^2+a^2c^2$, $D=u^2-(m^2-a^2)c^2$, and $N=(r^2+a^2)\Sigma+2mra^2S$. The angular shift and the exponential of twice the Weyl conformal exponent are
--   $$
--   W=-2mar/N,\qquad H=SN/D.
--   $$
--   With the axial norm $X$, the resulting local metric has Killing part $-\rho^2\,dt^2/X+X(d\varphi+W\,dt)^2$ and orbit part $(H/X)(d\rho^2+dz^2)$. The matrix is pulled back by the chart differential to the Kerr–Schild coordinate basis.
-- source:
--   S. Dain, A variational principle for stationary, axisymmetric solutions of Einstein’s equations, Appendix A, pp. 17–19, eqs. (90)–(94), (101)–(102), https://arxiv.org/abs/gr-qc/0508061. M. Visser, The Kerr spacetime: A brief introduction, eqs. (32)–(38), (53)–(57), https://arxiv.org/abs/0706.0622. P. T. Chruściel and J. L. Costa, §§6.4–6.7, including the normalized quadratures, https://arxiv.org/abs/0806.0016.

import Definitions.Def_NoHair_kerrWeylModel

noncomputable section

namespace NoHair.Weyl

/-- Boyer–Lindquist radius and polar cosine from logarithmic Weyl coordinates. -/
def kerrOrbitCoords (m a : ℝ) (p : OrbitPoint) : ℝ × ℝ :=
  let u := prolateRadius (Real.sqrt (m^2-a^2)) p
  (m+u,p.2/u)

/-- The numerator of the axial norm after removing the polar sine squared. -/
def kerrAxialNumerator (m a r c : ℝ) : ℝ :=
  (r^2+a^2)*(r^2+a^2*c^2)+2*m*r*a^2*(1-c^2)

/-- The Kerr angular shift on the Weyl half-plane. -/
def kerrWeylShift (m a : ℝ) (p : OrbitPoint) : ℝ :=
  let q := kerrOrbitCoords m a p
  (-(2*m*a*q.1)) / kerrAxialNumerator m a q.1 q.2

/-- The Kerr value of the exponential of twice the Weyl conformal exponent. -/
def kerrWeylScale (m a : ℝ) (p : OrbitPoint) : ℝ :=
  let q := kerrOrbitCoords m a p
  (1-q.2^2)*kerrAxialNumerator m a q.1 q.2 /
    ((q.1-m)^2-(m^2-a^2)*q.2^2)

/-- The pullback of the explicit Kerr Weyl–Papapetrou coefficients by a local
coordinate map. These coefficients involve only algebraic functions of the orbit point. -/
def kerrWeylMatrix (m a : ℝ) (C : E4 → E4) (y : E4) : Matrix (Fin 4) (Fin 4) ℝ :=
  let ρ := (C y) 2
  let p : OrbitPoint := (Real.log ρ, (C y) 3)
  let X := (kerrErnst m a).normSq p
  let W := kerrWeylShift m a p
  let b := fun (i j : Fin 4) => (fderiv ℝ C y (coordBasis j)) i
  fun i j => -(ρ^2/X)*b 0 i*b 0 j +
    X*(b 1 i+W*b 0 i)*(b 1 j+W*b 0 j) +
    kerrWeylScale m a p/X*(b 2 i*b 2 j+b 3 i*b 3 j)

end NoHair.Weyl


