-- Prove2me | Definitions.Def_NoHair_kerrWeylModel
-- name    : NoHair_kerrWeylModel
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-22T21:19:40.251189+00:00
-- url     : https://prove2.me/theorems/8210884e-5105-4313-ae7b-c98738288b0d
-- title:
--   Kerr comparison potentials, axis data, and normalized Weyl charts
-- statement:
--   In logarithmic Weyl coordinates $s=\log\rho$ and $z$, set $\ell=\sqrt{m^2-a^2}$. The Boyer–Lindquist radius and polar cosine follow from the two endpoint distances:
--   $$
--   R=\tfrac12\!\left(\sqrt{\rho^2+(z-\ell)^2}+\sqrt{\rho^2+(z+\ell)^2}\right),
--   \qquad r=m+R,\quad c=z/R .
--   $$
--   Put $S=1-c^2$ and $\Sigma=r^2+a^2c^2$. The reference Ernst potentials are
--   $$
--   X=S\left(r^2+a^2+\frac{2mra^2S}{\Sigma}\right),\qquad
--   Y=2ma(3c-c^3)+\frac{2ma^3cS^2}{\Sigma}.
--   $$
--   The chosen twist sign agrees with the outward radial equation for the angular shift. The upper and lower axis traces are normalized to $4J$ and $-4J$. Normalized local charts use Boyer–Lindquist time and azimuth differentials and Weyl radius and height. Metric reconstruction in these charts is expressed for one metric at a time.
-- source:
--   S. Dain, A variational principle for stationary, axisymmetric solutions of Einstein’s equations, Appendix A, pp. 17–19, eqs. (90)–(94), (101)–(102), https://arxiv.org/abs/gr-qc/0508061. M. Visser, The Kerr spacetime: A brief introduction, eqs. (32)–(38), (53)–(57), https://arxiv.org/abs/0706.0622. P. T. Chruściel and J. L. Costa, §§6.4–6.7, including the normalized quadratures, https://arxiv.org/abs/0806.0016.

import Definitions.Def_NoHair_weylPapapetrou

noncomputable section

open Set Filter Topology

namespace NoHair.Weyl

/-- The mean of the distances from a Weyl point to the two endpoints of the horizon interval. -/
def prolateRadius (ℓ : ℝ) (p : OrbitPoint) : ℝ :=
  (Real.sqrt (Real.exp (2*p.1) + (p.2-ℓ)^2) +
   Real.sqrt (Real.exp (2*p.1) + (p.2+ℓ)^2)) / 2

def kerrAxialNorm (m a r c : ℝ) : ℝ :=
  (1-c^2) * (r^2 + a^2 + 2*m*r*a^2*(1-c^2) / (r^2+a^2*c^2))

def kerrAxialTwist (m a r c : ℝ) : ℝ :=
  2*m*a*(3*c-c^3) + 2*m*a^3*c*(1-c^2)^2 / (r^2+a^2*c^2)

/-- The Kerr axial norm and twist on the Weyl half-plane. The twist is normalized
to opposite values on the two exterior pieces of the axis. -/
def kerrErnst (m a : ℝ) : ErnstPotentials :=
  let ℓ := Real.sqrt (m^2-a^2)
  let R := prolateRadius ℓ
  let r := fun p => m + R p
  let c := fun p : OrbitPoint => p.2 / R p
  ⟨fun p => kerrAxialNorm m a (r p) (c p), fun p => kerrAxialTwist m a (r p) (c p)⟩

/-- The normalized twist takes values ±4J on the two axis components. A horizon of
positive Weyl length has positive limiting axial norm in the interior of its interval. -/
def HasAxisData (u : ErnstPotentials) (ℓ J : ℝ) : Prop :=
  (∀ z : ℝ, ℓ < z →
    Tendsto (fun s : ℝ => u.normSq (s,z)) atBot (𝓝 0) ∧
    Tendsto (fun s : ℝ => u.twist (s,z)) atBot (𝓝 (4*J))) ∧
  (∀ z : ℝ, z < -ℓ →
    Tendsto (fun s : ℝ => u.normSq (s,z)) atBot (𝓝 0) ∧
    Tendsto (fun s : ℝ => u.twist (s,z)) atBot (𝓝 (-(4*J)))) ∧
  ∀ z : ℝ, |z| < ℓ → ∃ X : ℝ, 0 < X ∧
    Tendsto (fun s : ℝ => u.normSq (s,z)) atBot (𝓝 X)

def offAxisExterior (m a : ℝ) : Set E4 :=
  {y | y ∈ kerrNewmanDOC m a 0 ∧ (y 1 ≠ 0 ∨ y 2 ≠ 0)}

def kerrDelta (m a r : ℝ) : ℝ := r^2 - 2*m*r + a^2

/-- Local Boyer–Lindquist time and azimuth together with Weyl radius and height,
specified on the Kerr–Schild coordinate space. Time and azimuth may be translated. -/
structure IsKerrWeylChart (m a : ℝ) (V : Set E4) (c : E4 → E4) : Prop where
  source_open : IsOpen V
  off_axis : V ⊆ offAxisExterior m a
  image_open : IsOpen (c '' V)
  diffeo : IsDiffeoOnto c V (c '' V)
  pos : ∀ y ∈ V, 0 < (c y) 2
  orbit : ∀ y ∈ V,
    let r := ksRadius a y
    (c y) 2 = Real.sqrt (kerrDelta m a r) * Real.sqrt (1-(y 3 / r)^2) ∧
    (c y) 3 = (r-m) * (y 3 / r)
  killing_coords : ∀ y ∈ V, ∀ i : Fin 4,
    let r := ksRadius a y
    let Δ := kerrDelta m a r
    let dr := coordPartial (ksRadius a) i y
    let e := coordBasis i
    let dc := fderiv ℝ c y e
    dc 0 = e 0 - (2*m*r/Δ)*dr ∧
    dc 1 = (y 1 * e 2 - y 2 * e 1) / (y 1 ^ 2 + y 2 ^ 2)
      - (2*m*r*a / (Δ*(r^2+a^2)))*dr

/-- A single continuous metric is reconstructed in each normalized local Weyl chart. -/
structure IsWeylRepresentation (m a : ℝ) (G : E4 → Matrix (Fin 4) (Fin 4) ℝ)
    (u : ErnstPotentials) : Prop where
  quadratures : HasRadialQuadratures u
  continuous : ContinuousOn G (kerrNewmanDOC m a 0)
  coefficients : ∀ (V : Set E4) (c : E4 → E4), IsKerrWeylChart m a V c →
    ∀ y ∈ V, G y = metricInChart u c y

end NoHair.Weyl


