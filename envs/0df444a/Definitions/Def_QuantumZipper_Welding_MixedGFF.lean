-- Prove2me | Definitions.Def_QuantumZipper_Welding_MixedGFF
-- name    : QuantumZipper_Welding_MixedGFF
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T09:17:22.943973+00:00
-- url     : https://prove2.me/theorems/c904ad92-55b4-4599-ba27-80be2512ca59
-- title:
--   GFF on $D\subset\mathbb H$ with zero boundary conditions on $\partial D\setminus\mathbb R$ and free on $\partial D\cap\mathbb R$
-- statement:
--   This file supplies the domain and covariance of Proposition 1.6.
--
--   1. **Segment domains.** $D\subset\mathbb H$ is a bounded open connected set whose boundary meets $\mathbb R$ in a segment $[c,d]$ with $c<d$. The reflected set $D^*=D\cup(c,d)\cup\overline{D}^{\,*}$ is open, where $\overline D^{\,*}$ is the complex conjugate of $D$.
--   2. **Dirichlet Green's function (p. 38).** On a bounded domain $U$, $G_U(x,y)=-\log|y-x|-\tilde G_x(y)$, where $\tilde G_x$ is the harmonic extension of $y\mapsto-\log|y-x|$ from $\partial U$. Equivalently, $y\mapsto G_U(x,y)+\log|y-x|$ is harmonic on $U$ and $G_U(x,y)\to0$ at the boundary.
--   3. **Mixed Green's function.** By reflection, $G_D(x,y)=G_{D^*}(x,y)+G_{D^*}(x,\bar y)$. It vanishes on $\partial D\setminus\mathbb R$, has zero normal derivative on $(c,d)$, and has a $-\log|x-y|$ singularity. It is the covariance kernel of the GFF with zero boundary conditions on $\partial D\setminus\mathbb R$ and free boundary conditions on $\partial D\cap\mathbb R$.
--   4. **Index class.** The admissible measures carried by a compact subset of $D\cup(a,b)$: every circle in $D$, and every small semicircle centred in $(a,b)$.
--
--   For $D=\mathbb H$ the reflection formula gives $G^{\mathbb H_F}$ (the method of images of §3.2).
--
--   **Formalization Note** The openness of $D^*$ makes "free boundary conditions on $\partial D\cap\mathbb R$" meaningful: every point of $(c,d)$ has a half-disc neighbourhood in $D$. It excludes only degenerate domains, such as slits ending on $\mathbb R$. The harmonic extension exists for Dirichlet-regular domains and is unique by the maximum principle.
-- source:
--   Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2, Proposition 1.6, p. 24; §3.1.2, p. 38 (Green's function); §3.2, p. 40 (reflection)

import Mathlib
import Definitions.Def_QuantumZipper_Welding_Setting

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped ComplexConjugate

namespace QuantumZipper.Welding

/-! # The GFF on `D ⊂ ℍ` with zero boundary conditions on `∂D \ ℝ` and free boundary conditions on
`∂D ∩ ℝ` (arXiv:1012.4797v2, Proposition 1.6, p. 24) -/

/-- The open real segment `{x + 0i : c < x < d}` as a subset of `ℂ`. -/
def realSegment (c d : ℝ) : Set ℂ := {z : ℂ | z.im = 0 ∧ c < z.re ∧ z.re < d}

/-- `D` is a bounded subdomain of `ℍ` whose boundary meets `ℝ` in the segment `[c, d]`, `c < d`
(Proposition 1.6, p. 24: "a bounded subdomain of `ℍ` for which `∂D ∩ ℝ` is a segment of positive
length"), and across whose real boundary the free boundary condition can be imposed: the reflected
set `D ∪ (c, d) ∪ D̄*` (`D̄*` the complex conjugate of `D`) is open.

**Formalization Note** The openness of the reflected set says that each point of the open segment
`(c, d)` has a half-disc neighbourhood in `D`; this is what "free boundary conditions on `∂D ∩ ℝ`"
presupposes, and it excludes only degenerate domains (e.g. slits ending on `ℝ`). Disclosed reading. -/
def IsSegmentDomain (D : Set ℂ) (c d : ℝ) : Prop :=
  IsOpen D ∧ IsConnected D ∧ Bornology.IsBounded D ∧ D ⊆ Hplane ∧ c < d ∧
    frontier D ∩ {z : ℂ | z.im = 0} = {z : ℂ | z.im = 0 ∧ c ≤ z.re ∧ z.re ≤ d} ∧
    IsOpen (D ∪ realSegment c d ∪ (conj '' D))

/-- The reflected domain `D* = D ∪ (c, d) ∪ D̄*`. -/
def reflectedDomain (D : Set ℂ) (c d : ℝ) : Set ℂ :=
  D ∪ realSegment c d ∪ (conj '' D)

/-- **Dirichlet Green's function** of a bounded domain `U` (arXiv:1012.4797v2, §3.1.2, p. 38):
`G(x, y) = −log |y − x| − G̃_x(y)`, where `G̃_x` is the harmonic extension to `U` of the boundary
function `y ↦ −log |y − x|`. Stated as: for each `x ∈ U`, `y ↦ G(x, y) + log |y − x|` is harmonic on
`U`, and `G(x, y) → 0` as `y → p` within `U` for every boundary point `p`.

**Formalization Note** On a bounded domain the harmonic extension is unique (maximum principle), so
`G` is determined on `U × U` (the value `G(x, x)` is fixed by harmonicity of the regular part); it
exists for Dirichlet-regular `U` (e.g. Jordan domains). -/
def IsDirichletGreen (U : Set ℂ) (G : ℂ → ℂ → ℝ) : Prop :=
  ∀ x ∈ U, InnerProductSpace.HarmonicOnNhd (fun y => G x y + Real.log ‖y - x‖) U ∧
    ∀ p ∈ frontier U, Tendsto (G x) (𝓝[U] p) (𝓝 0)

/-- **Mixed Green's function** on `D`: Dirichlet on `∂D \ ℝ`, Neumann on `∂D ∩ ℝ`, obtained by
reflection, `G_D(x, y) = G_{D*}(x, y) + G_{D*}(x, ȳ)` with `G_{D*}` the Dirichlet Green's function
of the reflected domain. It is the covariance kernel of the GFF of Proposition 1.6 (zero boundary
conditions on `∂D \ ℝ`, free on `∂D ∩ ℝ`).

**Formalization Note** For `D = ℍ` (no Dirichlet part, `G_{ℂ} = −log |x − y|`) the same formula is
`G^{ℍ_F}(x, y) = −log |x − y| − log |x − ȳ|`, the free boundary Green's function (3.6); this is the
method of images of §3.2, p. 40. -/
def mixedGreen (Gstar : ℂ → ℂ → ℝ) (x y : ℂ) : ℝ :=
  Gstar x y + Gstar x (conj y)

/-- The index class of pairings for a field on `D` whose mean function is only continuous on
`D ∪ (a, b)`: admissible measures carried by a compact subset of `D ∪ (a, b)` (every circle in `D`,
and every small semicircle centred at a point of `(a, b)`, is of this kind). -/
def IsAdmissibleIn (D : Set ℂ) (a b : ℝ) (μ : Measure ℂ) : Prop :=
  IsAdmissible μ ∧ ∃ K : Set ℂ, IsCompact K ∧ K ⊆ D ∪ realSegment a b ∧ μ Kᶜ = 0

end QuantumZipper.Welding


