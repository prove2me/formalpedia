-- Prove2me | Definitions.Def_DelaunayStretch_SigmaSet
-- name    : DelaunayStretch_SigmaSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:51:54.178262+00:00
-- url     : https://prove2.me/theorems/ea227ffb-55d4-438b-a8ca-b871c71f9fd8
-- title:
--   Angular coordinates $(\gamma,\varphi,\theta,\psi)$ and the sets $\Omega$, $\Sigma$
-- statement:
--   Let $s=(O,G,\delta)$ be a gate state, where $O$ has center $o$ and radius $r$, and $G=[a_G,b_G]$ has midpoint $M$. Let $\nu=e(\varphi)$, $\varphi\in(-\pi/2,\pi/2)$, be the unit normal of $G$ with positive $x$-component, and write $o=M+X\nu$. The **angular coordinates** of $s$ are $(\gamma,\varphi,\theta,\psi)$, where $\gamma\in(-\pi/2,\pi/2)$ with $\sin\gamma=y(o)/r$, $\theta\in(0,\pi)$ with $\cos\theta=X/r$ and $\sin\theta=|G|/(2r)$, and $\psi=\varphi+\delta/(2r)$. Let
--
--   $$
--   \Omega=\{(\gamma,\varphi,\theta)\in\mathbb R^3:\ |\gamma-\varphi|<\theta<\pi-|\gamma+\varphi|\},\qquad
--   \Sigma=\{(\gamma,\varphi,\theta,\psi)\in\mathbb R^4:\ (\gamma,\varphi,\theta)\in\Omega,\ |\psi-\varphi|\le\sin\theta\}.
--   $$
--
--   The angular coordinates describe a gate state up to translation along the $x$-axis and scaling, and they are the variables of the function $H$ of the potential method.
--
--   **Formalization Note** $\varphi=\arg(-i(a_G-b_G))$, $\gamma=\arcsin(y(o)/r)$, $X=\langle o-M,\nu\rangle$, $\theta=\arccos(X/r)$; for a gate state $X^2+|G|^2/4=r^2$, so $\sin\theta=|G|/(2r)$ holds as well. Points of $\mathbb R^4$ are tuples $(\gamma,\varphi,\theta,\psi)$, and $\Omega\times\mathbb R$ is the set of tuples whose first three entries lie in $\Omega$. The same module defines the map $p\mapsto kp+t$ ($k>0$, $t\in\mathbb R$) acting on gate states (center, gate ends, radius and $\delta$), used in Lemma 4.2.
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026, sha256 49ad9397…f824), Definition 4.1, pp.21–22

import Mathlib
import Definitions.Def_DelaunayStretch_GateState

namespace DelaunayStretch

open Complex

/-- Points of `ℝ⁴`, written `z = (γ, φ, θ, ψ)`: `z.1 = γ`, `z.2.1 = φ`, `z.2.2.1 = θ`,
`z.2.2.2 = ψ`. -/
abbrev R4 := ℝ × ℝ × ℝ × ℝ

/-- `Ω = {(γ, φ, θ) ∈ ℝ³ : |γ − φ| < θ < π − |γ + φ|}` (Definition 4.1, p.22). -/
def OmegaSet : Set (ℝ × ℝ × ℝ) :=
  {p | |p.1 - p.2.1| < p.2.2 ∧ p.2.2 < Real.pi - |p.1 + p.2.1|}

/-- `Ω × ℝ ⊆ ℝ⁴`: the points `(γ, φ, θ, ψ)` with `(γ, φ, θ) ∈ Ω`. -/
def OmegaTimesR : Set R4 := {z | (z.1, z.2.1, z.2.2.1) ∈ OmegaSet}

/-- `Σ = {(γ, φ, θ, ψ) ∈ ℝ⁴ : (γ, φ, θ) ∈ Ω, |ψ − φ| ≤ sin θ}` (Definition 4.1, p.22).

Mo, Cheng, Ding, *The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined*,
preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026),
Definition 4.1, pp.21–22. -/
def SigmaSet : Set R4 :=
  {z | z ∈ OmegaTimesR ∧ |z.2.2.2 - z.2.1| ≤ Real.sin z.2.2.1}

namespace GateState

/-- The midpoint `M` of the gate `G = [aG, bG]`. -/
noncomputable def mid (s : GateState) : ℂ := (s.aG + s.bG) / 2

/-- The unit normal `ν = e(φ)` of `G` with positive `x`-component:
`ν = −i (aG − bG)/‖aG − bG‖` (Definition 4.1, p.21). -/
noncomputable def normal (s : GateState) : ℂ := (-I) * (s.aG - s.bG) / ((dist s.aG s.bG : ℝ) : ℂ)

/-- The number `X` with `o = M + X ν` (Definition 4.1, p.21): `X = ⟨o − M, ν⟩`. -/
noncomputable def offset (s : GateState) : ℝ :=
  ((s.O.center - s.mid) * (starRingEnd ℂ) s.normal).re

/-- The angular coordinate `γ ∈ (−π/2, π/2)`, `sin γ = y(o)/r` (Definition 4.1, p.21). -/
noncomputable def gammaCoord (s : GateState) : ℝ := Real.arcsin (s.O.center.im / s.O.radius)

/-- The angular coordinate `φ ∈ (−π/2, π/2)`, `ν = e(φ)` (Definition 4.1, p.21). -/
noncomputable def phiCoord (s : GateState) : ℝ := Complex.arg ((-I) * (s.aG - s.bG))

/-- The angular coordinate `θ ∈ (0, π)`, `cos θ = X/r` and `sin θ = |G|/(2r)`
(Definition 4.1, p.21). -/
noncomputable def thetaCoord (s : GateState) : ℝ := Real.arccos (s.offset / s.O.radius)

/-- The angular coordinate `ψ = φ + δ/(2r)` (Definition 4.1, p.21). -/
noncomputable def psiCoord (s : GateState) : ℝ := s.phiCoord + s.δ / (2 * s.O.radius)

/-- The **angular coordinates** `(γ, φ, θ, ψ)` of a gate state `s = (O, G, δ)`
(Definition 4.1, p.21): `O` has center `o` and radius `r`, `G = [aG, bG]` has midpoint `M` and
unit normal `ν = e(φ)` with positive `x`-component, `o = M + Xν`, `sin γ = y(o)/r`,
`cos θ = X/r`, `sin θ = |G|/(2r)` and `ψ = φ + δ/(2r)`.

**Formalization Note** `φ = arg(−i(aG − bG))`, which lies in `(−π/2, π/2)` because
`y(aG) > y(bG)`; `γ = arcsin(y(o)/r)`; `θ = arccos(X/r)`. For a gate state
`X² + |G|²/4 = r²`, so this `θ` also satisfies `sin θ = |G|/(2r)`. -/
noncomputable def angularCoords (s : GateState) : R4 :=
  (s.gammaCoord, s.phiCoord, s.thetaCoord, s.psiCoord)

/-- The image of `s` under the map `p ↦ k p + t` of the plane (`k > 0`, `t ∈ ℝ`), the
composition of a translation along the `x`-axis and a scaling of ratio `k` centered at a point
of the `x`-axis: the center, the gate ends, the radius and `δ` are transformed accordingly. -/
noncomputable def scaleTranslate (k t : ℝ) (s : GateState) : GateState :=
  ⟨⟨(k : ℂ) * s.O.center + t, k * s.O.radius⟩, (k : ℂ) * s.aG + t, (k : ℂ) * s.bG + t, k * s.δ⟩

end GateState

end DelaunayStretch


