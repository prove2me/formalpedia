-- Prove2me | Definitions.Def_PolyhedralPacking1261_Packing_Supplement_Kakeya
-- name    : PolyhedralPacking1261_Packing_Supplement_Kakeya
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T06:36:31.239653+00:00
-- url     : https://prove2.me/theorems/41ea2c73-f117-4326-98e7-1cd2cb6665a9
-- title:
--   Euclidean tubes, unoriented angles, the Kakeya maximal function and the maximal estimate (Theorem 18)
-- statement:
--   Work in Euclidean three-space $E_3=\mathbb R^3$ with the Euclidean norm $\|\cdot\|$ and Lebesgue measure $\mathrm{vol}$. For $\delta>0$, a direction $v$ and a center $x$, the **tube** $T_\delta(v,x)$ is the open $\delta$-neighbourhood of the unit segment $\{x+tv : |t|\le 1/2\}$:
--
--   $$T_\delta(v,x)=\{y : \exists\, t\in[-\tfrac12,\tfrac12],\ \|y-(x+tv)\|<\delta\},$$
--
--   so the round end caps are included. The **unoriented angle** between $v$ and $w$ is the smaller of the angle between $v$ and $w$ and the angle between $v$ and $-w$.
--
--   For a function $f:\mathbb R^3\to\mathbb R$ and a direction $\omega$, the **Kakeya maximal function** is
--
--   $$K_\delta f(\omega)=\sup_{x\in\mathbb R^3}\frac{1}{\mathrm{vol}(T_\delta(\omega,x))}\int_{T_\delta(\omega,x)}|f|\in[0,\infty].$$
--
--   The sphere $S^2$ carries its unnormalised surface-area measure $\sigma$ (total mass $4\pi$). The **Kakeya maximal estimate** (quoted in the paper as Theorem 18, from OpenAI's preprint, Corollary 9.1) is the proposition: there is $C_K\ge1$ such that for all $0<\delta\le1$ and all $f\in L^3(\mathbb R^3)$,
--
--   $$\|K_\delta f\|_{L^3(S^2,\sigma)}\le C_K\,\log^{4/3}(2/\delta)\,\|f\|_{L^3(\mathbb R^3)}.$$
--
--   It is a definition of a proposition, used only as a hypothesis; it is not asserted.
--
--   These objects are shared by the tube-union statements (Theorem 4, Lemma 19), the conditional clause of Theorem 2 and the tube containment of Lemma 11.
--
--   **Formalization Note** $E_3$ is `EuclideanSpace ℝ (Fin 3)`. The supremum and the integrals are in $[0,\infty]$ (lower Lebesgue integrals); $\sigma$ is Mathlib's `Measure.toSphere` of Lebesgue measure, whose total mass is $3\cdot\mathrm{vol}(B(0,1))=4\pi$. $L^3$ membership is `MemLp f 3`.
-- source:
--   Simon Bartlmae, Anders Aamand, Mikkel Abrahamsen, Polylogarithmic Approximation for Packing Convex Polyhedra, STOC 2027 submission #1261 (October 2026), canonical PDF SHA-256 b915da2d5fece730ea9946885b05ad09e10e575374e6a1df96e8a6149cb0e67e, Theorem 4 and §1.1 tube definition, PDF pp.4–5 (printed pp.3–4); Theorem 18 and the Kakeya maximal function, Appendix B.1, PDF pp.26–27 (printed pp.25–26)

import Mathlib

set_option autoImplicit false

open MeasureTheory

namespace PolyhedralPacking1261.Packing.Supplement

/-- Euclidean three-space: the norm is the Euclidean norm and `volume` is
Lebesgue measure. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The open `δ`-neighbourhood, in the Euclidean distance, of the unit segment
`{x + t v : |t| ≤ 1/2}`. Round end caps are included. -/
def tube (δ : ℝ) (v x : E3) : Set E3 :=
  {y | ∃ t : ℝ, |t| ≤ (1 / 2 : ℝ) ∧ dist y (x + t • v) < δ}

/-- The unoriented angle: the smaller of the angle between `v` and `w` and the
angle between `v` and `-w`. -/
noncomputable def unorientedAngle (v w : E3) : ℝ :=
  min (InnerProductGeometry.angle v w) (InnerProductGeometry.angle v (-w))

/-- The Kakeya maximal function `K_δ f (ω) = sup_x (1/vol T_δ(ω,x)) ∫_{T_δ(ω,x)} |f|`,
valued in `[0, ∞]`. -/
noncomputable def kakeyaMaximal (δ : ℝ) (f : E3 → ℝ) (ω : E3) : ENNReal :=
  ⨆ x : E3, (volume (tube δ ω x))⁻¹ * ∫⁻ y in tube δ ω x, ‖f y‖ₑ

/-- The unnormalised surface-area measure on the unit sphere `S²` (total mass `4π`). -/
noncomputable def sphereArea : Measure (Metric.sphere (0 : E3) 1) :=
  (volume : Measure E3).toSphere

/-- The external Kakeya maximal estimate quoted as Theorem 18 ([38, Corollary 9.1]):
there is `C_K ≥ 1` with `‖K_δ f‖_{L³(S²)} ≤ C_K log^{4/3}(2/δ) ‖f‖_{L³(ℝ³)}` for all
`0 < δ ≤ 1` and all `f ∈ L³(ℝ³)`. It is a proposition used as a hypothesis, never
asserted. -/
def KakeyaMaximalEstimate : Prop :=
  ∃ CK : ℝ, 1 ≤ CK ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ f : E3 → ℝ, MemLp f 3 volume →
    (∫⁻ ω, kakeyaMaximal δ f (ω : E3) ^ 3 ∂sphereArea) ^ (1 / 3 : ℝ) ≤
      ENNReal.ofReal (CK * Real.log (2 / δ) ^ (4 / 3 : ℝ)) * eLpNorm f 3 volume

end PolyhedralPacking1261.Packing.Supplement


