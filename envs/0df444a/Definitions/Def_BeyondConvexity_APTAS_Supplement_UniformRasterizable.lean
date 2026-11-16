-- Prove2me | Definitions.Def_BeyondConvexity_APTAS_Supplement_UniformRasterizable
-- name    : BeyondConvexity_APTAS_Supplement_UniformRasterizable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:12:32.685829+00:00
-- url     : https://prove2.me/theorems/22359d95-807f-445a-b8fd-d76825cf7822
-- title:
--   Dimensional uniform rasterizability
-- statement:
--   A grid with real side $h>0$ and arbitrary real phase $\tau$ has closed hypercubic cells indexed by $\mathbb Z^d$. Its cover $V_{h,\tau}(S)$ is the union of cells whose interiors meet the interior of $S$. Uniform rasterizability requires one rational-valued polynomial-time resolution $\Pi$ with $0<\Pi(\eta)\le1$ for rational $0<\eta<1$, such that for every valid class region $P$, every real translation $v$, every phase and every real $0<h\le\Pi(\eta)b(P)$,
--
--   $$\operatorname{Vol}_d(V_{h,\tau}(P+v)\setminus(P+v))\le\eta\operatorname{Vol}_d(P).$$
--
--   Volumes are extended nonnegative reals; valid finite simplicial regions and these covers have finite volume. The resolution machine operates on finite rational encodings; placements, phases and real scales are analytic quantifiers. This is the higher-dimensional version of Definitions 2 and 3, without an assumed bulk inequality.
-- source:
--   Lucas de Oliveira Silva, Elisa Dell'Arriva, Flávio Keidi Miyazawa, STOC 2027 submission #890 (October 2026), Definitions 2-3, printed pp.5-6 / PDF pp.6-7; Section 7, printed p.16 / PDF p.17

import Definitions.Def_BeyondConvexity_APTAS_Supplement_PolyhedralRegion

noncomputable section

namespace BeyondConvexity.APTAS.Supplement

def gridCell {d : ℕ} (h : ℝ) (τ : RPoint d) (z : Fin d → ℤ) : Set (RPoint d) :=
  {x | ∀ i, τ i + (z i : ℝ) * h ≤ x i ∧ x i ≤ τ i + ((z i : ℝ) + 1) * h}

def gridCover {d : ℕ} (h : ℝ) (τ : RPoint d) (S : Set (RPoint d)) : Set (RPoint d) :=
  ⋃ z : Fin d → ℤ, ⋃ (_ : (interior (gridCell h τ z) ∩ interior S).Nonempty),
    gridCell h τ z

/-- Definition 3 in dimension d. Every placement, phase and positive real scale
is quantified; the machine computes only the rational resolution. -/
def UniformRasterizable {d : ℕ} (P : Set (PolyhedralRegion d)) : Prop :=
  ∃ resolution : ℚ → ℚ,
    PolynomialOn AbelianCayleyHDX.encRat AbelianCayleyHDX.encRat
      (fun η => 0 < η ∧ η < 1) resolution ∧
    (∀ η : ℚ, 0 < η → η < 1 → 0 < resolution η ∧ resolution η ≤ 1) ∧
    ∀ η : ℚ, 0 < η → η < 1 → ∀ Q ∈ P, Q.Valid →
      ∀ (v τ : RPoint d) (h : ℝ), 0 < h → h ≤ (resolution η : ℝ) * Q.span →
        vol (gridCover h τ (translate v Q.region) \ translate v Q.region) ≤
          ENNReal.ofReal (η : ℝ) * vol Q.region

end BeyondConvexity.APTAS.Supplement


