-- Prove2me | Definitions.Def_BeyondConvexity_APTAS_RasterWitness
-- name    : BeyondConvexity_APTAS_RasterWitness
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:13:06.909207+00:00
-- url     : https://prove2.me/theorems/21bb7e15-24ed-4660-abab-c4320a873d19
-- title:
--   Uniform rasterization with an effective resolution
-- statement:
--   For a cell side $h>0$ and real phase $\tau$, the grid-cell cover of a region is the union of the closed grid cells whose interiors meet the region’s interior. A resolution function $\Pi$ is rational-valued, polynomial-time computable on rational $0<\eta<1$, and satisfies $0<\Pi(\eta)\le1$. For every valid object $P$ of the class, every translation of it, every phase, and every real $0<h\le\Pi(\eta)b(P)$, it obeys
--
--   $$\operatorname{Area}(V_{h,\tau}(P)\setminus P)\le\eta\operatorname{Area}(P).$$
--
--   Uniform rasterizability is existence of such a function. The associated bulk constant is $\lambda=\frac16\min\{\Pi(1/2),1/2\}$. This interface controls actual Lebesgue area uniformly over phases and placements, with no bound on boundary complexity.
-- source:
--   Lucas de Oliveira Silva, Elisa Dell'Arriva, Flávio Keidi Miyazawa, STOC 2027 submission #890 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/890.pdf, Definitions 2–3 and Proposition 1, printed pp.5–6 / PDF pp.6–7.

import Definitions.Def_BeyondConvexity_APTAS_PolynomialOn

noncomputable section

namespace BeyondConvexity.APTAS

def gridCell (h : ℝ) (τ : Point) (z : ℤ × ℤ) : Set Point :=
  Set.Icc (τ.1 + z.1 * h) (τ.1 + (z.1 + 1) * h) ×ˢ
    Set.Icc (τ.2 + z.2 * h) (τ.2 + (z.2 + 1) * h)

def gridCover (h : ℝ) (τ : Point) (S : Set Point) : Set Point :=
  ⋃ z : ℤ × ℤ, ⋃ (_ : (interior (gridCell h τ z) ∩ interior S).Nonempty),
    gridCell h τ z

def RasterWitness (P : Set Polygon) (resolution : ℚ → ℚ) : Prop :=
  PolynomialOn AbelianCayleyHDX.encRat AbelianCayleyHDX.encRat
    (fun η => 0 < η ∧ η < 1) resolution ∧
  (∀ η : ℚ, 0 < η → η < 1 → 0 < resolution η ∧ resolution η ≤ 1) ∧
    ∀ η : ℚ, 0 < η → η < 1 → ∀ p ∈ P, p.Valid →
      ∀ (v : Point) (h : ℝ) (τ : Point), 0 < h → h ≤ (resolution η : ℝ) * p.span →
        area (gridCover h τ (translate v p.region) \ translate v p.region) ≤
          (η : ℝ) * area p.region

def UniformlyRasterizable (P : Set Polygon) : Prop := ∃ resolution, RasterWitness P resolution

def bulkConstant (resolution : ℚ → ℚ) : ℚ := (1/6) * min (resolution (1/2)) (1/2)

end BeyondConvexity.APTAS


