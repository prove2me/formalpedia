-- Prove2me | Definitions.Def_UPPIntersection_Halfspaces_Sphere
-- name    : UPPIntersection_Halfspaces_Sphere
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T16:26:58.192448+00:00
-- url     : https://prove2.me/theorems/44c2bd45-a54d-4251-8c30-b1d039048cb1
-- title:
--   §2–3 — the uniform sphere law, the symmetrization $H_{f,g}$, partial derivatives and Taylor polynomials
-- statement:
--   For $d\ge2$, $S^{d-1}\subseteq\mathbb R^d$ is the Euclidean unit sphere with its Borel $\sigma$-algebra and its **uniform law** $\sigma_d$, the rotation-invariant probability measure. Points of $(S^{d-1})^k$ that are "independent uniform" are drawn from the product law $\sigma_d^{\otimes k}$.
--
--   For measurable $f,g:(S^{d-1})^k\to\mathbb R^r$ with $\|f\|_2,\|g\|_2\le1$ pointwise, the **symmetrization** is
--   $$H_{f,g}(s)=\mathbb E_{(X,Y)\sim D_s}\,\langle f(X),g(Y)\rangle,\qquad s\in[-1,1]^k,$$
--   where $D_s$ draws $X_1,\dots,X_k$ independent uniform on $S^{d-1}$, then $V_i$ independent uniform on the unit sphere of $X_i^\perp$, and sets $Y_i=s_iX_i+\sqrt{1-s_i^2}\,V_i$. Thus $\langle X_i,Y_i\rangle=s_i$ and $Y$ is again uniform.
--
--   For $h:\mathbb R^k\to\mathbb R$, a multi-index $\alpha\in\mathbb N^k$ has $|\alpha|=\sum_i\alpha_i$ and $\alpha!=\prod_i\alpha_i!$; $\partial^\alpha h=\partial_1^{\alpha_1}\cdots\partial_k^{\alpha_k}h$; and the Taylor polynomial at the origin of total degree at most $D$ is
--   $$T_D(s)=\sum_{|\alpha|\le D}\frac{\partial^\alpha h(0)}{\alpha!}\,s^\alpha .$$
--
--   These are the objects of Section 3, whose smoothness estimate for $H_{f,g}$ reduces the continuous margin problem to polynomial approximation.
--
--   **Formalization Note** $\sigma_d$ is `volume.toSphere` divided by its total mass. The uniform point $V_i$ on $X_i^\perp\cap S^{d-1}$ is realized as $w_i/\|w_i\|$ with $w_i=U_i-\langle U_i,X_i\rangle X_i$ for an independent uniform $U_i$, which has exactly that conditional law when $d\ge2$; on the probability-zero event where this does not give a unit vector, $Y_i:=X_i$. The kernel is defined for every $s$, and the integrand is measurable (checked in `Solutions/verification`). Partial derivatives are iterated one-variable `deriv`s along coordinate lines.
-- source:
--   Mark Bun, Mandar Juvekar, STOC 2027 submission #478 (October 2026), p. 12 (S^{d−1}, multi-indices on p. 13), p. 14 (§3, definition of H_{f,g} and experiment D_s), p. 15 (Corollary 3.2, Taylor polynomial); PDF page = printed page; source.pdf SHA-256 1d258c38a48636b0aa03fa9dfce0ba5e367df8b9c55ee6e67f9f3b6f76e0d388

import Mathlib

namespace UPPIntersection.Halfspaces

open MeasureTheory

/-- The unit sphere `S^{d-1} ⊆ ℝ^d`. -/
abbrev Sph (d : ℕ) : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1

/-- The normalized rotation-invariant (uniform) probability measure on `S^{d-1}`: the surface
measure `volume.toSphere` divided by its total mass. -/
noncomputable def sphereLaw (d : ℕ) : Measure (Sph d) :=
  ((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere Set.univ)⁻¹ •
    (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere

instance (d : ℕ) : IsFiniteMeasure (sphereLaw d) := by
  constructor
  simp only [sphereLaw, Measure.smul_apply, smul_eq_mul]
  set x := (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere Set.univ
  by_cases h0 : x = 0
  · simp [h0]
  by_cases ht : x = ⊤
  · simp [ht]
  rw [ENNReal.inv_mul_cancel h0 ht]
  exact ENNReal.one_lt_top

/-- `k` independent uniform points of `S^{d-1}`: the product law on `(S^{d-1})^k`. -/
noncomputable def sphereLawPow (d k : ℕ) : Measure (Fin k → Sph d) :=
  Measure.pi fun _ => sphereLaw d

/-- The second point of the experiment `D_s` for one coordinate. Given `x ∈ S^{d-1}` and an
auxiliary independent uniform point `u ∈ S^{d-1}`, let `w = u - ⟨u,x⟩x` and `v = w/‖w‖`, which is
uniform on the great subsphere `{v ∈ S^{d-1} : ⟨v,x⟩ = 0}` given `x`; return
`y = s x + √(1-s²) v`. For `s ∈ [-1,1]` and `w ≠ 0` (an event of probability one when `d ≥ 2`),
`‖y‖ = 1`; on the remaining null event the point `x` itself is returned. -/
noncomputable def partner {d : ℕ} (s : ℝ) (x u : Sph d) : Sph d :=
  let w : EuclideanSpace ℝ (Fin d) := (u : EuclideanSpace ℝ (Fin d)) -
    (inner ℝ (u : EuclideanSpace ℝ (Fin d)) (x : EuclideanSpace ℝ (Fin d))) • (x : EuclideanSpace ℝ (Fin d))
  let y : EuclideanSpace ℝ (Fin d) :=
    s • (x : EuclideanSpace ℝ (Fin d)) + Real.sqrt (1 - s ^ 2) • (‖w‖⁻¹ • w)
  if h : ‖y‖ = 1 then ⟨y, mem_sphere_zero_iff_norm.mpr h⟩ else x

/-- The spherical symmetrization `H_{f,g}(s) = E_{(X,Y) ∼ D_s} ⟨f(X), g(Y)⟩` (§3): `X_1,…,X_k`
independent uniform on `S^{d-1}`, `V_i` independent uniform on the unit sphere of `X_i^⊥`, and
`Y_i = s_i X_i + √(1-s_i²) V_i`. -/
noncomputable def symH {d k r : ℕ} (f g : (Fin k → Sph d) → EuclideanSpace ℝ (Fin r))
    (s : Fin k → ℝ) : ℝ :=
  ∫ p : (Fin k → Sph d) × (Fin k → Sph d),
    inner ℝ (f p.1) (g fun i => partner (s i) (p.1 i) (p.2 i))
    ∂((sphereLawPow d k).prod (sphereLawPow d k))

/-- The partial derivative `∂_i h` in the `i`-th coordinate. -/
noncomputable def partialDeriv {k : ℕ} (i : Fin k) (h : (Fin k → ℝ) → ℝ) : (Fin k → ℝ) → ℝ :=
  fun s => deriv (fun t => h (Function.update s i t)) (s i)

/-- The mixed partial derivative `∂^α h = ∂_1^{α_1} ∂_2^{α_2} ⋯ ∂_k^{α_k} h`. -/
noncomputable def multiPartial {k : ℕ} (α : Fin k → ℕ) (h : (Fin k → ℝ) → ℝ) :
    (Fin k → ℝ) → ℝ :=
  (List.finRange k).foldr (fun i acc => (partialDeriv i)^[α i] acc) h

/-- `α! = ∏_i α_i!`. -/
def multiFact {k : ℕ} (α : Fin k → ℕ) : ℕ := ∏ i, (α i).factorial

/-- The multi-indices `α ∈ ℕ^k` with `|α| = ∑_i α_i ≤ D`. -/
def multiIndicesLE (k D : ℕ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset fun _ => Finset.range (D + 1)).filter fun α => ∑ i, α i ≤ D

/-- The Taylor polynomial of `h` at the origin consisting of the terms of total degree at most `D`:
`T_D(s) = ∑_{|α| ≤ D} ∂^α h(0) / α! · s^α`. -/
noncomputable def taylorPoly {k : ℕ} (h : (Fin k → ℝ) → ℝ) (D : ℕ) (s : Fin k → ℝ) : ℝ :=
  ∑ α ∈ multiIndicesLE k D, multiPartial α h 0 / (multiFact α : ℝ) * ∏ i, s i ^ α i

end UPPIntersection.Halfspaces


