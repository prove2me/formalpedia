-- Prove2me | Definitions.Def_LCAGroup_LeftRegularRep
-- name    : LCAGroup_LeftRegularRep
-- status  : Definition
-- author  : @emmgaml
-- created : 2026-11-22T18:48:42.516653+00:00
-- url     : https://prove2.me/theorems/a8cb53e2-45de-498b-ba85-2de6dd9d3dfc
-- title:
--   Left regular representation $\lambda(g)f(x)=f(g^{-1}x)$ of a group with a left-invariant measure on $L^p(G,\nu)$
-- statement:
--   This is the **left regular representation** of a group on $L^p(G,\nu)$.
--
--   Let $G$ be a group with a $\sigma$-algebra for which left and right multiplications by fixed elements are measurable (e.g. a locally compact group with its Borel $\sigma$-algebra), let $\nu$ be a left-invariant measure on $G$ (e.g. a left Haar measure) and let $1\le p\le\infty$. For $g\in G$ and $f\in L^p(G,\nu)$ (complex valued) put
--   $$(\lambda_p(g)f)(x)=f(g^{-1}x)\qquad(x\in G).$$
--   Because $x\mapsto g^{-1}x$ preserves $\nu$, this is well defined on $\nu$-almost-everywhere classes and $\lambda_p(g)$ is a linear isometry of $L^p(G,\nu)$; moreover $\lambda_p(gh)=\lambda_p(g)\lambda_p(h)$. We record $\lambda_p(g)$ as a continuous linear operator.
--
--   In the source this is the action $\rho_G(g,\phi)(x)=\phi(g^{-1}x)$ of (4.3.1.4) on $R(G)=L^2(G,\nu)$ (Definition 4.3.1.1), which the source defines on $C_c(G)$ and extends by density to a continuous unitary representation (Lemma 4.3.1.5(2)); the extension coincides with the composition operator used here.
--
--   **Formalization Note.** `LCAGroup.leftRegularRep ν p g` is `Lp.compMeasurePreservingₗᵢ ℂ (fun x => g⁻¹ * x) (measurePreserving_mul_left ν g⁻¹)` viewed as a continuous linear map `Lp ℂ p ν →L[ℂ] Lp ℂ p ν`; the unfolding lemma `leftRegularRep_apply` is `rfl`. Isometry is Mathlib's `Lp.norm_compMeasurePreserving`. The operator is definitionally Mathlib's domain action: `LCAGroup.leftRegularRep ν p g f = DomMulAct.mk g⁻¹ • f` (by `rfl`); hence strong continuity $g\mapsto\lambda_p(g)f$ for $p<\infty$ follows from the instance `MeasureTheory.Lp.instContinuousSMulDomMulAct` (for locally finite left-invariant measures that are inner regular by compact sets on sets of finite measure, e.g. regular Haar measures).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 175, Definition 4.3.1.1, eq. (4.3.1.4); p. 176, Lemma 4.3.1.5(2)

import Mathlib

/-!
# The left regular representation on `L^p(G, ν)`

For a group `G` with a left-invariant measure `ν` (e.g. a left Haar measure on a locally
compact group) and `1 ≤ p ≤ ∞`, left translation `(λ_p(g) f)(x) = f(g⁻¹ x)` is a linear
isometry of `L^p(G, ν; ℂ)`; we record it as a continuous linear operator.
-/

open MeasureTheory
open scoped ENNReal

namespace LCAGroup

/-- The left regular representation of `G` on `L^p(G, ν; ℂ)`:
`leftRegularRep ν p g f` is the class of `x ↦ f (g⁻¹ * x)`. It is well defined on
`ν`-a.e. classes because `x ↦ g⁻¹ * x` preserves the left-invariant measure `ν`. -/
noncomputable def leftRegularRep {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (ν : Measure G) [ν.IsMulLeftInvariant] (p : ℝ≥0∞) [Fact (1 ≤ p)] (g : G) :
    Lp ℂ p ν →L[ℂ] Lp ℂ p ν :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun x => g⁻¹ * x)
    (measurePreserving_mul_left ν g⁻¹)).toContinuousLinearMap

@[simp]
theorem leftRegularRep_apply {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (ν : Measure G) [ν.IsMulLeftInvariant] (p : ℝ≥0∞) [Fact (1 ≤ p)] (g : G) (f : Lp ℂ p ν) :
    leftRegularRep ν p g f =
      Lp.compMeasurePreserving (fun x => g⁻¹ * x) (measurePreserving_mul_left ν g⁻¹) f :=
  rfl

end LCAGroup


