-- Prove2me | Definitions.Def_JRCurvedQFT_SharpTime_thetaStar
-- name    : JRCurvedQFT_SharpTime_thetaStar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:36:52.815824+00:00
-- url     : https://prove2.me/theorems/aa620b98-7bca-4276-9d67-6ef5ef68da25
-- title:
--   Time reflection on test functionals, $(\theta^*\ell)(u)=\ell(u\circ\theta)$
-- statement:
--   The time reflection acts on functionals on test functions by
--   $$(\theta^*\ell)(u)=\ell(u\circ\theta).$$
--   For a function $f$, $(\theta^*f)(u)=\int f\,(u\circ\theta)\,\mathrm{dvol}=\int (f\circ\theta)\,u\,\mathrm{dvol}$, since $\theta$ preserves the volume; so $\theta^*f=f\circ\theta=f^\theta$, the action (1.4) of the involution $\theta$ ($f^\psi=f\circ\psi^{-1}$).
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral, arXiv:hep-th/0609003v1, Eq. (1.4), p. 5; Definition 1.4, p. 7

import Mathlib
import Definitions.Def_JRCurvedQFT_SharpTime_StaticStructure

open scoped Manifold ContDiff ENNReal Topology
open Bundle MeasureTheory

namespace JRCurvedQFT.SharpTime

variable {d : ℕ} {M : Type} [EMetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]

/-- The time reflection acting on test functionals: `(θ^* ℓ)(u) = ℓ(u ∘ θ)`.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral*, arXiv:hep-th/0609003v1, (1.4), p. 5: `f^ψ = ψ_* f = f ∘ ψ⁻¹`; for `ψ = θ` (an involution) `f^θ = f ∘ θ`. On a function
`f`, `(θ^* ι f)(u) = ∫ f (u ∘ θ) dvol = ∫ (f ∘ θ) u dvol`, since `θ` preserves `dvol`.

**Formalization Note** Pitfall 4: `θ` is an involutive isometry, so pull-back and push-forward
agree; this one definition is used throughout. -/
def thetaStar (S : StaticStructure (d := d) M) (ℓ : (M → ℝ) → ℝ) : (M → ℝ) → ℝ :=
  fun u => ℓ (u ∘ S.reflection)

end JRCurvedQFT.SharpTime


