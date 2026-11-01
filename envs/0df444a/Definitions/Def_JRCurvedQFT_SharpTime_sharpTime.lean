-- Prove2me | Definitions.Def_JRCurvedQFT_SharpTime_sharpTime
-- name    : JRCurvedQFT_SharpTime_sharpTime
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:37:44.229697+00:00
-- url     : https://prove2.me/theorems/183dc62c-6fd2-464b-a1c5-270df32c3361
-- title:
--   Sharp-time distribution $f_t=f\otimes\delta(t-\cdot)$
-- statement:
--   For a function $f$ on $\Sigma$ and a time $t$, the **sharp-time distribution** $f_t(x,t')=f(x)\delta(t-t')$ is the functional
--   $$f_t(u)=\int_\Sigma f(x)\,u(\phi_t(x))\,\sqrt{\mathcal G}\,dx$$
--   on test functions $u$ on $M$: it integrates $u$ against $f$ on the time-$t$ copy $\phi_t(\Sigma)$ of the slice. The field at sharp time is $\Phi(f_t)=\int\Phi(x,t)f(x)\sqrt{\mathcal G}\,dx$ ((4.16)).
--
--   **Formalization Note** That $f_t$ lies in $H_{-1}(M)$ is not part of the definition; it is a conclusion of the theorems.
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral, arXiv:hep-th/0609003v1, p. 24 ("Given a function f on Σ, we obtain a distribution f_t"); Eq. (4.16), p. 25

import Mathlib
import Definitions.Def_JRCurvedQFT_SharpTime_sliceMeasure

open scoped Manifold ContDiff ENNReal Topology
open Bundle MeasureTheory

namespace JRCurvedQFT.SharpTime

variable {d : ℕ} {M : Type} [EMetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]

/-- The **sharp-time distribution** `f_t = f ⊗ δ(t − ·)`, as a functional on test functions:
`f_t(u) = ∫_Σ f(x) u(φ_t(x)) √𝒢 dx`.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral*, arXiv:hep-th/0609003v1, p. 24: "Given a function f on Σ, we obtain a distribution f_t supported at time t as
follows: f_t(x, t′) = f(x)δ(t − t′)"; the pairing with `√𝒢 dx` is (4.16), p. 25:
`Φ((f_i)_{t_i}) = ∫ Φ(x, t_i) f_i(x) √𝒢 dx`.

**Formalization Note** Reading 2: `f` is the ξ-invariant lift of a function on `Σ` and the integral
is over `ν = √𝒢 dx` (`sliceMeasure`). Membership of `f_t` in `H₋₁(M)` is not built in; it is a
conclusion of the theorems that use it. -/
noncomputable def sharpTime [MeasurableSpace M] (S : StaticStructure (d := d) M) (μ : Measure M)
    (f : M → ℝ) (t : ℝ) : (M → ℝ) → ℝ :=
  fun u => ∫ x, f x * u (S.flow t x) ∂(sliceMeasure S μ)

end JRCurvedQFT.SharpTime


