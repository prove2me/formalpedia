-- Prove2me | Definitions.Def_JRCurvedQFT_Symmetries_IsTimeReflection
-- name    : JRCurvedQFT_Symmetries_IsTimeReflection
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:05:55.541346+00:00
-- url     : https://prove2.me/theorems/9503a93e-8f89-466e-968d-07a43b8e9569
-- title:
--   Reflection data of the field: $\mathcal E_+$, $\Theta=\Gamma(\theta)$, and O-S positivity
-- statement:
--   A reflection datum $r$ on $\mathcal E$ (a closed subspace, a unitary involution $\Theta$, and $\operatorname{Re}\langle\Theta x,x\rangle\ge0$ on the subspace) is the **time reflection of the field** if its subspace is $\mathcal E_+$ and its unitary acts by
--   $$\Theta\,\Phi(f_1)\cdots\Phi(f_n)=\Phi(f_1\circ\theta)\cdots\Phi(f_n\circ\theta).$$
--   Together these say that $\Theta=\Gamma(\theta)$ is unitary and that Assumption 1 (O-S positivity) holds. The Hilbert space of quantum theory is then the OS completion of $r$.
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries, arXiv:0704.0052v1, §3.1, p. 3; Assumption 1, p. 3; Definition 2.2, p. 3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P92
import Definitions.Def_JRCurvedQFT_SharpTime_StaticStructure
import Definitions.Def_JRCurvedQFT_Symmetries_localSpace

open scoped Manifold ContDiff ENNReal Topology InnerProductSpace
open Bundle MeasureTheory
open QAlgorithms.Papers.Independent.Intakethird100.P92

namespace JRCurvedQFT.Symmetries

variable {d : ℕ} {M : Type} [EMetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- `r` is the reflection data of the field: its positive subspace is `E₊`, and its unitary is
`Θ = Γ(θ)`, `Θ Φ(f₁)…Φ(f_n) = Φ(f₁∘θ)…Φ(f_n∘θ)` ((2.2) with `θ⁻¹ = θ`).

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries*, arXiv:0704.0052v1, §3.1, p. 3 ("Let Θ = Γ(θ) be the reflection on E induced by θ"), Assumption 1, p. 3
(O-S positivity), Definition 2.2, p. 3.

**Formalization Note** Readings 5–6: `ReflectionData` (published, Neeb–Ólafsson) has exactly the
fields closed `plus`, unitary involution `theta`, and `0 ≤ Re⟪θx, x⟫` on `plus`. So a binder
`r : ReflectionData (fieldSpace Φ)` with `IsTimeReflection S Φ r` says that `Θ` is unitary on `E`
(Assumption 2 for `θ`) and that Assumption 1 holds; closedness and `Θ² = 1` are implied by the
paper's setting. The monomial rule is stated for any test functions `g i = f i ∘ θ`; such `g i`
always exist, because `θ` is a diffeomorphism. -/
structure IsTimeReflection (S : JRCurvedQFT.SharpTime.StaticStructure (d := d) M) (Φ : EuclideanField (d := d) M P)
    (r : ReflectionData (fieldSpace Φ)) : Prop where
  plus_eq : r.plus = localSpace Φ S.positiveTime
  theta_monomial : ∀ (n : ℕ) (f g : Fin n → testFunctions (d := d) M),
    (∀ i p, (g i : M → ℝ) p = (f i : M → ℝ) (S.reflection p)) →
    r.theta (fieldMonomial Φ f) = fieldMonomial Φ g

end JRCurvedQFT.Symmetries


