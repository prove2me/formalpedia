-- Prove2me | Definitions.Def_JRCurvedQFT_Symmetries_EuclideanField
-- name    : JRCurvedQFT_Symmetries_EuclideanField
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:01:47.922456+00:00
-- url     : https://prove2.me/theorems/ca546438-4407-4559-af76-39e853b8dad0
-- title:
--   Euclidean field with all monomials in $L^2$
-- statement:
--   A **Euclidean field** on $M$ over a measure space $(\Omega,P)$ is a real-linear map $f\mapsto\Phi(f)$ from test functions to measurable real functions on $\Omega$ such that every monomial $\Phi(f_1)\cdots\Phi(f_n)$, $n\ge0$, lies in $L^2(P)$.
--
--   The paper's case is $\Omega=S'$, $P=\mu$ and $\Phi(f)(\omega)=\omega(f)$.
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries, arXiv:0704.0052v1, §2.1, p. 3

import Mathlib
import Definitions.Def_JRCurvedQFT_Symmetries_testFunctions

open scoped Manifold ContDiff ENNReal Topology InnerProductSpace
open Bundle MeasureTheory

namespace JRCurvedQFT.Symmetries

variable {d : ℕ} {M : Type} [EMetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) M]
  {Ω : Type*} [MeasurableSpace Ω]

/-- A **Euclidean field** on `M` over the measure space `(Ω, P)`: a real-linear map `f ↦ Φ(f)` from
test functions to real random variables, all of whose monomials `Φ(f₁)…Φ(f_n)`, `n ≥ 0`, are in
`L²(P)`.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries*, arXiv:0704.0052v1, §2.1, p. 3: "one may consider a non-Gaussian, countably-additive measure µ on S′ and the
space E := L²(S′, µ). We are interested in the case that the monomials of the form
A(Φ) = Φ(f₁)…Φ(f_n) for f_i ∈ S are all elements of E".

**Formalization Note** Reading 4 (generalization): the paper's case is `Ω = S′`, `P = µ`,
`Φ(f)(ω) = ω(f)`. Every theorem takes `P` a probability measure. -/
structure EuclideanField (M : Type) [EMetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin d)) M]
    (P : Measure Ω) where
  /-- The field `Φ`. -/
  toFun : testFunctions (d := d) M →ₗ[ℝ] (Ω → ℝ)
  measurable : ∀ f, Measurable (toFun f)
  memLp_prod : ∀ (n : ℕ) (f : Fin n → testFunctions (d := d) M),
    MemLp (fun w => ∏ i, toFun (f i) w) 2 P

end JRCurvedQFT.Symmetries


