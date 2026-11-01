-- Prove2me | Definitions.Def_JRCurvedQFT_SharpTime_IsGaussianField
-- name    : JRCurvedQFT_SharpTime_IsGaussianField
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:38:46.697699+00:00
-- url     : https://prove2.me/theorems/f44b0ead-84ba-424e-b068-26863411b948
-- title:
--   The Euclidean free field: isonormal Gaussian process on $H_{-1}(M)$
-- statement:
--   Let $(\Omega,P)$ be a probability space. A family $\Phi=(\Phi(h))$ of real random variables indexed by functionals $h$ is the **Euclidean free field of mass $m$** if
--
--   1. for every $h\in H_{-1}(M)$, $\Phi(h)$ is measurable and Gaussian with mean $0$ and variance $\|h\|_{-1}^2=\langle h,Ch\rangle$;
--   2. $\Phi$ is linear almost surely: $\Phi(ah+k)=a\Phi(h)+\Phi(k)$ $P$-a.s., for $h,k\in H_{-1}(M)$ and $a\in\mathbb R$.
--
--   Then $\mathbb E\,e^{i\Phi(h)}=e^{-\frac12\langle h,Ch\rangle}$, the characteristic functional of the Gaussian measure with covariance $C=(-\Delta+m^2)^{-1}$ (p. 5), and $\mathcal E=L^2(\Omega,P)$ plays the role of $L^2(H_{-\infty},\mu)$.
--
--   **Formalization Note** Any isonormal field replaces the Minlos measure on $H_{-\infty}$ (Reading 6); all statements depend only on the joint law.
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral, arXiv:hep-th/0609003v1, §1.3, p. 5

import Mathlib
import Definitions.Def_JRCurvedQFT_SharpTime_IsHminus1

open scoped Manifold ContDiff ENNReal Topology
open Bundle MeasureTheory

namespace JRCurvedQFT.SharpTime

variable {d : ℕ} {M : Type} [EMetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]

/-- `Φ` is the **Euclidean free field**: an isonormal Gaussian process on `H₋₁(M)` over the
probability space `(Ω, P)`.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral*, arXiv:hep-th/0609003v1, p. 5: "There is a unique Gaussian measure µ defined on the dual H₋∞ with covariance C. This
means that S(f) ≡ ∫ e^{iΦ(f)} dµ(Φ) = e^{−½⟨f, Cf⟩}".

For every `h ∈ H₋₁(M)`: `Φ(h)` is measurable with law `N(0, ‖h‖²₋₁)`; and `Φ` is linear almost
surely: `Φ(a h + k) = a Φ(h) + Φ(k)` `P`-a.s.

**Formalization Note** Reading 6 (generalization): any isonormal field replaces Minlos' measure on
`H₋∞`; all statements depend only on the joint law, which is the Gaussian with covariance `C`
(characteristic function `e^{−½⟨f,Cf⟩}`). -/
def IsGaussianField [MeasurableSpace M] (μ : Measure M) (m : ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (Φ : ((M → ℝ) → ℝ) → Ω → ℝ) : Prop :=
  (∀ h, IsHminus1 (d := d) μ m h → Measurable (Φ h) ∧
    P.map (Φ h) = ProbabilityTheory.gaussianReal 0 ((negSobolevNorm (d := d) μ m h).toNNReal ^ 2)) ∧
  ∀ (a : ℝ) (h k : (M → ℝ) → ℝ), IsHminus1 (d := d) μ m h → IsHminus1 (d := d) μ m k →
    Φ (a • h + k) =ᵐ[P] fun w => a * Φ h w + Φ k w

end JRCurvedQFT.SharpTime


