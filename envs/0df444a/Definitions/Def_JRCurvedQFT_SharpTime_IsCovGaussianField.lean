-- Prove2me | Definitions.Def_JRCurvedQFT_SharpTime_IsCovGaussianField
-- name    : JRCurvedQFT_SharpTime_IsCovGaussianField
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:35:46.018247+00:00
-- url     : https://prove2.me/theorems/d341919d-e0e3-402d-a990-47b48f097777
-- title:
--   Gaussian field with mean zero and covariance $T$ on $L^2(M)$
-- statement:
--   For a bounded operator $T$ on real $L^2(M,\mathrm{dvol})$, a family $\Psi=(\Psi(f))_{f\in L^2(M)}$ of real random variables on a probability space $(\Omega,P)$ is a **Gaussian field with mean zero and covariance $T$** if every $\Psi(f)$ is measurable with law $N(0,\langle f,Tf\rangle_{L^2(M)})$ and $\Psi$ is almost surely linear: $\Psi(af+g)=a\Psi(f)+\Psi(g)$ $P$-a.s. for all real $a$ and $f,g\in L^2(M)$.
--
--   This is the Gaussian measure "with mean zero and covariance C" of §1.6, p. 8, for an arbitrary covariance (not only the free one), described through its field.
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral, arXiv:hep-th/0609003v1, §1.6, p. 8 (with p. 5 and (1.11), p. 7)

import Mathlib

open scoped ENNReal
open MeasureTheory

namespace JRCurvedQFT.SharpTime

/-- `Ψ` is a **Gaussian field with mean zero and covariance `T`**, indexed by `L²(M)`, over the
probability space `(Ω, P)`.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral*, arXiv:hep-th/0609003v1, §1.6, p. 8: "A Gaussian measure with mean zero and covariance C is reflection positive
iff C is reflection positive in the operator sense, eqn. (1.11)", where (1.11), p. 7, is stated for
"a bounded operator T on L²(M)"; p. 5: a Gaussian measure with covariance `C` has characteristic
function `S(f) = e^{−½⟨f, Cf⟩}`.

For every real `f ∈ L²(M)`: `Ψ(f)` is measurable with law `N(0, ⟨f, Tf⟩_{L²(M)})`; and `Ψ` is linear
almost surely: `Ψ(a f + g) = a Ψ(f) + Ψ(g)` `P`-a.s.

**Formalization Note** The covariance is an arbitrary bounded operator `T` on real `L²(M)` (the
theorems that use this predicate assume `T` positive and self-adjoint, as a covariance is), not
only the free covariance `(−Δ + m²)⁻¹`. The field is any process with this joint law, in place of
a Gaussian measure on `H₋∞`. -/
def IsCovGaussianField {M : Type} [MeasurableSpace M] (μ : Measure M)
    (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (Ψ : Lp ℝ 2 μ → Ω → ℝ) : Prop :=
  (∀ f, Measurable (Ψ f) ∧
    P.map (Ψ f) = ProbabilityTheory.gaussianReal 0 (inner ℝ f (T f)).toNNReal) ∧
  ∀ (a : ℝ) (f g : Lp ℝ 2 μ), Ψ (a • f + g) =ᵐ[P] fun w => a * Ψ f w + Ψ g w

end JRCurvedQFT.SharpTime


