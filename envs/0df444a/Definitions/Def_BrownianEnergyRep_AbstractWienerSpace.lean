-- Prove2me | Definitions.Def_BrownianEnergyRep_AbstractWienerSpace
-- name    : BrownianEnergyRep_AbstractWienerSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:00:31.555255+00:00
-- url     : https://prove2.me/theorems/1977dae7-f05c-43a0-a82e-d07abb20c061
-- title:
--   Abstract Wiener space $(H,W,\Gamma)$
-- statement:
--   An abstract Wiener space is a triple $(H,W,\Gamma)$ where $H$ is a real separable Hilbert space densely and continuously embedded in a real separable Banach space $W$, and $\Gamma$ is the Borel probability measure with
--   $$
--   \int_We^{i\varphi(x)}\,d\Gamma(x)=\exp\Big(-\frac{|\varphi|^2_{H^*}}2\Big),\qquad\varphi\in W^*\subset H^* .
--   $$
--   The Fourier-Wiener transform and the Gaussian regular representation are built on this setting.
--
--   **Formalization Note** The embedding is $j:H\to W$ and $|\varphi|_{H^*}$ is the norm of $\varphi\circ j$. The module also defines the element of $H$ that represents $\varphi\in W^*$, which is the identification of $W^*$ with a dense subspace of $H$.
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, §5, p.16

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- An abstract Wiener space `(H, W, Γ)` (arXiv:1511.07378v1, §5, p.16): a real separable Hilbert space `H`
densely and continuously embedded in a real separable Banach space `W`, and the Borel measure `Γ`
with `∫ e^{iφ(x)} dΓ(x) = exp(−|φ|²_{H*}/2)` for `φ ∈ W*`.

**Formalization Note** `j : H → W` is the embedding and `|φ|_{H*}` is the norm of `φ ∘ j`. -/
structure AbstractWienerSpace (H W : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] where
  complete_H : CompleteSpace H
  separable_H : TopologicalSpace.SeparableSpace H
  complete_W : CompleteSpace W
  separable_W : TopologicalSpace.SeparableSpace W
  borel_W : BorelSpace W
  j : H →L[ℝ] W
  j_injective : Function.Injective j
  j_dense : DenseRange j
  Γ : Measure W
  isProbabilityMeasure : IsProbabilityMeasure Γ
  charFun : ∀ φ : StrongDual ℝ W,
    ∫ x, Complex.exp (Complex.I * (φ x : ℂ)) ∂Γ = Real.exp (-‖φ.comp j‖ ^ 2 / 2)

/-- The element of `H` representing `φ ∈ W*`: the identification of `W*` with a subspace of `H`
(arXiv:1511.07378v1, p.16). -/
noncomputable def AbstractWienerSpace.dualRep {H W : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [MeasurableSpace W] (A : AbstractWienerSpace H W) (φ : StrongDual ℝ W) : H :=
  (InnerProductSpace.toDual ℝ H).symm (φ.comp A.j)

end BrownianEnergyRep


