-- Prove2me | Definitions.Def_FourierRankQLB_Supplement_gradPhaseOracle
-- name    : FourierRankQLB_Supplement_gradPhaseOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:14:56.371205+00:00
-- url     : https://prove2.me/theorems/5580b396-9372-4836-b3ca-0578332122ce
-- title:
--   Ideal gradient phase oracle $(G_f\psi)(x,u) = e^{i u^\top \nabla f(x)}\psi(x,u)$ (Eq. (58))
-- statement:
--   For a function $f : \mathbb R^n \to \mathbb R$, the **ideal gradient phase oracle** acts on the register $L^2(Y,\nu)\otimes W$ whose labels $y$ represent query pairs $\iota(y) = (x,u) \in \mathbb R^n\times\mathbb R^n$ by
--
--   $$
--   (G_f\psi)(y) = e^{i\,u^\top \nabla f(x)}\,\psi(y), \qquad (x,u) = \iota(y).
--   $$
--
--   The paper's register is $L^2(\mathbb R^n\times\mathbb R^n)$ ($Y = \mathbb R^n\times\mathbb R^n$, Lebesgue measure, $\iota$ the identity); the end of §6.1 extends Theorem 6.1 to finite label sets. One application of $G_f$ or $G_f^{-1}$ is one gradient query. In the ideal model the oracle is equivalent, by a Fourier transform, to the translation oracle $|x,y\rangle \mapsto |x, y + \nabla f(x)\rangle$.
--
--   **Formalization Note** $\nabla f$ is Mathlib's `gradient`, which is the gradient wherever $f$ is differentiable (and $0$ elsewhere); the theorems apply the oracle only to quadratic functions, which are differentiable everywhere. The module proves that $\nabla f$ is Borel measurable, so the phase is measurable.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Eq. (58), p.33; end of §6.1, p.34

import Mathlib
import Definitions.Def_FourierRankQLB_Ambient
import Definitions.Def_FourierRankQLB_Supplement_phaseMul

open MeasureTheory

namespace FourierRankQLB

namespace Supplement

/-- The gradient `∇f` of any `f : ℝⁿ → ℝ` is a Borel-measurable map. -/
theorem measurable_gradient_ambient {n : ℕ} (f : Ambient n → ℝ) : Measurable (gradient f) := by
  borelize (Ambient n →L[ℝ] ℝ)
  exact (InnerProductSpace.toDual ℝ (Ambient n)).symm.continuous.measurable.comp
    (measurable_fderiv ℝ f)

/-- The ideal gradient phase oracle `(G_f ψ)(x, u) = e^{i uᵀ ∇f(x)} ψ(x, u)` of Eq. (58) of a
function `f : ℝⁿ → ℝ`, on the register `L²(Y, ν) ⊗ W` whose labels `y` represent the query pairs
`ι y = (x, u) ∈ ℝⁿ × ℝⁿ`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Eq. (58), p. 33 and the end of §6.1, p. 34.

**Formalization Note.** The paper's register is `L²(ℝⁿ × ℝⁿ)` (`Y = ℝⁿ × ℝⁿ`, Lebesgue measure,
`ι = id`); the end of §6.1 allows a finite set of labels with counting measure; any σ-finite
label space is allowed here. `∇f` is Mathlib's `gradient`, which is the true gradient where `f` is
differentiable (every statement applies the oracle only to quadratic functions). The workspace `W`
is untouched. -/
noncomputable def gradPhaseOracle {n : ℕ} {Y : Type} [MeasurableSpace Y] (ν : Measure Y)
    (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (ι : Y → Ambient n × Ambient n) (hι : Measurable ι) (f : Ambient n → ℝ) :
    Lp W 2 ν ≃ₗᵢ[ℂ] Lp W 2 ν :=
  phaseMul ν W (fun y => inner ℝ (ι y).2 (gradient f (ι y).1))
    (Measurable.inner (measurable_snd.comp hι)
      ((measurable_gradient_ambient f).comp (measurable_fst.comp hι)))

end Supplement

end FourierRankQLB


