-- Prove2me | Definitions.Def_TaylorHG_PEP_Interp
-- name    : TaylorHG_PEP_Interp
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T18:06:18.643166+00:00
-- url     : https://prove2.me/theorems/a15b4f83-8e16-4672-8b48-0ad91e4a1d24
-- title:
--   Smooth strongly convex functions and interpolation
-- statement:
--   For $0\leq\mu<L\leq\infty$, the class $\mathcal F_{\mu,L}(\mathbb R^d)$ consists of convex functions $f$ whose subgradients satisfy
--
--   $$\frac1L\|g_1-g_2\|\leq\|x_1-x_2\|,$$
--
--   and for which $x\mapsto f(x)-\frac\mu2\|x\|^2$ is convex. Finite triples $(x_i,g_i,f_i)$ are interpolable if some member of this class has value $f_i$ and subgradient $g_i$ at each $x_i$. The file also defines the ordered-pair inequality (4), with every coefficient as printed in the paper.
--
--   **Formalization Note** The class uses real-valued functions and finite interpolation data. At $L=\infty$, $1/L=0$. Convex real-valued functions on the whole Euclidean space are proper and closed.
-- source:
--   Taylor, Hendrickx & Glineur, arXiv:1502.05666v6, p. 5, Definitions 1–2; p. 10, (4)

import Mathlib
import Definitions.Def_ShorNonsmooth_AlmostDiff_IsSubgradient

namespace TaylorHG.PEP

/-- Definition 1: the real-valued version of the paper's class. -/
def FClass {d : ℕ} (μ : NNReal) (L : ENNReal)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ConvexOn ℝ Set.univ f ∧
  (∀ x₁ x₂ g₁ g₂, ShorNonsmooth.AlmostDiff.IsSubgradient f x₁ g₁ →
    ShorNonsmooth.AlmostDiff.IsSubgradient f x₂ g₂ →
    (L⁻¹).toReal * ‖g₁ - g₂‖ ≤ ‖x₁ - x₂‖) ∧
  ConvexOn ℝ Set.univ (fun x => f x - (μ : ℝ) / 2 * ‖x‖ ^ 2)

/-- Definition 2: finite data interpolated by a member of `FClass`. -/
def Interpolable {d : ℕ} {ι : Type*} [Fintype ι] (μ : NNReal) (L : ENNReal)
    (x g : ι → EuclideanSpace ℝ (Fin d)) (fv : ι → ℝ) : Prop :=
  ∃ f : EuclideanSpace ℝ (Fin d) → ℝ,
    FClass μ L f ∧ ∀ i, f (x i) = fv i ∧
      ShorNonsmooth.AlmostDiff.IsSubgradient f (x i) (g i)

/-- The ordered-pair condition (4), with the paper's convention at `L = ∞`. -/
def InterpIneq {d : ℕ} {ι : Type*} (μ : NNReal) (L : ENNReal)
    (x g : ι → EuclideanSpace ℝ (Fin d)) (fv : ι → ℝ) (i j : ι) : Prop :=
  let ℓ := (L⁻¹).toReal
  (1 / (2 * (1 - (μ : ℝ) * ℓ))) *
    (ℓ * ‖g i - g j‖ ^ 2 + (μ : ℝ) * ‖x i - x j‖ ^ 2 -
      2 * ((μ : ℝ) * ℓ) * inner ℝ (g j - g i) (x j - x i)) ≤
    fv i - fv j - inner ℝ (g j) (x i - x j)

end TaylorHG.PEP


