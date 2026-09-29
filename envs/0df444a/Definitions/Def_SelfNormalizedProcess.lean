-- Prove2me | Definitions.Def_SelfNormalizedProcess
-- name    : SelfNormalizedProcess
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-07-29T00:15:10.745177+00:00
-- url     : https://prove2.me/theorems/e4b5be25-352d-4aee-81cd-7f554afba4e9
-- statement:
--   Shared setup for L&S Chapters 20-21: the noise-weighted action sum and the regularized design matrix
--
--   $$S_t = \sum_{s=1}^t \eta_s A_s, \qquad V_t(\lambda) = \lambda I + \sum_{s=1}^t A_s A_s^\top;$$
--
--   the exponential process
--
--   $$M_t(x) = \exp\Big(\langle x, S_t\rangle - \tfrac{1}{2}\|x\|^2_{V_t(\lambda)}\Big);$$
--
--   the regularized least-squares estimator
--
--   $$\hat\theta_t = V_t(\lambda)^{-1} \sum_{s=1}^t X_s A_s;$$
--
--   and, for optimal design, the notion of a design (probability measure supported in a compact action set $\mathcal{A} \subseteq \mathbb{R}^d$), its moment matrix and the G-objective
--
--   $$V(\pi) = \int a\,a^\top\,d\pi(a), \qquad g(\pi) = \sup_{a\in\mathcal{A}} \|a\|^2_{V(\pi)^{-1}},$$
--
--   and G-optimality (nondegenerate minimizer of $g$ among nondegenerate designs). Vectors are plain functions `Fin d → ℝ` and quadratic forms are written `x ⬝ᵥ M *ᵥ x`.
-- source:
--   L&S Eq. (20.1), Lemma 20.2 (p.257), Eq. (21.2) (p.267)

import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
Lattimore & Szepesvári, *Bandit Algorithms* (CUP 2020), Chapters 20-21.

Shared objects for self-normalized concentration (Ch 20, §20.1) and optimal
experimental design (Ch 21, §21.1). Vectors are plain `Fin d → ℝ` and matrix
quadratic forms are written with `dotProduct`/`mulVec` (`x ⬝ᵥ M *ᵥ x`).

Time is indexed by `ℕ` with the process starting at round `1`: sums over
`s ∈ Finset.range t` use index `s + 1`, so that the time-`t` objects depend on
rounds `1, …, t` and the time-`0` objects are the empty sum (the book's
convention `S_t = ∑_{s=1}^t η_s A_s`, `V_t(λ) = λ I + ∑_{s=1}^t A_s A_sᵀ`).
-/

open Matrix MeasureTheory

namespace BanditAlgorithm

/-- `S_t = ∑_{s=1}^t η_s A_s`, the noise-weighted sum of the actions
(L&S p.257). `S_0 = 0`. -/
noncomputable def selfNormalizedSum {Ω : Type*} (d : ℕ) (η : ℕ → Ω → ℝ)
    (A : ℕ → Ω → Fin d → ℝ) (t : ℕ) (ω : Ω) : Fin d → ℝ :=
  ∑ s ∈ Finset.range t, η (s + 1) ω • A (s + 1) ω

/-- `V_t(λ) = λ I + ∑_{s=1}^t A_s A_sᵀ`, the regularized design matrix of the
actions `A_1, …, A_t` (L&S Eq. (20.1)). `V_0(λ) = λ I`. -/
noncomputable def regularizedDesignMatrix {Ω : Type*} (d : ℕ) (lam : ℝ)
    (A : ℕ → Ω → Fin d → ℝ) (t : ℕ) (ω : Ω) : Matrix (Fin d) (Fin d) ℝ :=
  lam • (1 : Matrix (Fin d) (Fin d) ℝ) +
    ∑ s ∈ Finset.range t, vecMulVec (A (s + 1) ω) (A (s + 1) ω)

/-- `M_t(x) = exp (⟨x, S_t⟩ - ½ ‖x‖²_{V_t(λ)})`, the exponential process of
L&S Lemma 20.2 (p.257). -/
noncomputable def selfNormalizedProcess {Ω : Type*} (d : ℕ) (lam : ℝ)
    (η : ℕ → Ω → ℝ) (A : ℕ → Ω → Fin d → ℝ) (x : Fin d → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  Real.exp (x ⬝ᵥ selfNormalizedSum d η A t ω
    - 1 / 2 * (x ⬝ᵥ regularizedDesignMatrix d lam A t ω *ᵥ x))

/-- `θ̂_t = V_t(λ)⁻¹ ∑_{s=1}^t X_s A_s`, the `λ`-regularized least-squares
estimator computed from rewards `X_s` and actions `A_s` (L&S Eq. (20.1)). -/
noncomputable def regularizedLeastSquares {Ω : Type*} (d : ℕ) (lam : ℝ)
    (A : ℕ → Ω → Fin d → ℝ) (X : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : Fin d → ℝ :=
  (regularizedDesignMatrix d lam A t ω)⁻¹ *ᵥ
    ∑ s ∈ Finset.range t, X (s + 1) ω • A (s + 1) ω

/-- A *design* on an action set `𝒜 ⊆ ℝ^d` is a probability measure supported
in `𝒜` (L&S §21.1, generalizing the finitely supported `π : 𝒜 → [0,1]`,
`∑_a π(a) = 1`). -/
def IsDesignOn (d : ℕ) (𝒜 : Set (Fin d → ℝ)) (π : Measure (Fin d → ℝ)) : Prop :=
  IsProbabilityMeasure π ∧ π 𝒜ᶜ = 0

/-- `V(π) = ∫ a aᵀ dπ(a)`, the design matrix (moment matrix) of a design `π`
(L&S Eq. (21.2)); entrywise `V(π) i j = ∫ a_i a_j dπ(a)`. -/
noncomputable def designMatrix (d : ℕ) (π : Measure (Fin d → ℝ)) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => ∫ a, a i * a j ∂π

/-- `g(π) = sup_{a ∈ 𝒜} ‖a‖²_{V(π)⁻¹}`, the objective of the G-optimal design
problem (L&S Eq. (21.2)), as a real supremum over the action set. Only
meaningful when `V(π)` is invertible (Mathlib's `V(π)⁻¹` is the zero matrix
otherwise, giving the junk value `g(π) = 0`). -/
noncomputable def designGValue (d : ℕ) (𝒜 : Set (Fin d → ℝ))
    (π : Measure (Fin d → ℝ)) : ℝ :=
  sSup ((fun a => a ⬝ᵥ (designMatrix d π)⁻¹ *ᵥ a) '' 𝒜)

/-- `πs` is a *G-optimal design* for `𝒜`: its design matrix is nondegenerate
and it minimizes `g` among all nondegenerate designs on `𝒜`. Nondegeneracy
(`(designMatrix d π).PosDef`) is required of the competitors because Mathlib's
matrix inverse assigns the junk value `V(π)⁻¹ = 0` — hence `g(π) = 0` — to
degenerate designs, which morally have `g(π) = ∞`. -/
def IsGOptimalDesign (d : ℕ) (𝒜 : Set (Fin d → ℝ)) (πs : Measure (Fin d → ℝ)) : Prop :=
  (designMatrix d πs).PosDef ∧
    ∀ π : Measure (Fin d → ℝ), IsDesignOn d 𝒜 π → (designMatrix d π).PosDef →
      designGValue d 𝒜 πs ≤ designGValue d 𝒜 π

end BanditAlgorithm


