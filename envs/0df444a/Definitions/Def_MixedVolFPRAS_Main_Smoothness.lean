-- Prove2me | Definitions.Def_MixedVolFPRAS_Main_Smoothness
-- name    : MixedVolFPRAS_Main_Smoothness
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:30:33.469025+00:00
-- url     : https://prove2.me/theorems/64be038a-7147-4455-860d-b5b5416fd920
-- title:
--   R-well-rounded and (λ, Λ, M)-smooth convex bodies (Definitions 3.1, 3.2)
-- statement:
--   For $R>0$, a convex body $K\subseteq\mathbb{R}^n$ is **$R$-well-rounded** if $B_2^n\subseteq K\subseteq RB_2^n$ (Definition 3.1).
--
--   Fix parameters $\Lambda\ge1\ge\lambda>0$ and $M>0$. A convex body $K$ is **$(\lambda,\Lambda,M)$-smooth** (Definition 3.2) if
--   - $h_K$ is $C^\infty$ on $\mathbb{R}^n\setminus\{0\}$;
--   - $\lambda I\preceq D^2h_K(\theta)\preceq\Lambda I$ on $\theta^\perp$ for every $\theta\in S^{n-1}$;
--   - $|\partial_a\partial_b\partial_c h_K(\theta)|\le M$ for every $\theta\in S^{n-1}$ and all unit vectors $a,b,c\in\mathbb{R}^n$.
--
--   $$\lambda I\preceq D^2h_K(\theta)\preceq\Lambda I,\qquad |\partial_a\partial_b\partial_c h_K(\theta)|\le M .$$
--
--   **Formalization Note.** `IsWellRounded R K` is `unitBall n ⊆ K ∧ K ⊆ R • unitBall n`. `IsSmoothBody lam Lam M K` (`lam`, `Lam` for $\lambda$, $\Lambda$) contains the parameter conditions $1\le\Lambda$, $\lambda\le1$, $0<\lambda$, $0<M$, that $K$ is a convex body, `ContDiffOn ℝ ∞ (supportFunction K) {0}ᶜ`, the two positive-semidefiniteness conditions on `restrictedHessian (supportFunction K) θ` minus/plus multiples of the identity, and the bound on `iteratedFDeriv ℝ 3 (supportFunction K) θ ![a, b, c]`.
-- source:
--   Chen, Liu, An FPRAS for Mixed Volumes, STOC 2027 submission (manuscript sha256 0acf8d97…), p. 12, Definitions 3.1 and 3.2

import Mathlib
import Definitions.Def_MixedVolFPRAS_Main_ConvexGeometry
import Definitions.Def_MixedVolFPRAS_Main_MixedDiscriminant

open scoped Pointwise ContDiff

noncomputable section

namespace MixedVolFPRAS.Main

/-!
# Well-roundedness and `(λ, Λ, M)`-smoothness (Definitions 3.1 and 3.2)

Chen, Liu, *An FPRAS for Mixed Volumes*, p. 12.

* `K` is `R`-well-rounded when `B₂ⁿ ⊆ K ⊆ R B₂ⁿ`.
* For parameters `Λ ≥ 1 ≥ λ > 0` and `M > 0`, a convex body `K` is `(λ, Λ, M)`-smooth when
  `h_K` is `C^∞` on `ℝⁿ \ {0}`, `λ I ⪯ D²h_K(θ) ⪯ Λ I` on `θ^⊥` for every `θ ∈ Sⁿ⁻¹`, and
  `|∂_a ∂_b ∂_c h_K(θ)| ≤ M` for every `θ ∈ Sⁿ⁻¹` and all unit vectors `a, b, c`.
  The parameter conditions are part of the predicate. `lam`, `Lam` stand for `λ`, `Λ`.
-/

/-- Definition 3.1: `B₂ⁿ ⊆ K ⊆ R B₂ⁿ`. -/
def IsWellRounded {n : ℕ} (R : ℝ) (K : Set (E n)) : Prop :=
  unitBall n ⊆ K ∧ K ⊆ R • unitBall n

/-- Definition 3.2: `K` is a `(λ, Λ, M)`-smooth convex body, with `Λ ≥ 1 ≥ λ > 0`, `M > 0`. -/
def IsSmoothBody {n : ℕ} (lam Lam M : ℝ) (K : Set (E n)) : Prop :=
  1 ≤ Lam ∧ lam ≤ 1 ∧ 0 < lam ∧ 0 < M ∧ IsConvexBody K ∧
    ContDiffOn ℝ ∞ (supportFunction K) {0}ᶜ ∧
    (∀ θ ∈ unitSphere n,
      (restrictedHessian (supportFunction K) θ - lam • (1 : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ)).PosSemidef ∧
      (Lam • (1 : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ) - restrictedHessian (supportFunction K) θ).PosSemidef) ∧
    ∀ θ ∈ unitSphere n, ∀ a b c : E n, ‖a‖ = 1 → ‖b‖ = 1 → ‖c‖ = 1 →
      |iteratedFDeriv ℝ 3 (supportFunction K) θ ![a, b, c]| ≤ M

end MixedVolFPRAS.Main


