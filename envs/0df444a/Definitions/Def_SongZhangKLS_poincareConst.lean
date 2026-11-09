-- Prove2me | Definitions.Def_SongZhangKLS_poincareConst
-- name    : SongZhangKLS_poincareConst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:05:56.61942+00:00
-- url     : https://prove2.me/theorems/93ce7528-b2f9-4f08-b094-1806e9ce5e98
-- title:
--   Dirichlet energy and the Poincaré constant $C_P(\mu)$ with the $L^2$ requirement
-- statement:
--   Let $\mu$ be a measure on $\mathbb R^n$. For $f:\mathbb R^n\to\mathbb R$, the **Dirichlet energy** of $f$ is
--   $$\mathcal E_\mu(f)=\int\|\nabla f\|^2\,d\mu\in[0,\infty].$$
--
--   The **Poincaré constant** $C_P(\mu)$ is the least $C$ for which
--   $$\mathrm{Var}_\mu[f]\le C\int\|\nabla f\|^2\,d\mu \tag{1}$$
--   holds for every locally Lipschitz $f$ with finite Dirichlet energy, with the additional requirement that every such $f$ belongs to $L^2(\mu)$. If no finite $C$ has this property, $C_P(\mu)=+\infty$.
--
--   So $C_P(\mu)<\infty$ says both that finite energy forces square integrability and that the variance is controlled by the energy. This is the constant bounded uniformly in the dimension by the KLS conjecture.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`. The energy is a lower Lebesgue integral in $[0,\infty]$ and $\nabla f$ is Mathlib's `gradient` (zero where $f$ is not differentiable, which is a Lebesgue-null set for locally Lipschitz $f$). $C_P$ is an infimum in $[0,\infty]$ over finite $C\ge0$ with the variance in $[0,\infty]$ (`evariance`); the empty infimum is $+\infty$, and one finite-energy function outside $L^2(\mu)$ empties the family.
-- source:
--   Z. Song, X. Zhang, An O(1) Bound for the KLS Constant, arXiv:2610.01447 (preprint; version of October 2026, sha256 c7d2264f…8a6c), §1, eq. (1), p.2

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace SongZhangKLS

/-- The **Dirichlet energy** `∫ ‖∇f‖² dµ` of a function `f : ℝⁿ → ℝ` under a measure `µ`
(Song, Zhang, *An O(1) Bound for the KLS Constant*, arXiv:2610.01447, version of October 2026,
sha256 c7d2264f…8a6c, §1, p.2: "The Dirichlet energy of f is ∫‖∇f‖²dµ").

**Formalization Note.** ℝⁿ is `EuclideanSpace ℝ (Fin n)`. The energy is a lower Lebesgue
integral in `ℝ≥0∞`, so it is `⊤` exactly when the energy is infinite. `∇f` is Mathlib's
`gradient f`, which is `0` at points where `f` is not differentiable; for locally Lipschitz `f`
and `µ` absolutely continuous with respect to Lebesgue measure (every isotropic log-concave
measure) this changes nothing, because `f` is differentiable almost everywhere (Rademacher). -/
def dirichletEnergy {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ‖gradient f x‖ₑ ^ 2 ∂μ

/-- The **Poincaré constant** `C_P(µ)` (Song, Zhang, arXiv:2610.01447, version of October 2026,
sha256 c7d2264f…8a6c, §1, eq. (1), p.2): the least `C` such that
`Var_µ[f] ≤ C · ∫ ‖∇f‖² dµ` for every locally Lipschitz `f : ℝⁿ → ℝ` with finite Dirichlet energy,
"with the additional requirement that every such f belongs to L²(µ)"; `+∞` if no finite `C` works.

**Formalization Note.** The value lies in `ℝ≥0∞` and is the infimum over finite constants
`C ≥ 0` for which every locally Lipschitz `f` with `dirichletEnergy µ f < ⊤` satisfies both
`MemLp f 2 µ` and `evariance f µ ≤ C · dirichletEnergy µ f`. The infimum of the empty family is
`⊤`, which is the paper's `C_P(µ) = +∞`; a single finite-energy function outside `L²(µ)` empties the
family, which is the paper's "additional requirement". `evariance` is the variance in `ℝ≥0∞`
(no junk value off `L²`). Only nonnegative `C` are considered (a variance is nonnegative). -/
def poincareConst {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  ⨅ (C : ℝ≥0) (_ : ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, LocallyLipschitz f →
      dirichletEnergy μ f < ⊤ →
        MemLp f 2 μ ∧ evariance f μ ≤ (C : ℝ≥0∞) * dirichletEnergy μ f), (C : ℝ≥0∞)

end SongZhangKLS


