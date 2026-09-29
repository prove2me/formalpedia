-- Prove2me | Definitions.Def_UnifiedMEstimator_General_Core
-- name    : UnifiedMEstimator_General_Core
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:12:13.425213+00:00
-- url     : https://prove2.me/theorems/94a69204-bac5-4f28-81de-f99f339ad0ec
-- title:
--   Decomposable regularizers, dual norm, subspace compatibility constant, the set $\mathbb C(\mathcal M,\overline{\mathcal M}^\perp;\theta^*)$ and restricted strong convexity
-- statement:
--   This file fixes the objects of Section 2 of Negahban, Ravikumar, Wainwright and Yu on which their main theorem is stated.
--
--   Let $E$ be a finite-dimensional real inner product space with inner product $\langle\cdot,\cdot\rangle$ and induced norm $\|\cdot\|$ (the paper's $\mathbb R^p$ with an arbitrary inner product and the error norm it induces). For a subspace $S\subseteq E$ and $u\in E$ write $u_S=\Pi_S(u)$ for the orthogonal projection of $u$ onto $S$ (Eq. (4)) and $S^\perp$ for the orthogonal complement (Eq. (2)).
--
--   1. **Norm regularizer.** $\mathcal R:E\to\mathbb R$ is a norm: $\mathcal R(x)\ge0$, $\mathcal R(x)=0\iff x=0$, $\mathcal R(cx)=|c|\,\mathcal R(x)$ and $\mathcal R(x+y)\le\mathcal R(x)+\mathcal R(y)$.
--   2. **Decomposability** (Definition 1, Eq. (3)). Given subspaces $\mathcal M\subseteq\overline{\mathcal M}$, the regularizer is decomposable with respect to $(\mathcal M,\overline{\mathcal M}^\perp)$ if
--   $$\mathcal R(\theta+\gamma)=\mathcal R(\theta)+\mathcal R(\gamma)\qquad\text{for all }\theta\in\mathcal M,\ \gamma\in\overline{\mathcal M}^\perp .$$
--   The inclusion $\mathcal M\subseteq\overline{\mathcal M}$ is part of the definition.
--   3. **Dual norm** (Eq. (14)). $\mathcal R^*(v)=\sup_{\mathcal R(u)\le1}\langle u,v\rangle$.
--   4. **Subspace compatibility constant** (Definition 3, Eq. (21)). $\Psi(S)=\sup_{u\in S\setminus\{0\}}\mathcal R(u)/\|u\|$.
--   5. **The set $\mathbb C$** (Eq. (17)). For $\theta^*\in E$,
--   $$\mathbb C(\mathcal M,\overline{\mathcal M}^\perp;\theta^*)=\bigl\{\Delta\in E \;\big|\; \mathcal R(\Delta_{\overline{\mathcal M}^\perp})\le 3\,\mathcal R(\Delta_{\overline{\mathcal M}})+4\,\mathcal R(\theta^*_{\mathcal M^\perp})\bigr\}.$$
--   6. **Taylor error** (Eq. (18)). For a loss $\mathcal L:E\to\mathbb R$, $\delta\mathcal L(\Delta,\theta^*)=\mathcal L(\theta^*+\Delta)-\mathcal L(\theta^*)-\langle\nabla\mathcal L(\theta^*),\Delta\rangle$.
--   7. **Restricted strong convexity** (Definition 2, Eq. (19)). $\mathcal L$ satisfies RSC with curvature $\kappa_{\mathcal L}>0$ and tolerance $\tau_{\mathcal L}(\theta^*)$ if
--   $$\delta\mathcal L(\Delta,\theta^*)\ge\kappa_{\mathcal L}\|\Delta\|^2-\tau_{\mathcal L}^2(\theta^*)\qquad\text{for all }\Delta\in\mathbb C(\mathcal M,\overline{\mathcal M}^\perp;\theta^*).$$
--   8. **Optimal solutions of program (1).** $\hat\theta$ is optimal for $\lambda$ if $\mathcal L(\hat\theta)+\lambda\mathcal R(\hat\theta)\le\mathcal L(\theta)+\lambda\mathcal R(\theta)$ for every $\theta\in E$.
--
--   These are the conditions (G1)–(G2) and the quantities in which Theorem 1 of the paper, and all its corollaries, are stated.
--
--   **Formalization Note** Every finite-dimensional real inner product space is $\mathbb R^p$ with some inner product, so working on an abstract $E$ is the paper's generality; the projections are Mathlib's `Submodule.starProjection`. The dual norm and $\Psi$ are real suprema (`sSup`). When $\mathcal R$ is a norm on the finite-dimensional $E$ both sets are nonempty (except $\Psi(\{0\})$, whose set is empty and whose value is $0$) and bounded above, since all norms on $E$ are equivalent, so they equal the paper's suprema; for a function that is not a norm the value can be the junk $0$, which is why every theorem assumes the norm predicate. The tolerance is a real number $\tau$ entering as $\tau^2$, so it cannot be negative. The Taylor error uses Mathlib's `gradient`, which is the true gradient because every theorem assumes $\mathcal L$ differentiable. RSC bundles $\kappa>0$, as Definition 2 does.
-- source:
--   Negahban, Ravikumar, Wainwright and Yu, A Unified Framework for High-Dimensional Analysis of M-Estimators with Decomposable Regularizers, arXiv:1010.2731v3, pp. 3-9, Eq. (1) (p. 3), Eqs. (2)-(4) and Definition 1 (p. 4), Eq. (14) (p. 6), Eq. (17) (p. 7), Eq. (18) (p. 8), Definitions 2 and 3, Eqs. (19), (21) (p. 9)

import Mathlib

namespace UnifiedMEstimator.General

open scoped RealInnerProductSpace

/-!
Objects of Negahban, Ravikumar, Wainwright and Yu, *A Unified Framework for High-Dimensional
Analysis of M-Estimators with Decomposable Regularizers*, arXiv:1010.2731v3, Section 2 (pp. 3–9).

The parameter space `ℝ^p` with an arbitrary inner product `⟨·,·⟩` and its induced error norm
`‖·‖` (p. 4) is modelled by an arbitrary finite-dimensional real inner product space `E`.
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The regularizer `R : E → ℝ` is a norm (p. 3, "`R : ℝ^p → ℝ₊` is a norm"; condition (G1),
p. 10): nonnegative, definite, absolutely homogeneous and subadditive. -/
structure IsNormFn (R : E → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ R x
  eq_zero_iff : ∀ x, R x = 0 ↔ x = 0
  smul_abs : ∀ (c : ℝ) (x : E), R (c • x) = |c| * R x
  triangle : ∀ x y, R (x + y) ≤ R x + R y

/-- Definition 1 (p. 4, Eq. (3)): given subspaces `M ⊆ M̄`, the regularizer `R` is decomposable
with respect to `(M, M̄⊥)` if `R(θ + γ) = R(θ) + R(γ)` for all `θ ∈ M` and `γ ∈ M̄⊥`, where
`M̄⊥` is the orthogonal complement (2) of `M̄`. The inclusion `M ⊆ M̄` is part of the predicate. -/
def IsDecomposable (R : E → ℝ) (M Mbar : Submodule ℝ E) : Prop :=
  M ≤ Mbar ∧ ∀ θ ∈ M, ∀ γ ∈ Mbarᗮ, R (θ + γ) = R θ + R γ

/-- The dual norm (p. 6, Eq. (14)): `R*(v) := sup_{R(u) ≤ 1} ⟨u, v⟩`. For a norm `R` on the
finite-dimensional space `E` the set is nonempty (it contains `⟨0, v⟩ = 0`) and bounded above,
so the real supremum is the paper's. -/
noncomputable def dualNorm (R : E → ℝ) (v : E) : ℝ :=
  sSup {r : ℝ | ∃ u : E, R u ≤ 1 ∧ r = ⟪u, v⟫}

/-- The subspace compatibility constant (Definition 3, p. 9, Eq. (21)):
`Ψ(S) := sup_{u ∈ S ∖ {0}} R(u) / ‖u‖`. For a norm `R` on the finite-dimensional space `E` the
set is bounded above; it is empty exactly when `S = {0}`, in which case the value is `0`. -/
noncomputable def compat (R : E → ℝ) (S : Submodule ℝ E) : ℝ :=
  sSup {r : ℝ | ∃ u ∈ S, u ≠ 0 ∧ r = R u / ‖u‖}

/-- The set `C(M, M̄⊥; θ*)` of Lemma 1 (p. 7, Eq. (17)):
`{Δ | R(Δ_{M̄⊥}) ≤ 3 R(Δ_{M̄}) + 4 R(θ*_{M⊥})}`, where `u_S` is the orthogonal projection (4)
of `u` onto the subspace `S`. The bars are on both projections of `Δ`, not on that of `θ*`. -/
def setC (R : E → ℝ) (M Mbar : Submodule ℝ E) (θstar : E) : Set E :=
  {Δ : E | R (Mbarᗮ.starProjection Δ) ≤
      3 * R (Mbar.starProjection Δ) + 4 * R (Mᗮ.starProjection θstar)}

/-- The first-order Taylor-series error of the loss at `θ*` in direction `Δ` (p. 8, Eq. (18)):
`δL(Δ, θ*) := L(θ* + Δ) − L(θ*) − ⟨∇L(θ*), Δ⟩`. Every result using it assumes `L`
differentiable, so that `gradient L θstar` is the true gradient. -/
noncomputable def taylorErr (L : E → ℝ) (θstar Δ : E) : ℝ :=
  L (θstar + Δ) - L θstar - ⟪gradient L θstar, Δ⟫

/-- Restricted strong convexity (Definition 2, p. 9, Eq. (19)) with curvature `κ > 0` and
tolerance `τ = τ_L(θ*)`: `δL(Δ, θ*) ≥ κ ‖Δ‖² − τ²` for all `Δ ∈ C(M, M̄⊥; θ*)`. -/
def RSC (L R : E → ℝ) (M Mbar : Submodule ℝ E) (θstar : E) (κ τ : ℝ) : Prop :=
  0 < κ ∧ ∀ Δ ∈ setC R M Mbar θstar, κ * ‖Δ‖ ^ 2 - τ ^ 2 ≤ taylorErr L θstar Δ

/-- `θhat` is an optimal solution of the regularized M-estimation program (1), p. 3:
`θhat ∈ argmin_θ { L(θ) + λ R(θ) }`. -/
def IsOptimal (L R : E → ℝ) (lam : ℝ) (θhat : E) : Prop :=
  ∀ θ : E, L θhat + lam * R θhat ≤ L θ + lam * R θ

end UnifiedMEstimator.General


