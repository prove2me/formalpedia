-- Prove2me | Definitions.Def_HighDimStat_Decomposability_Core
-- name    : HighDimStat_Decomposability_Core
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:15:10.484732+00:00
-- url     : https://prove2.me/theorems/71648405-5c2f-4a90-929a-9cf001540509
-- title:
--   Decomposable regularizers, dual norms and restricted curvature (Ch. 9 core objects)
-- statement:
--   This file collects the shared geometric and statistical vocabulary of Wainwright's Chapter 9
--   "Decomposability and restricted strong convexity" — the objects that Proposition 9.13,
--   Theorem 9.19, Corollary 9.20 and Theorem 9.24 are all stated in terms of. `Ω` is a finite-
--   dimensional real inner product space (the parameter space, e.g. $\mathbb R^d$ or a matrix
--   space).
--
--   - **`IsRegularizerNorm Φ`**: `Φ : Ω → ℝ` is a genuine norm (nonnegative, definite,
--     absolutely homogeneous, subadditive), the standing hypothesis "let the regularizer
--     $\Phi:\Omega\to[0,\infty)$ be a norm" used throughout the chapter.
--   - **`dualNorm Φ v`**: the dual norm $\Phi^*(v) := \sup_{\Phi(u)\le 1}\langle u,v\rangle$,
--     Eq. (9.27).
--   - **`subspaceLip Φ S`**: the subspace Lipschitz constant $\Psi(S) := \sup_{u\in
--     S\setminus\{0\}}\Phi(u)/\|u\|$, Definition 9.18, Eq. (9.44).
--   - **`IsDecomposable Φ M Mbar`**: given a pair of subspaces $M\subseteq\bar{\mathcal M}$, the
--     regularizer decomposes as $\Phi(\alpha+\beta)=\Phi(\alpha)+\Phi(\beta)$ for every
--     $\alpha\in M$ and $\beta\in\bar{\mathcal M}^\perp$, Definition 9.9, Eq. (9.22).
--   - **`taylorError Ln g θstar Δ`**: the first-order Taylor-series error
--     $E_n(\Delta):=L_n(\theta^*+\Delta)-L_n(\theta^*)-\langle g,\Delta\rangle$, Eq. (9.36), with
--     `g` standing for the score function $\nabla L_n(\theta^*)$.
--   - **`goodEvent Φ g lamN`**: the "good event" $\mathcal G(\lambda_n):=\{\Phi^*(g)\le
--     \lambda_n/2\}$, Eq. (9.28)/(9.46), conditioning every result in this chapter.
--   - **`RSC Ln g θstar Φ κ τnSq R`**: the restricted strong convexity condition of Definition
--     9.15, Eq. (9.38): $E_n(\Delta)\ge\frac{\kappa}{2}\|\Delta\|^2-\tau_n^2\Phi^2(\Delta)$ for
--     every $\Delta$ with $\|\Delta\|\le R$.
--   - **`errorCone Φ M Mbar θstar`**: the cone $\mathbb
--     C_{\theta^*}(\mathcal M,\bar{\mathcal M}^\perp):=\{\Delta\mid
--     \Phi(\Delta_{\bar{\mathcal M}^\perp})\le
--     3\Phi(\Delta_{\bar{\mathcal M}})+4\Phi(\theta^*_{\mathcal M^\perp})\}$ of Proposition 9.13,
--     Eq. (9.29).
--   - **`DualCurvature Dg Φ κ τn R`**: the $\Phi^*$-curvature condition of Definition 9.22,
--     Eq. (9.55): $\Phi^*(\nabla L_n(\theta^*+\Delta)-\nabla L_n(\theta^*))\ge\kappa\Phi^*(\Delta)
--     -\tau_n\Phi(\Delta)$ for $\Delta$ with $\Phi^*(\Delta)\le R$, with `Dg Δ` standing for the
--     gradient increment $\nabla L_n(\theta^*+\Delta)-\nabla L_n(\theta^*)$.
--   - **`epsilonSq Φ M Mbar θstar lamN κ τnSq`**: the combined estimation-plus-approximation
--     error bound $\varepsilon_n^2(\mathcal M,\bar{\mathcal M})$ of Theorem 9.19, Eq. (9.47).
--
--   **Formalization Note** The book's printed text loses the overbar on $\bar{\mathcal M}$ in
--   several displayed places (a known PDF-extraction artifact of this source); every quantity
--   here was checked against the surrounding proof text, which fixes the bar unambiguously
--   (e.g. the proof of Theorem 9.19(a) applies $\Psi(\cdot)$ to $\Delta_{\bar{\mathcal M}}\in
--   \bar{\mathcal M}$, so that occurrence of the Lipschitz constant must be $\Psi(\bar{\mathcal
--   M})$, not $\Psi(\mathcal M)$; `subspaceLip Φ Mbar` throughout this mission reflects that
--   resolution). `errorCone` keeps the bar only on the two $\Delta$-projections
--   (`Mbar.starProjection`, `Mbarᗮ.starProjection`), never on `θ*`'s projection
--   (`Mᗮ.starProjection θstar`, the complement of the *small* subspace `M`), matching
--   Eq. (9.21)'s definition of the perturbation subspace and Eq. (9.29)'s own notation. `Ω`
--   carries `[FiniteDimensional ℝ Ω]` so that `starProjection` (orthogonal projection onto a
--   complete, hence closed, subspace) is always well defined, matching the book's implicit
--   finite-dimensional setting throughout Part II.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, pp. 269, 272-273, 277, 279 (PDF pp. 289, 292-293, 297, 299), Definitions 9.9, 9.15, 9.18, 9.22, Eqs. (9.20)-(9.29), (9.36)-(9.47)

import Mathlib

namespace HighDimStat.Decomposability

open scoped RealInnerProductSpace

variable {Ω : Type*} [NormedAddCommGroup Ω] [InnerProductSpace ℝ Ω] [FiniteDimensional ℝ Ω]

/-- A regularizer `Φ : Ω → ℝ` that is a genuine norm on `Ω` (Wainwright, *High-Dimensional
Statistics*, §9.4.1, p. 280: "let the regularizer `Φ : Ω → [0,∞)` be a norm", the standing
hypothesis used throughout Chapter 9). -/
structure IsRegularizerNorm (Φ : Ω → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ Φ x
  eq_zero_iff : ∀ x, Φ x = 0 ↔ x = 0
  smul_abs : ∀ (c : ℝ) (x : Ω), Φ (c • x) = |c| * Φ x
  triangle : ∀ x y, Φ (x + y) ≤ Φ x + Φ y

/-- The dual norm of a regularizer (p. 272, Eq. (9.27)): `Φ*(v) := sup_{Φ(u) ≤ 1} ⟨u, v⟩`. -/
noncomputable def dualNorm (Φ : Ω → ℝ) (v : Ω) : ℝ :=
  sSup {r : ℝ | ∃ u : Ω, Φ u ≤ 1 ∧ r = ⟪u, v⟫}

/-- The subspace Lipschitz constant of the pair `(Φ, ‖·‖)` on a subspace `S`
(Definition 9.18, p. 279, Eq. (9.44)): `Ψ(S) := sup_{u ∈ S \ {0}} Φ(u) / ‖u‖`. -/
noncomputable def subspaceLip (Φ : Ω → ℝ) (S : Submodule ℝ Ω) : ℝ :=
  sSup {r : ℝ | ∃ u ∈ S, u ≠ 0 ∧ r = Φ u / ‖u‖}

/-- A regularizer `Φ` is decomposable with respect to the subspace pair `(M, M̄)` with `M ≤ M̄`
(Definition 9.9, p. 269, Eq. (9.22)): `Φ(α + β) = Φ(α) + Φ(β)` for every `α ∈ M` and
`β ∈ M̄ᗮ` (the perturbation subspace, the orthogonal complement of the *larger* subspace `M̄`,
Eq. (9.21)). -/
def IsDecomposable (Φ : Ω → ℝ) (M Mbar : Submodule ℝ Ω) : Prop :=
  M ≤ Mbar ∧ ∀ α ∈ M, ∀ β ∈ Mbarᗮ, Φ (α + β) = Φ α + Φ β

/-- The first-order Taylor-series error of the cost function `Ln` at `θ* + Δ`, with `g`
standing for the score function `∇Ln(θ*)` (p. 277, Eq. (9.36)):
`E_n(Δ) := Ln(θ* + Δ) - Ln(θ*) - ⟨g, Δ⟩`. Convexity of `Ln` is exactly what makes this
quantity nonnegative for every `Δ` (p. 277, footnote 2). -/
def taylorError (Ln : Ω → ℝ) (g θstar : Ω) (Δ : Ω) : ℝ :=
  Ln (θstar + Δ) - Ln θstar - ⟪g, Δ⟫

/-- The "good event" `G(lamN)` (p. 273/280, Eq. (9.28)/(9.46)): the dual-norm bound on the
score function `∇Ln(θ*)` (represented here by `g`) that the choice of regularization weight
`lamN` is meant to satisfy: `Φ*(∇Ln(θ*)) ≤ lamN / 2`. -/
def goodEvent (Φ : Ω → ℝ) (g : Ω) (lamN : ℝ) : Prop :=
  dualNorm Φ g ≤ lamN / 2

/-- The restricted strong convexity (RSC) condition (Definition 9.15, p. 277, Eq. (9.38)),
with curvature `κ`, tolerance `τn²` and radius `R`:
`E_n(Δ) ≥ κ/2 ‖Δ‖² - τn² Φ²(Δ)` for every `Δ` in the ball `B(R) = {Δ | ‖Δ‖ ≤ R}`. -/
def RSC (Ln : Ω → ℝ) (g θstar : Ω) (Φ : Ω → ℝ) (κ τnSq R : ℝ) : Prop :=
  ∀ Δ : Ω, ‖Δ‖ ≤ R → taylorError Ln g θstar Δ ≥ κ / 2 * ‖Δ‖ ^ 2 - τnSq * Φ Δ ^ 2

/-- The error cone `C_{θ*}(M, M̄)` of Proposition 9.13 (p. 273, Eq. (9.29)): every error
vector conditioned on the good event lies here. `Mbar.starProjection Δ` and
`Mbarᗮ.starProjection Δ` are `Δ`'s orthogonal projections onto the *closure* `M̄` and its
complement `M̄ᗮ`; `Mᗮ.starProjection θstar` is `θ*`'s projection onto `M ᗮ`, the complement of
the *small* subspace `M` (not `M̄`) — the chapter's own warning to "keep the bar" on the two
`Δ`-projections but not on `θ*`'s. -/
def errorCone (Φ : Ω → ℝ) (M Mbar : Submodule ℝ Ω) (θstar : Ω) : Set Ω :=
  {Δ : Ω | Φ (Mbarᗮ.starProjection Δ) ≤
      3 * Φ (Mbar.starProjection Δ) + 4 * Φ (Mᗮ.starProjection θstar)}

/-- The Φ*-curvature condition (Definition 9.22, p. 284, Eq. (9.55)), with curvature `κ`,
tolerance `τn` and radius `R`, on the gradient increment `∇Ln(θ*+Δ) - ∇Ln(θ*)` (represented
abstractly here by the map `Dg : Δ ↦ ∇Ln(θ*+Δ) - ∇Ln(θ*)`):
`Φ*(Dg(Δ)) ≥ κ Φ*(Δ) - τn Φ(Δ)` for every `Δ` in the dual-norm ball `BΦ*(R)`. -/
def DualCurvature (Dg : Ω → Ω) (Φ : Ω → ℝ) (κ τn R : ℝ) : Prop :=
  ∀ Δ : Ω, dualNorm Φ Δ ≤ R → dualNorm Φ (Dg Δ) ≥ κ * dualNorm Φ Δ - τn * Φ Δ

/-- The combined estimation-plus-approximation error bound `ε_n²(M, M̄)` of Theorem 9.19
(p. 280, Eq. (9.47)). -/
noncomputable def epsilonSq (Φ : Ω → ℝ) (M Mbar : Submodule ℝ Ω) (θstar : Ω)
    (lamN κ τnSq : ℝ) : ℝ :=
  9 * lamN ^ 2 / κ ^ 2 * subspaceLip Φ Mbar ^ 2 +
    8 / κ * (lamN * Φ (Mᗮ.starProjection θstar) + 16 * τnSq * Φ (Mᗮ.starProjection θstar) ^ 2)

end HighDimStat.Decomposability


