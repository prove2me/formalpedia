-- Prove2me | Definitions.Def_StochFictPlay_Potential_Stability
-- name    : StochFictPlay_Potential_Stability
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:09:26.111696+00:00
-- url     : https://prove2.me/theorems/1101b2d4-06b7-463a-bdf6-a61ec895fa21
-- title:
--   Tangent space of $\Sigma$, unit tangent vectors, hyperbolic and linearly stable rest points
-- statement:
--   Let $\Sigma = \prod_\alpha \Delta S^\alpha \subseteq \prod_\alpha \mathbb R^{n^\alpha}$ and let $F$ be a vector field on $\prod_\alpha \mathbb R^{n^\alpha}$.
--
--   1. **Tangent space.** $T\Sigma = \prod_\alpha \mathbb R^{n^\alpha}_0 = \{\theta : \sum_i \theta^\alpha_i = 0 \text{ for every player } \alpha\}$.
--   2. **Unit tangent vectors.** $U = \{\theta \in T\Sigma : \sum_\alpha\sum_i (\theta^\alpha_i)^2 = 1\}$.
--   3. **Linearization on the tangent space.** If $F$ is differentiable at $x^*$ and $DF(x^*)$ maps $T\Sigma$ into itself, its eigenvalues on $T\Sigma$ are the complex roots, with multiplicity, of the characteristic polynomial of the restriction $DF(x^*)|_{T\Sigma}$.
--   4. **Hyperbolic.** $x^*$ is hyperbolic if all these eigenvalues have nonzero real part.
--   5. **Linearly stable.** $x^*$ is linearly stable if all these eigenvalues have negative real part; $LS(D)$ is the set of linearly stable rest points.
--
--   These notions enter Proposition 4.3 (hyperbolicity), Lemmas A.4–A.5 (the set $U$) and Theorem 6.1(iii) ($LS(P)$).
--
--   **Formalization Note** The paper does not define "linearly stable" beyond naming $LS(D)$; the standard meaning (every eigenvalue on the relevant tangent space has negative real part) is used. The restriction to the tangent space follows footnote 9: on the ambient space $DF(x^*)$ has the eigenvalue $-1$ in directions transverse to $\Sigma$. Eigenvalues are read off the characteristic polynomial's complex roots, which avoids complexifying the space. Invariance of $T\Sigma$ under $DF(x^*)$ is part of each definition; it holds for (P) and (PV) because their fields take values that sum to zero in each player's block along $\Sigma$.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 18, footnote 9 (hyperbolic rest point); p. 23 (LS(D)); p. 33 (the set U of unit tangent vectors)

import Mathlib
import Definitions.Def_StochFictPlay_Potential_Game
import Definitions.Def_StochFictPlay_Potential_Dynamics

namespace StochFictPlay.Potential

/-- The tangent space `∏_α ℝ^{n^α}_0 = {θ | ∑_i θ^α_i = 0 for every player α}` of the state
space `Σ` (Hofbauer–Sandholm 2002, manuscript p. 33), as a linear subspace of `Mixed n`. -/
def mixedTangent {p : ℕ} (n : Fin p → ℕ) : Submodule ℝ (Mixed n) where
  carrier := {θ | ∀ α, ∑ i, θ α i = 0}
  add_mem' := by
    intro a b ha hb α
    simp only [Set.mem_ofPred_eq, Pi.add_apply, Finset.sum_add_distrib] at *
    rw [ha α, hb α, add_zero]
  zero_mem' := by
    intro α
    simp
  smul_mem' := by
    intro c θ hθ α
    simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul] at *
    rw [← Finset.mul_sum, hθ α, mul_zero]

theorem mem_mixedTangent {p : ℕ} {n : Fin p → ℕ} {θ : Mixed n} :
    θ ∈ mixedTangent n ↔ ∀ α, ∑ i, θ α i = 0 :=
  Iff.rfl

/-- The set `U = {θ ∈ ∏_α ℝ^{n^α}_0 : ∑_α ∑_i (θ^α_i)² = 1}` of unit vectors in the tangent
space of `Σ` (manuscript p. 33), unit for the Euclidean norm. -/
def unitTangent {p : ℕ} (n : Fin p → ℕ) : Set (Mixed n) :=
  {θ | θ ∈ mixedTangent n ∧ ∑ α, ∑ i, θ α i ^ 2 = 1}

/-- The derivative `DF(x*)` of a field `F` on `Mixed n` maps the tangent space of `Σ` into
itself. Needed to restrict it to the "relevant tangent space" of footnote 9 (p. 18). -/
def TangentInvariantAt {p : ℕ} {n : Fin p → ℕ} (F : Mixed n → Mixed n) (x : Mixed n) : Prop :=
  ∀ v ∈ mixedTangent n, fderiv ℝ F x v ∈ mixedTangent n

/-- The restriction of `DF(x*)` to the tangent space of `Σ`, given that it maps the tangent
space into itself. -/
noncomputable def tangentDeriv {p : ℕ} {n : Fin p → ℕ} (F : Mixed n → Mixed n) (x : Mixed n)
    (h : TangentInvariantAt F x) : mixedTangent n →ₗ[ℝ] mixedTangent n :=
  ((fderiv ℝ F x : Mixed n →L[ℝ] Mixed n) : Mixed n →ₗ[ℝ] Mixed n).restrict h

/-- The eigenvalues of `DF(x*)` on the tangent space of `Σ`, with multiplicity: the complex roots
of the characteristic polynomial of the restricted derivative `tangentDeriv F x h`. -/
noncomputable def tangentEigenvalues {p : ℕ} {n : Fin p → ℕ} (F : Mixed n → Mixed n)
    (x : Mixed n) (h : TangentInvariantAt F x) : Multiset ℂ :=
  (LinearMap.charpoly (tangentDeriv F x h)).aroots ℂ

/-- A rest point `x*` of `ẋ = F(x)` on `Σ` is **hyperbolic** (manuscript p. 18, footnote 9) if
`F` is differentiable at `x*`, `DF(x*)` maps the tangent space of `Σ` into itself, and every
eigenvalue of `DF(x*)` on that tangent space has nonzero real part. -/
def IsHyperbolicAt {p : ℕ} {n : Fin p → ℕ} (F : Mixed n → Mixed n) (x : Mixed n) : Prop :=
  DifferentiableAt ℝ F x ∧ ∃ h : TangentInvariantAt F x,
    ∀ μ ∈ tangentEigenvalues F x h, μ.re ≠ 0

/-- `x*` is **linearly stable** (manuscript p. 23; standard meaning, the page does not define it
further): `F` is differentiable at `x*`, `DF(x*)` maps the tangent space of `Σ` into itself,
and every eigenvalue of `DF(x*)` on that tangent space has negative real part. -/
def IsLinearlyStableAt {p : ℕ} {n : Fin p → ℕ} (F : Mixed n → Mixed n) (x : Mixed n) : Prop :=
  DifferentiableAt ℝ F x ∧ ∃ h : TangentInvariantAt F x,
    ∀ μ ∈ tangentEigenvalues F x h, μ.re < 0

/-- The linearly stable rest points `LS(D) ⊂ RP(D)` of `ẋ = F(x)` on `X` (manuscript p. 23). -/
def linearlyStableSet {p : ℕ} {n : Fin p → ℕ} (F : Mixed n → Mixed n) (X : Set (Mixed n)) :
    Set (Mixed n) :=
  {x | x ∈ restPoints F X ∧ IsLinearlyStableAt F x}

end StochFictPlay.Potential


