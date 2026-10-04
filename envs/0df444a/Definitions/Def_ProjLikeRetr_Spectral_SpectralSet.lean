-- Prove2me | Definitions.Def_ProjLikeRetr_Spectral_SpectralSet
-- name    : ProjLikeRetr_Spectral_SpectralSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T02:42:16.695679+00:00
-- url     : https://prove2.me/theorems/ece24253-786e-4e38-b776-b426aaa8be55
-- title:
--   §3.4, pp. 11–12 — $\mathbb R^n_\downarrow$, sorted eigenvalues $\lambda(X)$, spectral sets $\lambda^{-1}(M)$, strong local symmetry (3.15)
-- statement:
--   Fix $n \in \mathbb N$. Vectors live in $\mathbb R^n$ with the Euclidean norm, and $\mathbf S_n$ denotes the real symmetric $n \times n$ matrices.
--
--   1. **Sorted vectors.** $\mathbb R^n_\downarrow = \{x \in \mathbb R^n : x_1 \ge x_2 \ge \cdots \ge x_n\}$.
--   2. **Eigenvalue map.** For $X \in \mathbf S_n$, $\lambda(X) \in \mathbb R^n_\downarrow$ is the vector of eigenvalues of $X$, repeated with multiplicity, in nonincreasing order: $\lambda_1(X) \ge \lambda_2(X) \ge \cdots \ge \lambda_n(X)$.
--   3. **Spectral sets.** For $M \subseteq \mathbb R^n$,
--   $$
--   \lambda^{-1}(M) = \{X \in \mathbf S_n : \lambda(X) \in M\}.
--   $$
--   4. **Permutations.** A permutation $\sigma$ of $\{1, \dots, n\}$ acts on $\mathbb R^n$ by permuting coordinates, $(Px)_i = x_{\sigma^{-1}(i)}$; these are the permutation matrices $P \in \mathbf \Sigma_n$, and they preserve the Euclidean norm, (3.13).
--   5. **Strong local symmetry** (3.15). For $\mathcal M \subseteq \mathbb R^n$, $\bar x \in \mathbb R^n$ and $\delta > 0$, the set $\mathcal M \cap B(\bar x, \delta)$ is strongly locally symmetric if for every $x \in \mathcal M \cap B(\bar x, \delta)$ and every $P \in \mathbf \Sigma_n$ with $Px = x$,
--   $$
--   P\big(\mathcal M \cap B(\bar x, \delta)\big) = \mathcal M \cap B(\bar x, \delta),
--   $$
--   where $B(\bar x, \delta)$ is the open Euclidean ball.
--
--   These are the objects of §3.4: spectral sets are the sets of symmetric matrices described by a property of their eigenvalues, and strong local symmetry of the underlying set $\mathcal M$ is the hypothesis of Theorem 3.5 under which $\lambda^{-1}(\mathcal M \cap \mathbb R^n_\downarrow)$ is a manifold and its projection is computed through $\mathcal M$.
--
--   **Formalization Note** Vectors are `EuclideanSpace ℝ (Fin n)` (Euclidean norm, not the sup norm). `eig X` uses Mathlib's `IsHermitian.eigenvalues₀`, which is sorted nonincreasingly; for a non-symmetric $X$ the value is the junk vector $0$, and every statement assumes $X$ symmetric. Over $\mathbb R$, `IsHermitian` is symmetry. The permutation action is `LinearIsometryEquiv.piLpCongrLeft`.
-- source:
--   Absil & Malick, Projection-like retractions on matrix manifolds, HAL hal-00651608v2, p. 11, §3.4 (notation, (3.9), (3.13)); p. 12, (3.14), Theorem 3.5, (3.15)

import Mathlib

namespace ProjLikeRetr.Spectral

/-- `ℝⁿ↓` (§3.4, p. 11): the vectors `x ∈ ℝⁿ` with `x₁ ≥ x₂ ≥ ⋯ ≥ xₙ`. -/
def sortedDesc (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i j : Fin n, i ≤ j → x j ≤ x i}

/-- `λ(X)` (§3.4, p. 11): for a symmetric `X`, the vector of its eigenvalues in nonincreasing
order `λ₁(X) ≥ ⋯ ≥ λₙ(X)` (Mathlib's sorted `eigenvalues₀`). Junk value `0` when `X` is not
symmetric; every statement assumes `X.IsHermitian`. -/
noncomputable def eig {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) : EuclideanSpace ℝ (Fin n) :=
  if h : X.IsHermitian then
    WithLp.toLp 2 (fun i : Fin n => h.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm i))
  else 0

/-- The spectral set `λ⁻¹(M) = {X ∈ 𝐒ₙ : λ(X) ∈ M}` of (3.14), p. 12. -/
def specSet {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin n))) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {X | X.IsHermitian ∧ eig X ∈ M}

/-- The action of a permutation `P ∈ 𝚺ₙ` on `ℝⁿ`, `(σ • x)ᵢ = x_{σ⁻¹ i}`; a linear isometry
of the Euclidean norm, which is (3.13). -/
noncomputable def permAct {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ x

/-- Strong local symmetry (3.15), p. 12: for every `x ∈ M ∩ B(x̄, δ)` and every permutation
`P` with `Px = x`, `P(M ∩ B(x̄, δ)) = M ∩ B(x̄, δ)`, with `B(x̄, δ)` the open ball. -/
def IsStronglyLocallySymmetric {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin n)))
    (xbar : EuclideanSpace ℝ (Fin n)) (δ : ℝ) : Prop :=
  ∀ x ∈ M ∩ Metric.ball xbar δ, ∀ σ : Equiv.Perm (Fin n), permAct σ x = x →
    permAct σ '' (M ∩ Metric.ball xbar δ) = M ∩ Metric.ball xbar δ

end ProjLikeRetr.Spectral


