-- Prove2me | Definitions.Def_UnphysicalHilbert_StateSpace
-- name    : UnphysicalHilbert_StateSpace
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-12T21:03:11.947247+00:00
-- url     : https://prove2.me/theorems/42b37515-917f-45f8-ab59-bc541871168d
-- title:
--   Pure states, finite mixtures and the entropy of an equal mixture
-- statement:
--   Let $H$ be a complex inner product space (not necessarily complete), with inner product $\langle\cdot,\cdot\rangle$ linear in the second argument.
--
--   1. **Rank-one operator.** For $\psi\in H$, $|\psi\rangle\langle\psi|$ is the linear map $x\mapsto\langle\psi,x\rangle\,\psi$.
--   2. **Mixture.** For a finite family of vectors $(\psi_i)_{i\in I}$ and real weights $(a_i)_{i\in I}$,
--   $$\mathrm{mixture}(a,\psi)=\sum_{i\in I} a_i\,|\psi_i\rangle\langle\psi_i| .$$
--   3. **Strictly convex weights.** $(a_i)$ are strictly convex weights if $a_i>0$ for all $i$ and $\sum_i a_i=1$. A family $(\psi_i)$ is **normalized** if $\|\psi_i\|=1$ for all $i$.
--   4. **Finite-rank density operator.** A linear map $\rho:H\to H$ is a finite-rank density operator if $\rho=\sum_{i=1}^n a_i|\psi_i\rangle\langle\psi_i|$ for some $n$, strictly convex weights $a$ and normalized vectors $\psi_1,\dots,\psi_n$.
--   5. **Von Neumann entropy (finite dimension).** For a self-adjoint operator $T$ on a finite-dimensional complex inner product space with eigenvalues $\lambda_1,\dots,\lambda_d$ (with multiplicity), $S(T)=-\sum_k \lambda_k\log\lambda_k$, with $0\log 0=0$.
--   6. **Entropy of an equal mixture.** For $\psi,\phi\in H$ let $\rho_{\psi\phi}=\tfrac12|\psi\rangle\langle\psi|+\tfrac12|\phi\rangle\langle\phi|$ and
--   $$I(\psi,\phi)=S\bigl(\rho_{\psi\phi}\big|_{\operatorname{span}\{\psi,\phi\}}\bigr).$$
--
--   These are the objects of the paper's Appendix A (eq. (11) for $I$).
--
--   **Formalization Note** Item 4 encodes "density operator of finite rank" as a finite strictly convex combination of pure states; by the spectral theorem these are exactly the positive, trace-one, finite-rank operators. In item 6, $\rho_{\psi\phi}$ maps $\operatorname{span}\{\psi,\phi\}$ into itself and vanishes on its orthogonal complement, so the restriction has the same nonzero spectrum as $\rho_{\psi\phi}$ and the entropy is well defined even when $H$ is infinite-dimensional or incomplete. The entropy function returns $0$ on non-self-adjoint input, which never occurs here.
-- source:
--   G. Carcassi, C. A. Aidala, F. Calderón, *The unphysicality of Hilbert spaces*, arXiv:2308.06669v3 [quant-ph], 22 Dec 2024, https://arxiv.org/abs/2308.06669, Appendix A, pp. 8–10 (Propositions 7–10, eq. (11))

import Mathlib

/-!
# Unphysicality of Hilbert spaces — mixtures of pure states and their entropy

Definitions used by the statements of Propositions 7–10 of
G. Carcassi, C. A. Aidala, F. Calderón, *The unphysicality of Hilbert spaces*,
arXiv:2308.06669v3, Appendix A.
-/

namespace UnphysicalHilbert

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The rank-one operator `|ψ⟩⟨ψ|`, i.e. `x ↦ ⟨ψ, x⟩ ψ`. -/
noncomputable def ketBra (ψ : H) : H →ₗ[ℂ] H :=
  (innerₛₗ ℂ ψ).smulRight ψ

/-- The weighted sum `∑ᵢ aᵢ |ψᵢ⟩⟨ψᵢ|` of rank-one operators. -/
noncomputable def mixture {ι : Type*} [Fintype ι] (a : ι → ℝ) (ψ : ι → H) : H →ₗ[ℂ] H :=
  ∑ i, (a i : ℂ) • ketBra (ψ i)

/-- `a` is a family of strictly positive weights summing to `1`
(the coefficients of a strictly convex combination). -/
def IsStrictConvexWeights {ι : Type*} [Fintype ι] (a : ι → ℝ) : Prop :=
  (∀ i, 0 < a i) ∧ ∑ i, a i = 1

/-- `ψ` is a family of normalized vectors. -/
def IsNormalizedFamily {ι : Type*} (ψ : ι → H) : Prop :=
  ∀ i, ‖ψ i‖ = 1

/-- A density operator of finite rank: a strictly convex combination of finitely many
pure states `|ψᵢ⟩⟨ψᵢ|` with `‖ψᵢ‖ = 1`. (By the spectral theorem, these are exactly the
positive, finite-rank, trace-one operators.) -/
def IsFiniteRankDensityOperator (ρ : H →ₗ[ℂ] H) : Prop :=
  ∃ (n : ℕ) (a : Fin n → ℝ) (ψ : Fin n → H),
    IsStrictConvexWeights a ∧ IsNormalizedFamily ψ ∧ ρ = mixture a ψ

/-- Von Neumann entropy `S(T) = -∑ λ log λ` (sum over the eigenvalues of `T`, counted with
multiplicity, using the convention `0 log 0 = 0`) of a self-adjoint operator on a
finite-dimensional complex inner product space. Returns `0` on non-self-adjoint input
(never used). -/
noncomputable def vonNeumannEntropyFin {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) : ℝ :=
  open Classical in
  if h : T.IsSymmetric then ∑ i, Real.negMulLog (h.eigenvalues rfl i) else 0

/-- The equal mixture `½|ψ⟩⟨ψ| + ½|ϕ⟩⟨ϕ|` of two pure states. -/
noncomputable def equalMixture (ψ ϕ : H) : H →ₗ[ℂ] H :=
  (1 / 2 : ℂ) • (ketBra ψ + ketBra ϕ)

/-- The two-dimensional (at most) subspace spanned by `ψ` and `ϕ`. -/
def pairSpan (ψ ϕ : H) : Submodule ℂ H :=
  Submodule.span ℂ {ψ, ϕ}

noncomputable instance pairSpan.finiteDimensional (ψ ϕ : H) :
    FiniteDimensional ℂ (pairSpan ψ ϕ) :=
  FiniteDimensional.span_of_finite ℂ (Set.toFinite _)

/-- The equal mixture maps the span of `ψ` and `ϕ` into itself. -/
theorem equalMixture_mapsTo (ψ ϕ : H) :
    ∀ x ∈ pairSpan ψ ϕ, equalMixture ψ ϕ x ∈ pairSpan ψ ϕ := by
  intro x _
  have hψ : ψ ∈ pairSpan ψ ϕ := Submodule.subset_span (by simp)
  have hϕ : ϕ ∈ pairSpan ψ ϕ := Submodule.subset_span (by simp)
  simp only [equalMixture, ketBra, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.smulRight_apply]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.smul_mem _ _ hψ)
    (Submodule.smul_mem _ _ hϕ))

/-- `I(ψ, ϕ) = S(½|ψ⟩⟨ψ| + ½|ϕ⟩⟨ϕ|)`: the von Neumann entropy of the equal mixture of two
pure states (paper, eq. (11)). The operator vanishes on the orthogonal complement of
`span {ψ, ϕ}` and maps that span into itself, so its entropy is computed from its
restriction to this finite-dimensional subspace. -/
noncomputable def equalMixtureEntropy (ψ ϕ : H) : ℝ :=
  vonNeumannEntropyFin ((equalMixture ψ ϕ).restrict (equalMixture_mapsTo ψ ϕ))

end UnphysicalHilbert


