-- Prove2me | Definitions.Def_F3SubsetSum_BorelAction
-- name    : F3SubsetSum_BorelAction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:29:37.186777+00:00
-- url     : https://prove2.me/theorems/60e1dd8b-b7be-4e19-8efa-3b3d52aa48f1
-- title:
--   The triangular group $\mathcal B$, its action on $R_d$, and coefficient functionals $e_\alpha$, $W_{\mathcal A}$
-- statement:
--   The **triangular group** $\mathcal B$ consists of the substitutions
--
--   $$
--   g(x_j)=a_jx_j+\sum_{i>j}a_{ij}x_i,\qquad a_j\in K\setminus\{0\},\ a_{ij}\in K .
--   $$
--
--   In characteristic $q$ they preserve $(x_1^q,\dots,x_n^q)$, so they act on each $R_d$ (substitute, then drop monomials divisible by some $x_j^q$) and on $R_d^*$ by $(g\lambda)(f)=\lambda(g^{-1}f)$. A subspace $W\subseteq R_D^*$ is **$\mathcal B$-invariant** if $gW=W$ for all $g\in\mathcal B$. For a reduced monomial $x^\alpha$, $e_\alpha\in R_{|\alpha|}^*$ extracts the coefficient of $x^\alpha$, and for a family $\mathcal A$ of reduced degree-$D$ monomials $W_{\mathcal A}=\langle e_\alpha : x^\alpha\in\mathcal A\rangle$.
--
--   These are the objects of the shifting argument (Lemma 4.17) that reduces symbolic rank to monomial combinatorics.
--
--   **Formalization Note** Since $\mathcal B$ is a group, $gW=W$ for all $g\in\mathcal B$ is stated in the equivalent inverse-free form $\lambda\circ g\in W$ for all $\lambda\in W$, $g\in\mathcal B$.
-- source:
--   Kothari, Metger, O'Donnell, Shutty, Wu, Exponential quantum speedup for F_3^n-Subset-Sum? Or, rigorous classical algorithms for Binary-Error LWE, arXiv:2609.40321v1, §4.4.2, p.26

import Mathlib
import Definitions.Def_F3SubsetSum_TruncatedRing

namespace F3SubsetSum

open MvPolynomial

variable {K : Type*} [Field K] {n : ℕ} (q : ℕ)

/-- **The triangular group `ℬ`** (Kothari, Metger, O'Donnell, Shutty, Wu, arXiv:2609.40321v1,
p.26): "every g ∈ ℬ is defined by g(x_j) = a_j x_j + Σ_{i>j} a_{ij} x_i, where a_j ≠ 0". A
substitution `g : Fin n → K[x_1, …, x_n]` (the images `g(x_j)`) belongs to `ℬ` when every `g(x_j)`
has this form. -/
def IsBorel (g : Fin n → MvPolynomial (Fin n) K) : Prop :=
  ∀ j, ∃ a : K, a ≠ 0 ∧ ∃ c : Fin n → K,
    g j = C a * X j + ∑ i ∈ Finset.univ.filter (fun i => j < i), C (c i) * X i

/-- **The action of a substitution on `R_d`** (p.26): substitute `x_j ↦ g(x_j)` in the reduced
representative and project back to `R_d`, discarding monomials divisible by some `x_j^q`.
For `g ∈ ℬ` and `K` of characteristic `q` this is the action of `g` on `R_d` ("these
substitutions preserve the ideal (x_1^q, …, x_n^q)"). -/
noncomputable def substR (g : Fin n → MvPolynomial (Fin n) K) (d : ℕ) :
    Rd K n q d →ₗ[K] Rd K n q d :=
  (Rd.ofPoly K n q d).comp ((aeval g).toLinearMap.comp (Rd.toPoly K n q d))

/-- **`ℬ`-invariance of a subspace of `R*_D`** (p.26). The dual action is
`(gλ)(f) = λ(g^{−1} f)`; `W` is `ℬ`-invariant when `gW = W` for every `g ∈ ℬ`.

**Formalization Note** Since `ℬ` is a group, `gW = W` for all `g ∈ ℬ` is equivalent to
`gW ⊆ W` for all `g ∈ ℬ`, and, replacing `g` by `g^{−1} ∈ ℬ`, to `λ ∘ g ∈ W` for all `λ ∈ W` and
`g ∈ ℬ`; this last form, which needs no inverse, is the one stated. -/
def IsBorelInvariant (D : ℕ) (W : Submodule K (Module.Dual K (Rd K n q D))) : Prop :=
  ∀ g : Fin n → MvPolynomial (Fin n) K, IsBorel g →
    ∀ ℓ ∈ W, ℓ.comp (substR q g D) ∈ W

/-- **The monomial coefficient functional** `e_α ∈ R*_{|α|}` (p.26): "the functional that
extracts the coefficient of x^α", here on `R_D` for an exponent vector `α`. -/
noncomputable def coeffFunctional (D : ℕ) (α : Fin n →₀ ℕ) : Module.Dual K (Rd K n q D) :=
  (lcoeff K α).comp (Rd.toPoly K n q D)

/-- **`W_𝒜 = ⟨e_α : x^α ∈ 𝒜⟩`** (Lemma 4.17, p.26), the span of the coefficient functionals of
a family `𝒜` of reduced degree-`D` monomials. -/
noncomputable def monomialSpan (D : ℕ) (𝒜 : Finset (Fin n →₀ ℕ)) :
    Submodule K (Module.Dual K (Rd K n q D)) :=
  Submodule.span K ((fun α => coeffFunctional (K := K) q D α) '' (𝒜 : Set (Fin n →₀ ℕ)))

end F3SubsetSum


