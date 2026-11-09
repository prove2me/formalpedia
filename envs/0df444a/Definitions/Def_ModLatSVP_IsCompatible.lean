-- Prove2me | Definitions.Def_ModLatSVP_IsCompatible
-- name    : ModLatSVP_IsCompatible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:10:31.8153+00:00
-- url     : https://prove2.me/theorems/c161b5e9-7f2a-4955-99cd-ee451cb8655e
-- title:
--   Modules over $\mathcal O_K$ with a compatible inner product
-- statement:
--   Let $K$ be a number field with involution $\star$. A module over $\mathcal O_K$ with a **compatible inner product** is the lattice $\mathbb Z^\iota$ with a positive definite Gram matrix $G$ together with an action of $K$ on its rational span $\mathbb Q^\iota$, written $x\mapsto\varphi(\alpha)x$, such that
--
--   1. $G$ is positive definite;
--   2. every $\alpha\in\mathcal O_K$ acts by an integer matrix, so $\mathbb Z^\iota$ is an $\mathcal O_K$-module;
--   3. multiplication by $\alpha^\star$ is the adjoint of multiplication by $\alpha$:
--   $$\varphi(\alpha)^{T}G=G\,\varphi(\alpha^\star)\qquad\text{for all }\alpha\in K .$$
--
--   This is the compatibility condition $A(\alpha)^TG=GA(\alpha^\star)$ of the paper's module input model; it is what makes duals and orthogonal projections of modules again modules.
--
--   **Formalization Note** Matrices act on coefficient columns: multiplication by $\alpha$ sends the basis vector $e_q$ to $\sum_p\varphi(\alpha)_{pq}e_p$. The action of $\mathcal O_K$ is extended to $K$ (i.e. to $M\otimes_{\mathbb Z}\mathbb Q$); by $\mathbb Q$-linearity, compatibility on all of $K$ is equivalent to compatibility on an integral basis. $G$ is real here and is cast from $\mathbb Q$ in the algorithmic statements.
-- source:
--   Kim, Lee, Son, Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions, STOC 2027 submission (manuscript sha256 e7151fad…), §2.2, p.12 (PDF p.12)

import Mathlib

open NumberField

namespace ModLatSVP

/-- A module over `𝓞_K` with a compatible inner product. Kim, Lee, Son, *Exact SVP and CVP in Structured
Lattices: Polynomial-Space Algorithms and Reductions*, STOC 2027 submission (manuscript sha256
e7151fad…), §2.2, p.12 (PDF p.12): "We represent M by a ℤ-basis, a positive definite rational Gram
matrix G, and the integer matrices A(α) describing multiplication by the elements α of a supplied
integral basis of 𝒪_K. We require the compatibility condition A(α)ᵀ G = G A(α⋆), so that multiplication
by α⋆ is the adjoint of multiplication by α."

`IsCompatible K τ G φ` says, for the lattice `ℤ^ι` with Gram matrix `G` and the action `φ` of `K` on its
rational span `ℚ^ι`:
1. `G` is positive definite (as a real matrix);
2. every `α ∈ 𝓞_K` acts by an integer matrix, so `ℤ^ι` is an `𝓞_K`-module;
3. `φ(α)ᵀ G = G φ(α⋆)` for every `α ∈ K`, where `α⋆ = τ α`.

**Formalization Note.** Matrices act on coefficient columns: multiplication by `α` sends the basis
vector `e_q` to `Σ_p φ(α)_{pq} e_p`. The action on `𝓞_K` is extended to its fraction field `K`, i.e. to
`M ⊗_ℤ ℚ`; a ring homomorphism `K →+* Matrix ι ι ℚ` is automatically `ℚ`-linear, so compatibility on all
of `K` is equivalent to the paper's condition on an integral basis. The Gram matrix is real so that the
geometric lemmas cover every Euclidean module lattice; the algorithmic statements cast a rational `G`. -/
def IsCompatible (K : Type*) [Field K] [NumberField K] (τ : K ≃ₐ[ℚ] K) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (G : Matrix ι ι ℝ) (φ : K →+* Matrix ι ι ℚ) : Prop :=
  G.PosDef ∧
  (∀ α : 𝓞 K, ∀ p q : ι, ∃ z : ℤ, φ (α : K) p q = z) ∧
  ∀ α : K, ((φ α).map (fun q : ℚ => (q : ℝ))).transpose * G =
    G * (φ (τ α)).map (fun q : ℚ => (q : ℝ))

end ModLatSVP


