-- Prove2me | Definitions.Def_F3SubsetSum_SymbolicRank
-- name    : F3SubsetSum_SymbolicRank
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:29:37.107983+00:00
-- url     : https://prove2.me/theorems/2c172672-0741-4a0c-b709-394cbc55a46e
-- title:
--   Contraction maps $C_L$ and the symbolic rank $\rho(W)$, $\bar\rho(W)$ (eqs. (43), (46))
-- statement:
--   Let $R_D^*$ be the dual of $R_D$. For a linear form $L$, the **contraction** is the dual of multiplication by $L^2$:
--
--   $$
--   C_L:R_D^*\to R_{D-2}^*,\qquad C_L(\lambda)(Q)=\lambda(L^2Q).
--   $$
--
--   With new variables $z_1,\dots,z_n$ and $L_z=\sum_iz_ix_i$, the generic contraction $C_{L_z}$ has scalars in the rational function field $K(z_1,\dots,z_n)$: it sends $\lambda$ to $\bigl(\lambda(L_z^2x^\beta)\bigr)_\beta=\bigl(\sum_{i,j}z_iz_j\lambda(x_ix_jx^\beta)\bigr)_\beta$. For a subspace $W\subseteq R_D^*$ the **symbolic rank** is
--
--   $$
--   \rho(W)=\operatorname{rank}_{K(z_1,\dots,z_n)}\bigl(C_{L_z}|_W\bigr),
--   $$
--
--   written $\rho$ for $K=\mathbb F_q$ (eq. (43)) and $\bar\rho$ for $K=\overline{\mathbb F}_q$ (eq. (46)). Specialising $z=a$ gives $C_{L_a}$, so $\rho(W)$ bounds every $\operatorname{rank}C_{L}|_W$ from above.
--
--   **Formalization Note** $\rho(W)$ is the dimension over $K(z)=$ `FractionRing (MvPolynomial (Fin n) K)` of the span of the vectors $(\lambda(L_z^2x^\beta))_\beta$, $\lambda\in W$; this equals the rank of the matrix of $C_{L_z}|_W$ in any basis, and no basis is chosen.
-- source:
--   Kothari, Metger, O'Donnell, Shutty, Wu, Exponential quantum speedup for F_3^n-Subset-Sum? Or, rigorous classical algorithms for Binary-Error LWE, arXiv:2609.40321v1, §4.4.1, p.25 (C_L, eq. (43)); §4.4.2, p.26 (eq. (46))

import Mathlib
import Definitions.Def_F3SubsetSum_TruncatedRing

namespace F3SubsetSum

open MvPolynomial

variable (K : Type*) [Field K] (n q : ℕ)

/-- **The contraction map** `C_L : R*_D → R*_{D−2}`, `C_L(λ)(Q) = λ(L²Q)`, "the dual of
multiplication by L²" (Kothari, Metger, O'Donnell, Shutty, Wu, arXiv:2609.40321v1, p.25), for
the linear form `L = ⟨a, x⟩`. Here `R*_D = Module.Dual K R_D`.

**Formalization Note** `D − 2` is natural-number subtraction; every statement assumes `D ≥ 2`.
Over `K = F̄_q` this is the specialisation `C̄_L` of p.26. -/
noncomputable def contraction (D : ℕ) (a : Fin n → K) :
    Module.Dual K (Rd K n q D) →ₗ[K] Module.Dual K (Rd K n q (D - 2)) :=
  (mulMap K n q (linForm a ^ 2) (D - 2) D).dualMap

/-- The entry of the generic contraction `C_{L_z}` (eq. (43), p.25) at the functional `ℓ = λ` and
the reduced degree-`(D−2)` monomial `x^β`: the polynomial
`λ(L_z² x^β) = Σ_{i,j} z_i z_j λ(x_i x_j x^β) ∈ K[z_1, …, z_n]`, where `L_z = Σ_i z_i x_i`.
The variables `z_1, …, z_n` are the variables of `MvPolynomial (Fin n) K`. -/
noncomputable def genericEntry (D : ℕ) (ℓ : Module.Dual K (Rd K n q D))
    (β : ReducedMono n q (D - 2)) : MvPolynomial (Fin n) K :=
  ∑ i : Fin n, ∑ j : Fin n,
    C (ℓ (mulMap K n q (X i * X j) (D - 2) D (Pi.single β 1))) * (X i * X j)

/-- **The symbolic rank** `ρ(W) = rank_{K(z_1, …, z_n)}(C_{L_z}|_W)`, eq. (43), p.25 (for
`K = F_q`), and `ρ̄(W)`, eq. (46), p.26 (for `K = F̄_q`). The contraction `C_{L_z}` with scalars
extended to the rational function field `K(z) = FractionRing K[z]` sends `λ ∈ W` to the vector
`(λ(L_z² x^β))_β` of `K(z)^{R_{D−2}}`; the rank of `C_{L_z}|_W` over `K(z)` is the dimension of
the `K(z)`-span of these vectors.

**Formalization Note** The `K(z)`-span of the images of all `λ ∈ W` equals the span of the
images of a `K`-basis of `W`, so this is the rank of the matrix of `C_{L_z}|_W` in any `K`-basis of
`W` and the monomial basis of `R_{D−2}`; no basis is chosen. -/
noncomputable def symbolicRank (D : ℕ) (W : Submodule K (Module.Dual K (Rd K n q D))) : ℕ :=
  Module.finrank (FractionRing (MvPolynomial (Fin n) K))
    (Submodule.span (FractionRing (MvPolynomial (Fin n) K))
      (Set.range fun ℓ : W => fun β : ReducedMono n q (D - 2) =>
        algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K))
          (genericEntry K n q D ℓ β)))

end F3SubsetSum


