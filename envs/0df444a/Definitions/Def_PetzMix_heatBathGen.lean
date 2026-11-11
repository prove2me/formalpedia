-- Prove2me | Definitions.Def_PetzMix_heatBathGen
-- name    : PetzMix_heatBathGen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:10:36.6002+00:00
-- url     : https://prove2.me/theorems/6aaa099d-35aa-463f-8710-c80c4c5bb73c
-- title:
--   Petz block update $\Phi_B$ and the heat-bath generator $\mathcal L_\ell$
-- statement:
--   Let $\sigma_\beta=e^{-\beta H}/\operatorname{tr}e^{-\beta H}$ be the Gibbs state of $H=\sum_i h^{(i)}_{i,i+1}$ at inverse temperature $\beta$. For a set of sites $B$ write $\sigma_{\beta,B^c}=\operatorname{tr}_B[\sigma_\beta]$. The **Petz block update** discards the state on $B$ and rebuilds it with the Petz recovery map of $\sigma_\beta$:
--   $$
--   \Phi_B(\rho)=\sigma_\beta^{1/2}\Big(I_B\otimes\sigma_{\beta,B^c}^{-1/2}\operatorname{tr}_B[\rho]\,\sigma_{\beta,B^c}^{-1/2}\Big)\sigma_\beta^{1/2}.
--   $$
--   For a block length $\ell$, the **Petz block heat-bath generator** is
--   $$
--   \mathcal L_\ell=\frac1\ell\sum_{B\in\mathcal B_{n,\ell}}(\Phi_B-\mathrm{id}),
--   $$
--   the sum over the $n$ cyclic blocks of length $\ell$. The normalization $1/\ell$ makes every site updated at total rate one.
--
--   The file also defines $\Gamma_\omega(X)=\omega^{1/2}X\omega^{1/2}$ and its inverse $\Gamma_\omega^{-1}(X)=\omega^{-1/2}X\omega^{-1/2}$, used to state KMS detailed balance.
--
--   **Formalization Note** $A^{1/2}$ and $A^{-1/2}$ are continuous functional calculus; the inverse square root is applied only to positive definite matrices. The partial trace is the public unnormalized re-embedding `ptr B X` $=I_B\otimes\operatorname{tr}_BX$, so `ptr B σ` $=I_B\otimes\sigma_{\beta,B^c}$ and the update carries no dimension factor. The Gibbs state is the public `QDSGibbs.gibbs`.
-- source:
--   Kim, Rapid mixing of quantum spin chains at any finite temperature, arXiv:2610.01190 (held copy sha256 38ff48d0…), (2)–(3), p.4; Definitions 2.6–2.7, (28)–(30), p.14; (35), p.15

import Mathlib
import Definitions.Def_PetzMix_ChainOp
import Definitions.Def_QDSGibbs_Interaction

open scoped Matrix ComplexOrder

set_option autoImplicit false

namespace PetzMix

open QDSGibbs

/-- The positive square root `A^{1/2}` of a positive semidefinite matrix (arXiv:2610.01190 (held
copy sha256 38ff48d0…), (3), p.4; (28), p.14).

**Formalization Note** The continuous functional calculus `cfc Real.sqrt A`. -/
noncomputable def msqrt {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  cfc Real.sqrt A

/-- The inverse square root `A^{−1/2}` of a positive definite matrix (arXiv:2610.01190, (3), p.4;
(28), p.14).

**Formalization Note** The continuous functional calculus of `x ↦ x^{−1/2}`. It is only applied to
positive definite matrices (the Gibbs state, its re-embedded marginals, and full-rank block states),
on whose spectrum the function is continuous, so it is the usual inverse square root. -/
noncomputable def misqrt {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  cfc (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) A

/-- The **Petz block update** `Φ_B = R^{σ}_{B^c→Λn} ∘ tr_B` (Kim, arXiv:2610.01190 (held copy sha256
38ff48d0…), (3), p.4; Definition 2.6, (28), and Definition 2.7, (29), p.14):
`Φ_B(ρ) = σ^{1/2} (I_B ⊗ σ_{B^c}^{−1/2} tr_B[ρ] σ_{B^c}^{−1/2}) σ^{1/2}`, `σ_{B^c} = tr_B[σ]`.

**Formalization Note** `ptr B X = I_B ⊗ tr_B X` is the public *unnormalized* re-embedded partial
trace, so `ptr B σ = I_B ⊗ σ_{B^c}` and `(ptr B σ)^{−1/2} = I_B ⊗ σ_{B^c}^{−1/2}`; the formula
`σ^{1/2} (ptr B σ)^{−1/2} (ptr B ρ) (ptr B σ)^{−1/2} σ^{1/2}` is exactly (3) with no dimension
factor. `σ` is a parameter; the paper applies it to the Gibbs state `σ_β`. -/
noncomputable def petzUpdate {n d : ℕ} (σ : ChainOp n d) (B : Finset (Fin n)) (ρ : ChainOp n d) :
    ChainOp n d :=
  msqrt σ * misqrt (ptr B σ) * ptr B ρ * misqrt (ptr B σ) * msqrt σ

/-- The **Petz block heat-bath generator** (arXiv:2610.01190, (3), p.4; Definition 2.7, (30), p.14):
`L_ℓ = ℓ^{−1} Σ_{B ∈ B_{n,ℓ}} (Φ_B − I)`, the sum over the `n` cyclic blocks `cycBlock ℓ s` of
length `ℓ`, with `Φ_B` the Petz update of the Gibbs state `σ_β = e^{−βH}/tr e^{−βH}`,
`H = Σ_i h i` ((2), p.4).

**Formalization Note** The normalization is `1/ℓ` (p.4: "each site is updated at total rate one"),
not `1/n`. The Gibbs state is the public `QDSGibbs.gibbs β H`. For `1 ≤ ℓ < n` the `n` blocks are
distinct and form `B_{n,ℓ}`. -/
noncomputable def heatBathGen {n d : ℕ} (β : ℝ) (h : Fin n → ChainOp n d) (ℓ : ℕ)
    (ρ : ChainOp n d) : ChainOp n d :=
  ((ℓ : ℂ)⁻¹) • ∑ s : Fin n, (petzUpdate (gibbs β (∑ i, h i)) (cycBlock ℓ s) ρ - ρ)

/-- The map `Γ_ω(X) = ω^{1/2} X ω^{1/2}` for a full-rank state `ω` (arXiv:2610.01190, proof of
Proposition 2.9, p.15). -/
noncomputable def kmsMap {ι : Type} [Fintype ι] [DecidableEq ι] (ω X : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  msqrt ω * X * msqrt ω

/-- The inverse `Γ_ω^{−1}(X) = ω^{−1/2} X ω^{−1/2}` of `Γ_ω` for a full-rank state `ω`
(arXiv:2610.01190, (35)–(36), p.15). -/
noncomputable def kmsInv {ι : Type} [Fintype ι] [DecidableEq ι] (ω X : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  misqrt ω * X * misqrt ω

end PetzMix


