-- Prove2me | Definitions.Def_DIObliviousTransfer_maskedDiff
-- name    : DIObliviousTransfer_maskedDiff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T09:03:52.970465+00:00
-- url     : https://prove2.me/theorems/c6226ccb-00cd-4d57-93c6-81a97cab0a0a
-- title:
--   The difference operator of diagonal code masking (6)
-- statement:
--   For a cq state $\rho_{\beta\Lambda E}$ with $\beta\in\mathbb F_{64}^m$ and a classical label $\Lambda$ selecting a secret $u(\lambda)\in\mathbb F_{64}^q$, sample $\sigma$ uniformly in $(\mathbb F_{64}^*)^m$ and $R$ uniformly in the twisted fiber $B^\sigma_{u(\lambda)}=\{r\in\sigma*B:\mathrm{sec}(\sigma^{-1}*r)=u(\lambda)\}$. The operator is
--   $$\rho_{\sigma,\beta+R,\Lambda E}-\rho_\sigma\otimes\tau_{km}\otimes\rho_{\Lambda E},$$
--   block diagonal in $(\sigma,\beta+R,\lambda)$, whose trace norm Lemma 7 bounds.
-- source:
--   Batra, Chen, Jain, Zhang, Robust and Leakage-Resilient Device-Independent Oblivious Transfer in MiniQCrypt, arXiv:2610.01421 (held version, sha256 8334c039f604ce147d1a21ffdf444ff4ac5d5f800a6aa57577a16a006e326a42), Lemma 7, p.26

import Mathlib
import Definitions.Def_DIObliviousTransfer_pGuess
import Definitions.Def_DIObliviousTransfer_CodeFamily

namespace DIObliviousTransfer

/-!
Batra, Chen, Jain, Zhang, arXiv:2610.01421 (held version, sha256 8334c039…), Lemma 7, p.26:
the state compared in diagonal code masking.

"Let `ρ_{βE}` be a possibly subnormalized cq state on `F₆₄^m` … After this state is fixed, sample
an independent uniform `σ ∈ (F₆₄^*)^m` and, given `σ`, sample `R` uniformly in `B^σ_u`,
independently of `βE`, for any prescribed secret `u ∈ F₆₄^q`. Then
`‖ρ_{σ,β+R,E} − ρ_σ ⊗ τ_{km} ⊗ ρ_E‖₁ ≤ 2^{−(ξm−b)/2}`. (6) The bound is uniform in `u`, including
a retained common classical label, included in `E`, that selects `u` and the cq state." (p.26)

**Formalization Note** (decisions D2, D15). The side information is `E = Λ × E'` with a classical
label `Λ` (the label-free case is `Λ = Unit`); the cq state is `β ↦ λ ↦ ρ_{β,λ}` and the secret
is `u(λ)`. `B^σ_u = {r ∈ σ ∗ B : sec(σ^{-1} ∗ r) = u}`. The difference operator is block diagonal
in the classical registers `(σ, β + R, λ)`.
-/

/-- The twisted secret fiber `B^σ_u = {r ∈ B^σ : sec_σ(r) = u}`, `sec_σ(r) = sec(σ^{-1} ∗ r)`. -/
noncomputable def twFiberB (C : CodeFamily) (m q : ℕ) (σ : Fin m → F64) (u : Fin q → F64) :
    Finset (Fin m → F64) := by
  classical
  exact Finset.univ.filter fun r => r ∈ twist σ (C.B m q) ∧ C.secB m q (fun i => (σ i)⁻¹ * r i) = u

/-- The operator `ρ_{σ, β+R, ΛE} − ρ_σ ⊗ τ_{km} ⊗ ρ_{ΛE}` of (6), block diagonal in
`(σ, z = β + R, λ)`, with `σ` uniform on `(F₆₄^*)^m` and `R` uniform on `B^σ_{u(λ)}`. -/
noncomputable def maskedDiff (C : CodeFamily) (m q : ℕ) {Λ E : Type} [Fintype Λ] [DecidableEq Λ]
    [Fintype E] (ρ : (Fin m → F64) → Λ → Matrix E E ℂ) (u : Λ → Fin q → F64) :
    Matrix (((Fin m → F64ˣ) × (Fin m → F64)) × (Λ × E))
      (((Fin m → F64ˣ) × (Fin m → F64)) × (Λ × E)) ℂ := by
  classical
  exact Matrix.of fun p p' =>
    if p.1 = p'.1 ∧ p.2.1 = p'.2.1 then
      ((1 : ℂ) / 63 ^ m) *
        (∑ β : Fin m → F64,
          ((if p.1.2 - β ∈ twFiberB C m q (fun i => (p.1.1 i : F64)) (u p.2.1) then
              (1 : ℂ) / (twFiberB C m q (fun i => (p.1.1 i : F64)) (u p.2.1)).card else 0) -
            (1 : ℂ) / 64 ^ m) * ρ β p.2.1 p.2.2 p'.2.2)
    else 0

end DIObliviousTransfer


