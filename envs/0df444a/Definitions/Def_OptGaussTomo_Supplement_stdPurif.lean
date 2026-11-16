-- Prove2me | Definitions.Def_OptGaussTomo_Supplement_stdPurif
-- name    : OptGaussTomo_Supplement_stdPurif
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:45:19.834694+00:00
-- url     : https://prove2.me/theorems/c6e68764-0767-496e-b4be-7b1fa0aff84e
-- title:
--   Standard purification $\psi^{\mathrm{std}}_\rho$ in infinite dimensions and its rotations
-- statement:
--   Let $\mathcal H=\ell^2(X)$ with its fixed basis and $\tilde{\mathcal H}$ a copy with basis $\{|\tilde x\rangle\}$. For a positive trace-class $\rho$ the **standard purification** is
--
--   $$
--   |\psi^{\mathrm{std}}_\rho\rangle=\sum_x\sqrt\rho\,|x\rangle\otimes|\tilde x\rangle\in\mathcal H\otimes\tilde{\mathcal H},
--   $$
--
--   whose coordinate at $(y,\tilde x)$ is $\langle y|\sqrt\rho|x\rangle$; $\psi^{\mathrm{std}}_\rho=|\psi^{\mathrm{std}}_\rho\rangle\langle\psi^{\mathrm{std}}_\rho|$. For a unitary $U$ acting on $\tilde{\mathcal H}$, the rotated purification $(I\otimes U)\psi^{\mathrm{std}}_\rho(I\otimes U^\dagger)$ is the rank-one operator of the vector with coordinates $\sum_u U_{xu}\langle y|\sqrt\rho|u\rangle$.
--
--   These are the objects averaged in the random purification identity (E.5).
--
--   **Formalization Note** $\sqrt\rho$ is the positive square root `opSqrt`; $\tilde{\mathcal H}$ is the second coordinate of $\ell^2(X\times X)$.
-- source:
--   Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, Optimal tomography of bosonic and fermionic Gaussian states, arXiv:2607.11847 (held version, sha256 0f7548a2a5cfd55079e5d7f1787c97c8561a818a53d7e29824715104bad416ed), App. E.1, p.62 (standard purification); Theorem E.1, eq. (E.5), p.63

import Mathlib
import Definitions.Def_OptGaussTomo_Supplement_opSqrt

namespace OptGaussTomo.Supplement

/-- The **standard purification** (Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen,
*Optimal tomography of bosonic and fermionic Gaussian states*, arXiv:2607.11847, held version,
sha256 0f7548a2…, App. E.1, p.62) of a positive trace-class `ρ` on `H = ℓ²(X)` with its fixed
basis: `|ψ^std_ρ⟩ = ∑ₓ √ρ|x⟩ ⊗ |x̃⟩ ∈ H ⊗ H̃`, whose coordinate at `(y, x̃)` is `⟨y|√ρ|x⟩`, and
`ψ^std_ρ = |ψ^std_ρ⟩⟨ψ^std_ρ|` as an operator on `ℓ²(X × X)`.

**Formalization Note.** `H̃` is the copy of `H` with the same index set, the second coordinate;
`√ρ` is `opSqrt`. -/
noncomputable def stdPurif {X : Type} (ρ : Matrix X X ℂ) : Matrix (X × X) (X × X) ℂ :=
  fun p q => opSqrt ρ p.1 p.2 * star (opSqrt ρ q.1 q.2)

/-- The rotated standard purification `(I ⊗ U) ψ^std_ρ (I ⊗ U†)` for a unitary `U` on `H̃`
(the integrand of (E.5), p.63). The vector `(I ⊗ U)|ψ^std_ρ⟩` has coordinate
`∑ᵤ U x u ⟨y|√ρ|u⟩` at `(y, x̃)`. -/
noncomputable def twirlTerm {X : Type} (U ρ : Matrix X X ℂ) : Matrix (X × X) (X × X) ℂ :=
  fun p q => (∑' u, U p.2 u * opSqrt ρ p.1 u) * star (∑' u, U q.2 u * opSqrt ρ q.1 u)

end OptGaussTomo.Supplement


