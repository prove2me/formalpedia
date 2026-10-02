-- Prove2me | Definitions.Def_TeschlQM_Shared_IsRelativelyCompact
-- name    : TeschlQM_Shared_IsRelativelyCompact
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T22:58:44.04258+00:00
-- url     : https://prove2.me/theorems/021b50dd-b2ed-44a4-87e8-6444dcc5a59e
-- title:
--   Relatively compact operator K with respect to A (5.12)
-- statement:
--   Let $A$ and $K$ be linear operators in a complex Hilbert space $\mathfrak H$. $K$ is **relatively compact with respect to $A$** if
--   $$K R_A(z) \in \mathfrak C(\mathfrak H)$$
--   for one $z \in \rho(A)$, where $\mathfrak C(\mathfrak H)$ are the compact operators. For the product $K R_A(z)$ to be an everywhere defined operator, $\operatorname{Ran} R_A(z) = \mathfrak D(A)$ must lie in $\mathfrak D(K)$.
--
--   Relatively compact perturbations leave the essential spectrum of a self-adjoint operator unchanged.
--
--   This one definition is shared by every chunk of the series that uses it and is reviewed once for all of them. It serves:
--
--   - chunk `08-weyl`: p. 148, Lemma 6.22; p. 148, Lemma 6.23
--   - chunk `12-one-particle`: p. 222, Theorem 10.2
--   - chunk `13-hvz`: p. 244, Lemma 11.5
--
--   **Formalization Note.** Stated as: there exist $z$, the resolvent $R = R_A(z)$ (`IsResolventAt A z R`) and a compact operator $C$ (Mathlib's `IsCompactOperator`) such that $R\varphi \in \mathfrak D(K)$ and $K R \varphi = C\varphi$ for every $\varphi$. On a Hilbert space `IsCompactOperator` coincides with the book's $\mathfrak C(\mathfrak H)$, the norm closure of the finite rank operators.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 128, Section 5.2, Eq. (5.12)

import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet

namespace TeschlQM.Shared

/-- Teschl (5.12), p. 128: the (possibly unbounded) operator `K` is **relatively compact** with
respect to `A` if `K R_A(z) ∈ ℭ(ℌ)` for one `z ∈ ρ(A)`: there are `z` and the resolvent
`R = R_A(z)` of `A` at `z`, and a compact operator `C`, such that `Ran R_A(z) ⊆ 𝔇(K)` (so
`K R_A(z)` is defined on all of `ℌ`; since `Ran R_A(z) = 𝔇(A)` this is `𝔇(A) ⊆ 𝔇(K)`) and
`K R_A(z) = C`. `ℭ(ℌ)` is Mathlib's `IsCompactOperator`, which on a Hilbert space coincides with
the norm closure of the finite rank operators used by the book. -/
def IsRelativelyCompact {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (K A : H →ₗ.[ℂ] H) : Prop :=
  ∃ z : ℂ, ∃ R : H →L[ℂ] H, IsResolventAt A z R ∧
    ∃ C : H →L[ℂ] H, IsCompactOperator C ∧ ∀ φ : H, ∃ h : R φ ∈ K.domain, K ⟨R φ, h⟩ = C φ

end TeschlQM.Shared


