-- Prove2me | Definitions.Def_TeschlQM_Dynamics_IsRelativelyCompact
-- name    : TeschlQM_Dynamics_IsRelativelyCompact
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T06:40:38.544737+00:00
-- url     : https://prove2.me/theorems/6c0c37d6-a8ff-4d44-b0c6-c6caecb02c10
-- title:
--   Resolvent R_A(z) and relatively compact operators (5.12)
-- statement:
--   Let $A$ be a linear operator in $\mathfrak H$ with domain $\mathfrak D(A)$. A bounded operator $R$ is the **resolvent** $R_A(z) = (A - z)^{-1}$ at $z \in \mathbb C$ if $R$ maps $\mathfrak H$ into $\mathfrak D(A)$ and is a two-sided inverse of $A - z : \mathfrak D(A) \to \mathfrak H$; $z$ belongs to the resolvent set $\rho(A)$ exactly when such an $R$ exists.
--
--   A (possibly unbounded) operator $K$ is **relatively compact with respect to $A$** if
--   $$K R_A(z) \in \mathfrak C(\mathfrak H) \qquad \text{for one } z \in \rho(A),$$
--   where $K R_A(z)$ is required to be defined on all of $\mathfrak H$, i.e. $\operatorname{Ran} R_A(z) = \mathfrak D(A) \subseteq \mathfrak D(K)$.
--
--   **Formalization Note.** Operators are `LinearPMap`s; a bounded $K \in \mathfrak L(\mathfrak H)$ is used as `(K : H →ₗ[ℂ] H).toPMap ⊤`. The auxiliary `applyExt K ψ` is $K\psi$ for $\psi \in \mathfrak D(K)$ and $0$ otherwise; the mission only evaluates it at vectors of $\mathfrak D(A) \subseteq \mathfrak D(K)$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 128, Section 5.2, Eq. (5.12); p. 73, Eq. (2.66)

import Mathlib
import Definitions.Def_TeschlQM_Shared_compactOperators

namespace TeschlQM.Dynamics

/-- Teschl, p. 73, (2.66): `R` is the **resolvent** `R_A(z) = (A − z)⁻¹` of `A` at `z ∈ ρ(A)`:
`R ∈ 𝔏(ℌ)` maps `ℌ` into `𝔇(A)` and is a two-sided inverse of `A − z : 𝔇(A) → ℌ`. In particular
`z ∈ ρ(A)` iff such an `R` exists. -/
def IsResolventAt {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) (z : ℂ) (R : H →L[ℂ] H) : Prop :=
  (∀ ψ : A.domain, R (A ψ - z • (ψ : H)) = ψ) ∧
    ∀ φ : H, ∃ hφ : R φ ∈ A.domain, A ⟨R φ, hφ⟩ - z • R φ = φ

/-- Teschl, p. 128, (5.12): the (possibly unbounded) operator `K` is **relatively compact** with
respect to `A` if `K R_A(z) ∈ ℭ(ℌ)` for one `z ∈ ρ(A)`: there are `z ∈ ρ(A)` with resolvent
`R = R_A(z)` and a compact operator `C` such that `Ran R_A(z) ⊆ 𝔇(K)` (so that `K R_A(z)` is
defined on all of `ℌ`) and `K R_A(z) = C`. A bounded `K ∈ 𝔏(ℌ)` enters as
`(K : H →ₗ[ℂ] H).toPMap ⊤`. -/
def IsRelativelyCompact {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (K A : H →ₗ.[ℂ] H) : Prop :=
  ∃ z : ℂ, ∃ R : H →L[ℂ] H, IsResolventAt A z R ∧
    ∃ C ∈ TeschlQM.Shared.compactOperators H, ∀ φ : H, ∃ hφ : R φ ∈ K.domain, K ⟨R φ, hφ⟩ = C φ

open Classical in
/-- The value `Kψ` of a partially defined operator at `ψ ∈ 𝔇(K)`, extended by `0` outside
`𝔇(K)`. In this mission it is only evaluated at points of `𝔇(A) ⊆ 𝔇(K)` (for relatively
compact `K`), where it is `Kψ`. -/
noncomputable def applyExt {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (K : H →ₗ.[ℂ] H) (ψ : H) : H :=
  if h : ψ ∈ K.domain then K ⟨ψ, h⟩ else 0

end TeschlQM.Dynamics


