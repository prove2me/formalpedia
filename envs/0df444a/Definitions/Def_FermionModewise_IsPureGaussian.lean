-- Prove2me | Definitions.Def_FermionModewise_IsPureGaussian
-- name    : FermionModewise_IsPureGaussian
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:33:06.714514+00:00
-- url     : https://prove2.me/theorems/cc1d94a5-9a39-437b-a564-c3c965ceb4c7
-- title:
--   Pure fermion Gaussian state
-- statement:
--   Let $(b_k)_{k\in\mu}$ satisfy the anticommutation relations. A unit vector $\psi$ is a **pure fermion Gaussian state** of these modes if there are a canonical family $(c_k)_{k\in\mu}$ obtained from $b$ and signs $\lambda_k\in\{+1,-1\}$ such that every factor of (4) fixes $\psi$:
--   $$\tilde\rho_k\,\psi=\psi,\qquad \tilde\rho_k=\tfrac12\big(\mathbb 1-\lambda_k\,[c_k^\dagger,c_k]\big),\quad k\in\mu .$$
--   For $\lambda_k=1$, $\tilde\rho_k$ projects onto the states annihilated by $c_k$; for $\lambda_k=-1$, onto the states in which mode $c_k$ is occupied.
--
--   Equation (4) of the paper writes a Gaussian state as $\rho=\bigotimes_k\tilde\rho_k$ with $|\lambda_k|\le1$, and pure states have $|\lambda_k|=1$. The definition above is the vector form of this: the $\tilde\rho_k$ are commuting projectors, and $|\psi\rangle\langle\psi|=\prod_k\tilde\rho_k$ implies $\tilde\rho_k\psi=\psi$ for each $k$.
--
--   **Formalization Note.** In the Fock representation the two conditions coincide; in a larger finite representation the condition above is the natural extension. Both signs of $\lambda_k$ are allowed, so occupied modes are included. The page prints the index $i$ inside $\tilde\rho_k$; it is read as $k$.
-- source:
--   Botero–Reznik, arXiv:quant-ph/0404176v3, eq. (4), p.3 (with |λ_i| = 1 for pure states)

import Mathlib
import Definitions.Def_FermionModewise_IsCanonicalFamily

open Matrix

namespace FermionModewise

/-- **Pure fermion Gaussian state** (Botero–Reznik, arXiv:quant-ph/0404176v3, eq. (4), p.3): a unit
vector `ψ` is a pure Gaussian state of the modes `b` if, for some canonical family `c` obtained
from `b` and some signs `λ_k ∈ {+1, −1}`, every factor `ρ̃_k = ½(1 − λ_k [c_k†, c_k])` of (4)
fixes `ψ`.

**Formalization Note.** (4) writes `ρ = ⊗_k ρ̃_k` with `|λ_k| = 1` for pure states. For `|λ_k| = 1`
each `ρ̃_k` is a projector (onto the `c_k`-vacuum for `λ_k = 1`, onto the occupied `c_k` mode for
`λ_k = −1`); the projectors commute, and `|ψ⟩⟨ψ| = ∏ ρ̃_k` implies `ρ̃_k ψ = ψ` for each `k`, which is
the condition stated. In the Fock representation the two coincide; in a larger finite
representation this condition is the natural extension. Both signs of `λ_k` are allowed, so
occupied modes are included. The page prints index `i` inside `ρ̃_k`; it is read as `k`. -/
def IsPureGaussian {ι μ : Type} [Fintype ι] [DecidableEq ι] [Fintype μ] [DecidableEq μ]
    (b : μ → Matrix ι ι ℂ) (ψ : ι → ℂ) : Prop :=
  star ψ ⬝ᵥ ψ = 1 ∧ ∃ c : μ → Matrix ι ι ℂ, IsCanonicalFamily b c ∧
    ∃ lam : μ → ℝ, (∀ k, |lam k| = 1) ∧
      ∀ k, ((1 / 2 : ℂ) • (1 - (lam k : ℂ) • ((c k)ᴴ * c k - c k * (c k)ᴴ))) *ᵥ ψ = ψ

end FermionModewise


