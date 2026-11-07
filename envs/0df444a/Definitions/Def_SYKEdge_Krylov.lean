-- Prove2me | Definitions.Def_SYKEdge_Krylov
-- name    : SYKEdge_Krylov
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:07:28.92621+00:00
-- url     : https://prove2.me/theorems/d150b398-1aeb-4357-b49c-6c57ed8fc4fe
-- title:
--   Krylov vectors $\psi_t=(a^*)^tf_0$, hopping amplitudes $\beta_t$, parameters $\nu,M,t_0$, the Krylov space $R_{t_0,M}$ and $\lambda_{\max}(\Pi_Rx\Pi_R)$
-- statement:
--   In the twisted Fock space of a hypergraph define
--   $$\psi_t=(a^*)^tf_0,\qquad v_t=\frac{\psi_t}{\|\psi_t\|},\qquad \beta_t=\frac{\|\psi_{t+1}\|}{\|\psi_t\|}\qquad(t\ge0),$$
--   and, with $q$ the leakage parameter of the sign matrix,
--   $$\nu=1-q,\qquad M=\lfloor1/\nu\rfloor,\qquad t_0=\lceil\kappa/\nu\rceil$$
--   for a parameter $\kappa$. The **Krylov space** is
--   $$R_{t_0,M}=\operatorname{span}\{v_t:\ t_0\le t<t_0+M\},$$
--   and $\lambda_{\max}(\Pi_Rx\Pi_R)$ is the largest value of $\langle\psi,x\psi\rangle$ over unit vectors $\psi\in R$.
--
--   On $R$ the operator $x$ acts as a one-dimensional hopping model with amplitudes $\beta_t$; its top eigenvalue is the witness value that the lower-bound argument transports to the SYK Hamiltonian.
--
--   **Formalization Note** $\psi_t\ne0$ for every $t$, so $v_t$ and $\beta_t$ are well defined. $\lfloor\cdot\rfloor$ and $\lceil\cdot\rceil$ are taken as natural numbers. $R$ is finite-dimensional, so the supremum defining $\lambda_{\max}(\Pi_Rx\Pi_R)$ is finite.
-- source:
--   Basu, Kothari, Midha, Sharp Bounds on Ground State Energy of the SYK Model, arXiv:2607.27185v2, eqs. (21)–(25) and Definition 4.11, p.28; Lemma 4.12, p.29

import Mathlib
import Definitions.Def_SYKEdge_Fock
import Definitions.Def_SYKEdge_SignMatrix

namespace SYKEdge

/-!
# The Krylov vectors `ψ_t, v_t`, the hopping amplitudes `β_t`, and the Krylov space `R_{t₀,M}`

A. Basu, P. K. Kothari, S. Midha, *Sharp Bounds on Ground State Energy of the SYK Model*,
arXiv:2607.27185v2, (21)–(25) and Definition 4.11, p.28; `λ_max(Π_R x Π_R)`, Lemma 4.12, p.29.

**Formalization Note.**
* `psiK S t = ψ_t = (a*)^t f₀`, `vK S t = v_t = ψ_t/‖ψ_t‖`, `betaK S t = β_t = ‖ψ_{t+1}‖/‖ψ_t‖`.
  The page notes `ψ_t ≠ 0` for every `t` (p.28), so these are well defined.
* `nuParam S = ν = 1 − q`, `MParam S = M = ⌊1/ν⌋`, `t0Param S κ = t₀ = ⌈κ/ν⌉` ((24) and Lemma 4.12),
  with `⌊·⌋`, `⌈·⌉` as natural numbers (`Nat.floor`, `Nat.ceil`).
* `krylovR S t₀ M = R_{t₀,M} = span{v_t : t₀ ⩽ t < t₀ + M}`, (25).
* `lamMaxOn S R = λ_max(Π_R x Π_R)`: the supremum of `re ⟨ψ, xψ⟩` over unit vectors `ψ ∈ R`, i.e. the
  top eigenvalue of the compression of `x` to `R` (the matrix displayed in the proof of Lemma 4.12).
  `R` is finite-dimensional, so the supremum is finite; it is over a nonempty set when `R ≠ 0`,
  e.g. for `M ⩾ 1`.
-/

/-- `ψ_t := (a*)^t f₀`, (21). -/
noncomputable def psiK {n m : ℕ} (S : Fin m → Finset (Fin n)) (t : ℕ) : Fock m :=
  (adagTot S ^ t) (fbasis 0)

/-- `v_t := ψ_t / ‖ψ_t‖`, (22). -/
noncomputable def vK {n m : ℕ} (S : Fin m → Finset (Fin n)) (t : ℕ) : Fock m :=
  ((((normF (psiK S t))⁻¹ : ℝ)) : ℂ) • psiK S t

/-- `β_t := ‖ψ_{t+1}‖ / ‖ψ_t‖`, (23). -/
noncomputable def betaK {n m : ℕ} (S : Fin m → Finset (Fin n)) (t : ℕ) : ℝ :=
  normF (psiK S (t + 1)) / normF (psiK S t)

/-- `ν := 1 − q`, (24). -/
noncomputable def nuParam {n m : ℕ} (S : Fin m → Finset (Fin n)) : ℝ :=
  1 - qParam S

/-- `M := ⌊1/ν⌋`, (24). -/
noncomputable def MParam {n m : ℕ} (S : Fin m → Finset (Fin n)) : ℕ :=
  ⌊1 / nuParam S⌋₊

/-- `t₀ := ⌈κ/ν⌉` (Lemma 4.12). -/
noncomputable def t0Param {n m : ℕ} (S : Fin m → Finset (Fin n)) (κ : ℝ) : ℕ :=
  ⌈κ / nuParam S⌉₊

/-- The Krylov space `R_{t₀,M} := span{v_t : t₀ ⩽ t < t₀ + M}`, Definition 4.11, (25). -/
noncomputable def krylovR {n m : ℕ} (S : Fin m → Finset (Fin n)) (t₀ M : ℕ) :
    Submodule ℂ (Fock m) :=
  Submodule.span ℂ (vK S '' Set.Ico t₀ (t₀ + M))

/-- `λ_max(Π_R x Π_R)`: the supremum of `re ⟨ψ, xψ⟩` over unit vectors `ψ ∈ R`. -/
noncomputable def lamMaxOn {n m : ℕ} (S : Fin m → Finset (Fin n)) (R : Submodule ℂ (Fock m)) :
    ℝ :=
  ⨆ ψ : {ψ : Fock m // ψ ∈ R ∧ normF ψ = 1}, (fockInner ψ.1 (xop S ψ.1)).re

end SYKEdge


