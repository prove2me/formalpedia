-- Prove2me | Definitions.Def_NoisyOWMPC_CompClose
-- name    : NoisyOWMPC_CompClose
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:45:59.095671+00:00
-- url     : https://prove2.me/theorems/fdc51134-8179-4cfd-a50b-3a4225d332c3
-- title:
--   Computational closeness $U_0\approx^c_\varepsilon U_1$ of input-indexed ensembles
-- statement:
--   For input-indexed ensembles $U_0(\lambda,x)$ and $U_1(\lambda,x)$ and an error function $\varepsilon$, write $U_0\approx^c_\varepsilon U_1$ if for every nonuniform polynomial-size distinguisher $\mathcal A$ there is a negligible function $\nu_{\mathcal A}$ such that for every $\lambda$ and every input $x$
--   $$\bigl|\Pr[\mathcal A(1^\lambda,U_0(\lambda,x))=1]-\Pr[\mathcal A(1^\lambda,U_1(\lambda,x))=1]\bigr|\le\varepsilon(\lambda)+\nu_{\mathcal A}(\lambda).$$
--
--   This is the security notion of Definition 4.2: "the same bound holds uniformly over the prescribed inputs and externally chosen public parameters; $\nu_{\mathcal A}$ does not depend on their particular values". With $\varepsilon=0$ it is $U_0\approx^c U_1$.
--
--   **Formalization Note** $\nu_{\mathcal A}$ is chosen after $\mathcal A$ and before $\lambda$ and $x$.
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), §3 Notation and conventions, p.15

import Mathlib
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_NoisyOWMPC_Distinguisher

namespace NoisyOWMPC

/-- **Computational closeness `U₀ ≈^c_ε U₁` of input-indexed ensembles** (Ishai, Lu, Zafar, STOC 2027
submission (manuscript sha256 3a9569fa…), §3 Notation and conventions, p.15): "for every nonuniform
PPT distinguisher `A`, there is a negligible function `ν_A` such that
`|Pr[A(1^λ, U₀) = 1] − Pr[A(1^λ, U₁) = 1]| ≤ ε(λ) + ν_A(λ)` … For input-indexed experiments, the
same bound holds uniformly over the prescribed inputs and externally chosen public parameters;
`ν_A` does not depend on their particular values."

Here `U_b(λ, x)` is the outcome string `u_b λ x ω` of a finite experiment with sample space `Ω_b λ`
and weights `w_b λ x`, for every input `x ∈ I λ`.

**Formalization Note** `ν_A` is chosen after `A` and before `λ` and the input `x` (uniformity over
inputs). Distinguishers are polynomial-size circuit families (`Distinguisher.IsPoly`). With `ε = 0`
this is `U₀ ≈^c U₁`. -/
def CompClose {I Ω₀ Ω₁ : ℕ → Type} [∀ l, Fintype (Ω₀ l)] [∀ l, Fintype (Ω₁ l)]
    (w₀ : ∀ l, I l → Ω₀ l → ℝ) (u₀ : ∀ l, I l → Ω₀ l → List Bool)
    (w₁ : ∀ l, I l → Ω₁ l → ℝ) (u₁ : ∀ l, I l → Ω₁ l → List Bool) (ε : ℕ → ℝ) : Prop :=
  ∀ A : Distinguisher, A.IsPoly → ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ (lam : ℕ) (x : I lam),
    |A.accProb lam (w₀ lam x) (u₀ lam x) - A.accProb lam (w₁ lam x) (u₁ lam x)| ≤ ε lam + ν lam

end NoisyOWMPC


