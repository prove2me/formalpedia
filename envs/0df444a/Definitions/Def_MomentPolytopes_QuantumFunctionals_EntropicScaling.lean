-- Prove2me | Definitions.Def_MomentPolytopes_QuantumFunctionals_EntropicScaling
-- name    : MomentPolytopes_QuantumFunctionals_EntropicScaling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:03:24.501204+00:00
-- url     : https://prove2.me/theorems/71ce99b8-1aff-46f0-882f-527007196268
-- title:
--   Entropic tensor scaling (7.5) and the quantum entropy inequality (7.6)
-- statement:
--   Let $\theta$ be a probability distribution on $[d]$, $\eta>0$, and $T$ a nonzero concise tensor tuple. The iteration (7.5) is
--   $$T_{k+1}=\Big(I\otimes\bigotimes_{\ell=1}^d\rho_\ell^{-\eta\theta_\ell/2}\Big)T_k,\qquad(\rho_1,\dots,\rho_d)=\mu(T_k),\qquad T_0=T ,$$
--   with the positive-definite matrix power $\rho_\ell^{-s}$ and no renormalization; for $\eta=1$ it is **entropic tensor scaling**.
--
--   For a positive-semidefinite $\rho$ on $\mathbb C^{n_1}\otimes\dots\otimes\mathbb C^{n_d}$ with marginals $\rho_\ell=\operatorname{tr}_{\check\ell}\rho$, put
--   $$\sigma=\Big(\bigotimes_{\ell=1}^d\rho_\ell^{-\eta\theta_\ell/2}\Big)\rho\Big(\bigotimes_{\ell=1}^d\rho_\ell^{-\eta\theta_\ell/2}\Big),\qquad\sigma_\ell=\operatorname{tr}_{\check\ell}\sigma .$$
--   The inequality **(7.6)** for $(\eta,\theta,\rho)$ is
--   $$\eta\sum_{\ell=1}^d\theta_\ell\,H\Big(\frac{\sigma_\ell}{\operatorname{tr}\sigma}\Big)\ \ge\ \log\operatorname{tr}\sigma .$$
--
--   **Formalization Note** $\rho_\ell^{-s}$ is `cfc (fun x => x ^ (-s))` (real power); for $\theta_\ell=0$ it is the identity. $H$ is the von Neumann entropy of `Spectra`; $\operatorname{tr}\sigma$ enters the logarithm through its real part (it is real and positive).
-- source:
--   Doğan, Sakabe, Walter, Convex optimization on moment polytopes, arXiv:2609.06633 (PDF sha256 fcf40771…), p. 55, eq. (7.5) and Lemma 7.4, eq. (7.6)

import Mathlib
import Definitions.Def_MomentPolytopes_QuantumFunctionals_Spectra
import Definitions.Def_MomentPolytopes_QuantumFunctionals_TensorAction

set_option autoImplicit false

namespace MomentPolytopes.QuantumFunctionals

variable {d n0 : ℕ} {n : Fin d → ℕ}

/-- The iteration (7.5), p. 55, with step size `η`:
`T_{k+1} = (I ⊗ ⊗_ℓ ρ_ℓ^{−ηθ_ℓ/2}) T_k`, `(ρ_1, …, ρ_d) = µ(T_k)`, `T_0 = T`, where `ρ_ℓ^{−s}`
is the matrix power of the positive-definite marginal (functional calculus of `x ↦ x^{−s}`).
No normalization is performed. For `η = 1` this is **entropic tensor scaling**. -/
noncomputable def entropicScalingSeq (η : ℝ) (θ : Fin d → ℝ) (T : Ten d n0 n) :
    ℕ → Ten d n0 n
  | 0 => T
  | k + 1 =>
      act (fun ℓ => cfc (fun x : ℝ => x ^ (-(η * θ ℓ / 2)))
          (momentMap (entropicScalingSeq η θ T k) ℓ))
        (entropicScalingSeq η θ T k)

/-- `σ := (⊗_ℓ ρ_ℓ^{−ηθ_ℓ/2}) ρ (⊗_ℓ ρ_ℓ^{−ηθ_ℓ/2})` with `ρ_ℓ = tr_ℓ̌ ρ` (eq. (7.6), p. 55). -/
noncomputable def sigmaOf (η : ℝ) (θ : Fin d → ℝ) (ρ : Matrix (MIdx n) (MIdx n) ℂ) :
    Matrix (MIdx n) (MIdx n) ℂ :=
  kron (fun ℓ => cfc (fun x : ℝ => x ^ (-(η * θ ℓ / 2))) (partialTrace ℓ ρ)) * ρ *
    kron (fun ℓ => cfc (fun x : ℝ => x ^ (-(η * θ ℓ / 2))) (partialTrace ℓ ρ))

/-- The quantum entropy inequality (7.6), p. 55:
`η ∑_ℓ θ_ℓ H(σ_ℓ / tr σ) ≥ log tr σ`, `σ_ℓ := tr_ℓ̌ σ`, `σ = sigmaOf η θ ρ`. -/
def EntropyIneq76 (η : ℝ) (θ : Fin d → ℝ) (ρ : Matrix (MIdx n) (MIdx n) ℂ) : Prop :=
  η * ∑ ℓ, θ ℓ * vnEntropy ((Matrix.trace (sigmaOf η θ ρ))⁻¹ • partialTrace ℓ (sigmaOf η θ ρ)) ≥
    Real.log (Matrix.trace (sigmaOf η θ ρ)).re

end MomentPolytopes.QuantumFunctionals


