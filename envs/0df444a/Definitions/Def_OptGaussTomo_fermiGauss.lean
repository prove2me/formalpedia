-- Prove2me | Definitions.Def_OptGaussTomo_fermiGauss
-- name    : OptGaussTomo_fermiGauss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:05:48.509176+00:00
-- url     : https://prove2.me/theorems/12c33870-d50e-46f9-9cad-ce9eff880a00
-- title:
--   Fermionic Gaussian states and pure fermionic Gaussian states on $m$ modes
-- statement:
--   The $m$-mode fermionic Fock space $\mathcal H_m=\bigwedge\mathbb C^m$ is identified with $m$ qubits $(\mathbb C^2)^{\otimes m}$ by the Jordan–Wigner map $c_{2j-1}\mapsto Z_1\cdots Z_{j-1}X_j$, $c_{2j}\mapsto Z_1\cdots Z_{j-1}Y_j$. A **fermionic Gaussian state** is a Gibbs state $\rho=e^{-H}/\operatorname{tr}e^{-H}$ of a quadratic Hamiltonian
--
--   $$
--   H=i\sum_{j,k=1}^{2m}h_{jk}c_jc_k,\qquad h_{jk}=-h_{kj}\in\mathbb R,
--   $$
--
--   or a limit of such states; a **pure** fermionic Gaussian state is a nondegenerate ground state of such an $H$. $\mathrm{fermiGauss}(m)$ is the set of all $m$-mode fermionic Gaussian states, $\mathrm{fermiPure}(m)$ the set of pure ones.
--
--   **Formalization Note** The class is the published `FermiCap.Gaussian.IsEvenGaussian`: $\rho=U\rho_\lambda U^\dagger$ with $U=e^{iH_2}$, $H_2$ Hermitian and quadratic in the Majorana operators, and $\rho_\lambda=2^{-m}\prod_j(I+\lambda_jZ_j)$, $\lambda_j\in[-1,1]$. This compact set contains every Gibbs state (standard form (C.4)) and each of its points is a limit of Gibbs states, so it is the paper's class. The larger class `IsGaussian` (with linear Majorana terms) is not used. Pure means idempotent.
-- source:
--   Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, Optimal tomography of bosonic and fermionic Gaussian states, arXiv:2607.11847 (held version, sha256 0f7548a2a5cfd55079e5d7f1787c97c8561a818a53d7e29824715104bad416ed), §C.1 pp.32–33 (pdf pp.32–33), eqs. (C.2)–(C.4)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_FermiCap_Gaussian_States

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open FermiCap.Gaussian (Qubits IsEvenGaussian IsPure)

namespace OptGaussTomo

/-!
# The classes of m-mode fermionic Gaussian states and pure fermionic Gaussian states

Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, *Optimal tomography of bosonic and
fermionic Gaussian states*, arXiv:2607.11847 (held version, sha256 0f7548a2…), §C.1, pp.32–33:
`H_m = ⋀ℂ^m ≅ (ℂ²)^{⊗m}` with the Jordan–Wigner Majorana operators; "A pure state in `H_m` is
Gaussian if it is the nondegenerate ground state of a quadratic Hamiltonian of the form (C.2).
… a mixed Gaussian state is a Gibbs state of a quadratic Hamiltonian, (C.3), or a limit of such
states."

**Formalization Note.** The class is the published `FermiCap.Gaussian.IsEvenGaussian`:
`ρ = U ρ_λ U†` with `U = exp(i H₂)`, `H₂` Hermitian in the span of the quadratic Majorana
monomials `c_p c_q`, and `ρ_λ = 2^{−m} ∏_j (I + λ_j Z_j)`, `λ_j ∈ [−1, 1]`. This set is compact,
contains every Gibbs state (C.3) (`|λ_j| < 1`, by the standard form (C.4)) and each of its points
is a limit of Gibbs states, so it is exactly the source's class. `FermiCap.Gaussian.IsGaussian`
(with linear Majorana terms) is a larger class and is not used. Pure states are the idempotent
ones (`IsPure`); a pure even Gaussian state is a nondegenerate ground state of (C.2). The arrays
of the published `State (Qubits m)` (density operators on `ℓ²(Qubits m)`) and `Op m` are the same
type, and on a finite basis both density notions agree.
-/

/-- The m-mode fermionic Gaussian states. -/
def fermiGauss (m : ℕ) : Set (State (Qubits m)) :=
  {ρ | IsEvenGaussian ρ.coefficients}

/-- The m-mode pure fermionic Gaussian states. -/
def fermiPure (m : ℕ) : Set (State (Qubits m)) :=
  {ρ | IsEvenGaussian ρ.coefficients ∧ IsPure ρ.coefficients}

end OptGaussTomo


