-- Prove2me | Definitions.Def_OptGaussTomo_boseGauss
-- name    : OptGaussTomo_boseGauss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:06:08.793119+00:00
-- url     : https://prove2.me/theorems/37388f55-5cf2-4db2-b8f0-9e1a2620120a
-- title:
--   Bosonic Gaussian states and pure bosonic Gaussian states on $m$ modes
-- statement:
--   The $m$-mode bosonic Hilbert space $L^2(\mathbb R^m)$ is described by its Fock basis $|x\rangle$, $x\in\mathbb N^m$. With the quadratures $(r_1,\dots,r_{2m})=(q_1,p_1,\dots,q_m,p_m)$, $q_j=(a_j^\dagger+a_j)/\sqrt2$, $p_j=i(a_j^\dagger-a_j)/\sqrt2$, and the Weyl operators $W(\xi)=e^{i\xi\cdot r}$, a state $\rho$ is **Gaussian with mean $\mu\in\mathbb R^{2m}$ and covariance matrix $V$** if
--
--   $$
--   \operatorname{tr}[\rho\,W(\xi)]=\exp\!\big(i\,\xi\cdot\mu-\tfrac14\,\xi^{\mathsf T}V\xi\big)\qquad\text{for all }\xi\in\mathbb R^{2m}.
--   $$
--
--   (The vacuum has $\mu=0$, $V=I$.) $\mathrm{boseGauss}(m)$ is the set of all $m$-mode bosonic Gaussian states, with any mean and covariance; $\mathrm{bosePure}(m)$ the set of pure ones, $\rho=|u\rangle\langle u|$ with $\|u\|=1$.
--
--   **Formalization Note** The predicate is the published `Support50.P14.GaussianAt`, which also records finite mean photon number, a symmetric $V$ and the moment identities; every Gaussian state satisfies them. This is the standard equivalent of the paper's definition (Gibbs states of quadratic Hamiltonians bounded below, and their trace-norm limits). **No energy bound** is imposed and the mean is arbitrary.
-- source:
--   Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, Optimal tomography of bosonic and fermionic Gaussian states, arXiv:2607.11847 (held version, sha256 0f7548a2a5cfd55079e5d7f1787c97c8561a818a53d7e29824715104bad416ed), §D.1 pp.42–43 (pdf pp.42–43), eq. (D.4); §D.6 p.55

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P47
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State rankOne)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Support50.P14 (GaussianAt)

namespace OptGaussTomo

/-!
# The classes of m-mode bosonic Gaussian states and pure bosonic Gaussian states

Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, *Optimal tomography of bosonic and
fermionic Gaussian states*, arXiv:2607.11847 (held version, sha256 0f7548a2…), §D.1, pp.42–43:
`H_m = L²(ℝ^m)`, quadratures `(r_1, …, r_{2m}) = (q_1, p_1, …, q_m, p_m)`; "A Gaussian state is a
Gibbs state … (D.4) for a quadratic Hamiltonian H which is bounded from below, or a (trace norm)
limit of such states"; §D.6, p.55: `ρ_{μ,V}` with first moment `μ ∈ ℝ^{2m}` and covariance `V`.

**Formalization Note.** `L²(ℝ^m)` is represented by its Fock basis `Occupation (Fin m) = Fin m → ℕ`
(published `Claimed50.P47`). A state is Gaussian iff it is `GaussianAt ρ d γ` for some mean `d`
and covariance `γ` (published `Support50.P14`): its characteristic function is
`exp(i ξ·d − ¼ ξᵀ γ ξ)`, with interleaved coordinates `(j, 0) = q_j`, `(j, 1) = p_j` and the
vacuum covariance `γ = I`, which is the source's convention for `V` (heterodyne seed `W = I`,
p.56), with `μ = d`. `GaussianAt` also contains `CompleteMoments` (finite mean photon number,
symmetric `γ`, the moment identities); every Gaussian state satisfies them, so nothing is added.
This is the standard equivalent of (D.4) together with its trace-norm limits. **No energy bound**
is imposed (`Support50.P14.InDomain`, which has an optional cap, is not used), and the mean is
arbitrary. Pure states are rank-one projectors `|u⟩⟨u|` of unit vectors.
-/

/-- The m-mode bosonic Gaussian states (any mean, any covariance, no energy bound). -/
def boseGauss (m : ℕ) : Set (State (Occupation (Fin m))) :=
  {ρ | ∃ d γ, GaussianAt ρ.coefficients d γ}

/-- The m-mode pure bosonic Gaussian states. -/
def bosePure (m : ℕ) : Set (State (Occupation (Fin m))) :=
  {ρ | (∃ d γ, GaussianAt ρ.coefficients d γ) ∧
    ∃ u : Hilbert (Occupation (Fin m)), ‖u‖ = 1 ∧ ρ.coefficients = rankOne u}

end OptGaussTomo


