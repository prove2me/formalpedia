-- Prove2me | Definitions.Def_OptGaussTomo_rootFidelity
-- name    : OptGaussTomo_rootFidelity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:05:44.416034+00:00
-- url     : https://prove2.me/theorems/14010004-d926-4ea8-9a44-a047c690870e
-- title:
--   Root fidelity $F(\rho,\sigma)$ in Uhlmann form
-- statement:
--   A vector $u\in\ell^2(I\times\mathbb N)$ **purifies** an operator $\rho$ on $\ell^2(I)$ if
--
--   $$
--   \rho_{ij}=\sum_{k\in\mathbb N}u_{(i,k)}\,\overline{u_{(j,k)}}\qquad\text{for all } i,j,
--   $$
--
--   i.e. $\rho$ is the partial trace of $|u\rangle\langle u|$ over the ancilla $\ell^2(\mathbb N)$. The root fidelity is
--
--   $$
--   F(\rho,\sigma)=\sup\{\,|\langle u,v\rangle| : \|u\|=\|v\|=1,\ u \text{ purifies } \rho,\ v \text{ purifies } \sigma\,\}.
--   $$
--
--   By Uhlmann's theorem $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1$, the fidelity of the paper; on pure states $F(\psi,\phi)=|\langle\psi|\phi\rangle|$. The paper's accuracy requirement is $F(\rho,\hat\rho)^2\ge1-\varepsilon^2$.
--
--   **Formalization Note** One definition serves the finite-dimensional fermionic and the infinite-dimensional bosonic systems. The ancilla $\ell^2(\mathbb N)$ is large enough for every density operator. The norm condition is implied by $\operatorname{Tr}\rho=1$; it makes the bound $F\le1$ visible. For densities the set is nonempty, so the supremum is a genuine value.
-- source:
--   Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, Optimal tomography of bosonic and fermionic Gaussian states, arXiv:2607.11847 (held version, sha256 0f7548a2a5cfd55079e5d7f1787c97c8561a818a53d7e29824715104bad416ed), §1 p.3 (pdf p.3); F = |⟨ψ|ψ̂⟩| on pure states, §C.3 p.37, §C.5 p.40, §D.7 p.60

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33

open QAlgorithms.RealRegisters (Hilbert)

namespace OptGaussTomo

/-!
# Root fidelity in Uhlmann form

Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, *Optimal tomography of bosonic and
fermionic Gaussian states*, arXiv:2607.11847 (held version, sha256 0f7548a2…), §1, p.3:
"an estimate `ρ̂` with fidelity to the true state `F(ρ, ρ̂)² ≥ 1 − ε²`"; on pure states
`F = |⟨ψ|ψ̂⟩|` (§C.3, p.37; §C.5, p.40; §D.7, p.60).

A vector `u ∈ ℓ²(I × ℕ)` **purifies** `ρ` if `ρ_ij = ∑_k u_(i,k) conj(u_(j,k))`, i.e. `ρ` is the
partial trace of `|u⟩⟨u|` over the ancilla `ℓ²(ℕ)`. The root fidelity is
`F(ρ, σ) = sup |⟨u, v⟩|` over unit purifications `u` of `ρ` and `v` of `σ`.

**Formalization Note.** By Uhlmann's theorem (valid on separable Hilbert spaces, with the
ancilla `ℓ²(ℕ)`, which is large enough for every density) this equals `‖√ρ √σ‖₁`, the root
fidelity of the source; on pure states it is `|⟨ψ|ψ̂⟩|`. The norm condition `‖u‖ = 1` is implied
by `Tr ρ = 1`; it is stated so that the supremum is visibly bounded by `1`. For densities the set
is nonempty (spectral decomposition), so the real supremum is not a junk value. One definition
serves both the finite (fermionic) and the infinite (bosonic) systems; the published
`WildeQIT.rootFidelity` is finite-dimensional only.
-/

/-- `u` purifies `ρ`: `ρ_ij = ∑_k u_(i,k) conj(u_(j,k))`. -/
def Purifies {I : Type} (ρ : Matrix I I ℂ) (u : Hilbert (I × ℕ)) : Prop :=
  ∀ i j, ρ i j = ∑' k : ℕ, u (i, k) * star (u (j, k))

/-- Root fidelity `F(ρ, σ)`: supremum of `|⟨u, v⟩|` over unit purifications. -/
noncomputable def rootFidelity {I : Type} (ρ σ : Matrix I I ℂ) : ℝ :=
  sSup {r : ℝ | ∃ u v : Hilbert (I × ℕ), ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ Purifies ρ u ∧ Purifies σ v ∧
    r = ‖inner ℂ u v‖}

end OptGaussTomo


