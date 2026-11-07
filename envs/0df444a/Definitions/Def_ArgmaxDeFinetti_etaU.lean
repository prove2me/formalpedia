-- Prove2me | Definitions.Def_ArgmaxDeFinetti_etaU
-- name    : ArgmaxDeFinetti_etaU
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:40:40.451895+00:00
-- url     : https://prove2.me/theorems/4424b8e7-ab88-4dbb-b48f-ac5e031d079e
-- title:
--   Partial inner product $\eta_u=(\langle u|^{\otimes(N-2)}\otimes I)\psi$
-- statement:
--   For $u\in\mathbb C^d$ and $\psi\in(\mathbb C^d)^{\otimes N}$ with $N=2+m$, the two-site vector $\eta_u$ is obtained by taking the inner product with $u$ on $N-2$ sites:
--   $$
--   \eta_u(a)=\sum_{c\in\{1,\dots,d\}^m}\Big(\prod_{k}\overline{u_{c_k}}\Big)\,\psi(a,c),\qquad a\in\{1,\dots,d\}^2 .
--   $$
--
--   **Formalization Note** The contraction is over sites $3,\dots,N$ and keeps sites $1,2$; the paper writes the contracted factors first. For symmetric $\psi$, the only case used, both give the same vector. Keeping sites $1,2$ matches $M_{12}$ in (3.19).
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), §3.1.2, p.23, eq. (3.7)

import Mathlib
import Definitions.Def_ArgmaxDeFinetti_tensorPow

open Matrix

namespace ArgmaxDeFinetti

/-- `η_u = (⟨u|^{⊗(N−2)} ⊗ I_{H^{⊗2}}) ψ`: the two-site vector obtained by taking the partial inner product
of `ψ ∈ (ℂ^d)^{⊗N}`, `N = 2 + m`, with `u` on `N − 2` sites, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), eq. (3.7), p.23.

**Formalization Note** The contraction is over sites `3, …, N` and keeps sites `1, 2` (index
`Fin.append a c`); the paper's notation writes the contracted factors first. For symmetric `ψ`, the only case
the paper uses, the two choices give the same vector. The keeping of sites `1, 2` matches `M₁₂` in (3.19)
(`siteOp M 0 1`) and the marginal `Tr_{3,…,N}`. `⟨u|` is conjugate-linear: the coefficients are
`conj(u)`. -/
def etaU {m d : ℕ} (u : Fin d → ℂ) (ψ : Vec (2 + m) d) : Vec 2 d :=
  fun a => ∑ c : Fin m → Fin d, (∏ k, star (u (c k))) * ψ (Fin.append a c)

end ArgmaxDeFinetti


