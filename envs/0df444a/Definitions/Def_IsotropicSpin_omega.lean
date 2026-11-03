-- Prove2me | Definitions.Def_IsotropicSpin_omega
-- name    : IsotropicSpin_omega
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:25:17.213564+00:00
-- url     : https://prove2.me/theorems/d948b598-5615-49d3-8d2a-c8d90b89f98a
-- title:
--   The matrix $\Omega_{kl}=\langle\phi,X_lX_k\phi\rangle$ of eq. (15) for $\Lambda_1$
-- statement:
--   For a vector $\phi\in\mathbb C^3$, the $3\times3$ matrix $\Omega$ of eq. (15) for the spin-1 channel $\Lambda_1$ has entries
--
--   $$
--   \Omega_{kl}=\langle\phi,X_lX_k\phi\rangle=\tfrac12\langle\phi,S_lS_k\phi\rangle,\qquad k,l=1,2,3,
--   $$
--
--   where $X_k=S_k/\sqrt{s(s+1)}=S_k/\sqrt2$ are the Kraus operators of $\Lambda_1=\sum_k X_k\cdot X_k$ and $S_k$ are the matrices (13). By (15), for a unit vector $\phi$ the output $\Lambda_1(|\phi\rangle\langle\phi|)$ and $\Omega$ have the same entropy, which reduces the lower bound (14) to the norm bound (16).
--
--   **Formalization Note** $\langle u,v\rangle=\sum_i\overline{u_i}v_i$ is linear in the second argument. Indices $0,1,2$ are the paper's $1,2,3$. $\phi$ is any vector; the paper uses unit vectors.
-- source:
--   Alicki, Isotropic quantum spin channels and additivity questions, arXiv:quant-ph/0402080v1, eq. (15), p.2

import Mathlib
import Definitions.Def_IsotropicSpin_spinOne

open scoped Matrix

namespace IsotropicSpin

/-- **The matrix `Ω`** of Alicki, arXiv:quant-ph/0402080v1, eq. (15), p. 2, for the spin-1 channel
`Λ₁`: `Ω_{kl} = ⟨φ, X_l X_k φ⟩`, where `X_k = S_k/√(s(s+1)) = S_k/√2` are the Kraus operators of
`Λ₁ = Σ_k X_k · X_k` (eq. (6) with `s = 1`). Since `X_l X_k = ½ S_l S_k`,
`Ω_{kl} = ½ ⟨φ, S_l S_k φ⟩`.

**Formalization Note** `⟨u, v⟩ = Σ_i conj(u_i) v_i` is linear in the second argument
(`star φ ⬝ᵥ v`). Indices `k, l = 0, 1, 2` are the paper's `1, 2, 3`. `φ` is any vector of `ℂ³`;
the paper uses unit vectors. -/
noncomputable def omega (φ : Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.of fun k l => (1 / 2 : ℂ) * (star φ ⬝ᵥ ((spinOne l * spinOne k) *ᵥ φ))

end IsotropicSpin


