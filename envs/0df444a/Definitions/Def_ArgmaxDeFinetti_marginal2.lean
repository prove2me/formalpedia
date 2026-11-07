-- Prove2me | Definitions.Def_ArgmaxDeFinetti_marginal2
-- name    : ArgmaxDeFinetti_marginal2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:40:15.345293+00:00
-- url     : https://prove2.me/theorems/d65e85c4-423b-4f33-9538-18f68922827d
-- title:
--   Two-site marginal $\rho^{(2)}_N=\operatorname{Tr}_{3,\dots,N}\rho_N$
-- statement:
--   For an operator $\rho_N$ on $N=2+m$ sites, the marginal on the first two sites is the partial trace over sites $3,\dots,N$:
--   $$
--   \big(\rho^{(2)}_N\big)_{a,b}=\sum_{c\in\{1,\dots,d\}^{m}}(\rho_N)_{(a,c),(b,c)},\qquad a,b\in\{1,\dots,d\}^2 .
--   $$
--
--   **Formalization Note** $N$ is written $2+m$ with $m\ge0$; the index of $N$ sites is the concatenation $(a,c)$ of the indices of sites $1,2$ and of sites $3,\dots,N$.
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), §2.1 'Bosonic states', p.19

import Mathlib
import Definitions.Def_ArgmaxDeFinetti_tensorPow

open Matrix

namespace ArgmaxDeFinetti

/-- The two-site marginal `ρ^{(2)}_N = Tr_{3,…,N} ρ_N` of an operator on `N = 2 + m` sites: the partial
trace over every site but the first two, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), §2.1 "Bosonic states", p.19.

**Formalization Note** `N` is written `2 + m`; the tensor index of `N` sites is `Fin.append a c` with
`a` the indices of sites `1, 2` and `c` those of sites `3, …, N`. -/
def marginal2 {m d : ℕ} (ρ : Op (2 + m) d) : Op 2 d :=
  fun a b => ∑ c : Fin m → Fin d, ρ (Fin.append a c) (Fin.append b c)

end ArgmaxDeFinetti


