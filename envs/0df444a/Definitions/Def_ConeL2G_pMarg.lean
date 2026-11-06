-- Prove2me | Definitions.Def_ConeL2G_pMarg
-- name    : ConeL2G_pMarg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:40:37.306567+00:00
-- url     : https://prove2.me/theorems/c5b47d3f-d1eb-42ec-a554-283c0cfd1f3e
-- title:
--   The conditional marginal $p_{i,c}$
-- statement:
--   For an available color $c\in L_i^{-x_{N_H(i)}}$,
--   $$p_{i,c}(x)=\Pr_\mu[X_i=c\mid X_{-i}=x_{-i}]=\frac{1}{\ell_i^{-x_{N_H(i)}}},$$
--   since the conditional law of $X_i$ is uniform on the available colors.
--
--   **Formalization Note** The value does not depend on $c$ and is written $1/\ell_i^{-x_{N_H(i)}}$; it is used only for available $c$.
-- source:
--   Li–Oveis Gharan, Local-to-Global Theorems Based on Cones with Applications to Graph Coloring, arXiv:2610.37721, Section 2.1, p.7

import Mathlib
import Definitions.Def_ConeL2G_avail

namespace ConeL2G

/-- **The conditional marginal** `p_{i,c}(x) = P_µ[Xᵢ = c | X_{−i} = x_{−i}] = 1/ℓ_i^{−x_{N_H(i)}}`
for an available color `c`. Li–Oveis Gharan, arXiv:2610.37721, Section 2.1, p.7: "Conditioned on
`X_{−i} = x_{−i}`, observe that the distribution of `Xᵢ` is uniform on `L_i^{−x_{N_H(i)}}`. For
`c ∈ L_i^{−x_{N_H(i)}}`, we define `p_{i,c}(x) = P_µ[Xᵢ = c | X_{−i} = x_{−i}]`."

**Formalization Note.** Since the conditional law is uniform on the available colors, the value
does not depend on `c`; it is written as `1/|avail|`, which is the paper's value for every
available `c` (and is only used for available `c`). -/
noncomputable def pMarg {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {K : ℕ} (L : V → Finset (Fin K)) (i : V) (x : V → Fin K) : ℝ :=
  1 / ((avail H L i x).card : ℝ)

end ConeL2G


