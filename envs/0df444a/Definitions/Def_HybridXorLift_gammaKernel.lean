-- Prove2me | Definitions.Def_HybridXorLift_gammaKernel
-- name    : HybridXorLift_gammaKernel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:13:32.479363+00:00
-- url     : https://prove2.me/theorems/f7ffe7ee-0605-45e6-8d76-dd73175281f3
-- title:
--   Kernel $\Gamma_{I,\zeta}(x, x')$
-- statement:
--   Fix a nonempty set $I \subseteq [n]$ of blocks. For physical inputs $x, x'$,
--   $$
--   \Gamma_{I,\zeta}(x, x') = \begin{cases} \prod_{i \in I} \prod_{j=1}^r L_{x_{ij}, x'_{ij}}, & x_{\bar I} = x'_{\bar I}, \\ 0, & \text{otherwise}, \end{cases}
--   $$
--   where $L$ is the one-bit kernel with $\tau = 1/(2q)$. The condition $x_{\bar I} = x'_{\bar I}$ asks for equality of the complete blocks outside $I$, which is stronger than equality of their parities.
--
--   **Formalization Note** The formula is defined for all pairs of physical inputs; the paper's kernel on $X_{I,\zeta} = \{x : \sigma(x)_{\bar I} = \zeta\}$ is its restriction, and this is how the potential uses it.
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), §3.2, Eq. (3.5), p.12 (PDF p.14)

import Definitions.Def_HybridXorLift_kernelL

namespace HybridXorLift

/-- The kernel `Γ_{I,ζ}(x, x′)` (Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), §3.2, Eq. (3.5), p.12 (PDF p.14)): equal to
`∏_{i∈I} ∏_{j=1}^r L_{x_{ij}, x′_{ij}}` when `x` and `x′` agree on every physical bit of every
block outside `I` ("equality of the complete blocks outside I, which is stronger than equality
of their parities"), and `0` otherwise; `L` is `kernelL q` with `τ = 1/(2q)`.

**Formalization Note** The function is defined on all pairs of physical inputs; the paper's
`Γ_{I,ζ}` is its restriction to `X_{I,ζ} × X_{I,ζ}`, which is how `psi` uses it. -/
noncomputable def gammaKernel {n r : ℕ} (q : ℕ) (I : Finset (Fin n))
    (x x' : Fin n × Fin r → Bool) : ℝ :=
  if ∀ i ∉ I, ∀ j, x (i, j) = x' (i, j) then
    ∏ i ∈ I, ∏ j, kernelL q (x (i, j)) (x' (i, j))
  else 0

end HybridXorLift


