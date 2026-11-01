-- Prove2me | Definitions.Def_WildeQIT_QMemory_qRelEntropy
-- name    : WildeQIT_QMemory_qRelEntropy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:56:15.116506+00:00
-- url     : https://prove2.me/theorems/8f3cc850-bd86-4b6c-a64d-c4aa4e97f143
-- title:
--   Quantum relative entropy $D(\rho\|\sigma)$, $+\infty$ off support
-- statement:
--   Let $\rho$ be a density operator and $\sigma$ a positive semi-definite operator on $\mathcal H$. The **support** of an operator is the orthogonal complement of its kernel. The **quantum relative entropy** is
--
--   $$
--   D(\rho\|\sigma)\equiv\mathrm{Tr}\{\rho[\log\rho-\log\sigma]\}\quad\text{if }\operatorname{supp}(\rho)\subseteq\operatorname{supp}(\sigma),
--   $$
--
--   and $D(\rho\|\sigma)=+\infty$ otherwise. Logarithms are base 2.
--
--   Many entropies of the chapter are relative entropies, and its monotonicity under channels implies the main entropy inequalities.
--
--   **Formalization Note** The value lies in `EReal`, so $+\infty$ is representable. The support condition is written $\ker\sigma\subseteq\ker\rho$, which is equivalent because the support is the orthogonal complement of the kernel. $\log\sigma$ is `cfc (Real.logb 2) σ`, which is the logarithm on the support of $\sigma$ (since `Real.logb 2 0 = 0`), the operator the formula uses under the support condition.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Definitions 11.8.1–11.8.2, eqs. (11.103)–(11.107), p. 340

import Mathlib

namespace WildeQIT.QMemory

/-- **Quantum relative entropy** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, Definitions 11.8.1–11.8.2, p. 340): for a density operator `ρ` and a positive
semi-definite `σ`, `D(ρ‖σ) ≡ Tr{ρ [log ρ − log σ]}` (11.106) if `supp(ρ) ⊆ supp(σ)` (11.107),
and `+∞` otherwise.

**Formalization Note** The value lies in `EReal` so that `+∞` is representable. The support
condition is written `ker σ ⊆ ker ρ`; since `supp(A) = ker(A)^⊥` (Definition 11.8.1), the two
inclusions are equivalent. Logarithms are base 2 (bits) via `cfc (Real.logb 2)`; because
`Real.logb 2 0 = 0`, `log σ` is the logarithm on the support of `σ`, which is the operator the
book's formula uses under (11.107). The support test is decided classically. -/
noncomputable def qRelEntropy {n : Type} [Fintype n] [DecidableEq n]
    (ρ σ : Matrix n n ℂ) : EReal :=
  haveI := Classical.propDecidable
  if LinearMap.ker (Matrix.toLin' σ) ≤ LinearMap.ker (Matrix.toLin' ρ) then
    (((Matrix.trace (ρ * cfc (Real.logb 2) ρ)).re
      - (Matrix.trace (ρ * cfc (Real.logb 2) σ)).re : ℝ) : EReal)
  else ⊤

end WildeQIT.QMemory


