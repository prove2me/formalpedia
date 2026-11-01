-- Prove2me | Definitions.Def_DuanEP_Pure_entanglement
-- name    : DuanEP_Pure_entanglement
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:21:42.995992+00:00
-- url     : https://prove2.me/theorems/e16ac035-83c2-4f78-8d0d-1374886f33e9
-- title:
--   Entanglement $E(|\psi\rangle)$ of a pure bipartite state
-- statement:
--   For a pure bipartite state with coefficients $\psi:I\times J\to\mathbb C$, the **entanglement** is the von Neumann entropy of its reduced density operator on the first component:
--
--   $$
--   E(|\psi\rangle)=S\big(\mathrm{Tr}_J|\psi\rangle\langle\psi|\big),\qquad S(\rho)=-\mathrm{Tr}\,\rho\log\rho .
--   $$
--
--   The paper (p. 1): "For and only for a pure state, the entanglement is uniquely quantified by the von Neumann entropy of the reduced density operator of its one-component."
--
--   **Formalization Note** The partial trace is the platform's `traceSecond` and the entropy is the platform's `homogeneousEntropy` (Frontier18.P01): Lindblad's $\mathrm{Tr}\,\eta(X)-\eta(\mathrm{Tr}\,X)$ with $\eta(x)=-x\log x$, computed as a supremum over finite coordinate compressions, valued in $[0,\infty]$; on a density operator it is the von Neumann entropy, possibly infinite. Logarithms are natural (nats).
-- source:
--   Duan, Giedke, Cirac, Zoller, Entanglement purification of Gaussian continuous variable quantum states, arXiv:quant-ph/9912017v2, p. 1, after Eq. (1)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01
import Definitions.Def_DuanEP_Pure_pureKernel

open scoped ENNReal
open QAlgorithms.Papers.Independent.Frontier18.P01

namespace DuanEP.Pure

/-- The entanglement `E(|ψ⟩)` of a bipartite pure state with coefficients `ψ : I × J → ℂ`: "for and
only for a pure state, the entanglement is uniquely quantified by the von Neumann entropy of the reduced
density operator of its one-component" (Duan, Giedke, Cirac, Zoller, *Entanglement purification of Gaussian continuous variable quantum states*, arXiv:quant-ph/9912017v2, p. 1, after Eq. (1)). It is the von Neumann entropy of
the `I`-marginal `Tr_J |ψ⟩⟨ψ|`.

**Formalization Note** The marginal is the platform's `traceSecond` (partial trace over the second
factor `J`, here the `B` side) and the entropy is the platform's `homogeneousEntropy`
(Lindblad's `Tr η(X) − η(Tr X)`, computed as the supremum over finite coordinate compressions, valued
in `ℝ≥0∞` so that infinite entropy is allowed); for a density operator it is the von Neumann entropy.
Logarithms are natural (nats); the paper does not state a base. -/
noncomputable def entanglement {I J : Type} (ψ : I × J → ℂ) : ℝ≥0∞ :=
  homogeneousEntropy (traceSecond (pureKernel ψ))

end DuanEP.Pure


