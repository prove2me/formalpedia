-- Prove2me | Definitions.Def_ModFormPIR_Supplement_Track1Exponent
-- name    : ModFormPIR_Supplement_Track1Exponent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:46:50.658203+00:00
-- url     : https://prove2.me/theorems/9d9ad139-d11c-4333-9046-8e7de39c7401
-- title:
--   The Track 1 constants $\eta(\alpha)$, $\alpha^*$ and $\eta_{\mathrm{ends}}$
-- statement:
--   Let $H_2(t)=-t\log_2t-(1-t)\log_2(1-t)$ be the binary entropy function. For $\alpha\in[0,\tfrac13]$ put
--
--   $$\eta(\alpha)=\frac1{\log_2 3}\max\Big\{H_2(\alpha)+\alpha,\;H_2\big(\tfrac13-\alpha\big)+\tfrac23+\alpha\Big\}.$$
--
--   The two terms are equal at a unique point $\alpha^*=0.2994\ldots$ of $[0,\tfrac13]$, and $\eta_{\mathrm{ends}}=\eta(\alpha^*)=0.7444\ldots$ (Corollary 8.4).
--
--   $\eta(\alpha)$ is the exponent of the Fourier sparsity $3^{(\eta(\alpha)+o(1))d}$ of the "both ends" cone-delta functions on $\mathbb Z_3^d$ (Lemma 8.3), and $\eta_{\mathrm{ends}}$ is the exponent of the three-server scheme of Main Theorem 5.2.
--
--   **Formalization Note** $H_2$ is the platform's `WildeQIT.binaryEntropy`. On $[0,\tfrac13]$ the difference $H_2(\alpha)-H_2(\tfrac13-\alpha)-\tfrac23$ of the two terms is continuous and strictly increasing, negative at $0$ and positive at $\tfrac13$; so $\alpha^*$ is defined as the supremum of the points of $[0,\tfrac13]$ where the first term is at most the second, a set that contains $0$ and is bounded by $\tfrac13$.
-- source:
--   Henzinger, Ragavan, Doubly-Efficient Private Information Retrieval from Modular Forms, STOC 2027 submission (manuscript sha256 2442f3db…), Corollary 8.4, p.31 (PDF p.35)

import Mathlib
import Definitions.Def_WildeQIT_binaryEntropy

set_option autoImplicit false

namespace ModFormPIR

namespace Supplement

/-!
# The Track 1 constants: `η(α)`, `α*` and `η_ends`

Henzinger, Ragavan, *Doubly-Efficient Private Information Retrieval from Modular Forms*, STOC 2027
submission (manuscript sha256 2442f3db…), Corollary 8.4, p.31 (PDF p.35).

**Formalization Note.**
* `H₂` is the platform's base-2 binary entropy `WildeQIT.binaryEntropy`,
  `H₂(t) = −t log₂ t − (1 − t) log₂(1 − t)`, with `H₂(0) = H₂(1) = 0`; it is the paper's `H₂` on `[0, 1]`.
* `α*` is "the point where the two terms are equal". On `[0, 1/3]` the difference of the two terms of `η(α)`,
  `H₂(α) − H₂(1/3 − α) − 2/3`, is continuous and strictly increasing, negative at `0` and positive at `1/3`,
  so the crossing point is unique and equals the supremum of the points of `[0, 1/3]` where the first term is
  at most the second. That supremum is the definition below; its set contains `0` and is bounded by `1/3`, so
  it is never a junk value.
-/

/-- Corollary 8.4: `η(α) = (1/log₂ 3) · max{H₂(α) + α, H₂(1/3 − α) + 2/3 + α}`. -/
noncomputable def etaAlpha (α : ℝ) : ℝ :=
  (1 / Real.logb 2 3) *
    max (WildeQIT.binaryEntropy α + α) (WildeQIT.binaryEntropy (1 / 3 - α) + 2 / 3 + α)

/-- Corollary 8.4: `α* = 0.2994…`, the point of `[0, 1/3]` where the two terms of `η(α)` are equal. -/
noncomputable def alphaStar : ℝ :=
  sSup {α : ℝ | α ∈ Set.Icc (0 : ℝ) (1 / 3) ∧
    WildeQIT.binaryEntropy α + α ≤ WildeQIT.binaryEntropy (1 / 3 - α) + 2 / 3 + α}

/-- Corollary 8.4: `η_ends = η(α*) = 0.7444…`. -/
noncomputable def etaEnds : ℝ := etaAlpha alphaStar

end Supplement

end ModFormPIR


