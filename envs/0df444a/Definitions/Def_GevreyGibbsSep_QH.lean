-- Prove2me | Definitions.Def_GevreyGibbsSep_QH
-- name    : GevreyGibbsSep_QH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:41:19.835705+00:00
-- url     : https://prove2.me/theorems/dbf93f97-50eb-4520-8827-c565005694d2
-- title:
--   Quantum state space $\ell^2(\mathbb R^d\times\mathbb R^d\times W)$
-- statement:
--   The state space of a first-order quantum algorithm is the Hilbert space $\ell^2(\mathbb R^d\times\mathbb R^d\times W)$ with orthonormal basis $|x\rangle|b\rangle|w\rangle$.
--
--   **Formalization Note** The paper does not define its registers. Taking the exact real labels as basis makes the oracle (7) a permutation of basis states; finite-precision registers can be simulated in it.
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Eq. (7), p.6

import Mathlib
import Definitions.Def_GevreyGibbsSep_oracle
import Definitions.Def_GevreyGibbsSep_QReg

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- The quantum state space `ℓ²(ℝ^d × ℝ^d × W)` on the basis `|x⟩|b⟩|w⟩` (reading of Eq. (7),
p.6, arXiv:2608.24527 (sha256 d4fd40eb…)).

**Formalization Note** The paper does not define its register spaces; the exact-real basis
reading makes the oracle (7) a permutation of basis states. -/
noncomputable abbrev QH (d : ℕ) (W : Type) := lp (fun _ : QReg d W => ℂ) 2

end GevreyGibbsSep


