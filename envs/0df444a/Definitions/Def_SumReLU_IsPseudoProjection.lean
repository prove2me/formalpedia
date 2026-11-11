-- Prove2me | Definitions.Def_SumReLU_IsPseudoProjection
-- name    : SumReLU_IsPseudoProjection
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:26:43.274595+00:00
-- url     : https://prove2.me/theorems/e3586124-408e-4b72-a4e5-94005d66e064
-- title:
--   Pseudo-projections $\Phi\Phi^\top=I$ and their complex extension
-- statement:
--   A real linear map $\Phi:(\mathbb R^d)^{\otimes p}\to\mathbb R^k$, written as a $k\times d^p$ matrix, is a pseudo-projection if
--   $$
--   \Phi\Phi^\top=I_k .
--   $$
--   Its complex extension acts on complex tensors by $\Phi(W+iT)=\Phi(W)+i\Phi(T)$, i.e. by the same matrix with entries viewed as complex numbers.
-- source:
--   Diakonikolas, Diakonikolas, Wang, Zarifis, Learning Positive Linear Combinations of ReLUs in Fully Polynomial Time, arXiv:2610.32940 (PDF sha256 66803576…6c48), Definition 4.18 and Remark 4.20, p.37 (PDF p.39)

import Mathlib
import Definitions.Def_SumReLU_CTensor

open Matrix

namespace SumReLU

/-- A real linear map `Φ : (ℝᵈ)^{⊗p} → ℝᵏ` (a `k × dᵖ` matrix) is a **pseudo-projection** if
`ΦΦᵀ = I_k`.

Diakonikolas, Diakonikolas, Wang, Zarifis, *Learning Positive Linear Combinations of ReLUs in
Fully Polynomial Time*, arXiv:2610.32940 (PDF sha256 66803576…6c48), Definition 4.18, p.37 (PDF p.39). -/
def IsPseudoProjection {k d p : ℕ} (Φ : Matrix (Fin k) (Fin p → Fin d) ℝ) : Prop :=
  Φ * Φᵀ = 1

/-- The complex-linear extension `Φ(W + iT) = Φ(W) + iΦ(T)` of a real `Φ` applied to a complex
tensor (Remark 4.20, p.37, PDF p.39): the matrix with entries cast to `ℂ` times the tensor. -/
noncomputable def pseudoApply {k d p : ℕ} (Φ : Matrix (Fin k) (Fin p → Fin d) ℝ)
    (F : CTensor d p) : Fin k → ℂ :=
  (Φ.map fun r : ℝ => (r : ℂ)) *ᵥ F

end SumReLU


