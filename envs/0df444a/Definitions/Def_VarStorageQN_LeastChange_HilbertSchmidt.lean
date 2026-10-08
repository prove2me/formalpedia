-- Prove2me | Definitions.Def_VarStorageQN_LeastChange_HilbertSchmidt
-- name    : VarStorageQN_LeastChange_HilbertSchmidt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:45:47.730617+00:00
-- url     : https://prove2.me/theorems/c79b59de-9e44-4bad-a730-d7995d910965
-- title:
--   Hilbert–Schmidt membership and norm from an orthonormal basis
-- statement:
--   Let $\mathcal H$ be a complete real inner-product space with an orthonormal basis $(e_i)_{i\in I}$, where $I$ may be uncountable. A bounded operator $A$ belongs to the Hilbert–Schmidt class when the family $(\|Ae_i\|^2)_{i\in I}$ is summable. On that class its norm is
--
--   $$\|A\|_{\mathrm{HS}}=\left(\sum_{i\in I}\|Ae_i\|^2\right)^{1/2}. $$
--
--   This is the operator class and size measure used in both Annex minimization problems. Basis independence is a separate milestone.
--
--   **Formalization Note** `HSSummable b A` records the domain of the norm explicitly. The real `tsum` used in `hsNorm b A` has a default value for nonsummable families, so `hsNorm` is used as a norm only with summability. The index type of `b` is arbitrary; no finite-dimensional or separability assumption is made.
-- source:
--   Gilbert & Lemaréchal, Some numerical experiments with variable-storage quasi-Newton algorithms, IIASA Working Paper WP-88-121 (August 1988), p. 26, Annex, (A.1) and paragraph after (A.1)

import Mathlib

namespace VarStorageQN.LeastChange

open InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Membership in the Hilbert–Schmidt class, tested on an arbitrary Hilbert basis. -/
def HSSummable {ι : Type*} (b : HilbertBasis ι ℝ H) (B : H →L[ℝ] H) : Prop :=
  Summable fun i => ‖B (b i)‖ ^ 2

/-- The sum (A.1); used as a norm only when `HSSummable b B`. -/
noncomputable def hsNorm {ι : Type*} (b : HilbertBasis ι ℝ H) (B : H →L[ℝ] H) : ℝ :=
  Real.sqrt (∑' i, ‖B (b i)‖ ^ 2)

end VarStorageQN.LeastChange


