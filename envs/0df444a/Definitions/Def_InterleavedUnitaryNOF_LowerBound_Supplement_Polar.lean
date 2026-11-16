-- Prove2me | Definitions.Def_InterleavedUnitaryNOF_LowerBound_Supplement_Polar
-- name    : InterleavedUnitaryNOF_LowerBound_Supplement_Polar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T10:45:01.473797+00:00
-- url     : https://prove2.me/theorems/ac82d0e8-63ec-438a-ba96-c472e9cf068b
-- title:
--   Polar replacement and Euclidean operator norm
-- statement:
--   For a complex square matrix $U$, define its polar replacement by
--
--   $$\widetilde U=U\bigl(\sqrt{U^\dagger U}\bigr)^{-1}.$$
--
--   The square root is the positive spectral square root. The operator norm is induced by the Euclidean vector norm. For the published ten-matrix input, polar replacement is applied separately to each of its ten factors, retaining the published product order. No invertibility or approximation certificate is supplied to this construction. Under the near-unitary promise the Gram matrix is positive definite; outside that domain Lean's total square root and matrix inverse conventions apply.
--
--   This definition supplies the objects in Claim 3.1 and the local quantum gates. It reuses the published complex matrices and input grouping.
-- source:
--   Haoyu Wang, Pei Wu, Guangxu Yang, STOC 2027 submission #1513 (October 2026), §3, p.8 before Claim 3.1; Appendix B, p.22

import Mathlib
import Definitions.Def_InterleavedUnitaryNOF_LowerBound_Input

open scoped MatrixOrder ComplexOrder

namespace InterleavedUnitaryNOF.LowerBound.Supplement

/-- The Euclidean-induced operator norm, not the entrywise matrix norm. -/
noncomputable def opNorm {m : ℕ} (U : Mat m) : ℝ :=
  ‖CStarMatrix.ofMatrix U‖

/-- Section 3, p.8: the positive spectral square root followed by matrix inversion.
On a near-unitary input the Gram matrix is positive definite; no invertibility
certificate is part of this construction. Singular inputs use Mathlib's total inverse. -/
noncomputable def polar {m : ℕ} (U : Mat m) : Mat m :=
  U * (CFC.sqrt (U.conjTranspose * U))⁻¹

/-- Apply the same polar construction separately to all ten factors. -/
noncomputable def polarInput {m : ℕ} (u : MatrixInput m) : MatrixInput m :=
  (fun a => polar (u.1 a), fun a => polar (u.2.1 a), fun a => polar (u.2.2 a))

end InterleavedUnitaryNOF.LowerBound.Supplement


