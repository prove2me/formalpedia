-- Prove2me | Definitions.Def_SeqHolevo_IsOrthProjector
-- name    : SeqHolevo_IsOrthProjector
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:58:28.205845+00:00
-- url     : https://prove2.me/theorems/09947772-de2d-4ae1-b9d9-fedef16c73ba
-- title:
--   Orthogonal projector on $\ell^2(J)$
-- statement:
--   An operator $\Pi$ on $\ell^2(J)$ (given by its coefficient array) is an **orthogonal projector** when
--
--   $$0\le\Pi\le I\qquad\text{and}\qquad\Pi^2=\Pi .$$
--
--   Sen's non-commutative union bound is stated for sequences of such projectors, and the error analysis uses the typical projector $\Pi$ and its complement $\hat\Pi=I-\Pi$.
--
--   **Formalization Note** $0\le\cdot\le I$ is the published Loewner order on coefficient arrays (all finite quadratic forms); it makes $\Pi$ bounded and self-adjoint, so $\Pi^2=\Pi$ (coefficientwise) says exactly that $\Pi$ is an orthogonal projection.
-- source:
--   Wilde–Guha–Tan–Lloyd, Explicit capacity-achieving receivers for optical communication and quantum reading, arXiv:1202.0518v2, Appendix B, pp.6–7 (Π, Π̂ = I − Π, the projectors of Sen's bound)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01
import Definitions.Def_SeqHolevo_idArr
import Definitions.Def_SeqHolevo_arrMul

open QAlgorithms.Papers.Independent.Frontier18.P01 (IsPositive TraceOperatorLE)

namespace SeqHolevo

/-- Wilde–Guha–Tan–Lloyd, *Explicit capacity-achieving receivers for optical communication and quantum reading*, arXiv:1202.0518v2, Appendix B, pp.6–7 (PDF pages): an (orthogonal) projector `Π` on ℓ²(J): `0 ≤ Π ≤ I`
and `Π² = Π`. Sen's non-commutative union bound (p.7) is stated for a "sequence of projectors",
and the smoothing step (p.6) uses the typical projector `Π` and `Π̂ = I − Π`.

**Formalization Note.** `IsPositive` and `TraceOperatorLE` are the published Loewner order on
coefficient arrays (`QAlgorithms.Papers.Independent.Frontier18.P01`, all finite quadratic forms).
`0 ≤ Π ≤ I` makes `Π` a bounded self-adjoint operator, so `Π² = Π` (coefficientwise, via
`arrMul`) says exactly that `Π` is an orthogonal projector. -/
def IsOrthProjector {J : Type} (P : Matrix J J ℂ) : Prop :=
  IsPositive P ∧ TraceOperatorLE P (idArr J) ∧ arrMul P P = P

end SeqHolevo


