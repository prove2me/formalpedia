-- Prove2me | Definitions.Def_DerandSq_NCPoly_eval
-- name    : DerandSq_NCPoly_eval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:01:45.472787+00:00
-- url     : https://prove2.me/theorems/eb8c25e6-d498-44d2-befe-d5b0756cdbd7
-- title:
--   Evaluation $P(u) = \sum_w A_w \otimes w(u)$
-- statement:
--   For $P = \sum_w A_w \otimes w \in M_D(\mathbb C) \otimes \mathbb C^*\langle x_i : i\in\iota\rangle$ and a tuple $u = (u_i)$ of bounded operators on a Hilbert space $E$,
--   $$
--   P(u) = \sum_w A_w \otimes w(u),
--   $$
--   a bounded operator on $\mathbb C^D \otimes E$. With $u$ the permutation matrices this is $P(U^N)$ on $\mathbb C^D \otimes \mathbb C^N$; with $u$ the left-regular generators it is $P(u)$ in $M_D(\mathbb C) \otimes C^*_{\mathrm{red}}(\Gamma)$, whose norm is the operator norm on $\mathbb C^D \otimes \ell^2(\Gamma)$.
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), §2.4–2.5, pp.12–13

import Mathlib
import Definitions.Def_DerandSq_NCPoly
import Definitions.Def_AccessibleMaps_tensorOp
import Definitions.Def_DerandSq_wordOp

namespace DerandSq

/-- `P(u) = ∑_w A_w ⊗ w(u)`: a ∗-polynomial with matrix coefficients evaluated at a tuple `u` of
bounded operators on a Hilbert space `E`, an operator on `D` copies of `E` (Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), §2.4–2.5,
pp.12–13).

**Formalization Note** The matrix coefficient `A_w ⊗ w(u)` is the published
`AccessibleMaps.tensorOp` (block `(a, b)` equal to `A_w a b • w(u)`) on
`AccessibleMaps.Composite (Fin D) E = PiLp 2 (fun _ : Fin D => E)`. -/
noncomputable def NCPoly.eval {D : ℕ} {ι : Type*} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (P : NCPoly D ι) (u : ι → E →L[ℂ] E) :
    PiLp 2 (fun _ : Fin D => E) →L[ℂ] PiLp 2 (fun _ : Fin D => E) :=
  ∑ w ∈ P.support, AccessibleMaps.tensorOp (P w) (wordOp u w)

end DerandSq


