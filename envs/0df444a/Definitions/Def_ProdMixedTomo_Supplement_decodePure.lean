-- Prove2me | Definitions.Def_ProdMixedTomo_Supplement_decodePure
-- name    : ProdMixedTomo_Supplement_decodePure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:30:57.583425+00:00
-- url     : https://prove2.me/theorems/0810cab9-ac39-4400-a586-1fd563a3946a
-- title:
--   Decoding the learner's output as a pure product state
-- statement:
--   When the measuring machine of the base mission halts in state $s$, its output memory holds, for each qubit $j<n$, a direction $b_j=(M[4j],M[4j+1],M[4j+2])\in\mathbb R^3$. The decoded **pure product output** is
--   $$
--   |\hat\pi\rangle\langle\hat\pi|=\bigotimes_{j=1}^n P(b_j),\qquad P(b)=\tfrac12\Bigl(I+\tfrac{b}{\|b\|}\cdot\sigma\Bigr),\quad P(0)=|0\rangle\langle 0|.
--   $$
--   Each $P(b_j)$ is a rank-one projector, so the output is always an element of $\Pi_n$; $P(0)$ is the "any unit vector" chosen in the paper's rounding step when the estimated Bloch vector vanishes.
--
--   This is the meaning of "outputs a description of a pure product state $|\hat\pi\rangle$" in Theorem 3.6.
--
--   **Formalization Note** The layout is that of the base decoder `decodeState`, with the weight cell $M[4j+3]$ ignored.
-- source:
--   Arulandu, Diakonikolas, Kane, Li, Agnostic Product Mixed State Tomography via Robust Statistics, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Theorem 3.6 and its proof, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_ProdMixedTomo_States
import Definitions.Def_ProdMixedTomo_Machine

namespace ProdMixedTomo.Supplement

/-- The learner's output decoded as a pure product state `|π̂⟩⟨π̂| = ⨂ⱼ P(bⱼ)`, with the direction
`bⱼ = (M[4j], M[4j+1], M[4j+2])` read from the halted machine state.

Arulandu, Diakonikolas, Kane, Li, *Agnostic Product Mixed State Tomography via Robust Statistics*,
arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Theorem 3.6, p.19 (PDF p.21): "outputs … a description of a pure product state |π̂⟩"; proof:
"ĉ_j = c̃_j/‖c̃_j‖₂ is the rounded Bloch vector (choose any unit vector if c̃_j = 0)".

**Formalization Note.** Same output layout as the base `decodeState` (`ProdMixedTomo.Machine`),
with the weight cell `M[4j+3]` ignored. `P(b) = ½(I + (b/‖b‖)·σ)` is the base `proj`, a rank-one
projector for every `b` (`P(0) := |0⟩⟨0|`, the "any unit vector" of the proof), so the decoded
output always lies in `Π_n`. -/
noncomputable def decodePure (n : ℕ) (s : MState) : QMat n :=
  prodMat fun j => proj (fun k : Fin 3 => s.core.mem (4 * (j : ℤ) + (k : ℤ)))

end ProdMixedTomo.Supplement


