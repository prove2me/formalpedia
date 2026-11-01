-- Prove2me | Definitions.Def_WildeQIT_Packing_seqDecodeSuccess
-- name    : WildeQIT_Packing_seqDecodeSuccess
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:56:07.394591+00:00
-- url     : https://prove2.me/theorems/b69624b0-034f-44ff-a57f-57afb0a9815e
-- title:
--   Sequential decoder success: $\mathrm{Tr}\{\Pi_{c_m}\hat\Pi_{c_{m-1}}\cdots\hat\Pi_{c_1}\Pi\sigma\Pi\hat\Pi_{c_1}\cdots\hat\Pi_{c_{m-1}}\Pi_{c_m}\}$
-- statement:
--   Let $\Pi$ be a code subspace projector, $\{\Pi_x\}_{x\in\mathcal X}$ codeword subspace projectors, and $c_1,\dots,c_{|\mathcal M|}$ a code. Write $\hat\Pi_x\equiv I-\Pi_x$. The **sequential decoder** first performs the measurement $\{\Pi,I-\Pi\}$ and then, in order, the measurements $\{\Pi_{c_i},I-\Pi_{c_i}\}$, $i=1,2,\dots$. On a state $\sigma$, the probability that it answers "yes" to the code subspace test, "no" to the tests of messages $1,\dots,m-1$, and "yes" to the test of message $m$ is
--
--   $$\operatorname{Tr}\bigl\{\Pi_{c_m}\hat\Pi_{c_{m-1}}\cdots\hat\Pi_{c_1}\,\Pi\,\sigma\,\Pi\,\hat\Pi_{c_1}\cdots\hat\Pi_{c_{m-1}}\Pi_{c_m}\bigr\}.$$
--
--   With $\sigma=\sigma_{c_m}$ this is the probability of decoding message $m$ correctly (16.82).
--
--   **Formalization Note** Messages are indexed from $0$, so the tests preceding message $m$ are those of the messages $i<m$; for the first message the products of the $\hat\Pi$'s are the identity. The value is the real part of the complex trace.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §16.6, eq. (16.82), p. 499

import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Basic
import Mathlib.Data.List.FinRange

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §16.6 (Sequential
Decoding), eq. (16.82), p. 499.
-/

open Matrix
open scoped ComplexOrder

namespace WildeQIT.Packing

/-- **Success probability of the sequential decoder** (Wilde, arXiv:1106.1445v8, eq. (16.82),
p. 499). For a code `c_1, …, c_{|ℳ|}`, a code subspace projector `Π`, codeword subspace projectors
`{Π_x}` and a state `σ`, the probability that the sequential decoder, applied to `σ`, answers
"yes" to the code subspace test `{Π, I − Π}`, "no" to the tests `{Π_{c_i}, I − Π_{c_i}}` for
`i = 1, …, m − 1`, and "yes" to the `m`-th test is
`Tr{Π_{c_m} Π̂_{c_{m−1}} ⋯ Π̂_{c_1} Π σ Π Π̂_{c_1} ⋯ Π̂_{c_{m−1}} Π_{c_m}}`, with `Π̂_x ≡ I − Π_x`.

**Formalization Note.** Messages are `Fin M` (index base `0`: the book's message `m` is
`m - 1` here, and the tests before message `m` are those of the messages `i < m`). The product
`Π̂_{c_1} ⋯ Π̂_{c_{m−1}}` is the list product of `I − Π_{c_i}` over `i < m` in increasing order,
and `Π̂_{c_{m−1}} ⋯ Π̂_{c_1}` is the product of the reversed list; for the first message both are
`I`. The value is the real part of the complex trace; `P` stands for the book's `Π` and `Px x` for `Π_x` (`Π` is reserved Lean syntax) (the trace is real when `σ` is Hermitian and
the projectors are Hermitian). The decoder applies to the received state `σ`; in §16.6 it is
`σ_{c_m}`. -/
noncomputable def seqDecodeSuccess {X n : Type} [Fintype n] [DecidableEq n] {M : ℕ}
    (P : Matrix n n ℂ) (Px : X → Matrix n n ℂ) (c : Fin M → X) (m : Fin M)
    (σ : Matrix n n ℂ) : ℝ :=
  let L : List (Matrix n n ℂ) :=
    ((List.finRange M).filter (fun i => decide (i < m))).map (fun i => 1 - Px (c i))
  (Px (c m) * L.reverse.prod * P * σ * P * L.prod * Px (c m)).trace.re

end WildeQIT.Packing


