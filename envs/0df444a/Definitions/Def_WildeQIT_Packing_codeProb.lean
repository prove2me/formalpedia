-- Prove2me | Definitions.Def_WildeQIT_Packing_codeProb
-- name    : WildeQIT_Packing_codeProb
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:56:09.120558+00:00
-- url     : https://prove2.me/theorems/0f38231b-68e8-4095-898b-3ea74f8102ee
-- title:
--   Probability of a random code: $p(\mathcal C)=\prod_m p_X(c_m)$
-- statement:
--   A **code** $\mathcal C=\{c_m\}_{m\in\mathcal M}$ assigns to each message $m$ of a finite message set $\mathcal M$ a codeword $c_m$ in the finite alphabet $\mathcal X$. When the codewords are drawn independently, each according to the distribution $p_X$, the code $\mathcal C$ is chosen with probability
--
--   $$p(\mathcal C)=\prod_{m\in\mathcal M}p_X(c_m).$$
--
--   The expectation $\mathbb E_{\mathcal C}\{f(\mathcal C)\}$ over this random code is $\sum_{\mathcal C}p(\mathcal C)f(\mathcal C)$, the sum running over all functions $\mathcal M\to\mathcal X$.
--
--   **Formalization Note** A code is a function from the message type to the alphabet; codewords need not be distinct.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §16.4.1, eq. (16.17), p. 490

import Mathlib.Analysis.Complex.Basic
import Definitions.Def_WildeQIT_FinDist

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §16.4.1 (Code
Construction), eq. (16.17), p. 490.
-/

namespace WildeQIT.Packing

/-- **Probability of a random code** (Wilde, arXiv:1106.1445v8, eq. (16.17), p. 490). A code
`C = {c_m}_{m ∈ ℳ}` assigns a codeword `c_m ∈ 𝒳` to each message `m`. When the codewords are drawn
independently according to `p_X`, the code `C` has probability
`p(C) = ∏_{m ∈ ℳ} p_X(c_m)`.

**Formalization Note.** A code is a function `c : ι → X` from the finite message set `ι` to the
alphabet `X`; codewords need not be distinct. The expectation `E_C{f(C)}` over the random code is
the finite sum `∑_c codeProb p c * f c`. -/
noncomputable def codeProb {ι X : Type} [Fintype ι] [Fintype X] (p : FinDist X)
    (c : ι → X) : ℝ :=
  ∏ m, p.prob (c m)

end WildeQIT.Packing


