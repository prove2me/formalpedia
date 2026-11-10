-- Prove2me | Definitions.Def_SubspaceConv_psiTr
-- name    : SubspaceConv_psiTr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:16:05.305272+00:00
-- url     : https://prove2.me/theorems/a8041e42-4413-4c99-bc2c-730c51532634
-- title:
--   The additive character $\psi(x)=\zeta^{\operatorname{Tr}(x)}$ of §3.4
-- statement:
--   For a finite field $\mathbb F_q$ of characteristic $p$ and a commutative ring $R$,
--   $$\psi(x)=\zeta^{\operatorname{Tr}_{\mathbb F_q/\mathbb F_p}(x)}\in R[t]/(1+t+\dots+t^{p-1}),$$
--   where $\operatorname{Tr}(x)=x+x^p+\dots+x^{p^{m-1}}\in\mathbb F_p$ and the exponent is its integer representative in $\{0,\dots,p-1\}$. It replaces the complex character $e^{2\pi i\operatorname{Tr}(t)/p}$ of §2.1 when the coefficient ring has no $p$-th roots of unity.
--
--   **Formalization Note** The trace is `Algebra.trace (ZMod p) F` for the canonical `ZMod p`-algebra structure on $\mathbb F$, and the representative is `ZMod.val`.
-- source:
--   Perles, Weinstein, A Fast Algorithm for Subspace Convolution, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §3.4, p.13; §2.1, p.11 (trace, integer representative)

import Mathlib
import Definitions.Def_SubspaceConv_ExtRing

namespace SubspaceConv

/-- The additive character of §3.4, `ψ(x) = ζ^{Tr_{F_q/F_p}(x)}`, with values in
`ExtRing A p`, `p = char F_q` (Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §3.4, p.13; and §2.1, p.11, for the trace).

**Formalization Note** The trace is `Algebra.trace (ZMod p) F` for the canonical
`ZMod p`-algebra structure on `F` (`ZMod.algebra`, `p = ringChar F`), and the exponent is its
representative in `{0, …, p − 1}` (`ZMod.val`), as in §2.1 ("the exponential uses an integer
representative"). -/
noncomputable def psiTr (F : Type*) [Field F] [Fintype F] (A : Type*) [CommRing A] :
    F → ExtRing A (ringChar F) :=
  fun x =>
    letI := ZMod.algebra F (ringChar F)
    AdjoinRoot.root _ ^ (Algebra.trace (ZMod (ringChar F)) F x).val

end SubspaceConv


