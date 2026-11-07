-- Prove2me | Definitions.Def_QuasiPolyTrace_stat
-- name    : QuasiPolyTrace_stat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:31:02.712799+00:00
-- url     : https://prove2.me/theorems/8efbc003-be01-4370-b62a-b78eafa3e6a3
-- title:
--   The statistic $x^{(s)}_p$ of the deletion channel
-- statement:
--   Let $u=(u_1,\dots,u_n)\in\{0,1\}^n$ and $p\in[0,1]$. The **deletion channel** $\mathrm{Del}_p(u)$ keeps each bit independently with probability $p$ (the **retention probability**) and outputs the kept bits in order, a **trace** $U$ of length between $0$ and $n$. For a finite set $s$ of integer positions, the **statistic**
--
--   $$
--   u^{(s)}_p=\mathbb E_{U\sim \mathrm{Del}_p(u)}\Big[\prod_{i\in s}U_i\Big]
--   $$
--
--   is the probability that every position of $s$ is present in the trace and carries a $1$. By the paper's convention a position beyond the end of the trace, or smaller than $1$, reads $0$. The **order** of the statistic is $|s|$.
--
--   Order-one statistics are the means of individual trace bits used by mean-based algorithms; the paper builds higher-order statistics that separate two strings.
--
--   **Formalization Note** The trace law is that of the reused published block `OAI.TraceReconstruction`: a retention mask has weight `maskWeight (1 - p)` (that block's parameter is the *deletion* probability $1-p$). The paper's statistics are tuples of distinct positions; bits are $0/1$, so a set loses nothing. Positions are integers so that shifted statistics $s+\ell$ may leave $\{1,2,\dots\}$, where they read $0$ (p.7). A substring $x_{[i:n]}$ is passed as the list itself (see `window`).
-- source:
--   Burudgunte, Valiant, Wang, Quasipolynomial Trace Reconstruction, manuscript of November 2, 2026 (later version of arXiv:2607.04073; sha256 9ecb6d18…), Definition 1, p.6 (deletion channel); Definition 3, p.6 (statistic x^{(s)}_p); convention on invalid indices, p.7

import Mathlib
import Definitions.Def_TraceReconstruction

namespace QuasiPolyTrace

open OAI.TraceReconstruction

/-- **The statistic `x^{(s)}_p`.** Burudgunte, Valiant, Wang, *Quasipolynomial Trace Reconstruction*, manuscript of November 2, 2026
(later version of arXiv:2607.04073; sha256 9ecb6d18…), Definition 3, p.6: "the expected value of product of
locations `s_1, …, s_k` in a trace from x, where by convention, any accesses outside the range of the
trace are interpreted as being 0: `x^{(s)}_p := E_{U∼Del_p(x)}[U_{s_1} U_{s_2} ⋯ U_{s_k}]`".

`stat p u s` is the expectation, over a trace `U` of the binary string `u` through the deletion channel
with retention probability `p` (Definition 1: each bit kept independently with probability `p`), of the
product of the bits of `U` at the 1-based positions in `s`. A position `≤ 0` or beyond the end of the
trace reads `0`.

**Formalization Note.**
* The trace law is the one of the reused block `OAI.TraceReconstruction`: a retention mask `a` has
  weight `maskWeight (1 - p) a` (that block's argument is the *deletion* probability `q = 1 − p`), and the
  trace is `traceOfMask`.
* A statistic is a finite set of integer positions. The paper's tuples have distinct entries in every use
  (Lemma 36: "k-tuple of distinct positive integers"), and bits are 0/1, so a set loses nothing; the order
  of the statistic is its cardinality.
* Positions are integers so that shifted statistics `s + ℓ` (Definition 3) can leave `{1, 2, …}`; the
  paper's convention (p.7) is that a statistic with an index smaller than 1 "implicitly returns value 0",
  and this definition returns 0 in that case.
* A substring `x[i:j]` is passed as the list `u` itself (see `window`). -/
noncomputable def stat (p : ℝ) (u : List Bool) (s : Finset ℤ) : ℝ :=
  ∑ a : Mask u.length, maskWeight (1 - p) a *
    ∏ i ∈ s, (if 1 ≤ i ∧ (traceOfMask (fun k => u.get k) a).getD (i.toNat - 1) false = true
      then (1 : ℝ) else 0)

end QuasiPolyTrace


