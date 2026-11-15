-- Prove2me | Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_Supplement_FullyRandomMaxLoad
-- name    : LinearHashingPoissonesque_ExpectedLoads_Supplement_FullyRandomMaxLoad
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T05:04:34.136267+00:00
-- url     : https://prove2.me/theorems/f4a204b7-4498-46d7-bb08-b28028a26c19
-- title:
--   Expected maximum load of a fully random function
-- statement:
--   For positive integers $m,n$, let $f:[m]\to[n]$ be chosen uniformly from all $n^m$ functions. Using the published all-bin load averages, define
--
--   $$R(m,n)=\frac{1}{n^m}\sum_{f:[m]\to[n]}L_1^+([m],f)=\mathbb E_f\!\left[\max_{i\in[n]}|f^{-1}(i)|\right].$$
--
--   Every labelled bin contributes to the maximum, including empty bins, and the averaging imposes no injectivity or balancing condition. This is the fully random comparison quantity in Lemma 5 and Theorem 2.
--
--   **Formalization Note** The labels are `Fin m` and `Fin n`, in bijection with the source's one-based labels. At $m=0$ this definition gives zero; at $n=0<m$ the empty sum and real division by zero also give zero. The source claims use only positive $m,n$.
-- source:
--   Vinayak Kumar, STOC 2027 submission #1155 (October 2026), p.17, Lemma 5 (definition of R); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1155.pdf#page=17

import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_ExtremeLoads

namespace LinearHashingPoissonesque.ExpectedLoads.Supplement

/-- Lemma 5, p.17: uniform average of the maximum load over all n^m functions.
For m,n ≥ 1 the denominator is positive and every bin is included. -/
noncomputable def fullyRandomMaxLoad (m n : ℕ) : ℝ :=
  (∑ f : Fin m → Fin n,
    heaviestAverage (Finset.univ : Finset (Fin m)) f 1) / (n : ℝ) ^ m

end LinearHashingPoissonesque.ExpectedLoads.Supplement


