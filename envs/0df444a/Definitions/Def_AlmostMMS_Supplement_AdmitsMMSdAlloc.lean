-- Prove2me | Definitions.Def_AlmostMMS_Supplement_AdmitsMMSdAlloc
-- name    : AlmostMMS_Supplement_AdmitsMMSdAlloc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:27:48.008924+00:00
-- url     : https://prove2.me/theorems/a21a8947-e1d3-4f17-bac7-c3fed84f4d9e
-- title:
--   MMS($d$) allocation (1-out-of-$d$ maximin share)
-- statement:
--   Let $N=[n]$ be a set of agents and $M$ a set of $m$ indivisible items, and let every agent $i$ have a valuation $v_i$ on bundles of items. For $d\ge1$, the **$d$-maximin share** $\mathrm{MMS}(M,v_i,d)$ is the largest value agent $i$ can guarantee by splitting $M$ into $d$ bundles and receiving the worst one:
--   $$
--   \mathrm{MMS}(M,v_i,d)=\max_{(B_1,\dots,B_d)}\ \min_{j\in[d]} v_i(B_j),
--   $$
--   the maximum taken over all partitions of $M$ into $d$ (possibly empty) bundles.
--
--   A partition $(A_1,\dots,A_n)$ of $M$ among the $n$ agents is an **MMS($d$) allocation** (a 1-out-of-$d$ MMS allocation) if
--   $$
--   v_i(A_i)\ \ge\ \mathrm{MMS}(M,v_i,d)\qquad\text{for every agent } i\in N.
--   $$
--   Every item goes to exactly one agent. For $d=n$ this is an ordinary MMS allocation; for $d>n$ every agent is benchmarked against a smaller share, so MMS($d$) allocations become easier to find as $d$ grows, and the question is how large $d$ must be for them to exist always.
--
--   **Formalization Note** An allocation is a map sending each item to an agent; agent $i$ receives the items mapped to $i$. The share is the published `LittleCharity.MMS.mms (v i) d univ`, a maximum over labelled $d$-partitions with possibly empty bundles.
-- source:
--   Feige, Grinberg, Almost-MMS allocations with small agent redundancy, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…), §1.1, p.2 (1-out-of-d MMS allocation)

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting

namespace AlmostMMS.Supplement

open Finset

/-- **MMS(d) allocation** (1-out-of-`d` MMS, p.2). Feige, Grinberg, *Almost-MMS allocations with small
agent redundancy*, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…): a partition
`(A_1, …, A_n)` of all items `M` among the `n` agents such that `v_i(A_i) ≥ MMS(M, v_i, d)` for every
agent `i ∈ N`.

**Formalization Note.** An allocation is a total map `A : Fin m → Fin n` sending every item to exactly
one agent; agent `i` receives `univ.filter (A · = i)`. The benchmark is the published
`LittleCharity.MMS.mms (v i) d univ`, the maximum over labelled (possibly empty) `d`-partitions of the
minimum bundle value, with `d` parts rather than `n`. -/
def AdmitsMMSdAlloc {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (d : ℕ) : Prop :=
  ∃ A : Fin m → Fin n, ∀ i, LittleCharity.MMS.mms (v i) d univ ≤ v i (univ.filter fun e => A e = i)

end AlmostMMS.Supplement


