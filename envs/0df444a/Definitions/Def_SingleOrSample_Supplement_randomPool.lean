-- Prove2me | Definitions.Def_SingleOrSample_Supplement_randomPool
-- name    : SingleOrSample_Supplement_randomPool
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:33:24.799854+00:00
-- url     : https://prove2.me/theorems/f9507c14-f78e-447b-b1ed-6b7efb08bfb9
-- title:
--   The random-pool instance distribution $\mathcal D_{n,\alpha}$
-- statement:
--   Fix $\alpha\in(0,1]$ and an integer $K\ge1$. Let $d=\lceil1/\alpha\rceil$, $T=K^{2^d-1}$, $n=(d+1)T$ agents and $m=n^{d+3}$ goods. There are $d+1$ rounds $r=0,\dots,d$; round $r$ has $q_r=K^{2^r-1}$ **pools** ($q_0=1$, $q_{r+1}=Kq_r^2$), each of $nM_r$ goods with $M_r=n^{d-r+2}$, and $s_r=T/q_r=K^{2^d-2^r}$ agents per pool. The round-$0$ pool is the set of all goods.
--
--   1. Each round-$r$ pool $P$ is partitioned uniformly at random into $n$ labelled **bins** $B_{P,1},\dots,B_{P,n}$ of size $M_r$, independently over pools. All $s_r$ agents of $P$ have the valuation $v_P(S)=\max_{j}|S\cap B_{P,j}|$.
--   2. For $r<d$, a **global lottery** draws a uniformly random set $Q_r$ of $q_{r+1}$ bins among all $nq_r$ round-$r$ bins; these bins are the round-$(r+1)$ pools.
--
--   All randomness is drawn before the first arrival. Agents arrive by round; within a round, pool by pool, each pool's agents consecutively. The pools of round $r+1$ are ordered by the position of their bins, i.e. by (parent pool, label). $\mathcal D_{n,\alpha}$ is the induced law of the valuation profile.
--
--   **Formalization Note** The parameters $n,m,d,K$ are separate; the statements fix $d=\lceil1/\alpha\rceil$, $n=(d+1)K^{2^d-1}$, $m=n^{d+3}$, under which every partition and every lottery is possible ($q_{r+1}\le T\le nq_r$). The exponent of $K$ is $2^d-1$ (the text layer of the manuscript prints it as "K2d−1"; the rendered page shows $K^{2^d-1}$). The paper's "support order" for the arrival of pools is read as the (parent pool, label) order.
-- source:
--   Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), App. C.2, pp.35–36 (rounds and pool counts; items, partitions and valuations; the random instance; arrival order)

import Mathlib
import Definitions.Def_SingleOrSample_swr

open scoped Classical

namespace SingleOrSample.Supplement

/-- The labelled partitions of a pool `P` into `n` bins `B_1, …, B_n` of size `M` each: pairwise
disjoint subsets of `P` of size `M` whose union is `P`. -/
noncomputable def labelledPartitions {m : ℕ} (n M : ℕ) (P : Finset (Fin m)) :
    Finset (Fin n → Finset (Fin m)) :=
  Finset.univ.filter fun f =>
    (∀ j, f j ⊆ P ∧ (f j).card = M) ∧ Pairwise (fun j j' => Disjoint (f j) (f j')) ∧
      Finset.univ.biUnion f = P

/-- The uniform law on labelled partitions of `P` into `n` bins of size `M` (Chawla, Huang, Kulkarni,
Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027
submission, arXiv:2609.32286, manuscript sha256 28cd3d7b…, App. C.2, p.36: "partitioned uniformly at
random into `n` labeled bins"), and the point mass at the empty bins if there is none (`|P| ≠ nM`, which
the construction never meets). -/
noncomputable def uniformPartition {m : ℕ} (n M : ℕ) (P : Finset (Fin m)) :
    PMF (Fin n → Finset (Fin m)) :=
  if h : (labelledPartitions n M P).Nonempty then PMF.uniformOfFinset _ h
  else PMF.pure fun _ => ∅

/-- Independent draws from a list of laws, as a law on lists. -/
noncomputable def seqPMF {α : Type} : List (PMF α) → PMF (List α)
  | [] => PMF.pure []
  | p :: ps => p.bind fun a => (seqPMF ps).map fun as => a :: as

/-- The bins of a list selected by a set `Q` of positions, in the order of their positions. -/
def selectBins {m : ℕ} (bins : List (Finset (Fin m))) (Q : Finset ℕ) : List (Finset (Fin m)) :=
  ((List.range bins.length).filter (· ∈ Q)).map fun k => bins.getD k ∅

/-- The rounds of the random-pool construction (App. C.2, pp.35–36), from round `r` on, with `left`
rounds still to draw, given the ordered list of round-`r` pools: each pool is partitioned uniformly and
independently into `n` labelled bins of size `M_r = n^(d − r + 2)`; unless `r` is the last round, a
**global lottery** draws a uniformly random set `Q_r` of `q_{r+1} = K^(2^(r+1) − 1)` positions among
all `n·q_r` round-`r` bins (listed pool by pool, each pool's bins in label order), and the selected bins,
in that order, are the round-`(r+1)` pools. The result lists, round by round, the partitions of the
pools (each partition a function from labels to bins).

**Formalization Note.** All randomness of the instance is drawn here, before the first arrival. The
order of the round-`(r+1)` pools is that of their bins' positions, i.e. (parent pool, label)
lexicographically: this is the "support order" of the page's arrival rule. -/
noncomputable def poolRounds {m : ℕ} (n d K : ℕ) :
    ℕ → ℕ → List (Finset (Fin m)) → PMF (List (List (Fin n → Finset (Fin m))))
  | 0, _, _ => PMF.pure []
  | left + 1, r, pools =>
    (seqPMF (pools.map (uniformPartition n (n ^ (d - r + 2))))).bind fun parts =>
      if left = 0 then PMF.pure [parts]
      else
        (uniformOfSize (Finset.range (parts.flatMap fun f => List.ofFn f).length)
            (K ^ (2 ^ (r + 1) - 1))).bind fun Q =>
          (poolRounds n d K left (r + 1)
              (selectBins (parts.flatMap fun f => List.ofFn f) Q)).map fun rest => parts :: rest

/-- The valuation profile of the random-pool instance (App. C.2, pp.35–36), from the drawn rounds
`R`: with `T = K^(2^d − 1)` agents per round and `s_r = K^(2^d − 2^r)` agents per round-`r` pool,
the agent with Lean index `i` (the page's `i + 1`) is in round `r = ⌊i/T⌋`, at pool
`p = ⌊(i mod T)/s_r⌋` of that round, and has the valuation `v_P(S) = max_j |S ∩ B_{P,j}|` of that pool's
bins. Agents thus arrive by round, pools in list order, each pool's `s_r` agents consecutively. -/
noncomputable def poolProfile {m n : ℕ} (d K : ℕ) (R : List (List (Fin n → Finset (Fin m)))) :
    Fin n → Finset (Fin m) → ℝ :=
  fun i S =>
    ((Finset.univ.sup fun j =>
        (S ∩ ((R.getD ((i : ℕ) / K ^ (2 ^ d - 1)) []).getD
          (((i : ℕ) % K ^ (2 ^ d - 1)) / K ^ (2 ^ d - 2 ^ ((i : ℕ) / K ^ (2 ^ d - 1))))
          (fun _ => ∅)) j).card : ℕ) : ℝ)

/-- The **random-pool instance distribution** `D_{n,α}` (App. C.2, pp.35–36) with `d = ⌈1/α⌉` rounds
after round `0`, `K` the pool growth factor, `n = (d+1)·K^(2^d − 1)` agents and `m = n^(d+3)` goods:
`d + 1` rounds starting from the single round-0 pool of all goods (`q_0 = 1`, `q_{r+1} = K q_r²`, so
`q_r = K^(2^r − 1)`), mapped to the profile of valuations.

**Formalization Note.** `n`, `m`, `d`, `K` are separate parameters; the theorems that use `D_{n,α}` fix
`d = ⌈1/α⌉`, `n = (d+1)K^(2^d−1)` and `m = n^(d+3)`, so that every partition and lottery is possible:
a round-`r` pool has `n·M_r` goods and `q_{r+1} ≤ n q_r`. -/
noncomputable def randomPool (n m d K : ℕ) : PMF (Fin n → Finset (Fin m) → ℝ) :=
  (poolRounds n d K (d + 1) 0 [Finset.univ]).map (poolProfile d K)

end SingleOrSample.Supplement


