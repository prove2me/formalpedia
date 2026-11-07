-- Prove2me | Definitions.Def_MinSumClust_lemma50Process
-- name    : MinSumClust_lemma50Process
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:46:40.564432+00:00
-- url     : https://prove2.me/theorems/811567d6-046f-475d-a7a8-dc2e22a3d207
-- title:
--   The random process of Lemma 50
-- statement:
--   Let $N$ binary variables $X_1,\dots,X_N$, an initial segment $[N']$ and $M$ nonempty intervals $B_1,\dots,B_M$ partitioning $[N'+1:N]$ from left to right be given, with $l_i=\min B_i$, an integer $K$ and nonnegative weights $w_{it}$ for $t<l_i$. The process is:
--
--   1. for each block $B_i$ independently, a uniform representative $r_i\in B_i$;
--   2. among the $N-M$ non-representatives, a uniform set of $K$ gets value $1$, the others $0$;
--   3. for $i=1,\dots,M$ in increasing order: $X_{r_i}=1$ if some $j\in B_i\setminus\{r_i\}$ has $X_j=1$, otherwise $X_{r_i}=\mathbf 1\bigl(\sum_{t<l_i}w_{it}X_t>\frac23\sum_{t<l_i}w_{it}\bigr)$.
--
--   It models Algorithm 6, with $X$ marking the closed $\mathcal S_2$ clusters.
--
--   **Formalization Note** Indices are 0-based: block $i$ is $[l_i,l_{i+1})$ (the last ends at $N$). The independent representatives are one uniform choice from the product of the blocks.
-- source:
--   Anand, Charikar, Gao, Grandoni, Lee, Sharma, van Wijland, A Constant Approximation for Min-sum k-Clustering, STOC 2027 submission (manuscript of November 3, 2026, sha256 103c52a5…), Lemma 50, pp.45–46 (PDF pp.47–48)

import Mathlib

namespace MinSumClust

/-- The end of block `i` (exclusive): the start of block `i + 1`, or `N` for the last block. -/
def blockEnd (N M : ℕ) (l : Fin M → ℕ) (i : Fin M) : ℕ :=
  if h : i.val + 1 < M then l ⟨i.val + 1, h⟩ else N

/-- Block `B_i = [l_i, l_{i+1})` of indices (0-based). -/
def block (N M : ℕ) (l : Fin M → ℕ) (i : Fin M) : Finset (Fin N) :=
  Finset.univ.filter fun j => l i ≤ j.val ∧ j.val < blockEnd N M l i

/-- **The random process of Lemma 50**, pp.45–46 (PDF pp.47–48).

Anand et al., *A Constant Approximation for Min-sum k-Clustering*, STOC 2027 submission (manuscript
of November 3, 2026, sha256 103c52a5…), Lemma 50, pp.45–46. Given block starts `l` and weights `w`:
* independently for each block `B_i` a uniform representative `r_i ∈ B_i`;
* among the `N − M` non-representatives, a uniform `K`-subset gets value `1`, the others `0`;
* for `i = 1, …, M` in increasing order: `X_{r_i} = 1` if some `j ∈ B_i \ {r_i}` has `X_j = 1`,
  otherwise `X_{r_i} = 1(∑_{t<l_i} w_{it} X_t > (2/3) ∑_{t<l_i} w_{it})`.

**Formalization Note.** Indices are 0-based: the paper's `[N′+1 : N]` is `[N′, N)` and `t < l_i`
keeps its meaning. The independent representatives are one uniform choice from the product of the
blocks. If a sampled set is empty (excluded by the lemma's hypotheses) the process returns all
zeros. -/
noncomputable def lemma50Process (N M K : ℕ) (l : Fin M → ℕ) (w : Fin M → Fin N → ℝ) :
    PMF (Fin N → Bool) :=
  if h : (Fintype.piFinset (block N M l)).Nonempty then
    (PMF.uniformOfFinset _ h).bind fun r =>
      let nonrep := Finset.univ \ Finset.univ.image r
      if h' : (nonrep.powersetCard K).Nonempty then
        (PMF.uniformOfFinset _ h').map fun T =>
          (List.finRange M).foldl
            (fun (X : Fin N → Bool) (i : Fin M) =>
              Function.update X (r i)
                (if ∃ j ∈ block N M l i, j ≠ r i ∧ X j = true then true
                else decide ((2 / 3 : ℝ) * ∑ t ∈ Finset.univ.filter (fun t : Fin N => t.val < l i),
                      w i t <
                    ∑ t ∈ Finset.univ.filter (fun t : Fin N => t.val < l i),
                      w i t * (if X t then 1 else 0))))
            (fun j => decide (j ∈ T))
      else PMF.pure fun _ => false
  else PMF.pure fun _ => false

end MinSumClust


