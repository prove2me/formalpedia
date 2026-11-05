-- Prove2me | Definitions.Def_SecSampling_ColoredLastZero
-- name    : SecSampling_ColoredLastZero
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:31:04.568641+00:00
-- url     : https://prove2.me/theorems/dc894492-9d3f-4676-9f69-516bd33f4229
-- title:
--   The colored last zero problem: strategies, winning probability and performance
-- statement:
--   **The colored last zero problem** (Definition 3, pp.25–26). An adversary picks integers $m\le n$. A string of $n$ independent bits, each $1$ with probability $p$, is drawn; positions $1,\dots,m$ are **red** and $m+1,\dots,n$ **blue**. The player is told $n$, the number $r$ of red ones and the number $b$ of blue ones (but not $m$), sees the bits one by one, and wins if she stops on the last red $0$.
--
--   A strategy is a rule $Q(n,r,b,h)\in[0,1]$ giving the probability of stopping at the current bit after the prefix $h$. Its winning probability on $I$ is $Q(n,r,b,I[1,\ell])\prod_{j<\ell}(1-Q(n,r,b,I[1,j]))$ with $\ell$ the position of the last red $0$, and its **performance** on $(m,n)$ is the weighted sum of these over all strings of length $n$.
--
--   This is the variant used to transfer the impossibility result to players who know $n$ (§5.5).
--
--   **Formalization Note.** An instance with no red $0$ is won by vacuity, as in AOSp (p.2). The player does not see colours; since stopping on a blue bit always loses, seeing them would not change any winning probability.
-- source:
--   J. Correa, A. Cristi, L. Feuilloley, T. Oosterwijk & A. Tsigonias-Dimitriadis, The Secretary Problem with Independent Sampling, arXiv:2011.07869v1, https://arxiv.org/abs/2011.07869v1, §5.5, Definition 3, pp.25–26 (PDF pp.26–27)

import Mathlib
import Definitions.Def_SecSampling_LastZero

namespace SecSampling

/-- A (possibly randomized) **player strategy for the colored last zero problem**
(arXiv:2011.07869v1, Definition 3, pp.25–26): `Q n r b h` is the probability of stopping at the
current bit, given the size `n`, the number `r` of red 1s, the number `b` of blue 1s, and the
prefix `h` of bits seen so far, the current bit last. The player is not told `m`. -/
abbrev ColStrategy : Type := ℕ → ℕ → ℕ → List Bool → ℝ

/-- A colored strategy's stopping probabilities lie in `[0, 1]`. -/
def IsColStrategy (Q : ColStrategy) : Prop :=
  ∀ (n r b : ℕ) (h : List Bool), 0 ≤ Q n r b h ∧ Q n r b h ≤ 1

/-- The probability that `Q` wins the colored instance `I` with red part `I[1, m]`
(Definition 3): it stops on the last red `0`, i.e. on the last `0` among positions `1, …, m`.

**Formalization Note.** If there is no red `0`, the instance is won by vacuity, as in AOSp
(p.2) and the last zero problem. -/
noncomputable def winColored (Q : ColStrategy) (m : ℕ) (I : List Bool) : ℝ :=
  if false ∈ I.take m then
    Q I.length (bitNorm (I.take m)) (bitNorm (I.drop m)) (I.take (lastZero (I.take m))) *
      ∏ j ∈ Finset.Ico 1 (lastZero (I.take m)),
        (1 - Q I.length (bitNorm (I.take m)) (bitNorm (I.drop m)) (I.take j))
  else 1

/-- The **performance** of `Q` on the pair `(m, n)` chosen by the adversary (Definition 3,
items 1–2): its winning probability on a random string of length `n` with independent bits equal
to 1 with probability `p`, entries `1, …, m` red. -/
noncomputable def perfColored (p : ℝ) (Q : ColStrategy) (m n : ℕ) : ℝ :=
  ∑ I ∈ strings n, weight p I * winColored Q m I

end SecSampling


