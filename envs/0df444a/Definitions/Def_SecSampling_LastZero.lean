-- Prove2me | Definitions.Def_SecSampling_LastZero
-- name    : SecSampling_LastZero
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:30:23.997267+00:00
-- url     : https://prove2.me/theorems/4b083dde-892c-4881-9c2d-d1f731cc053a
-- title:
--   The last zero problem: norm, weights, strategies, winning probability, performance
-- statement:
--   **The last zero problem** (Definition 1, p.14). An adversary picks a size $n$. A string of $n$ bits is drawn with each bit independently equal to $1$ with probability $p$ and $0$ otherwise. The player is told the **norm** of the string (its number of ones), then sees the bits one by one and decides at each bit whether to stop; she wins if she stops on the last $0$. A string without a $0$ is won by vacuity, as in AOSp where everything is sampled (p.2).
--
--   A string $I$ of size $n$ and norm $m$ has **weight** $p^m(1-p)^{n-m}$, its probability (p.17). A (randomized) player strategy is a rule $q(m,h)\in[0,1]$, the probability of stopping at the current bit given the norm $m$ and the prefix $h$ seen so far; it does not depend on $n$. With $r$ the position of the last $0$ of $I$, the strategy wins in $I$ with probability
--   $$\mathrm{win}_q(I)=q\big(m,I[1,r]\big)\prod_{j=1}^{r-1}\Big(1-q\big(m,I[1,j]\big)\Big),$$
--   its **selection probability** of $I$; its **performance** at size $n$ is $\sum_{|I|=n}p^{m(I)}(1-p)^{n-m(I)}\,\mathrm{win}_q(I)$.
--
--   The **$k$-max strategy** (§5.4, p.23) is the AOSp $k$-max algorithm on increasing instances (1 = sampled): it stops at a $0$ in position $j$ iff fewer than $k=\lfloor 1/(1-p)\rfloor$ ones come after position $j$.
--
--   These are the objects of the conflict-graph part of the proof.
--
--   **Formalization Note.** Strings are `List Bool` with `true` = 1; positions are 1-based. `lastZero I` is the 1-based position of the last $0$ (and $0$ if none).
-- source:
--   J. Correa, A. Cristi, L. Feuilloley, T. Oosterwijk & A. Tsigonias-Dimitriadis, The Secretary Problem with Independent Sampling, arXiv:2011.07869v1, https://arxiv.org/abs/2011.07869v1, §5.1, Definition 1, p.14 (PDF p.15); §5.2.2, pp.17–18 (weights, selection probability, performance); §5.4, p.23 (k-max in the last zero problem)

import Mathlib
import Definitions.Def_SecSampling_AOSp

namespace SecSampling

/-- The **norm** of a bit string: its number of ones (arXiv:2011.07869v1, §5.1, p.14: "Let the
norm of a sequence of bits be the number of ones it has").

**Formalization Note.** Bit strings are `List Bool` with `true` = 1 = sampled and `false` = 0 =
online; positions are 1-based in the docstrings. -/
def bitNorm (I : List Bool) : ℕ := I.count true

/-- The 1-based position of the last `0` of `I`, and `0` if `I` contains no `0`. -/
def lastZero (I : List Bool) : ℕ :=
  if false ∈ I then I.length - I.reverse.idxOf false else 0

/-- The **weight** `p^m (1−p)^{n−m}` of a string of size `n` and norm `m`: the probability that
independent sampling produces it (arXiv:2011.07869v1, §5.2.2, p.17). -/
noncomputable def weight (p : ℝ) (I : List Bool) : ℝ :=
  p ^ bitNorm I * (1 - p) ^ (I.length - bitNorm I)

/-- The finite set of all bit strings of length `n`. -/
def strings (n : ℕ) : Finset (List Bool) :=
  Finset.univ.image (fun f : Fin n → Bool => List.ofFn f)

/-- A (possibly randomized) **player strategy for the last zero problem** (arXiv:2011.07869v1,
Definition 1, p.14): `q m h` is the probability of stopping at the current bit, given the norm `m`
of the sequence and the prefix `h` seen so far, the current bit last. The player does not know the
size `n` (Definition 1, items 3–4). -/
abbrev LZStrategy : Type := ℕ → List Bool → ℝ

/-- A strategy's stopping probabilities lie in `[0, 1]`. -/
def IsLZStrategy (q : LZStrategy) : Prop :=
  ∀ (m : ℕ) (h : List Bool), 0 ≤ q m h ∧ q m h ≤ 1

/-- Probability that `q`, run on `I` with norm `m`, stops exactly at position `r`: it continues at
positions `1, …, r−1` and stops at `r`. -/
noncomputable def stopProbAt (q : LZStrategy) (m : ℕ) (I : List Bool) (r : ℕ) : ℝ :=
  q m (I.take r) * ∏ j ∈ Finset.Ico 1 r, (1 - q m (I.take j))

/-- The **probability that `q` wins in instance `I`** (its selection probability of the node `I`):
the probability that it stops on the last `0` of `I` (Definition 1, item 5, p.14).

**Formalization Note.** An instance with no `0` is won by vacuity, as an AOSp instance with
everything sampled is won (p.2); the paper's p.7 "no-zero rule" is a proof device only. -/
noncomputable def winLZ (q : LZStrategy) (I : List Bool) : ℝ :=
  if false ∈ I then stopProbAt q (bitNorm I) I (lastZero I) else 1

/-- The **performance** of `q` at size `n`: its winning probability when the instance is a random
string of length `n` with independent bits equal to 1 with probability `p` (Definition 1,
items 1–2, p.14; §5.2.2, p.18). -/
noncomputable def perfLZ (p : ℝ) (q : LZStrategy) (n : ℕ) : ℝ :=
  ∑ I ∈ strings n, weight p I * winLZ q I

/-- The **k-max algorithm for the last zero problem** (arXiv:2011.07869v1, §5.4, p.23): read
through the increasing reduction (values increasing in position, 1 = sampled), it stops at a `0`
in position `j` iff fewer than `k = ⌊1/(1−p)⌋` ones lie after position `j`, i.e. iff
`m − #(ones in positions 1..j) < k` with `m` the norm. It never stops at a `1`.

**Formalization Note.** The subtraction is in `ℕ`; it is exact because `m` is the norm of the
whole string and so at least the number of ones in any prefix. -/
noncomputable def kmaxLZ (p : ℝ) : LZStrategy := fun m h =>
  if h.getLast? = some false ∧ m - h.count true < kOf p then 1 else 0

end SecSampling


