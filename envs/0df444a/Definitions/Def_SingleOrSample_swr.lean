-- Prove2me | Definitions.Def_SingleOrSample_swr
-- name    : SingleOrSample_swr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:46:38.504482+00:00
-- url     : https://prove2.me/theorems/d05f657b-0626-4870-925a-53c65b6cdcbd
-- title:
--   Single-round sampling without replacement $\mathrm{SwR}(G,p)$
-- statement:
--   For a finite set $G$ and $p\in[0,1]$, $\mathrm{SwR}(G,p)$ returns a uniformly random subset of $G$ of random size $P$, where $P$ takes values in $\{\lfloor p|G|\rfloor,\lceil p|G|\rceil\}$ and $\mathbb E[P]=p|G|$. Explicitly, $P=\lfloor p|G|\rfloor+1$ with probability $x=p|G|-\lfloor p|G|\rfloor$, and $P=\lfloor p|G|\rfloor$ otherwise.
--
--   A single pick from a bucket of size $s$ is $\mathrm{SwR}(B,1/s)$.
--
--   **Formalization Note** The size $\lfloor p|G|\rfloor+1$ is used only with the probability $x$, and $x>0$ forces it to be at most $|G|$. If it exceeds $|G|$, then $x=0$ and the fallback value of the helper `uniformOfSize` has no mass.
-- source:
--   Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), Definition 4, p.8

import Mathlib

open scoped Classical

namespace SingleOrSample

/-- The uniform law on subsets of `G` of size `s`, and the point mass at `∅` if there is none (a size
`s > |G|`, which `swr` only ever uses with probability `0`). -/
noncomputable def uniformOfSize {α : Type*} (G : Finset α) (s : ℕ) : PMF (Finset α) :=
  if hs : (G.powersetCard s).Nonempty then PMF.uniformOfFinset (G.powersetCard s) hs else PMF.pure ∅

/-- A coin with probability `x ∈ [0, 1]` of `true`. -/
noncomputable def coin (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : PMF Bool :=
  PMF.ofFintype (fun b => ENNReal.ofReal (if b then x else 1 - x)) (by
    rw [Fintype.sum_bool]
    simp only [if_true, Bool.false_eq_true, if_false]
    rw [← ENNReal.ofReal_add hx0 (by linarith)]
    simp)

/-- Single-round sampling without replacement `SwR(G, p)` (Chawla, Huang, Kulkarni, Mehta, Shahkar,
Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission,
arXiv:2609.32286, manuscript sha256 28cd3d7b…, Definition 4, p.8): a uniformly random subset of `G` of a
random size `P ∈ {⌊p|G|⌋, ⌈p|G|⌉}` with `E[P] = p|G|`.

**Formalization Note.** `P = ⌊p|G|⌋ + 1` with probability `x = p|G| − ⌊p|G|⌋` (the fractional part) and
`P = ⌊p|G|⌋` otherwise, which is the unique such law and is how the proof of Lemma B.1 (p.30) writes it.
When `p|G|` is an integer, `x = 0` and `P` is that integer. -/
noncomputable def swr {α : Type*} (G : Finset α) (p : unitInterval) : PMF (Finset α) :=
  (coin (Int.fract ((p : ℝ) * G.card)) (Int.fract_nonneg _) (Int.fract_lt_one _).le).bind fun up =>
    uniformOfSize G (⌊(p : ℝ) * G.card⌋₊ + if up then 1 else 0)

end SingleOrSample


