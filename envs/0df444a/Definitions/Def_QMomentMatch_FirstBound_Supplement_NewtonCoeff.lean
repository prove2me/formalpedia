-- Prove2me | Definitions.Def_QMomentMatch_FirstBound_Supplement_NewtonCoeff
-- name    : QMomentMatch_FirstBound_Supplement_NewtonCoeff
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:40:38.601342+00:00
-- url     : https://prove2.me/theorems/1612ccbb-9044-4c6c-8bb0-f2566ae86610
-- title:
--   Newton coefficients $d_\ell(\mathbf w)$ (20), $\alpha_j=1-2^{1-j}$, the good set $\mathcal G$, block counts of the singleton completion, binomial weights
-- statement:
--   This file adds the objects of §4 of the paper that the base definitions do not contain. Throughout, $A\ge1$, $S=\{0\}\cup[A]=\{0,1,\dots,A\}$, $N\ge1$ and $m=\lfloor N/2\rfloor$; $h(\mathbf z)=\Pr_{f\sim\mathcal D_{\mathbf c(\mathbf z)}}[\mathcal A^f=1]$ is the averaged acceptance probability of a fixed $T$-query algorithm $\mathcal A$ (the base definition `hAcc`), and for $\mathbf w\in S^{m-1}$ and $s\in S$, $(\mathbf w,s)\in S^m$ appends $s$ as last coordinate.
--
--   1. **Exponents.** $\alpha_j=1-2^{1-j}$ for integers $j$, so $\alpha_1=0$, $\alpha_2=1/2$ and $\alpha_{j+1}=(1+\alpha_j)/2$.
--   2. **Newton coefficients** of a function $q$ on $\{0,1,2,\dots\}$:
--   $$d_\ell=\sum_{s=0}^{\ell}(-1)^{\ell-s}\binom{\ell}{s}q(s).$$
--   3. **The functions $q_{\mathbf w}$ and their Newton coefficients** (eq. (20)): $q_{\mathbf w}(s)=h(\mathbf w,s)$ for $s\in S$, and
--   $$d_\ell(\mathbf w)=\sum_{s=0}^{\ell}(-1)^{\ell-s}\binom{\ell}{s}q_{\mathbf w}(s)\qquad(0\le\ell\le A).$$
--   4. **The good set** $\mathcal G=\{\mathbf w\in S^{m-1}:\sum_i w_i\le 3N/4\}$, through its indicator $\mathbf 1_{\mathcal G}$.
--   5. **The singleton completion** $\mathbf c(\mathbf w,\ell)$ of $(\mathbf w,\ell)$: the frequency vector of step 2 of Definition 2.1 for the multiplicities $(\mathbf w,\ell)$ (non-zero entries of $(\mathbf w,\ell)$, completed by singletons and padded with zeros). Its number of $j$-blocks is the number of entries equal to $j$: $\rho$ counts the $\ell$-blocks and $b_j$ the $j$-blocks; $n_j=1+b_j$ and $n_*=\min_{1\le j<\ell}n_j$.
--   6. **Binomial weights** $\Pr[\mathrm{Bin}(n,a)=k]=\binom nk a^k(1-a)^{n-k}$.
--
--   These objects are the vocabulary of Lemmas 3.3, 3.6, 4.1, 4.8 and 4.9, which bound the Newton coefficients of $q_{\mathbf w}$ in the proof of Theorem 2.6.
--
--   **Formalization Note** $q_{\mathbf w}(s)$ is set to $0$ for $s>A$; this value never enters, since $d_\ell(\mathbf w)$ is only used for $\ell\le A$. $n_*$ is set to $1$ when $\ell\le1$ (the range $1\le j<\ell$ is then empty); the paper uses it only for $\ell\ge2$. $m=\lfloor N/2\rfloor$ is fixed inside $q_{\mathbf w}$ and $\mathbf c(\mathbf w,\ell)$, as in the base distribution $\Pi_N$.
-- source:
--   Chandrima Kayal, Frédéric Magniez, Sayantan Sen, Dániel Szabó, STOC 2027 submission #564 (October 2026), Lemma 3.3 p. 16, Lemma 3.6 p. 17, §4.1 eq. (20) p. 24, Lemma 4.9 p. 32

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QMomentMatch_FirstBound_Basic
import Definitions.Def_QMomentMatch_FirstBound_InducedDist

/-!
# Newton coefficients `d_ℓ(w)`, the exponents `α_j`, the good set `G`, block counts of the
singleton completion, and binomial weights

Kayal, Magniez, Sen, Szabó, *Quantum Query Lower Bounds from Classical Moment Matching*,
STOC 2027 submission #564, Lemma 3.3 (p. 16), Lemma 3.6 (p. 17), §4.1 eq. (20) (p. 24),
Lemma 4.9 (p. 32).

Conventions (as in the base files). `S = {0} ∪ [A]` is `Fin (A + 1)`; `m = ⌊N/2⌋` is `N / 2`;
`w ∈ S^{m−1}` is `w : Fin (N / 2 - 1) → Fin (A + 1)` and `(w, s)` is `appendLast w s`;
`h(z) = Pr_{f ∼ D_{c(z)}}[A^f = 1]` is the base `hAcc`.
-/

namespace QMomentMatch.FirstBound.Supplement

open QAlgorithms QMomentMatch.FirstBound

/-- p. 24: `α_j = 1 − 2^{1−j}` (an integer power of `2`, so `α_1 = 0`, `α_2 = 1/2`, …). -/
noncomputable def alpha (j : ℕ) : ℝ :=
  1 - (2 : ℝ) ^ ((1 : ℤ) - (j : ℤ))

/-- Lemma 3.3 (p. 16) and eq. (20) (p. 24): the `ℓ`-th Newton coefficient
`d_ℓ = ∑_{s=0}^{ℓ} (−1)^{ℓ−s} (ℓ choose s) q(s)` of a function `q` on the integers `0, 1, 2, …`. -/
noncomputable def newtonCoeff (q : ℕ → ℝ) (ℓ : ℕ) : ℝ :=
  ∑ s ∈ Finset.range (ℓ + 1), (-1 : ℝ) ^ (ℓ - s) * ((ℓ.choose s : ℕ) : ℝ) * q s

/-- p. 24: `q_w(s) = h(w, s)` for `s ∈ S = {0, …, A}`, with `m = ⌊N/2⌋` and `h` the acceptance
probability of the `T`-query algorithm `alg` (output map `out`) averaged over `D_{c(w,s)}`.
Arguments `s > A` (outside `S`) are given the value `0`; they never occur below, because
`d_ℓ(w)` is used only for `ℓ ≤ A`. -/
noncomputable def qW {N : ℕ} [NeZero N] {W : Type*} [Fintype W] [DecidableEq W] {T : ℕ}
    (alg : QueryAlg (Fin N) (ZMod N) W T) (out : (Fin N × ZMod N) × W → Bool)
    {A : ℕ} (w : Fin (N / 2 - 1) → Fin (A + 1)) (s : ℕ) : ℝ :=
  if h : s < A + 1 then hAcc alg out (appendLast (m := N / 2) w (⟨s, h⟩ : Fin (A + 1))) else 0

/-- Eq. (20), p. 24: the Newton coefficients `d_ℓ(w) = ∑_{s=0}^{ℓ} (−1)^{ℓ−s} (ℓ choose s) q_w(s)`
(`0 ≤ ℓ ≤ A`). -/
noncomputable def newtonW {N : ℕ} [NeZero N] {W : Type*} [Fintype W] [DecidableEq W] {T : ℕ}
    (alg : QueryAlg (Fin N) (ZMod N) W T) (out : (Fin N × ZMod N) × W → Bool)
    {A : ℕ} (w : Fin (N / 2 - 1) → Fin (A + 1)) (ℓ : ℕ) : ℝ :=
  newtonCoeff (qW alg out w) ℓ

/-- p. 24: the indicator `1_G(w)` of the good set `G = {w ∈ S^{m−1} : ∑_i w_i ≤ 3N/4}`
(a real inequality). -/
noncomputable def goodInd (N : ℕ) {A n : ℕ} (w : Fin n → Fin (A + 1)) : ℝ :=
  if (∑ i, (((w i : ℕ)) : ℝ)) ≤ 3 * (N : ℝ) / 4 then 1 else 0

/-- Lemma 4.9, p. 32 (and §4.2.1, p. 26): the completion `c(w, ℓ)` of `(w, ℓ)` with singletons,
i.e. the frequency vector of Definition 2.1 step 2 for the multiplicities `(w, ℓ)`, as the multiset
of its entries (the base `drawsFreq`). -/
def completion (N : ℕ) {A : ℕ} (w : Fin (N / 2 - 1) → Fin (A + 1)) (ℓ : Fin (A + 1)) :
    Multiset ℕ :=
  drawsFreq N (appendLast (m := N / 2) w ℓ)

/-- Lemma 4.9, p. 32: the number of `j`-blocks of the completion `c(w, ℓ)`, i.e. the number of its
entries equal to `j` (`ρ` is the case `j = ℓ`, `b_j` the case `1 ≤ j < ℓ`). -/
def blockCount (N : ℕ) {A : ℕ} (w : Fin (N / 2 - 1) → Fin (A + 1)) (ℓ : Fin (A + 1)) (j : ℕ) :
    ℕ :=
  (completion N w ℓ).count j

/-- Lemma 4.9, p. 32: `n_* = min_{1 ≤ j < ℓ} n_j` with `n_j = 1 + b_j`. (The index range is
nonempty exactly when `ℓ ≥ 2`, which Lemma 4.9 assumes; the value `1` for `ℓ ≤ 1` is never
used.) -/
def nStar (N : ℕ) {A : ℕ} (w : Fin (N / 2 - 1) → Fin (A + 1)) (ℓ : Fin (A + 1)) : ℕ :=
  if h : (Finset.Ico 1 (ℓ : ℕ)).Nonempty then
    (Finset.Ico 1 (ℓ : ℕ)).inf' h fun j => 1 + blockCount N w ℓ j
  else 1

/-- Lemma 3.6, p. 17: the binomial probability `Pr[Bin(n, a) = k] = (n choose k) a^k (1−a)^{n−k}`
(zero for `k > n`). -/
noncomputable def binomPmf (n : ℕ) (a : ℝ) (k : ℕ) : ℝ :=
  ((n.choose k : ℕ) : ℝ) * a ^ k * (1 - a) ^ (n - k)

end QMomentMatch.FirstBound.Supplement


