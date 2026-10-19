-- Prove2me | Definitions.Def_PrivSeqLearn_QueryComplexity_OB
-- name    : PrivSeqLearn_QueryComplexity_OB
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T20:14:23.014258+00:00
-- url     : https://prove2.me/theorems/419f5f98-72d2-4c31-8f17-bfe26f268009
-- title:
--   Definition 6.1 and §6, pp. 15–18 — bisection searches, the Opportunistic Bisection strategy (15)–(18) and the union of guesses G (19)
-- statement:
--   The Opportunistic Bisection (OB) strategy of Tsitsiklis, Xu and Xu, for an accuracy $\epsilon > 0$ and an integer $L \ge 2$ (written 0-based below).
--
--   1. **Bisection searches** (Definition 6.1, pp. 15–16). Starting from an interval $\mathcal J_1 = [\ell, h)$, each step queries the mid-point $m$ of the current interval $\mathcal J_i$ and replaces it by $[\inf \mathcal J_i, m)$ if the driving bit is $0$ and by $[m, \sup \mathcal J_i)$ if it is $1$ (eqs. (11)–(14)). The search is **truthful** when the bits are the responses, and **fictitious** when they are independent fair bits $Z_1, Z_2, \dots$.
--
--   2. **Phase 1, opportunistic guesses** (eqs. (15)–(16), p. 16). The first $2L$ queries are deterministic: $q_{i+1} = i/L$ and $q_{L+i+1} = i/L + \epsilon$ for $i = 0, \dots, L-1$. The $i$-th **guess** is $[i/L, i/L + \epsilon)$; it contains $v^*$ exactly when the response to $i/L$ is $1$ and the response to $i/L + \epsilon$ is $0$.
--
--   3. **Sub-intervals** (eq. (17), p. 17): $\mathcal J^{(i)} = [i/L + \epsilon, (i+1)/L)$, the gaps between consecutive guesses.
--
--   4. **Phase 2, local bisection** (p. 17). With
--   $$M = \left\lceil \log_2 \frac{1}{\epsilon L} \right\rceil,$$
--   the next $M$ queries are a truthful bisection search of the sub-interval $\mathcal J^*$ containing $v^*$ if no guess contains $v^*$, and otherwise a fictitious bisection search of a sub-interval $\tilde{\mathcal J}$, where $\tilde{\mathcal J}$ and $Z_1, \dots, Z_M$ are drawn from the seed. The total number of queries is $N = 2L + M$ (eq. (18)).
--
--   5. **Estimate** (proof of Proposition 6.2, p. 18): the mid-point $i/L + \epsilon/2$ of the guess that contains $v^*$, if there is one; otherwise the mid-point of the final interval $\mathcal J_{M+1}$ of the truthful search.
--
--   6. **Union of guesses** (eq. (19), p. 18):
--   $$\mathcal G = \bigcup_{i=0}^{L-1} \left[\frac iL, \frac iL + \epsilon\right).$$
--
--   The OB strategy attains the upper bound of the main theorem.
--
--   **Formalization Note** The seed space is $\{0, \dots, L \cdot 2^M - 1\}$, decoded as a pair $(\tilde{\mathcal J}, z)$ with $\tilde{\mathcal J} \in \{0, \dots, L-1\}$ and $z \in \{0, \dots, 2^M - 1\}$, and $Z_{j+1}$ is the $j$-th binary digit of $z$. Under the uniform seed, $\tilde{\mathcal J}$ is uniform and $Z_1, \dots, Z_M$ are i.i.d. fair bits, as the paper requires. On a response history, $\mathcal J^*$ is read off the Phase 1 responses (the number of queries $i/L$ answered $1$, minus one). The query and estimation maps are defined on all response histories; on histories that no true value produces, they still return values in $[0,1)$, and they are never used there. The last sub-interval is $[(L-1)/L + \epsilon, 1)$: eq. (17) writes $q_{L+1}$ for $i = L$, read as $1$. The estimate function is specified in the paper only inside the proof of Proposition 6.2; it is defined here as that proof sets it.
-- source:
--   Tsitsiklis, Xu, Xu, Private Sequential Learning, arXiv:1805.02136v3, pp. 15–18, Definition 6.1 (eqs. (11)–(14)), Phase 1 (eqs. (15)–(16), p. 16), Phase 2 and eqs. (17)–(18) (p. 17), estimate from the proof of Proposition 6.2 and eq. (19) (p. 18)

import Mathlib
import Definitions.Def_PrivSeqLearn_QueryComplexity_Setting

namespace PrivSeqLearn.QueryComplexity

/-- One run of a bisection search of `[lo, hi)` (Tsitsiklis, Xu, Xu, Private Sequential Learning,
arXiv:1805.02136v3, Definition 6.1, p. 16, eqs. (11)–(14)), driven by a list of bits:
with `m` the mid-point of the current interval, bit `false` keeps `[inf J, m)` and bit `true`
keeps `[m, sup J)`. Returns the endpoints of the final interval. The search is truthful when the
bits are the responses `r_i`, and fictitious when they are the seed bits `Z_i`. -/
noncomputable def bisect (lo hi : ℝ) : List Bool → ℝ × ℝ
  | [] => (lo, hi)
  | b :: bs => if b then bisect ((lo + hi) / 2) hi bs else bisect lo ((lo + hi) / 2) bs

/-- The mid-point of an interval given by its endpoints. -/
noncomputable def midpt (J : ℝ × ℝ) : ℝ := (J.1 + J.2) / 2

/-- The number `M = ⌈log₂ (1/(ϵL))⌉` of Phase 2 queries (p. 17, eq. (18), footnote 1, p. 4). -/
noncomputable def obM (ϵ : ℝ) (L : ℕ) : ℕ := ⌈Real.logb 2 (1 / (ϵ * L))⌉₊

/-- Left endpoint `(i-1)/L + ϵ` of the `i`-th sub-interval `J^(i)` (eq. (17), p. 17), 0-based:
sub-interval `i` is `[i/L + ϵ, (i+1)/L)`. -/
noncomputable def subLo (ϵ : ℝ) (L : ℕ) (i : ℕ) : ℝ := (i : ℝ) / L + ϵ

/-- Right endpoint `i/L` of the `i`-th sub-interval (eq. (17)), 0-based: `(i+1)/L`. -/
noncomputable def subHi (L : ℕ) (i : ℕ) : ℝ := ((i : ℝ) + 1) / L

/-- The 0-based index of the first Phase 1 guess `[i/L, i/L + ϵ)` that caught the true value, read
off a response history `h`: the response to `q_{i+1} = i/L` is `1` and the response to
`q_{L+i+1} = i/L + ϵ` is `0`. `none` if no guess caught it. -/
def caughtGuess (L : ℕ) (h : List Bool) : Option ℕ :=
  (List.range L).find? (fun i => h.getD i false && !(h.getD (L + i) true))

/-- The 0-based index of the sub-interval `J*` containing the true value when no guess caught it:
(number of Phase 1 queries `i/L`, `i < L`, answered `1`) − 1. -/
def jstar (L : ℕ) (h : List Bool) : ℕ :=
  ((List.range L).filter (fun i => h.getD i false)).length - 1

/-- Seed decoding: the seed `y ∈ Fin (L · 2^M)` is read as the pair `(J̃, z) ∈ Fin L × Fin (2^M)`;
`J̃` is the sub-interval of the fictitious search. -/
def seedSub {L M : ℕ} (y : Fin (L * 2 ^ M)) : ℕ := (finProdFinEquiv.symm y).1

/-- Seed decoding: the Bernoulli bits `Z_1, …, Z_M` are the binary digits of `z`;
`seedBits y j` is the 0-based `Z_{j+1}`, and the list holds the first `j` of them. -/
def seedBits {L M : ℕ} (y : Fin (L * 2 ^ M)) (j : ℕ) : List Bool :=
  (List.range j).map (fun i => Nat.testBit (finProdFinEquiv.symm y).2 i)

/-- The Opportunistic Bisection strategy (§6, pp. 16–17) for accuracy `ϵ` and `L` guesses, of length
`N = 2L + M` with `M = obM ϵ L` (eq. (18)), with seed space `Fin (L · 2^M)`.

* Phase 1 (eqs. (15)–(16)): on a history of length `k < L` the query is `k/L`; on a history of
  length `L + i` (`i < L`) it is `i/L + ϵ`.
* Phase 2: on a history of length `2L + j`, if some guess caught the true value, the query is the
  mid-point of the current interval of the fictitious bisection of `J^(J̃)` driven by the seed bits
  `Z_1, …, Z_j`; otherwise it is the mid-point of the current interval of the truthful bisection of
  `J*` driven by the Phase 2 responses so far.
* Estimate (proof of Proposition 6.2, p. 18): the mid-point `i/L + ϵ/2` of the guess `i` that caught
  the true value, or else the mid-point of the final truthful interval `H*`. -/
noncomputable def obStrategy (ϵ : ℝ) (L : ℕ) (hL : 0 < L) : Strategy (2 * L + obM ϵ L) where
  Ybar := L * 2 ^ obM ϵ L
  Ybar_pos := Nat.mul_pos hL (Nat.two_pow_pos _)
  query h y :=
    if h.length < L then (h.length : ℝ) / L
    else if h.length < 2 * L then ((h.length - L : ℕ) : ℝ) / L + ϵ
    else
      match caughtGuess L h with
      | some _ => midpt (bisect (subLo ϵ L (seedSub y)) (subHi L (seedSub y))
          (seedBits y (h.length - 2 * L)))
      | none => midpt (bisect (subLo ϵ L (jstar L h)) (subHi L (jstar L h)) (h.drop (2 * L)))
  est h _ :=
    match caughtGuess L h with
    | some i => (i : ℝ) / L + ϵ / 2
    | none => midpt (bisect (subLo ϵ L (jstar L h)) (subHi L (jstar L h)) (h.drop (2 * L)))

/-- The union of the guesses `G = ⋃_{i=1}^{L} [q_i, q_{i+L}) = ⋃_{i<L} [i/L, i/L + ϵ)`, eq. (19), p. 18. -/
def guessUnion (ϵ : ℝ) (L : ℕ) : Set ℝ :=
  ⋃ i : Fin L, Set.Ico ((i : ℝ) / L) ((i : ℝ) / L + ϵ)

end PrivSeqLearn.QueryComplexity


