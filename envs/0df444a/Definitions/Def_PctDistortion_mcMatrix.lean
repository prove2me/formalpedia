-- Prove2me | Definitions.Def_PctDistortion_mcMatrix
-- name    : PctDistortion_mcMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:40:57.898998+00:00
-- url     : https://prove2.me/theorems/95d01707-a899-41ed-8e5c-925797678643
-- title:
--   The Markov chain MC (4), irreducibility, aperiodicity, reflection
-- statement:
--   With $\ell=sr+1$ and arithmetic modulo $\ell$, the **Markov chain MC** on $\{0,\dots,\ell-1\}$ moves
--   $$0\to r\ \text{with probability }1,\qquad i\to i+r\ \text{w.p. }\tfrac{1+\hat\nu}{2},\qquad i\to i+r+1\ \text{w.p. }\tfrac{1-\hat\nu}{2}\quad(i>0).\tag{4}$$
--   A transition matrix $M$ is **irreducible** if every state is reachable from every state ($(M^k)_{ij}>0$ for some $k$), and **aperiodic** if every state has period $1$: the only natural number dividing every return time $k$ with $(M^k)_{ii}>0$ is $1$. The **reflection about 0** of a vector $a$ is $b$ with $b_0=a_0$ and $b_i=a_{\ell-i}$.
--
--   Lemma 4 identifies Alice's and Bob's equilibrium strategies of the reduced game with the stationary distribution of MC and its reflection.
--
--   **Formalization Note** States are $\mathbb Z/\ell$ (`Fin (s*r+1)`); stationarity is the published `MarkovChain.IsStationary`.
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), eq. (4), p.14; Lemma 4, p.14

import Mathlib

set_option autoImplicit false

namespace PctDistortion

/-- The transition matrix of the **Markov chain MC** (4) on `{0, …, ℓ − 1}`, `ℓ = s r + 1`
(arithmetic modulo `ℓ`, `ν̂ = νH`; `Fin.ofNat ℓ r` is `r mod ℓ`): `0 → r` with probability `1`; for `i > 0`,
`i → i + r` with probability `(1 + ν̂)/2` and `i → i + r + 1` with probability `(1 − ν̂)/2`.

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), eq. (4), p.14: "0 → r with probability 1; i → i + r with probability (1 + ν̂)/2 if i > 0;
i → i + r + 1 with probability (1 − ν̂)/2 if i > 0." -/
noncomputable def mcMatrix (νH : ℝ) (s r : ℕ) : Matrix (Fin (s * r + 1)) (Fin (s * r + 1)) ℝ :=
  fun i j =>
    if i = 0 then (if j = Fin.ofNat (s * r + 1) r then 1 else 0)
    else (if j = i + Fin.ofNat (s * r + 1) r then (1 + νH) / 2 else 0) +
      (if j = i + Fin.ofNat (s * r + 1) r + 1 then (1 - νH) / 2 else 0)

/-- A transition matrix `M` on a finite state space is **irreducible**: every state `j` is
reachable from every state `i`, `(M^n)_{ij} > 0` for some `n`. -/
def IsIrreducible {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) : Prop :=
  ∀ i j, ∃ k : ℕ, 0 < (M ^ k) i j

/-- A transition matrix `M` is **aperiodic**: every state has period `1`, i.e. the only natural
number dividing every `k` with `(M^k)_{ii} > 0` is `1`. -/
def IsAperiodic {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) : Prop :=
  ∀ i, ∀ d : ℕ, (∀ k : ℕ, 0 < (M ^ k) i i → d ∣ k) → d = 1

/-- The **reflection about `0`** of a vector on `{0, …, ℓ − 1}`: `b₀ = a₀` and
`b_i = a_{ℓ−i}` for `i ∈ {1, …, ℓ − 1}`, i.e. `b_i = a_{−i}` modulo `ℓ`.

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), Lemma 4, p.14: "b is the reflection of a about 0, meaning b0 = a0, and bi = aℓ−i for
i ∈ {1, . . . , ℓ − 1}." -/
def reflect {ℓ : ℕ} (a : Fin ℓ → ℝ) : Fin ℓ → ℝ :=
  fun i => a (-i)

end PctDistortion


