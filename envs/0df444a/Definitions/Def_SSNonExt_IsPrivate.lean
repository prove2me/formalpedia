-- Prove2me | Definitions.Def_SSNonExt_IsPrivate
-- name    : SSNonExt_IsPrivate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:54:46.255621+00:00
-- url     : https://prove2.me/theorems/faa5de87-ffd5-4eb1-965a-732dcb81d754
-- title:
--   Threshold secret sharing from a source class: shares $\mathrm{Shr}_J$, perfect correctness, $\delta$-privacy (Definition 2.1)
-- statement:
--   Let $K$ be a finite key set, $M$ a message set and $\mathcal S$ a class of distributions on $K$. A **$t$-out-of-$n$ sharing scheme** consists of a deterministic map
--
--   $$\mathrm{Shr}=(\mathrm{Shr}_1,\dots,\mathrm{Shr}_n):M\times K\to C^n$$
--
--   together with reconstruction maps. The dealer samples one key $K\sim P$ from an unknown $P\in\mathcal S$ and outputs $\mathrm{Shr}(m,K)$; there is no other randomness. For a set $J\subseteq[n]$ of parties, $\mathrm{Shr}_J(m,k)$ is the tuple of shares of the parties in $J$.
--
--   1. The scheme is **perfectly correct** if for every $J$ with $|J|\ge t$ there is a map $\mathrm{Rec}_J$ with $\mathrm{Rec}_J(\mathrm{Shr}_J(m,k))=m$ for all $m\in M$ and all $k\in K$.
--   2. The scheme is **$\delta$-private for $\mathcal S$** if for every $P\in\mathcal S$, every $J$ with $|J|<t$ and all $m,m'\in M$,
--   $$\mathrm{TV}\big(\mathrm{Shr}_J(m,K),\mathrm{Shr}_J(m',K)\big)\le\delta,\qquad K\sim P.$$
--   It is **perfectly private** if $\delta=0$, i.e. the law of the shares of every unauthorized set does not depend on the message.
--
--   For $t=n=2$ the two shares are written $F=\mathrm{Shr}_1$ and $G=\mathrm{Shr}_2$.
--
--   **Formalization Note** All parties use one share alphabet $C$ (the paper allows $C_1,\dots,C_n$; in this paper both alphabets are $\{0,1\}\times V$). Parties are indexed by `Fin n`. The reconstruction map of $J$ sees only the shares of $J$.
-- source:
--   Aggarwal, Secret Sharing Despite Non-Extractable Randomness, arXiv:2610.20173 (version of 2026-11-03, sha256 438a7f71…), Definition 2.1, p.5 (PDF p.5); §2, sentence after Definition 2.1, p.6

import Mathlib
import Definitions.Def_SSNonExt_TV

namespace SSNonExt

/-- The shares `Shr_J(m, k)` of the parties in `J ⊆ [n]` (Definition 2.1, p.5).
D. Aggarwal, *Secret Sharing Despite Non-Extractable Randomness*, arXiv:2610.20173 (version of
2026-11-03, sha256 438a7f71…), Definition 2.1, p.5.

**Formalization Note.** A deterministic sharing map `Shr = (Shr₁, …, Shrₙ) : M × K → C₁ × ⋯ × Cₙ` is
`shr : M → K → Fin n → C`, with party `j` receiving `shr m k j`; all parties share one alphabet `C`
(in this paper both share alphabets are `{0,1} × V`). Parties are indexed from `0`. -/
def shrJ {M K C : Type*} {n : ℕ} (shr : M → K → Fin n → C) (J : Finset (Fin n)) (m : M) (k : K) :
    J → C :=
  fun j => shr m k j

/-- **Perfect correctness** of a `t`-out-of-`n` scheme (Definition 2.1, p.5): for every set `J` of at
least `t` parties there is a reconstruction map `Rec_J` with `Rec_J(Shr_J(m, k)) = m` for all messages
`m` and all keys `k`.
arXiv:2610.20173 (version of 2026-11-03, sha256 438a7f71…), Definition 2.1, p.5.

**Formalization Note.** The reconstruction map of `J` is a function of the shares of `J` alone; it
may not depend on the key or the message. -/
def PerfectlyCorrect {M K C : Type*} {n : ℕ} (t : ℕ) (shr : M → K → Fin n → C) : Prop :=
  ∀ J : Finset (Fin n), t ≤ J.card → ∃ rec : (J → C) → M, ∀ m k, rec (shrJ shr J m k) = m

/-- **δ-privacy for a source class** `S` (Definition 2.1, p.5): for every `P ∈ S`, every set `J` of
fewer than `t` parties and all messages `m, m′`,
`TV(Shr_J(m, K), Shr_J(m′, K)) ≤ δ` with `K ∼ P`. The scheme is perfectly private when `δ = 0`.
arXiv:2610.20173 (version of 2026-11-03, sha256 438a7f71…), Definition 2.1, p.5.

**Formalization Note.** `TV` is the `½ ℓ¹` distance of §2 between the push-forwards
`P.map (Shr_J(m, ·))` and `P.map (Shr_J(m′, ·))`; with `δ = 0` it says that the two laws are equal. -/
def IsPrivate {M K C : Type*} [Fintype C] {n : ℕ} (t : ℕ) (δ : ℝ) (S : Set (PMF K))
    (shr : M → K → Fin n → C) : Prop :=
  ∀ P ∈ S, ∀ J : Finset (Fin n), J.card < t → ∀ m m' : M,
    TV (P.map (shrJ shr J m)) (P.map (shrJ shr J m')) ≤ δ

end SSNonExt


