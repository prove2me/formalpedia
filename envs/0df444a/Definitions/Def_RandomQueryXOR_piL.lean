-- Prove2me | Definitions.Def_RandomQueryXOR_piL
-- name    : RandomQueryXOR_piL
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:57:59.393954+00:00
-- url     : https://prove2.me/theorems/25d8f134-5524-42c3-ae57-2b4a05172aae
-- title:
--   Protocol $\pi_L$: embedding the sides $\rho$ into the index sequence $L$
-- statement:
--   Fix $f:\{0,1\}^n\to\{0,1\}$, an input $x^\star$ with at least one sensitive zero, and $k$ players. Protocol $\pi_L$ builds an index sequence $L=(\ell_1,\dots,\ell_T)\in[2n]^T$:
--
--   1. pick the special index $h$ uniformly among the sensitive zeros of $x^\star$, i.e. $\{i: x^\star(i)=0,\ f(x^\star)\ne f(x^\star\oplus e_i)\}$;
--   2. draw $m_1,\dots,m_T$ uniformly from $[n]$ with public randomness;
--   3. if $m_t\ne h$, let $\ell_t$ be $2m_t-1$ or $2m_t$ by a public fair coin; if $m_t=h$ is the $a$-th occurrence of $h$ and $a\le k$, let $\ell_t=2m_t-1$ if $\rho_a=\text{'}\alpha\text{'}$ and $\ell_t=2m_t$ if $\rho_a=\text{'}\beta\text{'}$; otherwise choose by a public fair coin.
--
--   The sides $\rho$ of the two-bit game decide which bit of the planted pair is read at the occurrences of $h$.
--
--   **Formalization Note** 0-based times and occurrence numbers (the paper's $a\le k$ is $a<k$); a public coin $c_t$ is drawn for every $t$ (unused coins do not change the law). `piLLaw` is the joint law of $(h,(m_t),(c_t),\rho)$ with $\rho$ uniform as in the two-bit game.
-- source:
--   Garg, Sundaresan, Velusamy, XOR-Functions and Beyond in the Random Query Model, arXiv:2611.04353, §4.2, protocol π_L, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_ShallowShadows_ShadowNorm_uniformDist
import Definitions.Def_RandomQueryXOR_uniformOn
import Definitions.Def_RandomQueryXOR_sens
import Definitions.Def_RandomQueryXOR_xorLift

set_option autoImplicit false
set_option synthInstance.maxSize 2048

namespace RandomQueryXOR

open WildeQIT
open ShallowShadows.ShadowNorm (uniformDist)

/-- The number of times `s < t` with `m_s = h` (so `m_t = h` is occurrence number
`occBefore h m t` of `h`, counted from `0`). -/
def occBefore {n T : ℕ} (h : Fin n) (m : Fin T → Fin n) (t : Fin T) : ℕ :=
  (Finset.univ.filter fun s : Fin T => s < t ∧ m s = h).card

/-- The number of occurrences `|{t ∈ [T] : m_t = h}|` of `h` in `(m_t)_{t ∈ [T]}`. -/
def occCount {n T : ℕ} (h : Fin n) (m : Fin T → Fin n) : ℕ :=
  (Finset.univ.filter fun s : Fin T => m s = h).card

/-- The index `2i − 1` (`b = false`) or `2i` (`b = true`) of the `i`-th pair, 0-based. -/
def pairIdx {n : ℕ} (i : Fin n) (b : Bool) : Fin (2 * n) :=
  if b then pairSnd i else pairFst i

/-- The index sequence `L = (ℓ_1, …, ℓ_T)` produced by protocol π_L (Garg, Sundaresan, Velusamy,
*XOR-Functions and Beyond in the Random Query Model*, arXiv:2611.04353, p.19 = PDF p.21):
"(iii) For each t ∈ [T]: • If m_t ≠ h, set ℓ_t as one of 2m_t − 1 or 2m_t at random with public
randomness. • If m_t = h, then let this be the a-th occurrence of h in the sequence of m_t
values. If a ≤ k, we set ℓ_t = 2m_t − 1 if ρ_a = 'α' and ℓ_t = 2m_t if ρ_a = 'β'. Otherwise, we
set ℓ_t to be one of 2m_t − 1 or 2m_t at random using public randomness."

**Formalization Note** 0-based: time `t : Fin T`, occurrence number `a` counted from `0` (the
paper's `a ≤ k` is `a < k`), player `ρ ⟨a, _⟩`; `ρ_a = false` is 'α' (index `2h − 1`,
`pairFst h`). The public coin choosing between `2m_t − 1` and `2m_t` is `c t` (`false` ↦
`2m_t − 1`), drawn for every `t` (unused coins do not change the law). -/
def piL {n T : ℕ} (k : ℕ) (h : Fin n) (m : Fin T → Fin n) (c : Fin T → Bool)
    (ρ : Fin k → Bool) : Fin T → Fin (2 * n) := fun t =>
  if m t = h then
    if hk : occBefore h m t < k then pairIdx h (ρ ⟨occBefore h m t, hk⟩)
    else pairIdx (m t) (c t)
  else pairIdx (m t) (c t)

/-- The randomness of π_L: the special index `h`, the sequence `(m_t)`, the public coins
`(c_t)` and the sides `ρ = (ρ_1, …, ρ_k)` of the two-bit game. -/
abbrev PiLSpace (n T k : ℕ) := Fin n × (Fin T → Fin n) × (Fin T → Bool) × (Fin k → Bool)

/-- The law of the randomness of π_L (arXiv:2611.04353, p.19 = PDF p.21): "(i) Pick a special
index h ∈ [n] uniformly at random from {i ∈ [n] | x⋆_f(i) = 0 and f(x⋆_f) ≠ f(x⋆_f ⊕ e_i)} …
(ii) For each t ∈ [T], sample m_t uniform over [n] with public randomness."; the coins `c_t` are
fair and `ρ_a` uniform on {'α', 'β'} (Definition 4.5), all independent. Requires the set of
sensitive zeros of `x⋆ = xs` to be nonempty. -/
noncomputable def piLLaw {n T : ℕ} (f : (Fin n → Bool) → Bool) (xs : Fin n → Bool) (k : ℕ)
    (hZ : (sensZeros f xs).Nonempty) : FinDist (PiLSpace n T k) :=
  haveI : Nonempty (Fin n) := ⟨hZ.choose⟩
  (uniformOn (sensZeros f xs) hZ).prod ((uniformDist (Fin T → Fin n)).prod
    ((uniformDist (Fin T → Bool)).prod (uniformDist (Fin k → Bool))))

end RandomQueryXOR


