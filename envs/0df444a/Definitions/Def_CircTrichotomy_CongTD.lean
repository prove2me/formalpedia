-- Prove2me | Definitions.Def_CircTrichotomy_CongTD
-- name    : CircTrichotomy_CongTD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T22:00:56.531104+00:00
-- url     : https://prove2.me/theorems/2acd4c83-53be-4279-9321-cf2fc529b297
-- title:
--   The ordered modular threshold congruence $\mathcal C^{t,d}_k$
-- statement:
--   For $k,t\ge1$, $d\in\mathbb N$ and $u,v\in\Sigma^+$, $u\,\mathcal C^{t,d}_k\,v$ if
--   1. $u\,\mathcal C^t_k\,v$, and
--   2. there is an order-preserving bijection $\beta:R^t_k(u)\cup\{0,|u|-1\}\to R^t_k(v)\cup\{0,|v|-1\}$ such that (a) $(u)_i=(v)_{\beta(i)}$ for all rare positions $i$ of $u$, and (b) $j-i\equiv^d_k\beta(j)-\beta(i)$ for all $i<j$ in the domain.
--
--   So the rare positions, together with the two endpoints, carry the same letters in the same order, with pairwise distances that agree modulo $k$ up to threshold $d$.
--
--   **Formalization Note** $\beta$ is a map $\mathbb N\to\mathbb N$ that is a bijection between the two finite sets and strictly increasing on the first.
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Definition B.4, p.22

import Mathlib
import Definitions.Def_CircTrichotomy_CongT
import Definitions.Def_CircTrichotomy_rarePos

set_option autoImplicit false

namespace CircTrichotomy

/-- **Ordered modular threshold congruence `𝒞^{t,d}_k`** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Definition B.4, p.22): "Let
k, t ∈ ℕ>0 and d ∈ ℕ. The relation 𝒞^{t,d}_k on Σ⁺ is defined as follows: u 𝒞^{t,d}_k v if
(1) u 𝒞^t_k v, and
(2) there is an order-preserving bijection β : R^t_k(u) ∪ {0, |u| − 1} → R^t_k(v) ∪ {0, |v| − 1}
such that
(a) (u)_i = (v)_{β(i)} for all i ∈ R^t_k(u), and
(b) j − i ≡^d_k β(j) − β(i) for all i, j ∈ R^t_k(u) ∪ {0, |u| − 1} such that i < j."

**Formalization Note** `β` is a function `ℕ → ℕ` that is a bijection between the two finite sets
(`Set.BijOn`) and strictly increasing on the first (order-preserving). Since `β` is strictly
increasing, `β(j) − β(i)` for `i < j` is a true (non-truncated) difference. -/
def CongTD {α : Type} (k t d : ℕ) (u v : List α) : Prop :=
  CongT k t u v ∧ ∃ β : ℕ → ℕ,
    Set.BijOn β (rarePos t k u ∪ {0, u.length - 1}) (rarePos t k v ∪ {0, v.length - 1}) ∧
    StrictMonoOn β (rarePos t k u ∪ {0, u.length - 1}) ∧
    (∀ i ∈ rarePos t k u, u[i]? = v[β i]?) ∧
    ∀ i ∈ rarePos t k u ∪ {0, u.length - 1}, ∀ j ∈ rarePos t k u ∪ {0, u.length - 1},
      i < j → thrModEq d k (j - i) (β j - β i)

end CircTrichotomy


