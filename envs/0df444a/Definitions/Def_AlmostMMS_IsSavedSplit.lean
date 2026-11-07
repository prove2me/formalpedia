-- Prove2me | Definitions.Def_AlmostMMS_IsSavedSplit
-- name    : AlmostMMS_IsSavedSplit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:48:36.169198+00:00
-- url     : https://prove2.me/theorems/9e42aab5-75b8-4fc6-a8a9-34d876a0d2a7
-- title:
--   Definition 4.3, Lemma 4.1, pp.34, 32 — protected prefixes and the saved-items property
-- statement:
--   Write $S=\{a_1,\dots,b_1\}\cup\dots\cup\{a_t,\dots,b_t\}$ with each $[a_s,b_s]$ a maximal consecutive interval. The **protected prefixes** are $L_S=\{b_s:s\in[t]\}$.
--
--   The triple $(W,S,\eta)$ has the **saved-items property** if $1\in S$ and, with $E=M-S$, for every $i\notin W$ and $\alpha\in Q$ such that the breakpoint $\ell=m_i(\alpha)$ belongs to $E$:
--
--   1. $\ell\ge\eta$, and $\{\ell-\eta+1,\dots,\ell\}\subseteq E$;
--   2. $|\{(i',\alpha'):i'\in N,\ \alpha'\in Q,\ \ell-\eta<m_{i'}(\alpha')\le\ell\}|\le n/2$.
--
--   **Formalization Note** $b_s$ is a one-based item number, and $t$ is the cardinality of $L_S$.
-- source:
--   Feige, Grinberg, Almost-MMS allocations with small agent redundancy, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…), Definition 4.3, p.34; Lemma 4.1, p.32

import Mathlib
import Definitions.Def_AlmostMMS_bp
import Definitions.Def_AlmostMMS_Q

namespace AlmostMMS

open Finset

/-- **Protected prefixes** `L_S = {b_s : s ∈ [t]}` (Definition 4.3, p.34), where
`S = {a₁, …, b₁} ∪ … ∪ {a_t, …, b_t}` is the decomposition into maximal consecutive intervals.
Feige, Grinberg, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…).

**Formalization Note.** `b_s` is a one-based item number. It is `e.val + 1` for the items `e ∈ S` whose
successor is not in `S`, one for each maximal interval, so the number of intervals `t` is the
cardinality of this set. -/
def protectedPrefixes {m : ℕ} (S : Finset (Fin m)) : Finset ℕ :=
  (S.filter fun e => ∀ e' ∈ S, e'.val ≠ e.val + 1).image fun e => e.val + 1

open Classical in
/-- **The property of saved items** (Lemma 4.1, p.32): the first item is in `S`, and for every `i ∉ W`
and `α ∈ Q`, if the breakpoint `ℓ = m_i(α)` belongs to `E = Sᶜ`, then `ℓ ≥ η`, the items
`ℓ - η + 1, …, ℓ` belong to `E`, and `|{(i', α') : α' ∈ Q, ℓ - η < m_{i'}(α') ≤ ℓ}| ≤ n/2`.

**Formalization Note.** "`ℓ` belongs to `E`" means `ℓ ≥ 1` and the item at position `ℓ - 1` is not in
`S`; here `e` is that item, so `ℓ = e.val + 1`. The conditions `ℓ - η < x` are written `ℓ < x + η`, so
no natural subtraction occurs. -/
def IsSavedSplit {n m : ℕ} (v : Fin n → Fin m → ℝ) (q : ℕ) (W : Finset (Fin n)) (S : Finset (Fin m))
    (η : ℕ) : Prop :=
  (∀ e : Fin m, e.val = 0 → e ∈ S) ∧
  ∀ i, i ∉ W → ∀ α ∈ Q q, ∀ e : Fin m, e.val + 1 = bp v i α → e ∉ S →
    η ≤ e.val + 1 ∧
    (∀ e' : Fin m, e.val + 1 < e'.val + 1 + η → e'.val ≤ e.val → e' ∉ S) ∧
    ((((univ : Finset (Fin n)) ×ˢ Q q).filter fun p =>
        e.val + 1 < bp v p.1 p.2 + η ∧ bp v p.1 p.2 ≤ e.val + 1).card : ℝ) ≤ (n : ℝ) / 2

end AlmostMMS


