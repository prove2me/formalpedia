-- Prove2me | Definitions.Def_AlmostMMS_load
-- name    : AlmostMMS_load
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:48:39.201685+00:00
-- url     : https://prove2.me/theorems/5c08bc0a-e15f-48d0-ab17-5a7b286edbee
-- title:
--   Definition 2.4, p.12 — the prefix load $P_i(\pi,\ell)$ and $|F\cap[\ell]|$
-- statement:
--   For a demand profile $\pi$, a finite multiset of demands, the **$\ell$-prefix load** is
--   $$
--   P_i(\pi,\ell)=|\{\alpha\in\pi : m_i(\alpha)\le\ell\}|,
--   $$
--   counted with multiplicity: the number of demands of $\pi$ that agent $i$ can satisfy only by the first $\ell$ items. The no-profile $\bot$ has load $0$. The module also defines $|F\cap[\ell]|$, the number of items of $F$ among the first $\ell$ items, against which loads are compared.
--
--   **Formalization Note** $\bot$ is `none` and the empty profile $\emptyset$ is `some 0`; the two are different objects.
-- source:
--   Feige, Grinberg, Almost-MMS allocations with small agent redundancy, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…), Definitions 2.4, 2.5, p.12; Definition 2.14, p.16

import Mathlib
import Definitions.Def_AlmostMMS_bp

namespace AlmostMMS

open Finset

/-- **Prefix load** `P_i(π, ℓ)` (Definition 2.4, p.12): the number of demands of the profile `π`, with
multiplicity, whose breakpoint for agent `i` is at most `ℓ`.
Feige, Grinberg, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…).

**Formalization Note.** Profiles are finite multisets (Definition 2.2), so this is a `Multiset.filter`. -/
noncomputable def load {n m : ℕ} (v : Fin n → Fin m → ℝ) (i : Fin n) (π : Multiset ℝ) (ℓ : ℕ) : ℕ :=
  (π.filter fun α => bp v i α ≤ ℓ).card

/-- Prefix load of an optional profile (Definition 2.14, p.16): the no-profile `⊥`, written `none`,
has load `0`, and the empty profile `∅` is `some 0`. -/
noncomputable def optLoad {n m : ℕ} (v : Fin n → Fin m → ℝ) (i : Fin n) :
    Option (Multiset ℝ) → ℕ → ℕ
  | none, _ => 0
  | some π, ℓ => load v i π ℓ

/-- `|F ∩ [ℓ]|`: the number of items of `F` among the first `ℓ` items (Lemma 2.2, p.12). -/
def prefixCount {m : ℕ} (F : Finset (Fin m)) (ℓ : ℕ) : ℕ :=
  (F.filter fun e => e.val < ℓ).card

end AlmostMMS


