-- Prove2me | Definitions.Def_RvsCert_UC1
-- name    : RvsCert_UC1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:40:36.643206+00:00
-- url     : https://prove2.me/theorems/53caec66-aedf-4997-bde0-d2a42f21a2fb
-- title:
--   Unambiguous 1-certificate complexity $\mathrm{UC}_1(f)$
-- statement:
--   For a Boolean function $f$ on a finite set $\iota$ of bit positions,
--   $$
--   \mathrm{UC}_1(f)=\min_{P}\ \max_{\rho\in P}|\rho|,
--   $$
--   the minimum over unambiguous collections $P$ of 1-certificates of the largest number $|\rho|$ of bits fixed by a member. Every certificate in such a family is a 1-certificate, so $C_1(f)\le\mathrm{UC}_1(f)$.
--
--   **Formalization Note** An infimum of natural numbers; the set is never empty, since the 1-inputs themselves, written as total assignments, form an unambiguous collection.
-- source:
--   Ben-David–Kothari, Randomized query complexity can beat certificate complexity, arXiv:2609.15063v1, Lemma 2, p.2 (standard notion)

import Mathlib
import Definitions.Def_RvsCert_IsUnambiguous1Cover

namespace RvsCert

/-- **Unambiguous 1-certificate complexity** `UC1(f)` (standard; Lemma 2, p.2 of
Ben-David–Kothari, *Randomized query complexity can beat certificate complexity*, arXiv:2609.15063v1): the least `k` such that some unambiguous collection of 1-certificates
of `f` has every member fixing at most `k` bits.

**Formalization Note.** `sInf` in `ℕ`; the set is nonempty for finite `ι` (the family of all
1-inputs, written as total assignments, is an unambiguous cover with members of size `card ι`;
checked in the verification file). -/
noncomputable def UC1 {ι : Type} [Fintype ι] (f : (ι → Bool) → Bool) : ℕ :=
  sInf {k : ℕ | ∃ P : Finset (ι → Option Bool), IsUnambiguous1Cover f P ∧
    ∀ ρ ∈ P, (Finset.univ.filter fun i => (ρ i).isSome).card ≤ k}

end RvsCert


