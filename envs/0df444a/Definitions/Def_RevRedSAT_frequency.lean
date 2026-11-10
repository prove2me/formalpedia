-- Prove2me | Definitions.Def_RevRedSAT_frequency
-- name    : RevRedSAT_frequency
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:45:37.18199+00:00
-- url     : https://prove2.me/theorems/0dcde3a4-316c-4e72-bbd8-39b385c3a1f5
-- title:
--   Rank, frequency and support of a set family (Definition 6.1)
-- statement:
--   **Definition 6.1.** Let $\mathcal F\subseteq 2^U$ be a set family. It has **rank at most $d$** if every set in $\mathcal F$ has size at most $d$. Its **frequency** is the maximum, over $u\in U$, of the number of sets containing $u$, with value zero when $U$ is empty. Its **support** is
--
--   $$\operatorname{supp}(\mathcal F)=\bigcup_{F\in\mathcal F}F,$$
--
--   the elements occurring in at least one set.
--
--   **Formalization Note** The universe is $\{0,\dots,n-1\}$; rank is written as a hypothesis $|S|\le d$ for all $S\in\mathcal F$.
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Definition 6.1, p.39

import Mathlib

set_option autoImplicit false

namespace RevRedSAT

/-- **Frequency of a set family (Definition 6.1).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Definition 6.1, p.39: "Let
F ⊆ 2^U be a set family. It has rank at most d if every set in F has size at most d. Its frequency is
the maximum, over u ∈ U, of the number of sets containing u, with value zero when U is empty. Its
support is supp(F) = ⋃_{F∈F} F, the elements occurring in at least one set."

**Formalization Note** The universe is `Fin n`; rank at most `d` is written `∀ S ∈ F, S.card ≤ d`
in the statements. -/
def frequency {n : ℕ} (F : Finset (Finset (Fin n))) : ℕ :=
  Finset.univ.sup fun u => (F.filter fun S => u ∈ S).card

/-- The support `supp(F) = ⋃_{F ∈ F} F` (Definition 6.1, p.39). -/
def supp {n : ℕ} (F : Finset (Finset (Fin n))) : Finset (Fin n) :=
  F.biUnion id

end RevRedSAT


