-- Prove2me | Definitions.Def_StableCount_Count
-- name    : StableCount_Count
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:47:36.595115+00:00
-- url     : https://prove2.me/theorems/33980d8e-b675-48d5-bb53-97049a1c11fa
-- title:
--   The number $s(I)$ of stable matchings, the maximum $\mathrm{SM}(n)$ and the partner counts $D^m_v$, $D^w_v$
-- statement:
--   Let $I$ be a stable matching instance with $n$ men and $n$ women, each with a strict ranking of the other set. A matching is stable if no man and woman each prefer the other to their assigned partner. Then
--
--   1. $s(I)$ is the number of stable matchings of $I$;
--   2. $\mathrm{SM}(n)$ is the maximum of $s(I)$ over all instances with $n$ men and $n$ women;
--   3. a stable partner of a person is a partner occurring in at least one stable matching, and $D^m_v$, $D^w_v$ are the numbers of stable partners of man $v$ and of woman $v$.
--
--   These are the quantities bounded by the main theorem of the paper.
--
--   **Formalization Note** Instances, matchings and stability are the published `StableMatching.Instance`, `StableMatching.Matching` and `StableMatching.Instance.IsStable`. $\mathrm{SM}(n)$ is `sSup` in `ℕ` of a nonempty set bounded by $n!$, hence a maximum. Man $v$ and woman $v$ are unrelated: both sides are indexed by `Fin n`.
-- source:
--   Ghorbani, Mnich, A 2.81^n upper bound on the number of stable matchings, arXiv:2611.06494 (held PDF sha256 9445f6a8…), §1, p.1; Theorem 1, p.2

import Mathlib
import Definitions.Def_StableMatching_GaleShapley

namespace StableCount

open StableMatching

variable {n : ℕ}

/-- `s(I)`, the number of stable matchings of the instance `I` (Ghorbani, Mnich, *A 2.81ⁿ upper
bound on the number of stable matchings*, arXiv:2611.06494, held PDF sha256 9445f6a8…, §1, p.1).

**Formalization Note** Instances, matchings and stability are the published
`StableMatching.Instance`, `StableMatching.Matching` and `StableMatching.Instance.IsStable`, with men
and women both indexed by `Fin n` and strict preferences given by rank bijections. -/
def numStable (I : Instance n) : ℕ := Fintype.card {μ : Matching n // I.IsStable μ}

/-- `SM(n)`, the maximum of `s(I)` over all instances with `n` men and `n` women
(arXiv:2611.06494, held PDF sha256 9445f6a8…, §1, p.1).

**Formalization Note** This is `sSup` in `ℕ`. The set of values is nonempty and bounded by `n!`, so
the supremum is the maximum; it is not a junk value. -/
noncomputable def SM (n : ℕ) : ℕ := sSup (Set.range (numStable (n := n)))

/-- The stable partners of man `v`: the women matched to him in at least one stable matching
(arXiv:2611.06494, held PDF sha256 9445f6a8…, §1, p.1). -/
def manPartners (I : Instance n) (v : Fin n) : Finset (Fin n) :=
  (Finset.univ.filter fun μ : Matching n => I.IsStable μ).image fun μ => μ v

/-- The stable partners of woman `w`: the men matched to her in at least one stable matching
(arXiv:2611.06494, held PDF sha256 9445f6a8…, §1, p.1). -/
def womanPartners (I : Instance n) (w : Fin n) : Finset (Fin n) :=
  (Finset.univ.filter fun μ : Matching n => I.IsStable μ).image fun μ => μ.symm w

/-- `Dᵐ_v`, the number of stable partners of man `v` (arXiv:2611.06494, held PDF sha256 9445f6a8…,
Theorem 1, p.2). -/
def Dm (I : Instance n) (v : Fin n) : ℕ := (manPartners I v).card

/-- `Dʷ_v`, the number of stable partners of woman `v` (arXiv:2611.06494, held PDF sha256
9445f6a8…, Theorem 1, p.2). -/
def Dw (I : Instance n) (w : Fin n) : ℕ := (womanPartners I w).card

end StableCount


