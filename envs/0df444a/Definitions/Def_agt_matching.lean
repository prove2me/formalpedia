-- Prove2me | Definitions.Def_agt_matching
-- name    : agt_matching
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-13T03:10:35.661681+00:00
-- url     : https://prove2.me/theorems/810786a8-9059-44d7-9ed4-cfb0e89bddb0
-- title:
--   Matchings, stability, cores, and house allocation
-- statement:
--   This bundle fixes the two-sided matching and house allocation vocabulary of §§10.3–10.4 of *Algorithmic Game Theory* (Schummer–Vohra). Preferences are the strict total orders of the Mission III bundle (`IsPrefProfile`), with $P\,i\,a\,b$ reading "$i$ strictly prefers $a$ to $b$"; following the book's dummy-partner convention $|M| = |W|$, a matching is a bijection $\mu : M \simeq W$.
--
--   1. **`IsBlockingPair`** — $(m,w)$ blocks $\mu$ when $m$ prefers $w$ to his partner $\mu(m)$ and $w$ prefers $m$ to her partner $\mu^{-1}(w)$ (§10.4).
--   2. **`IsStableMatching`** — no pair blocks $\mu$.
--   3. **`IsMaleOptimal`** — $\mu$ is stable and every man weakly prefers $\mu$ to every stable alternative: Gale–Shapley's *optimal assignment* (1962, Theorem 2), the property of the male-propose Deferred Acceptance outcome. The book's own definition (p. 257) is the weaker no-Pareto-improvement form — no stable $\nu$ makes every man weakly and some man strictly better off; for finite strict markets the two are equivalent, but the equivalence is a theorem, so the definition is attributed to Gale–Shapley rather than to the book's phrasing.
--   4. **`MatchDominated`** — a coalition can defect: some rematching $\nu$ and nonempty set $S$ of men such that every man in $S$ strictly prefers his new partner and every new partner strictly prefers her new man; the core is the set of undominated matchings.
--   5. **`HouseBlocked`** — §10.3: a nonempty coalition $S$ can redistribute the houses its members own — a permutation mapping $S$ into itself — leaving every member weakly and some member strictly better off; the core is the set of unblocked allocations.
--
--   *A note on conventions.* Algorithm-defined objects (deferred acceptance, top trading cycles) enter only through the properties characterizing their outputs — male-optimality, core membership — never as code; the mission's theorems are about every mechanism with the given property. Coalitions are encoded by a full rematching `Equiv` plus the improving set, closed under the rematching; pairs and singletons are special cases.
-- source:
--   N. Nisan, T. Roughgarden, E. Tardos, V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press 2007, https://doi.org/10.1017/CBO9780511800481, Ch. 10, Sections 10.3-10.4, pp. 253-258

import Definitions.Def_agt_social
import Mathlib.Logic.Equiv.Basic

/-!
Two-sided matching and house allocation, following Chapter 10
(Schummer–Vohra, "Mechanism Design without Money") of
Nisan–Roughgarden–Tardos–Vazirani (eds.), *Algorithmic Game Theory* (2007),
§§10.3–10.4.

A set `M` of men and a set `W` of women; each agent holds a strict
preference ordering over the opposite side, reusing the preference-profile
vocabulary of the social-choice bundle (`IsPrefProfile`), with `P i a b`
reading "`i` strictly prefers `a` to `b`".  Following the book's dummy-agent
convention — being single is represented by a dummy partner, so
`|M| = |W|` may always be assumed — a **matching** is a bijection `M ≃ W`.

The house allocation problem of §10.3 has agents `N`, agent `i` owning
house `i` and holding a strict preference over all houses (identified with
`N`); an **allocation** is a permutation of `N`.
-/

namespace AGT

variable {M W : Type*}

/-- `(m, w)` is a **blocking pair** for the matching `μ` (§10.4): `m`
prefers `w` to his partner and `w` prefers `m` to hers. -/
def IsBlockingPair (PM : M → W → W → Prop) (PW : W → M → M → Prop)
    (μ : M ≃ W) (m : M) (w : W) : Prop :=
  PM m w (μ m) ∧ PW w m (μ.symm w)

/-- A matching is **stable** if it admits no blocking pair (§10.4). -/
def IsStableMatching (PM : M → W → W → Prop) (PW : W → M → M → Prop)
    (μ : M ≃ W) : Prop :=
  ∀ m w, ¬ IsBlockingPair PM PW μ m w

/-- A stable matching is **male-optimal** if every man likes it at least as
much as any other stable matching — Gale–Shapley's notion of an *optimal*
assignment (Gale–Shapley 1962, Theorem 2), the property of the male-propose
Deferred Acceptance outcome.

The book's own definition (p. 257, before Theorem 10.11) is the weaker
no-Pareto-improvement form: no stable `ν` makes every man weakly and some
man strictly better off.  For finite markets with strict preferences the
two are equivalent — the man-by-man optimum exists, and any
Pareto-undominated stable matching differing from it would be strictly
improved somewhere by it — but the equivalence is a theorem, not a
rephrasing, so this definition is attributed to Gale–Shapley and not to
the book's phrasing. -/
def IsMaleOptimal (PM : M → W → W → Prop) (PW : W → M → M → Prop)
    (μ : M ≃ W) : Prop :=
  IsStableMatching PM PW μ ∧
    ∀ ν : M ≃ W, IsStableMatching PM PW ν →
      ∀ m, μ m = ν m ∨ PM m (μ m) (ν m)

/-- The matching `μ` is **dominated** (blocked by a coalition, §10.4): some
rematching `ν` and nonempty set `S` of men exist such that every man in `S`
strictly prefers his new partner and every new partner strictly prefers her
new man — the men of `S` and their `ν`-partners can jointly defect.  The
**core** of the matching game is the set of undominated matchings. -/
def MatchDominated (PM : M → W → W → Prop) (PW : W → M → M → Prop)
    (μ : M ≃ W) : Prop :=
  ∃ (ν : M ≃ W) (S : Set M), S.Nonempty ∧
    (∀ m ∈ S, PM m (ν m) (μ m)) ∧
    (∀ m ∈ S, PW (ν m) m (μ.symm (ν m)))

/-- The allocation `σ` of the house allocation problem is **blocked**
(§10.3): a nonempty coalition `S` can reallocate the houses its members
own — a permutation `τ` mapping `S` into itself — so that every member is
weakly better off and some member strictly.  The **core** is the set of
unblocked allocations. -/
def HouseBlocked {N : Type*} (P : N → N → N → Prop) (σ : N ≃ N) : Prop :=
  ∃ (S : Set N) (τ : N ≃ N), S.Nonempty ∧ (∀ i ∈ S, τ i ∈ S) ∧
    (∀ i ∈ S, τ i = σ i ∨ P i (τ i) (σ i)) ∧
    (∃ i ∈ S, P i (τ i) (σ i))

end AGT


