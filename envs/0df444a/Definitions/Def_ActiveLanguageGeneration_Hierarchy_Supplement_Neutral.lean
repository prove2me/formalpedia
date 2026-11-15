-- Prove2me | Definitions.Def_ActiveLanguageGeneration_Hierarchy_Supplement_Neutral
-- name    : ActiveLanguageGeneration_Hierarchy_Supplement_Neutral
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T05:20:23.907285+00:00
-- url     : https://prove2.me/theorems/b3c26f0f-3b97-4b44-aae7-f7a674631288
-- title:
--   Neutral enumeration, neutral k-generation and neutral generation in the limit
-- statement:
--   Let $U$ be a universe of strings carrying a fixed global ordering $u_1\prec u_2\prec\cdots$ of order type $\omega$. For an infinite language $L\subseteq U$, the **neutral enumeration** of $L$ lists the elements of $L$ in increasing $\prec$-order; it is the unique full, repetition-free enumeration $x_1,x_2,\ldots$ of $L$ with $x_1\prec x_2\prec\cdots$.
--
--   Fix a repetition convention $q\in\{\mathrm R,\mathrm{NR}\}$ (correctness $G(x_1,\ldots,x_t)\in L\setminus\{x_1,\ldots,x_t\}$, and for NR additionally $G(x_1,\ldots,x_t)\notin\{G(x_1,\ldots,x_j):1\le j<t\}$). For a positive integer $k$, a collection $C$ is **neutrally $k$-generatable** under $q$ if one generator $G$ is $q$-correct at every time $t\ge k$ on the neutral enumeration of every $L\in C$. It is **neutrally generatable in the limit** under $q$ if one generator $G$ has, for every $L\in C$, a finite time $t^\star\ge1$ after which it is $q$-correct on the neutral enumeration of $L$:
--
--   $$
--   \exists G\ \forall L\in C\ \exists t^\star\ \forall t\ge t^\star:\ \operatorname{Correct}_q(G,L,x^{\prec}_L,t).
--   $$
--
--   These are the neutral classes $\mathrm{Neu}_{\mathrm R}$ and $\mathrm{Neu}_{\mathrm{NR}}$ of the paper, compared with the active and adversarial classes throughout the mission.
--
--   **Formalization Note** The ordering is a `LinearOrder` on $U$; theorems add `LocallyFiniteOrderBot U` and `Infinite U`, which make it of order type $\omega$. The neutral enumeration is the predicate "injective, range exactly $L$, strictly monotone"; the generatability predicates quantify over every enumeration with this property, which on an $\omega$-ordered universe is exactly one. Stream index $n$ is time $t=n+1$. Thresholds are positive.
-- source:
--   Debmalya Panigrahi, Fan Wei, Ian Zhang, STOC 2027 submission #1167 (October 2026), Language Generation Beyond Adversarial Examples, Definitions 2.3, 2.4, 2.5, 2.7, printed p.5–6 (PDF p.6–7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1167.pdf

import Definitions.Def_ActiveLanguageGeneration_Hierarchy_Language

set_option autoImplicit false

namespace ActiveLanguageGeneration.Hierarchy.Supplement

open ActiveLanguageGeneration.Hierarchy

/-- Definition 2.3, printed p.5 (PDF p.6): the canonical enumeration of `L` induced by the
global ordering `≺` of the universe, i.e. the full injective enumeration listing `L` in
increasing order. On an ω-ordered universe (`[LocallyFiniteOrderBot U]`, as every theorem of
this supplement assumes) it exists and is unique for every infinite `L`, so quantifying over
all `x` with this property is the same as speaking of "the" neutral enumeration. -/
def NeutralEnumeration {U : Type} [LinearOrder U] (L : Language U) (x : ℕ → U) : Prop :=
  IsEnumeration L x ∧ StrictMono x

/-- Definition 2.5 with Definition 2.7: one generator correct, under convention `mode`, at
every time `t ≥ k` on the neutral enumeration of every language of `C`.
Only positive thresholds are in the paper's domain. -/
def NeutralKGeneratable {U : Type} [LinearOrder U] (mode : Repetition)
    (C : LanguageCollection U) (k : ℕ) : Prop :=
  0 < k ∧ ∃ G : Generator U, ∀ L ∈ C, ∀ x : ℕ → U,
    NeutralEnumeration L x → ∀ n : ℕ, k ≤ n + 1 → CorrectAt mode G L x n

/-- Definition 2.4 with Definition 2.7: one generator, and for each language a finite positive
success time on its neutral enumeration. All earlier outputs still count for NR. -/
def NeutralLimitGeneratable {U : Type} [LinearOrder U] (mode : Repetition)
    (C : LanguageCollection U) : Prop :=
  ∃ G : Generator U, ∀ L ∈ C, ∀ x : ℕ → U, NeutralEnumeration L x →
    ∃ tStar : ℕ, 0 < tStar ∧ ∀ n : ℕ, tStar ≤ n + 1 → CorrectAt mode G L x n

end ActiveLanguageGeneration.Hierarchy.Supplement


