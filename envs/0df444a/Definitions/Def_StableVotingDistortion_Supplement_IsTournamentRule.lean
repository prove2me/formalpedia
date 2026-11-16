-- Prove2me | Definitions.Def_StableVotingDistortion_Supplement_IsTournamentRule
-- name    : StableVotingDistortion_Supplement_IsTournamentRule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:55:59.153967+00:00
-- url     : https://prove2.me/theorems/ce2e6ead-5a15-4a68-b5db-4d613a301280
-- title:
--   $\ell$-tournament rules and lower bounds on the distortion of a voting rule
-- statement:
--   A **randomized voting rule** $f$ assigns to every election with $n\ge1$ voters and $m\ge1$ candidates (labelled $1,\dots,n$ and $1,\dots,m$) a lottery over its candidates.
--
--   For a set $S$ of candidates and an ordering $c_1\succ c_2\succ\dots\succ c_j$ of $S$, the **ordering fraction** of an election is the fraction of its voters whose ranking restricted to $S$ is that ordering, $\Pr_{v\sim V}[c_1\succ_v c_2\succ_v\dots\succ_v c_j]$.
--
--   A rule $f$ is an **$\ell$-tournament rule** if it only sees the aggregate rankings of tuples of at most $\ell$ candidates: whenever two elections on the same candidate set and with the same number of voters have the same ordering fraction for every set $S$ with $|S|\le\ell$ and every ordering of $S$, $f$ returns the same lottery on both.
--
--   A rule $f$ has **metric distortion at least $x$** if no $B<x$ bounds its distortion: for every $B<x$ there are an election $E$, a pseudometric $d$ consistent with $E$ and a candidate $a$ with $\mathrm{cost}_d(f(E))>B\cdot\mathrm{cost}_d(a)$.
--
--   These are the objects of the small-tournament lower bound, Theorem 9.
--
--   **Formalization Note** A rule is the platform's `RandomSizeStable.Stability.VotingRule` (one family on every `Election (Fin n) (Fin m)`). An ordering of $S$ with $|S|=j$ is an injective listing $\sigma:\{0,\dots,j-1\}\to C$. The rule's information is the voters' ordering distribution on each small set (the paper's "distribution of the voters' orderings"); invariance is required only between elections with the same number of voters, where equal fractions are equal counts, so the class contains every rule that sees only fractions and every rule that sees only counts. No neutrality or anonymity is assumed.
-- source:
--   Cai, Frank, Hastings, Ramakrishnan, Wang, Ye, Stable Voting Rules on the Edge of Optimal Metric Distortion, arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §1, p.4; Appendix B, p.40 and footnote 15

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_StableVotingDistortion_HasDistortionAtMost
import Definitions.Def_RandomSizeStable_Stability_VotingRule

set_option autoImplicit false

open PctDistortion

namespace StableVotingDistortion.Supplement

open Classical in
/-- The fraction of voters of `E` whose ranking, restricted to the candidates `σ 0, …, σ (j − 1)`, is the
ordering `σ 0 ≻ σ 1 ≻ ⋯ ≻ σ (j − 1)`: `Pr_{v ∼ V}[σ 0 ≻_v σ 1 ≻_v ⋯ ≻_v σ (j−1)]`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Appendix B, p.40: "the distribution of the
voters' orderings of S"; footnote 15, p.40: "the quantities Pr_{v∼V}[a ≻_v b1, . . . , bj]".

**Formalization Note.** An ordering of a set `S` of `j` candidates is an injective listing `σ : Fin j → Fin m`
from best to worst. The voter count is `n`; the fraction is a count divided by `n`. -/
noncomputable def orderFraction {n m : ℕ} (E : Election (Fin n) (Fin m)) {j : ℕ} (σ : Fin j → Fin m) : ℝ :=
  ((Finset.univ.filter (fun v : Fin n => ∀ i i' : Fin j, i < i' → E.prefers v (σ i) (σ i'))).card : ℝ) / n

/-- `f` is an **`ℓ`-tournament rule**: a randomized voting rule that only sees the aggregate rankings of tuples of
at most `ℓ` candidates. Two elections on the same candidates and the same number of voters that have, for every
set `S` of at most `ℓ` candidates and every ordering of `S`, the same fraction of voters ordering `S` that way, get
the same lottery.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §1, p.4: "k-tournament rules, which only see the
aggregate rankings of tuples of k candidates"; Appendix B, p.40: "for every set S with |S| ≤ ℓ, the distribution
of the voters' orderings of S … no ℓ-tournament rule can distinguish among the m + 1 candidates".

**Formalization Note.** A randomized voting rule is the platform's `RandomSizeStable.Stability.VotingRule`: one
family of maps on every `Election (Fin n) (Fin m)`, `n, m > 0`, returning a lottery. The rule's information is
the voters' ordering distribution on each small set; no neutrality, anonymity or other property is assumed.
The invariance is required only between elections with the same number `n` of voters (where equal fractions
are equal counts). This covers both readings of "sees the aggregate rankings" (fractions, or counts): every
rule determined by the fractions satisfies it, so Theorem 9 stated for this class implies it for the
fraction-only class; the paper's proof (Corollary 13, p.41) compares only an election with its relabelings,
which have the same `n`. -/
def IsTournamentRule (ℓ : ℕ) (f : RandomSizeStable.Stability.VotingRule) : Prop :=
  ∀ (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (E E' : Election (Fin n) (Fin m)),
    (∀ j ≤ ℓ, ∀ σ : Fin j → Fin m, Function.Injective σ → orderFraction E σ = orderFraction E' σ) →
      (f n m hn hm E).1 = (f n m hn hm E').1

/-- The randomized voting rule `f` has **metric distortion at least `x`**: for every `B < x` some election (finite,
nonempty) has a consistent pseudometric under which `f`'s lottery violates the bound `B`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §2, p.6: "distortion(f) := sup_E sup_{d consistent
with E} cost_d(f(E)) / min_{a∈C} cost_d(a)".

**Formalization Note.** `distortion(f) ≥ x` is written as: no `B < x` is a valid bound, with the base mission's
inequality form `HasDistortionAtMost` of a bound. -/
def RuleDistortionAtLeast (f : RandomSizeStable.Stability.VotingRule) (x : ℝ) : Prop :=
  ∀ B < x, ∃ (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (E : Election (Fin n) (Fin m)),
    ¬ HasDistortionAtMost E (f n m hn hm E).1 B

end StableVotingDistortion.Supplement


