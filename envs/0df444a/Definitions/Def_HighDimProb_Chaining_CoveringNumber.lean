-- Prove2me | Definitions.Def_HighDimProb_Chaining_CoveringNumber
-- name    : HighDimProb_Chaining_CoveringNumber
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:01:49.770986+00:00
-- url     : https://prove2.me/theorems/2874d254-a7d8-4245-b3e9-01b67224d4fa
-- title:
--   The covering number $N(T,d,\varepsilon)$ of a metric space
-- statement:
--   This is the **covering number** of a metric space, the measure of metric size that Dudley's
--   integral inequality (Theorem 8.1.3) integrates over all scales $\varepsilon$.
--
--   Let $(T,d)$ be a metric space and $\varepsilon > 0$. A subset $N \subseteq T$ is an
--   $\varepsilon$-net of $T$ if every point of $T$ is within distance $\varepsilon$ of some point
--   of $N$, i.e. $\forall t \in T\ \exists t' \in N : d(t,t') \le \varepsilon$. The covering
--   number $N(T,d,\varepsilon)$ is the smallest possible cardinality of a (finite) $\varepsilon$-net
--   of $T$; if $T$ admits no finite $\varepsilon$-net, $N(T,d,\varepsilon) := \infty$.
--
--   **Formalization Note** The value is taken in `ℕ∞ = WithTop ℕ`, as the infimum, over the
--   subtype of finite $\varepsilon$-nets of $T$, of their cardinality — the infimum of an empty
--   family in a complete lattice is $\top$, reproducing the book's own convention with no case
--   split. The metric $d$ is the ambient `MetricSpace T` instance's `dist`, matching Theorem
--   8.1.3's own hypothesis of a genuine metric space $(T,d)$ (as opposed to the pseudometric
--   convention used for the canonical metric of Chapter 7). This is this chunk's own copy of the
--   same-named definition already built for `06-gaussian-processes`: that chunk's copy is still a
--   draft (not in `missions/README.md`'s published-definitions list), so per `CAPTAIN_BRIEF.md`
--   Addendum 2 rule 5 it is redefined here rather than imported.
-- source:
--   Vershynin, High-Dimensional Probability (2018), p. 81, Definition 4.2.2 (K := T); used in Chapter 8, p. 188 and p. 205

import Mathlib

namespace HighDimProb.Chaining

/-- The **covering number** `N(T, d, ε)`: the smallest cardinality of an `ε`-net of `T` in the
metric `d = dist` of the ambient `MetricSpace T` instance, i.e. of a finite `N ⊆ T` such that
every point of `T` is within distance `ε` of some point of `N`. Vershynin, *High-Dimensional
Probability* (2018), p. 81 (PDF p. 89), Definition 4.2.2 (`K := T`), used throughout Chapter 8
(Section 8.1, p. 188, PDF p. 196; Section 8.3.4, p. 205, PDF p. 213). Valued in `ℕ∞ = WithTop ℕ`:
taking the infimum of `Finset.card` over the subtype of finite `ε`-nets gives the book's own
convention that `N(T, d, ε) := ∞` when `T` admits no finite `ε`-net, since the infimum of an
empty family in a complete lattice is `⊤`. This chunk's own copy of the definition already built
for `06-gaussian-processes` (`HighDimProb.RandomProcesses.coveringNumber`, taking `d` as an
explicit function): that chunk's definitions are still drafts (not in `missions/README.md`'s
published list), so per `CAPTAIN_BRIEF.md` Addendum 2 rule 5 this chapter redefines its own copy,
here fixing `d := dist` from a `MetricSpace T` instance rather than an explicit metric function,
since Theorem 8.1.3 is stated for a genuine metric space `(T,d)`. -/
noncomputable def coveringNumber (T : Type) [MetricSpace T] (ε : ℝ) : ℕ∞ :=
  ⨅ (N : {s : Finset T // ∀ t : T, ∃ t' ∈ s, dist t t' ≤ ε}), (N.1.card : ℕ∞)

end HighDimProb.Chaining


