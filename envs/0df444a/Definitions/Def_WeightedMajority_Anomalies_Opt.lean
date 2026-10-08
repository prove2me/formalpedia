-- Prove2me | Definitions.Def_WeightedMajority_Anomalies_Opt
-- name    : WeightedMajority_Anomalies_Opt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:38:23.478816+00:00
-- url     : https://prove2.me/theorems/c96a5a8c-716d-485c-9e80-6970e37faf38
-- title:
--   Anomalies, the sequence classes $S_\eta$ and $\mathrm{opt}(F,\eta)$ (Section 8)
-- statement:
--   Let $X$ be an arbitrary domain and let $F$ be a class (pool) of $\{0,1\}$-valued functions on $X$; $F$ may be infinite. A **trial** is a pair $(x, y)$ of an instance $x \in X$ and a label $y \in \{0,1\}$, and a sequence of trials $\mathcal S = ((x_1,y_1),\dots,(x_T,y_T))$ is finite. The same instance may occur several times with different labels.
--
--   1. **Anomalies.** For a function $f : X \to \{0,1\}$, the number of anomalies of $\mathcal S$ with respect to $f$ is the number of trials that are inconsistent with $f$:
--   $$\mathrm{anom}_f(\mathcal S) = \#\{\, t \le T : f(x_t) \ne y_t \,\}.$$
--   2. **The class $S_\eta$.** A sequence has at most $\eta$ anomalies with respect to $F$ when $\min_{f \in F} \mathrm{anom}_f(\mathcal S) \le \eta$, that is, when some $f \in F$ has at most $\eta$ anomalies on it. $S_\eta$ is the collection of all such sequences.
--   3. **The optimal mistake bound.** A deterministic on-line prediction algorithm $A$ predicts, at each trial, a label from the instance and the earlier trials. Writing $M_A(\mathcal S)$ for the number of trials of $\mathcal S$ on which $A$'s prediction differs from the label,
--   $$\mathrm{opt}(F,\eta) = \min_{A}\ \sup_{\mathcal S \in S_\eta} M_A(\mathcal S),$$
--   the minimum over all deterministic algorithms of the worst-case number of mistakes over sequences with at most $\eta$ anomalies; it may be $+\infty$.
--
--   $\mathrm{opt}(F,\eta)$ is the best mistake bound attainable for the class $F$ in the presence of $\eta$ anomalies. For $\eta = 0$ the sequences of $S_0$ are exactly those labelled by some $f \in F$, so $\mathrm{opt}(F,0)$ is the optimal mistake bound of the realizable (noise-free) setting.
--
--   **Formalization Note** Algorithms and mistake counts are those of the published `UnderstandingML_Online` module: an algorithm is any function from the history (the list of earlier trials) and the current instance to a label, and sequences are indexed by `Fin T`. $\mathrm{opt}$ takes values in $\mathbb N \cup \{\infty\}$ (`ℕ∞`), the minimum is an infimum and the maximum a supremum over all lengths $T$ and all sequences. $\eta$ is a natural number.
-- source:
--   Littlestone, Warmuth, The Weighted Majority Algorithm, Inform. and Comput. 108 (1994), pp. 249–250, Section 8 (definitions of anomalies, S_η and opt(F, η)); p. 214, Section 1

import Mathlib
import Definitions.Def_UnderstandingML_Online

namespace WeightedMajority.Anomalies

open UnderstandingML

/-- The number of **anomalies** of the sequence of trials `S` with respect to the function `f`
(Littlestone–Warmuth §8, p. 249): the number of trials `t` whose label `(S t).2` differs from
`f` at the instance `(S t).1`. -/
noncomputable def anomalies {X : Type*} (f : X → Bool) {T : ℕ} (S : Fin T → X × Bool) : ℕ :=
  (Finset.univ.filter (fun t : Fin T ↦ f (S t).1 ≠ (S t).2)).card

/-- `S ∈ S_η` (§8, p. 250): the sequence `S` has at most `η` anomalies with respect to the pool
`F`, i.e. the minimum over `f ∈ F` of the number of anomalies of `S` with respect to `f` is at
most `η`; equivalently some `f ∈ F` has at most `η` anomalies on `S`. -/
def HasAtMostAnomalies {X : Type*} (F : Set (X → Bool)) (η : ℕ) {T : ℕ}
    (S : Fin T → X × Bool) : Prop :=
  ∃ f ∈ F, anomalies f S ≤ η

/-- `opt(F, η)` (§8, p. 250): the minimum over all deterministic online prediction algorithms
`A` of the maximum, over all finite sequences of trials `S ∈ S_η`, of the number of mistakes
made by `A` on `S`. Valued in `ℕ∞`, so it is `⊤` when every algorithm can be forced to make
arbitrarily many mistakes. -/
noncomputable def opt {X : Type*} (F : Set (X → Bool)) (η : ℕ) : ℕ∞ :=
  ⨅ A : OnlineAlg X Bool,
    ⨆ (T : ℕ) (S : Fin T → X × Bool) (_ : HasAtMostAnomalies F η S), (mistakes A S : ℕ∞)

end WeightedMajority.Anomalies


