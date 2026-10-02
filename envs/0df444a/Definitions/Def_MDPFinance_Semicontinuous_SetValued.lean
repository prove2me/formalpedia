-- Prove2me | Definitions.Def_MDPFinance_Semicontinuous_SetValued
-- name    : MDPFinance_Semicontinuous_SetValued
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T20:24:02.823614+00:00
-- url     : https://prove2.me/theorems/463ffa94-bcb5-4bab-bbc8-c726a2d23b39
-- title:
--   Semicontinuity and continuity of a set-valued mapping
-- statement:
--   A set-valued mapping $x \mapsto D(x) \subseteq A$ is **upper semicontinuous** (Definition
--   A.2.1a, Appendix A.2) if, for every $x$: whenever $x_n \to x$ and $a_n \in D(x_n)$ for all $n$,
--   the sequence $(a_n)$ has an accumulation point in $D(x)$. It is **lower semicontinuous**
--   (Definition A.2.1b) if, for every $x$: whenever $x_n \to x$, every point of $D(x)$ is an
--   accumulation point of some sequence $a_n \in D(x_n)$. It is **continuous** (Definition A.2.1c)
--   if it is both.
--
--   These notions govern whether the admissible-action correspondence $x \mapsto D_n(x)$ behaves
--   well enough, as $x$ varies, for the maximal-reward operator $T_n$ to inherit semicontinuity or
--   continuity from the one-stage data — the content of Proposition 2.4.3/Theorem 2.4.6 (upper
--   semicontinuous case) and Proposition 2.4.8/Theorem 2.4.10 (continuous case) in this mission.
--
--   **Formalization Note.** Formalized with the book's own sequential definition rather than
--   Mathlib's neighborhood-filter-based `UpperHemicontinuous`/`LowerHemicontinuous` for
--   correspondences, which the book's own remark (p. 351) notes is "slightly more restrictive" than
--   other definitions in the literature — using the book's own wording avoids silently adopting a
--   different, non-equivalent notion of set-valued continuity.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 351, Definition A.2.1

import Mathlib

open Filter Topology

namespace MDPFinance.Semicontinuous

variable {E A : Type*} [TopologicalSpace E] [TopologicalSpace A]

/-- A set-valued mapping `x ↦ D(x)` is upper semicontinuous (Bäuerle–Rieder, Definition A.2.1a,
p. 351, PDF 358, Appendix A.2): for every `x`, if `xₙ → x` and `aₙ ∈ D(xₙ)` for all `n`, then
`(aₙ)` has an accumulation point in `D(x)`. Stated with sequences, exactly as the book's own
Appendix A.2 defines it (its own remark: "slightly more restrictive than other definitions
appearing in the literature", so Mathlib's neighborhood-filter-based `UpperHemicontinuous` for
correspondences is not used in its place — see `MODERATION_NOTES.md`). -/
def USCSetValued (D : E → Set A) : Prop :=
  ∀ x : E, ∀ xs : ℕ → E, Tendsto xs atTop (𝓝 x) →
    ∀ as : ℕ → A, (∀ n, as n ∈ D (xs n)) → ∃ a ∈ D x, MapClusterPt a atTop as

/-- A set-valued mapping `x ↦ D(x)` is lower semicontinuous (Bäuerle–Rieder, Definition A.2.1b,
p. 351, PDF 358): for every `x`, if `xₙ → x`, then every point of `D(x)` is an accumulation
point of some sequence `aₙ ∈ D(xₙ)`. -/
def LSCSetValued (D : E → Set A) : Prop :=
  ∀ x : E, ∀ xs : ℕ → E, Tendsto xs atTop (𝓝 x) →
    ∀ a ∈ D x, ∃ as : ℕ → A, (∀ n, as n ∈ D (xs n)) ∧ MapClusterPt a atTop as

/-- A set-valued mapping is continuous if it is upper and lower semicontinuous (Bäuerle–Rieder,
Definition A.2.1c, p. 351, PDF 358). -/
def ContinuousSetValued (D : E → Set A) : Prop :=
  USCSetValued D ∧ LSCSetValued D

end MDPFinance.Semicontinuous


