-- Prove2me | Definitions.Def_SPOBounds_Natarajan_NatarajanDim
-- name    : SPOBounds_Natarajan_NatarajanDim
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T18:27:08.279127+00:00
-- url     : https://prove2.me/theorems/8ee1bca9-c813-4ba8-85e0-68902941488f
-- title:
--   N-shattering (Definition 1), the induced decision class $w^*(\mathcal H)$, and the sample restriction $\mathfrak F_{|\mathbb X}$
-- statement:
--   1. **Induced decision class.** For an oracle $w^*$ and a class $\mathcal H$ of cost predictors $f:\mathcal X\to\mathbb R^d$,
--   $$w^*(\mathcal H) := \{x\mapsto w^*(f(x)) : f\in\mathcal H\}.$$
--   2. **N-shattering (Definition 1).** A class $\mathcal F$ of functions on $\mathcal X$ *N-shatters* a finite set $\mathbb X\subseteq\mathcal X$ if there are $g_1,g_2$ with $g_1(x)\ne g_2(x)$ for all $x\in\mathbb X$ such that for every $T\subseteq\mathbb X$ some $g\in\mathcal F$ satisfies $g(x)=g_1(x)$ for $x\in T$ and $g(x)=g_2(x)$ for $x\in\mathbb X\setminus T$. The *Natarajan dimension* $d_N(\mathcal F)$ is the largest cardinality of an N-shattered set.
--   3. **Sample restriction.** For a sample with features $x_1,\dots,x_n$,
--   $$\mathfrak F_{|\mathbb X} := \{(w^*(f(x_1)),\dots,w^*(f(x_n))) : f\in\mathcal H\},$$
--   the set of decision vectors that $w^*(\mathcal H)$ induces on the sample.
--
--   The Natarajan dimension extends the VC dimension to multiclass prediction; here the "labels" are the decisions returned by the oracle, and the paper allows these to range over the possibly infinite set $S$.
--
--   **Formalization Note** The functions $g_1,g_2$ are taken on all of $\mathcal X$ (only their values on $\mathbb X$ matter), and their codomain is not restricted to $S$: taking $T=\mathbb X$ and $T=\emptyset$ forces $g_1,g_2$ to agree on $\mathbb X$ with members of $\mathcal F$, so for $\mathcal F=w^*(\mathcal H)$ their values on $\mathbb X$ lie in $S$ anyway. The Natarajan dimension itself is not defined as a number: a supremum in $\mathbb N$ would silently be $0$ when shattered sets are unboundedly large. The theorems instead carry a natural number $k$ with the hypothesis that every N-shattered finite set has at most $k$ elements.
-- source:
--   El Balghiti, Elmachtoub, Grigas, Tewari, Generalization Bounds in the Predict-then-Optimize Framework, arXiv:1905.11488v3, p. 10, Definition 1; p. 11 (w*(H)); p. 31, Appendix B.1 (restriction to the sample)

import Mathlib

namespace SPOBounds.Natarajan

/-- The class `w*(H) = {x ↦ w*(f(x)) : f ∈ H}` of decisions induced by `H` (p. 11). -/
def oracleClass {X Y Z : Type*} (w : Y → Z) (H : Set (X → Y)) : Set (X → Z) :=
  {g | ∃ f ∈ H, g = fun x => w (f x)}

/-- Definition 1 (p. 10): `F` N-shatters the finite set `T` if there are `g₁, g₂` with
`g₁ x ≠ g₂ x` for every `x ∈ T` such that for every `U ⊆ T` some `g ∈ F` agrees with `g₁` on
`U` and with `g₂` on `T \ U`. The Natarajan dimension is the maximal size of an N-shattered set;
it is not defined as a number here: statements carry an upper bound `k` on the sizes of all
N-shattered sets instead. -/
def NShatters {X Z : Type*} (F : Set (X → Z)) (T : Finset X) : Prop :=
  ∃ g₁ g₂ : X → Z, (∀ x ∈ T, g₁ x ≠ g₂ x) ∧
    ∀ U ⊆ T, ∃ g ∈ F, (∀ x ∈ U, g x = g₁ x) ∧ ∀ x ∈ T, x ∉ U → g x = g₂ x

/-- The set `𝔉_{|𝕏} = {(w*(f(x₁)), …, w*(f(xₙ))) : f ∈ H}` of decision vectors that `w*(H)`
induces on the features of the sample `s` (p. 31). -/
def sampleDecisions {X Y Z C : Type*} {n : ℕ} (w : Y → Z) (H : Set (X → Y))
    (s : Fin n → X × C) : Set (Fin n → Z) :=
  {v | ∃ f ∈ H, v = fun i => w (f (s i).1)}

end SPOBounds.Natarajan


