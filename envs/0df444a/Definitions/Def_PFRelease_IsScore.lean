-- Prove2me | Definitions.Def_PFRelease_IsScore
-- name    : PFRelease_IsScore
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:43:30.044354+00:00
-- url     : https://prove2.me/theorems/7cd50fd6-7383-44f0-b570-265f750f11d6
-- title:
--   Friendliness score and the induced predicate $F_\tau(\varphi)$
-- statement:
--   A **friendliness score** is a function $\varphi:\mathcal X^*\times\mathcal X\to[0,\infty]$ that, at every non-null record $x$, is invariant under permutations of its first argument and satisfies $\varphi(\emptyset,x)=0$. Given a threshold $\tau>0$, the induced **friendliness predicate** is
--   $$
--   F_\tau(\varphi;s,x):=\mathbf 1\{\varphi(s,x)\ge\tau\}.
--   $$
--   Higher scores mean smaller influence of the record on a release; PFR tests at $2\tau$ and releases under $F_\tau$.
--
--   **Formalization Note** Scores are `ℝ≥0∞`-valued (the value $\infty$ is allowed); permutation invariance is `List.Perm`. Values at $x=\perp$ are unrestricted (footnote 5, p.12). The real threshold enters through `ENNReal.ofReal`.
-- source:
--   Shenfeld, Tsfadia, Ligett, Propose-Filter-Release: Scaling Noise to Typical Sensitivity via Private Filtering, arXiv:2610.40654 (held version, sha256 e1d516b3…), Definition 4.4, p.12 (PDF p.14)

import Mathlib

namespace PFRelease

/-- A friendliness score (Shenfeld, Tsfadia, Ligett, arXiv:2610.40654, held version sha256
e1d516b3…, Definition 4.4, p.12 = PDF p.14): a function `φ : X* × X → [0, ∞]` that, at every
non-null record `x`, is invariant under permutations of its first argument and satisfies
`φ(∅, x) = 0`.

**Formalization Note** `φ : List (Option X) → Option X → ℝ≥0∞` (values in `[0, ∞]`, `∞`
allowed); datasets of `X*` are lists of records, nulls included. Permutation invariance is
`List.Perm`. Values at the null record `x = ⊥` (`none`) are unrestricted (footnote 5, p.12). -/
def IsScore {X : Type*} (φ : List (Option X) → Option X → ENNReal) : Prop :=
  (∀ x : Option X, x ≠ none → ∀ s s' : List (Option X), s.Perm s' → φ s x = φ s' x) ∧
  (∀ x : Option X, x ≠ none → φ [] x = 0)

/-- The friendliness predicate induced by a score `φ` at threshold `τ` (Definition 4.4, p.12):
`F_τ(φ; s, x) := 1{φ(s, x) ≥ τ}`.

**Formalization Note** The real threshold `τ` is compared in `ℝ≥0∞` through `ENNReal.ofReal`;
the theorems assume `τ > 0`. The value `true` encodes `1`. -/
noncomputable def predOf {X : Type*} (φ : List (Option X) → Option X → ENNReal) (τ : ℝ)
    (s : List (Option X)) (x : Option X) : Bool :=
  decide (ENNReal.ofReal τ ≤ φ s x)

end PFRelease


