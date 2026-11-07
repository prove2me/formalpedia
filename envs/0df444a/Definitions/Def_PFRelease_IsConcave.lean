-- Prove2me | Definitions.Def_PFRelease_IsConcave
-- name    : PFRelease_IsConcave
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:43:44.878297+00:00
-- url     : https://prove2.me/theorems/d31a6dff-e3fa-4a27-a1ff-b2bd72d275e4
-- title:
--   Concave friendliness score
-- statement:
--   A friendliness score $\varphi$ is **concave** if
--   $$
--   \varphi((s,s'),x)\ \ge\ \frac{|s|\,\varphi(s,x)+|s'|\,\varphi(s',x)}{|s|+|s'|}
--   $$
--   for all nonempty datasets $s,s'$ and every non-null record $x$, where $(s,s')$ is the concatenation and sizes count null records.
--
--   Concavity combines friendliness with separate blocks into friendliness with their union; the element–element score $\varphi_\psi(s,x)=\frac1{|s|}\sum_j\psi(x,s_j)$ satisfies it with equality.
--
--   **Formalization Note** The inequality is in $[0,\infty]$, in the division form of the page (the denominator is positive and finite).
-- source:
--   Shenfeld, Tsfadia, Ligett, Propose-Filter-Release: Scaling Noise to Typical Sensitivity via Private Filtering, arXiv:2610.40654 (held version, sha256 e1d516b3…), Definition 4.4, p.12 (PDF p.14)

import Mathlib

namespace PFRelease

/-- Concavity of a friendliness score (Shenfeld, Tsfadia, Ligett, arXiv:2610.40654, held version
sha256 e1d516b3…, Definition 4.4, p.12 = PDF p.14): `φ((s, s′), x) ≥ (|s| φ(s, x) + |s′| φ(s′, x)) /
(|s| + |s′|)` for any nonempty datasets `s`, `s′` and non-null record `x`, where `(s, s′)` is the
concatenation and `|s|` counts null records.

**Formalization Note** The inequality is in `ℝ≥0∞`; the division is by the positive finite
`|s| + |s′|` (the division form of the page). Nonemptiness of both datasets and `x ≠ ⊥` are
required exactly as on the page. -/
def IsConcave {X : Type*} (φ : List (Option X) → Option X → ENNReal) : Prop :=
  ∀ (s s' : List (Option X)) (x : Option X), s ≠ [] → s' ≠ [] → x ≠ none →
    ((s.length : ENNReal) * φ s x + (s'.length : ENNReal) * φ s' x) /
        ((s.length : ENNReal) + (s'.length : ENNReal)) ≤ φ (s ++ s') x

end PFRelease


