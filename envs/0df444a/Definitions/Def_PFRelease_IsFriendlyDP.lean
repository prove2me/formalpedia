-- Prove2me | Definitions.Def_PFRelease_IsFriendlyDP
-- name    : PFRelease_IsFriendlyDP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:45:52.866965+00:00
-- url     : https://prove2.me/theorems/efd39209-0320-44c5-affc-e01b0d608c26
-- title:
--   Friendly differential privacy with respect to a predicate
-- statement:
--   A **friendliness predicate** is a function $F:\mathcal X^*\times\mathcal X\to\{0,1\}$; a record $x$ is friendly with a dataset $s$ if $F(s,x)=1$. A mechanism $M$ is **$(\varepsilon,\delta)$-friendly-DP with respect to $F$** (on datasets of $n$ records) if
--   $$
--   M(s^{i\to\perp})\approx_{\varepsilon,\delta}M(s)
--   $$
--   for every $s\in\mathcal X^n$ and slot $i$ such that $s_i\ne\perp$ and $F(s^{i\to\perp},s_i)=1$.
--
--   Friendly DP asks for privacy only at the neighbouring pairs the predicate admits; the release mechanism of PFR needs only this.
--
--   **Formalization Note** The predicate is `List (Option X) → Option X → Bool`; it is applied to the $n$-slot dataset $s^{i\to\perp}$ (slot $i$ null, not deleted), as on the page.
-- source:
--   Shenfeld, Tsfadia, Ligett, Propose-Filter-Release: Scaling Noise to Typical Sensitivity via Private Filtering, arXiv:2610.40654 (held version, sha256 e1d516b3…), Definition 3.1, p.8 (PDF p.10), and Definition 4.1, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_PFRelease_Indist

open MeasureTheory

namespace PFRelease

/-- Friendly differential privacy (Shenfeld, Tsfadia, Ligett, arXiv:2610.40654, held version
sha256 e1d516b3…, Definition 4.1, p.11 = PDF p.13). Given a friendliness predicate
`F : X* × X → {0, 1}` (Definition 3.1, p.8), a mechanism `M` is `(ε, δ)`-friendly-DP with respect
to `F` (on datasets of `n` records) if `M(s^{i→⊥}) ≈_{ε,δ} M(s)` for every `s ∈ Xⁿ` and slot `i`
with `sᵢ ≠ ⊥` and `F(s^{i→⊥}, sᵢ) = 1`.

**Formalization Note** A predicate is `F : List (Option X) → Option X → Bool` (`true` = 1); its
first argument is a dataset of `X*` as the list of its records, nulls included. The predicate is
applied to the `n`-slot dataset `s^{i→⊥}` (slot `i` null, not deleted), as on the page. -/
def IsFriendlyDP {X Y : Type*} [MeasurableSpace Y] {n : ℕ} (M : (Fin n → Option X) → Measure Y)
    (F : List (Option X) → Option X → Bool) (ε δ : ℝ) : Prop :=
  ∀ (s : Fin n → Option X) (i : Fin n), s i ≠ none →
    F (toList (nullOut s {i})) (s i) = true → Indist (M (nullOut s {i})) (M s) ε δ

end PFRelease


