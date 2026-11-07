-- Prove2me | Definitions.Def_PFRelease_Indist
-- name    : PFRelease_Indist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:44:39.727406+00:00
-- url     : https://prove2.me/theorems/7eee7ad5-3c5b-467c-b5e2-b9615d50ca68
-- title:
--   $(\varepsilon,\delta)$-indistinguishability and $(\varepsilon,\delta)$-DP
-- statement:
--   Two random variables $X,Y$ over a common domain are **$(\varepsilon,\delta)$-indistinguishable**, written $X\approx_{\varepsilon,\delta}Y$, if for every event $O$
--   $$
--   \Pr[X\in O]\le e^{\varepsilon}\Pr[Y\in O]+\delta
--   \quad\text{and}\quad
--   \Pr[Y\in O]\le e^{\varepsilon}\Pr[X\in O]+\delta .
--   $$
--   A randomized mechanism $M$ on datasets of $n$ records is **$(\varepsilon,\delta)$-differentially private** if $M(s)\approx_{\varepsilon,\delta}M(s')$ for every pair of zero-out neighbours $s\simeq s'$, that is, $M(s)\approx_{\varepsilon,\delta}M(s^{i\to\perp})$ for every $s\in\mathcal X^n$ and every slot $i$.
--
--   This is the privacy notion of every result of the mission.
--
--   **Formalization Note** Random variables are represented by their laws; both inequalities are required, in $[0,\infty]$, for every measurable event. The ranges $\varepsilon\ge0$, $\delta\in[0,1]$ are hypotheses of the theorems. Since the relation is symmetric, quantifying over the ordered pairs $(s,s^{i\to\perp})$ covers both orders of a neighbouring pair.
-- source:
--   Shenfeld, Tsfadia, Ligett, Propose-Filter-Release: Scaling Noise to Typical Sensitivity via Private Filtering, arXiv:2610.40654 (held version, sha256 e1d516b3…), Definition 2.1, p.7 (PDF p.9)

import Mathlib
import Definitions.Def_PFRelease_Dataset

open MeasureTheory

namespace PFRelease

/-- `(ε, δ)`-indistinguishability `P ≈_{ε,δ} Q` of two laws on a common space (Shenfeld, Tsfadia,
Ligett, arXiv:2610.40654, held version sha256 e1d516b3…, Definition 2.1, p.7 = PDF p.9):
`Pr[X ∈ O] ≤ e^ε Pr[Y ∈ O] + δ` **and** `Pr[Y ∈ O] ≤ e^ε Pr[X ∈ O] + δ` for every event `O`.

**Formalization Note** Random variables are represented by their laws `P Q : Measure Ω`; events
are measurable sets; the inequalities are in `ℝ≥0∞`, with `e^ε` and `δ` embedded by
`ENNReal.ofReal`. The ranges `ε ≥ 0`, `δ ∈ [0, 1]` of the definition are hypotheses of the
theorems that use it. -/
def Indist {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω) (ε δ : ℝ) : Prop :=
  ∀ O : Set Ω, MeasurableSet O →
    P O ≤ ENNReal.ofReal (Real.exp ε) * Q O + ENNReal.ofReal δ ∧
    Q O ≤ ENNReal.ofReal (Real.exp ε) * P O + ENNReal.ofReal δ

/-- A randomized mechanism `M` on datasets of `n` records is `(ε, δ)`-differentially private
(Definition 2.1, p.7) if `M(s) ≈_{ε,δ} M(s′)` for every pair of zero-out neighbours `s ≃ s′`,
i.e. `{s, s′} = {s, s^{i→⊥}}` for some slot `i` (§2, p.7).

**Formalization Note** `M s` is the law of the output on input `s`. Since `Indist` is symmetric,
quantifying over the ordered pairs `(s, s^{i→⊥})` covers both orders of every neighbouring pair. -/
def IsDPOn {X Y : Type*} [MeasurableSpace Y] {n : ℕ} (M : (Fin n → Option X) → Measure Y)
    (ε δ : ℝ) : Prop :=
  ∀ (s : Fin n → Option X) (i : Fin n), Indist (M s) (M (nullOut s {i})) ε δ

end PFRelease


