-- Prove2me | Definitions.Def_RobustRiskOpt_Model
-- name    : RobustRiskOpt_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:41:41.313982+00:00
-- url     : https://prove2.me/theorems/6bbe9f1f-659d-41b7-8919-72039ff2bd60
-- title:
--   The uncertainty models $(L^0_n,\pi^W_n)$ and $(L^q_n,\pi^q_n)$, $q\in[1,\infty]$
-- statement:
--   Assumption G allows two kinds of **uncertainty model** $(\mathcal Z,\pi)$, a set of $n$-random vectors with a pseudo-metric:
--
--   1. the space $L^0_n$ of all random vectors, with the pseudo-metric $\pi^W_n(Y,Z)=\pi_P(F_Y,F_Z)$, where $\pi_P$ is the Prokhorov metric on probability measures on $\mathbb R^n$,
--   $$
--   \pi_P(\mu,\nu)=\inf\{\varepsilon>0:\mu(A)\le\nu(A_\varepsilon)+\varepsilon\ \text{ and }\ \nu(A)\le\mu(A_\varepsilon)+\varepsilon\ \text{ for all Borel }A\},
--   $$
--   with $A_\varepsilon$ the open $\varepsilon$-thickening of $A$;
--   2. for $q\in[1,\infty]$, the space $L^q_n$ of random vectors with finite $q$-th moment (essentially bounded for $q=\infty$), with the metric $\pi^q_n(Y,Z)=\|Y-Z\|_q$, that is $(\mathbb E[|Y-Z|^q])^{1/q}$ for $q<\infty$ and $\operatorname{ess\,sup}|Y-Z|$ for $q=\infty$.
--
--   Convergence in $\pi^W_n$ is convergence in distribution. The value $q=\infty$ gives the strongest of these metrics.
--
--   **Formalization Note** The two models are the constructors of an inductive type, with $1\le q$ a field of the second constructor. The distances are $[0,\infty]$-valued: Mathlib's `levyProkhorovEDist` applied to the two laws, and `eLpNorm`. They are finite on the carrier.
-- source:
--   Embrechts–Schied–Wang, Robustness in the Optimization of Risk Measures, arXiv:1809.09268v3, 11 Feb 2021, Example 3, (3)–(5), and footnote 7, p.9; Assumption G, p.13; §2.1, p.5

import Mathlib
import Definitions.Def_RobustRiskOpt_Admissible

open MeasureTheory
open scoped ENNReal

namespace RobustRiskOpt

/-- The two kinds of uncertainty model `(𝒵, π)` allowed by Assumption G, p.13
(Embrechts–Schied–Wang, arXiv:1809.09268v3): `(L⁰ₙ, π^W_n)`, or `(L^q_n, π^q_n)` for some
`q ∈ [1, ∞]`. The value `q = ∞` is included: it is the `L^∞`-metric of (3). -/
inductive UncertaintyModel
  /-- `(L⁰ₙ, π^W_n)`, Example 3(iii), p.9. -/
  | weak
  /-- `(L^q_n, π^q_n)` with `q ∈ [1, ∞]`, Example 3(i)–(ii), p.9. -/
  | lp (q : ℝ≥0∞) (hq : 1 ≤ q)

namespace UncertaintyModel

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

/-- The set `𝒵` of `n`-random vectors of the model: all of `L⁰ₙ`, or `L^q_n`, §2.1, p.5
(Embrechts–Schied–Wang, arXiv:1809.09268v3). -/
def carrier (M : UncertaintyModel) (P : Measure Ω) : Set (Ω → E n) :=
  match M with
  | weak => {Y | Measurable Y}
  | lp q _ => {Y | Measurable Y ∧ MemLp Y q P}

/-- The pseudo-metric `π` of the model, Example 3, p.9 and footnote 7
(Embrechts–Schied–Wang, arXiv:1809.09268v3).

* `weak`: `π^W_n(Y, Z) = π_P(F_Y, F_Z)`, (5), the Prokhorov distance of the laws of `Y` and `Z`.
  Mathlib's `levyProkhorovEDist` is the infimum of the `ε` with `μ(B) ≤ ν(B_ε) + ε` and
  `ν(B) ≤ μ(B_ε) + ε` for all Borel `B`, with `B_ε` the open `ε`-thickening, as in footnote 7.
* `lp q`: `π^q_n(Y, Z) = ‖Y − Z‖_q`, which is `ess-sup |Y − Z|` at `q = ∞`, (3), and
  `(𝔼[|Y − Z|^q])^{1/q}` at `q < ∞`, (4).

**Formalization Note** The distances are `ℝ≥0∞`-valued and are finite on the carrier. -/
noncomputable def dist (M : UncertaintyModel) (P : Measure Ω) (Y Z : Ω → E n) : ℝ≥0∞ :=
  match M with
  | weak => levyProkhorovEDist (P.map Y) (P.map Z)
  | lp q _ => eLpNorm (fun ω => Y ω - Z ω) q P

end UncertaintyModel

end RobustRiskOpt


