-- Prove2me | Definitions.Def_LeGallBrownianMap_IsBrownianLabels
-- name    : LeGallBrownianMap_IsBrownianLabels
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:36:13.215557+00:00
-- url     : https://prove2.me/theorems/b102d49d-338e-461a-af8e-e8a8cf39326e
-- title:
--   Brownian labels $Z$ on the CRT coded by $e$
-- statement:
--   Let $(e_s)_{0\le s\le1}$ be a random excursion path and $Z=(Z_s)_{0\le s\le 1}$ a real process on the same probability space. $Z$ is a process of **Brownian labels** given $e$ if, conditionally given $e$, $Z$ is a centred Gaussian process with covariance
--
--   $$
--   \mathbb E[Z_sZ_t\mid e] = \min_{s\wedge t\le r\le s\vee t} e_r ,
--   $$
--
--   and $Z$ has continuous paths (the paper always works with the continuous modification). In particular $Z_0=0$ and $\mathbb E[(Z_s-Z_t)^2\mid e] = d_e(s,t)$. These labels play the role of Brownian motion indexed by the CRT.
--
--   **Formalization Note** The conditional statement is written without regular conditional probabilities: for every finite set of times $I$, every $\lambda\in\mathbb R^I$ and every measurable set $A$ of paths,
--   $\mathbb E[\mathbf 1_A(e)\,e^{i\sum_{s\in I}\lambda_s Z_s}] = \mathbb E[\mathbf 1_A(e)\,e^{-\frac12\sum_{s,t\in I}\lambda_s\lambda_t m_e(s,t)}]$ with $m_e(s,t)=\min_{[s\wedge t,s\vee t]}e$. It also requires each $Z_t$ to be measurable and almost every path to be continuous.
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, §2.4, p.13

import Mathlib

open MeasureTheory

namespace LeGallBrownianMap

/-- Le Gall, *Uniqueness and universality of the Brownian map*, arXiv:1105.4842v2, §2.4, p.13:
"We consider a real-valued process Z = (Z_s)_{0≤s≤1} such that, conditionally given
(e_s)_{0≤s≤1}, Z is a centered Gaussian process with covariance
E[Z_s Z_t | e] = min_{s∧t≤r≤s∨t} e_r. […] It is easy to verify that Z has a continuous
modification […]. From now on, we always deal with this modification."

`IsBrownianLabels e Z P` says: every `Z_t` is measurable, almost every path `t ↦ Z_t` is
continuous, and for every finite set `I ⊆ [0,1]` of times, every `λ : [0,1] → ℝ` and every
measurable set `A` of paths,
`E[1_A(e) exp(i Σ_{s∈I} λ_s Z_s)] = E[1_A(e) exp(−½ Σ_{s,t∈I} λ_s λ_t m_e(s,t))]`, where
`m_e(s,t) = min_{[s∧t, s∨t]} e`.

**Formalization Note.** This is the conditional statement of the paper written without regular
conditional probabilities: the displayed identity for all `A` in the σ-algebra of `e` says that
the conditional characteristic function of `(Z_s)_{s∈I}` given `e` is the centred Gaussian one
with covariance `m_e`, i.e. that conditionally given `e` the process `Z` is centred Gaussian with
that covariance. Path sets carry the product σ-algebra of `[0,1] → ℝ`. The minimum is written
`sInf (e '' uIcc s t)`, which equals the minimum for the continuous excursion. The continuity
clause is the paper's choice of the continuous modification. `Z_0 = 0` follows (`e_0 = 0`). -/
def IsBrownianLabels {Ω : Type} [MeasurableSpace Ω] (e : Ω → unitInterval → ℝ)
    (Z : unitInterval → Ω → ℝ) (P : Measure Ω) : Prop :=
  (∀ t, Measurable (Z t)) ∧ (∀ᵐ ω ∂P, Continuous (fun t => Z t ω)) ∧
  ∀ (I : Finset unitInterval) (lam : unitInterval → ℝ) (A : Set (unitInterval → ℝ)),
    MeasurableSet A →
    ∫ ω, A.indicator (fun _ => (1 : ℂ)) (e ω) *
        Complex.exp (Complex.I * ((∑ s ∈ I, lam s * Z s ω : ℝ) : ℂ)) ∂P =
      ∫ ω, A.indicator (fun _ => (1 : ℂ)) (e ω) *
        Complex.exp (((-(1 / 2) * ∑ s ∈ I, ∑ t ∈ I,
          lam s * lam t * sInf (e ω '' Set.uIcc s t) : ℝ)) : ℂ) ∂P

end LeGallBrownianMap


