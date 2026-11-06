-- Prove2me | Definitions.Def_ABPOnline_IsBrownianWrt
-- name    : ABPOnline_IsBrownianWrt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:54:31.975007+00:00
-- url     : https://prove2.me/theorems/c73b12bd-b4f8-4d93-b7fa-8e55f038c227
-- title:
--   $\mathcal G$-Brownian motion on $[0,1]$
-- statement:
--   Let $\mathcal G=(\mathcal G_t)$ be a filtration on $(\Omega,\mathcal F,\mathbb P)$. A process $B$ is a **$\mathcal G$-Brownian motion** (on $[0,1]$) if it is a standard Brownian motion on $[0,1]$, $B_t$ is $\mathcal G_t$-measurable for every $t\in[0,1]$, and for every $t\in[0,1]$ the future increments $(B_u-B_t)_{t\le u\le1}$ are independent of $\mathcal G_t$.
--
--   This is the limit object of Proposition 3.1; its filtration may contain more information than the natural filtration of $B$, which is why Lemma 3.2 projects onto $\mathcal F^B$.
--
--   **Formalization Note** The independence is joint over all future increments, as used in the proof of Lemma 3.2; for an adapted process it is equivalent to independence of each increment $B_u-B_t$ from $\mathcal G_t$.
-- source:
--   Jo, Lee, The Exact Online Threshold for the Asymmetric Binary Perceptron, arXiv:2609.02124 (artifact sha256 bd5e2bdb18a47b7e806191ae9b888a6e4e7e150a9bd50e541b7587007d07a7a2), Proposition 3.1, p.9 (PDF p.10); Lemma 3.2 and its proof, p.10 (PDF p.11)

import Mathlib
import Definitions.Def_ABPOnline_IsBrownianOn1

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ABPOnline

/-- `B` is a **`G`-Brownian motion on `[0,1]`** (arXiv:2609.02124, Proposition 3.1 and Lemma 3.2,
printed pp.9–10, PDF pp.10–11): a standard Brownian motion on `[0,1]` that is adapted to the
filtration `G = (G_t)_{0≤t≤1}` and whose future increments `(B_u − B_t)_{t≤u≤1}` are independent of
`G_t` for every `t ∈ [0,1]`.

**Formalization Note** Time is `ℝ≥0` and only `[0,1]` is constrained. The independence is
stated jointly for all future increments, which is what the proof of Lemma 3.2 (p.10) uses; it is
equivalent to the independence of each increment `B_u − B_t` from `G_t` for an adapted `B`. -/
def IsBrownianWrt {Ω : Type*} [mΩ : MeasurableSpace Ω] (G : Filtration ℝ≥0 mΩ)
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) : Prop :=
  IsBrownianOn1 B P ∧ (∀ t ≤ 1, Measurable[G t] (B t)) ∧
    ∀ t ≤ 1, Indep (G t)
      (⨆ u : ℝ≥0, ⨆ (_ : t ≤ u ∧ u ≤ 1),
        MeasurableSpace.comap (fun ω => B u ω - B t ω) inferInstance) P

end ABPOnline


