-- Prove2me | Definitions.Def_PreservePast_cmiBits
-- name    : PreservePast_cmiBits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T10:39:42.315494+00:00
-- url     : https://prove2.me/theorems/655ce3c5-13a3-4a23-81d3-9bd820b9b0bf
-- title:
--   Conditional mutual information in bits, the reference law, $\mathrm{kl}_2$ and $h_2$
-- statement:
--   For random variables $V$, $M$ and $Z$ on one probability space, the **conditional mutual information** in bits is the relative entropy of the actual joint law of $(Z,V,M)$ from the law that makes $V$ and $M$ independent conditional on $Z$ while keeping the laws of $(Z,V)$ and $(Z,M)$:
--   $$
--   I(V;M\mid Z)=\frac1{\ln2}\,D\big(P_{Z,V,M}\,\big\|\,P_Z\otimes(P_{V\mid Z}\times P_{M\mid Z})\big).
--   $$
--   The second law is the **reference law** of Lemma 1. The binary relative entropy and the binary entropy, in bits, are
--   $$
--   \mathrm{kl}_2(s\|p)=s\log_2\frac sp+(1-s)\log_2\frac{1-s}{1-p},\qquad h_2(s)=-s\log_2s-(1-s)\log_2(1-s).
--   $$
--
--   **Formalization Note** $I$ is the published `ThompsonTutorial.InfoRatio.condMutualInfo` (in nats, valued in $[0,\infty]$) divided by $\ln 2$; conditional laws are Mathlib's regular conditional distributions, so $V$ and $M$ take values in standard Borel spaces. $h_2$ is Mathlib's `Real.binEntropy` divided by $\ln2$; $0\log0=0$.
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb…d00fa), §1.2.1, pp.2–3 (PDF pp.4–5), Lemma 1; §C.2, p.18; §3.1, p.6

import Mathlib
import Definitions.Def_ThompsonTutorial_InfoRatio_condMutualInfo

open MeasureTheory ProbabilityTheory

namespace PreservePast

/-- **Conditional mutual information in bits** `I(V; M | 𝒰)`.
P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), §1.2.1, p.3 (PDF p.5), Lemma 1: "Compare the actual joint law with the law making V
independent of M conditional on 𝒰"; §3.1, p.6: "Logarithms in bit counts and relative entropies are
base two."

`cmiBits P V M Z` is the relative entropy, in bits, of the joint law of `(Z, (V, M))` from the law
`P_Z ⊗ (P_{V|Z} × P_{M|Z})` under which `V` and `M` are conditionally independent given `Z`
(the published `ThompsonTutorial.InfoRatio.condMutualInfo`, in nats, divided by `ln 2`).

**Formalization Note.** Valued in `ℝ≥0∞`. Conditional laws are Mathlib's `condDistrib` (standard
Borel, nonempty targets). -/
noncomputable def cmiBits {Ω A B C : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B] [MeasurableSpace C]
    (P : Measure Ω) [IsFiniteMeasure P] (V : Ω → A) (M : Ω → B) (Z : Ω → C) : ENNReal :=
  ThompsonTutorial.InfoRatio.condMutualInfo P V M Z / ENNReal.ofReal (Real.log 2)

/-- The reference law of Lemma 1 (p.3): the joint law of `(Z, (V, M))` modified to make `V`
independent of `M` conditional on `Z`, keeping the laws of `(Z, V)` and `(Z, M)`. -/
noncomputable def refLaw {Ω A B C : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B] [MeasurableSpace C]
    (P : Measure Ω) [IsFiniteMeasure P] (V : Ω → A) (M : Ω → B) (Z : Ω → C) : Measure (C × (A × B)) :=
  (P.map Z) ⊗ₘ (condDistrib V Z P ×ₖ condDistrib M Z P)

/-- Binary relative entropy in bits, `kl₂(s‖p) = s log₂(s/p) + (1 − s) log₂((1 − s)/(1 − p))`
(p.18). Lean's `log 0 = 0` gives the convention `0 log 0 = 0` at `s ∈ {0, 1}`. -/
noncomputable def kl2 (s p : ℝ) : ℝ :=
  s * Real.logb 2 (s / p) + (1 - s) * Real.logb 2 ((1 - s) / (1 - p))

/-- Binary entropy in bits, `h₂(s) = −s log₂ s − (1 − s) log₂(1 − s)` (p.2). -/
noncomputable def h2 (s : ℝ) : ℝ := Real.binEntropy s / Real.log 2

end PreservePast


