-- Prove2me | Definitions.Def_PrivPACLower_ICP_Exponential
-- name    : PrivPACLower_ICP_Exponential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T13:47:10.873503+00:00
-- url     : https://prove2.me/theorems/30773b53-b7b7-4773-8680-a6250f97186a
-- title:
--   Exponential weights and private hypothesis selection
-- statement:
--   For a finite candidate set $C$, score $s(D,c)$, privacy parameter $\varepsilon$, and positive sensitivity bound $\Delta$, the exponential mechanism has weights
--
--   $$p_D(c)=\frac{\exp(\varepsilon s(D,c)/(2\Delta))}{\sum_{a\in C}\exp(\varepsilon s(D,a)/(2\Delta))}.$$
--
--   The output law is the sum of Dirac measures with these weights. The optimum is $\max_{c\in C}s(D,c)$. For fixed binary hypotheses $h_1,\ldots,h_r$, private selection uses score minus the number of sample mistakes. A target $c:X\to\{0,1\}$ labels a domain PMF $\mu$, giving the labeled law of $(x,c(x))$. Selection failure averages, over the i.i.d. sample, the probability of returning an index whose population error exceeds $\alpha$.
--
--   This separates the general exponential mechanism from its hypothesis-selection application.
--
--   **Formalization Note** Nonemptiness, positivity and discrete candidate measurability are theorem hypotheses. They make the normalizer strictly positive and ensure the real supremum is an attained maximum. The finite weighted laws are explicitly computed before the privacy and utility claims.
-- source:
--   Prathamesh Dharangutte, Amartya Sanyal, STOC 2027 submission #366 (October 2026), p. 37, Lemma 21 and proof of Lemma 22. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/366.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Privacy
import Definitions.Def_PrivPACLower_ICP_Learning
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivPACLower.ICP

/-- Explicit normalized exponential weights. Positivity of sensitivity and nonempty C
are required by Lemma 21, ensuring the normalizing constant is positive. -/
noncomputable def expWeight {Z C : Type*} {n : ℕ}
    (score : (Fin n → Z) → C → ℝ) (ε sensitivity : ℝ) (D : Fin n → Z) (c : C) : ℝ :=
  Real.exp (ε * score D c / (2*sensitivity))

noncomputable def exponentialLaw {Z C : Type*} [Fintype C] [MeasurableSpace C] {n : ℕ}
    (score : (Fin n → Z) → C → ℝ) (ε sensitivity : ℝ) (D : Fin n → Z) : Measure C :=
  ∑ c, ENNReal.ofReal (expWeight score ε sensitivity D c /
    ∑ a, expWeight score ε sensitivity D a) • Measure.dirac c

noncomputable def optimum {Z C : Type*} [Fintype C] {n : ℕ}
    (score : (Fin n → Z) → C → ℝ) (D : Fin n → Z) : ℝ :=
  sSup (Set.range (score D))

noncomputable def selectionScore {X : Type*} {r n : ℕ} (hs : Fin r → X → Bool)
    (S : Fin n → X × Bool) (i : Fin r) : ℝ :=
  - ∑ j, if hs i (S j).1 ≠ (S j).2 then 1 else 0

noncomputable def labelLaw {X : Type*} (μ : PMF X) (c : X → Bool) : PMF (X × Bool) :=
  μ.map (fun x => (x,c x))

noncomputable def selectionFailure {X : Type*} {r n : ℕ}
    (A : PrivateUniformGen.Characterization.Mechanism (X × Bool) (Fin r) n)
    (hs : Fin r → X → Bool) (μ : PMF X) (c : X → Bool) (α : ℝ) : ℝ≥0∞ :=
  ∑' S, sampleWeight (labelLaw μ c) S *
    (A S : Measure (Fin r)) {i | ENNReal.ofReal α < populationError (labelLaw μ c) (hs i)}

end PrivPACLower.ICP


