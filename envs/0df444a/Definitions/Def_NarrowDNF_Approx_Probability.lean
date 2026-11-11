-- Prove2me | Definitions.Def_NarrowDNF_Approx_Probability
-- name    : NarrowDNF_Approx_Probability
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:05:55.079195+00:00
-- url     : https://prove2.me/theorems/abc0c852-231c-4637-aa6d-e1af0e41edd3
-- title:
--   Finite biased-cube probabilities and expectations
-- statement:
--   Let $n$ be a natural number, and let $x$ range over the Boolean cube $\{0,1\}^n$, ordered coordinatewise with $0<1$. For a real bias $p$, define an event probability and a real-cost expectation by
--   $$\mathbb P_p(E)=\sum_x\mathbf1_E(x)\prod_i p^{x_i}(1-p)^{1-x_i},\qquad
--   \mathbb E_p c=\sum_x c(x)\prod_i p^{x_i}(1-p)^{1-x_i}.$$
--   The implementation uses the equivalent piecewise Bernoulli masses, avoiding power conventions. Disagreement error is $\operatorname{err}_p(f,g)=\mathbb P_p[f\ne g]$. These are probabilities and expectations on the source's range $0<p<1$; the formulas remain algebraically defined outside that range. The published total resampling influence is imported unchanged, rather than redefined.
--
--   This interface supplies the shared finite probability space for every target. **Formalization Note** The cube is `Fin n → Bool`; expectation is a finite sum and has no undefined-integral default.
-- source:
--   Chenghua Liu, Boning Meng, STOC 2027 submission #1509 (October 2026), Section 1, p. 1 (PDF p. 2)

import Mathlib
import Definitions.Def_FriedgutCoalition_wProb
import Definitions.Def_FriedgutCoalition_pInfl

namespace NarrowDNF.Approx

/-- The source cube, with the pointwise order false < true. -/
abbrev Cube (n : ℕ) := Fin n → Bool

/-- Product Bernoulli event probability, using the published exact finite sum. -/
noncomputable def prob {n : ℕ} (p : ℝ) (E : Cube n → Prop) : ℝ :=
  FriedgutCoalition.wProb (FriedgutCoalition.bern p) E

/-- Exact finite expectation; no Bochner-integrability default. -/
noncomputable def expect {n : ℕ} (p : ℝ) (c : Cube n → ℝ) : ℝ :=
  ∑ x : Cube n, (∏ i : Fin n, FriedgutCoalition.bern p (x i)) * c x

noncomputable def error {n : ℕ} (p : ℝ) (f g : Cube n → Bool) : ℝ :=
  prob p (fun x => f x ≠ g x)

end NarrowDNF.Approx


