-- Prove2me | Definitions.Def_SampleCRS_AlmostGreedy_experiment
-- name    : SampleCRS_AlmostGreedy_experiment
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:02:26.938966+00:00
-- url     : https://prove2.me/theorems/fb92c9d4-e5cf-43c0-85a0-e418582d8282
-- title:
--   Independent samples, uniform order, and conditional acceptance
-- statement:
--   Fix $n$, capacity $k\ge1$ and $p\in[0,1]^n$. An outcome is $(X,Y,Q,\sigma)$, consisting of online activations, one sample per element, one coin, and an arrival permutation. The two Boolean vectors have independent product Bernoulli laws with the same coordinate probabilities $p_j$. The coin is independent with bias $q_k=(k+1)/(2k+1)$, and every permutation is independent with probability $1/n!$.
--
--   $$w(X,Y,Q,\sigma)=w_p(X)w_p(Y)q_k^{Q}(1-q_k)^{1-Q}/n!.$$
--
--   Write $A_i$ for the event that the defined run accepts $i$. Its probability and conditional acceptance are
--   $$\operatorname{acceptProb}(k,p,i)=\sum_\omega w(\omega)\mathbf1_{A_i}(\omega),\qquad C_i=\frac{\sum_\omega w(\omega)\mathbf1_{A_i\cap\{X_i=1\}}(\omega)}{p_i}\quad(p_i>0).$$
--
--   These quantities average all four sources of randomness. The explicit conditioning event avoids interpreting a fixed order or a fixed sample as the theorem's guarantee. The formula for $C_i$ is used only at positive $p_i$; the denominator $n!$ is never zero, including $n=0$.
-- source:
--   Shaddin Dughmi, Vasilis Livanos, Pranav Nuti, STOC 2027 submission #686 (October 2026), §2, pp.5–6; Algorithm 4, p.14

import Mathlib
import Definitions.Def_SampleCRS_AlmostGreedy_activationLaw
import Definitions.Def_SampleCRS_AlmostGreedy_run

namespace SampleCRS.AlmostGreedy

/-- Independent activations X, samples Y, a single coin Q, and a uniform permutation σ. -/
abbrev Outcome (n : ℕ) :=
  (Fin n → Bool) × (Fin n → Bool) × Bool × Equiv.Perm (Fin n)

/-- The exact bias of the at-most-once coin of Algorithm 4, line 12. -/
noncomputable def coinBias (k : ℕ) : ℝ := ((k : ℝ) + 1) / (2 * (k : ℝ) + 1)

/-- Joint weight of an outcome, with all four randomness sources independent.
Each permutation has weight 1/n!, including the unique permutation at n = 0. -/
noncomputable def weight {n : ℕ} (k : ℕ) (p : Fin n → ℝ) (ω : Outcome n) : ℝ :=
  activationWeight p ω.1 * activationWeight p ω.2.1 *
    (if ω.2.2.1 = true then coinBias k else 1 - coinBias k) / (n.factorial : ℝ)

/-- Unconditional probability that Algorithm 4 accepts i, averaged over X,Y,Q,σ. -/
noncomputable def acceptProb {n : ℕ} (k : ℕ) (p : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ ω : Outcome n, weight k p ω *
    (if i ∈ run k ω.2.2.2 ω.1 ω.2.1 ω.2.2.1 then 1 else 0)

/-- C_i = Pr[i accepted and X_i = 1]/p_i, used only when p_i > 0.
The explicit intersection makes the conditioning event visible. -/
noncomputable def conditionalAcceptance {n : ℕ} (k : ℕ) (p : Fin n → ℝ)
    (i : Fin n) : ℝ :=
  (∑ ω : Outcome n, weight k p ω *
    (if i ∈ run k ω.2.2.2 ω.1 ω.2.1 ω.2.2.1 ∧ ω.1 i = true then 1 else 0)) / p i

end SampleCRS.AlmostGreedy


