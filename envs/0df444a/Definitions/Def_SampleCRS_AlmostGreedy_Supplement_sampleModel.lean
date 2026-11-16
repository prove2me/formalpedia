-- Prove2me | Definitions.Def_SampleCRS_AlmostGreedy_Supplement_sampleModel
-- name    : SampleCRS_AlmostGreedy_Supplement_sampleModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:33:24.290202+00:00
-- url     : https://prove2.me/theorems/d90fdcb8-8754-40b4-b431-c44097194061
-- title:
--   Sample policies and the full-information adversarial optimum
-- statement:
--   A sample policy sees all $m$ Bernoulli sample rows before it begins and returns an online kernel. The same policy is used for every hidden vector $p$. The sample array, online activations and subsequent kernel random choices are independent in the experiment. Each sample row has the published activation law, and the sample-array weight is
--   $$w(Y)=\prod_{s=1}^m w_p(Y^{(s)}).$$
--   Sample acceptance averages the actual kernel law over this array. With $m=0$, the empty product is one.
--
--   For capacity $k$, let $\gamma_{\rm adv}(k)$ be the supremum of $c\in[0,1]$ attainable by full-information online schemes uniformly over every finite $n$ and every admissible vector of mass $k$:
--   $$\gamma_{\rm adv}(k)=\sup\{c\in[0,1]:\ \forall n,p,\ \sum_i p_i=k\Rightarrow\exists\pi_p,\ \Pr[A_i]\ge cp_i\}.$$
--   Here full-information policies may depend on $p$; sample policies cannot. This bounded, nonempty supremum defines the adversarial optimum independently of any impossibility conclusion or ODE characterization.
-- source:
--   Shaddin Dughmi, Vasilis Livanos, Pranav Nuti, STOC 2027 submission #686 (October 2026), §2, pp.5–6; §5.2, p.22

import Mathlib
import Definitions.Def_SampleCRS_AlmostGreedy_Supplement_onlineKernel

namespace SampleCRS.AlmostGreedy.Supplement

/-- All samples are visible before the run. There is no hidden `p` argument. -/
abbrev SamplePolicy (n m : ℕ) := (Fin m → Fin n → Bool) → OnlineKernel n

noncomputable def sampleWeight {n m : ℕ} (p : Fin n → ℝ)
    (Y : Fin m → Fin n → Bool) : ℝ :=
  ∏ s, activationWeight p (Y s)

noncomputable def sampleAccept {n m : ℕ} (k : ℕ) (π : SamplePolicy n m)
    (p : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ Y, sampleWeight p Y * policyAccept k (π Y) p i

/-- Full-information adversarial balance: the policy may be chosen after seeing p.
Relabelling a fixed, even advance-known, order to `0,…,n-1` loses no information. -/
def AdvAttainable (k : ℕ) (c : ℝ) : Prop :=
  c ∈ Set.Icc (0 : ℝ) 1 ∧
  ∀ (n : ℕ) (p : Fin n → ℝ), ValidProb p → (∑ i, p i) = (k : ℝ) →
    ∃ π : OnlineKernel n, BalancedInstance k c π p

/-- The operational known-p adversarial optimum, not the random-order constant.
The defining set is bounded by 1; 0 is attainable by rejecting every arrival. -/
noncomputable def gammaAdv (k : ℕ) : ℝ := sSup {c : ℝ | AdvAttainable k c}

end SampleCRS.AlmostGreedy.Supplement


