-- Prove2me | Definitions.Def_SampleCRS_AlmostGreedy_activationLaw
-- name    : SampleCRS_AlmostGreedy_activationLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:01:37.109648+00:00
-- url     : https://prove2.me/theorems/cf2e8360-5d3a-4320-a0b0-8f686ce0f71a
-- title:
--   Independent online activation law and counts
-- statement:
--   Let $p=(p_1,\ldots,p_n)\in[0,1]^n$. For an activation vector $X\in\{0,1\}^n$, give its success set the published independent Bernoulli weight
--   $$w_p(X)=\prod_{j:X_j=1}p_j\prod_{j:X_j=0}(1-p_j),\qquad \mathbb E_p[f(X)]=\sum_X w_p(X)f(X).$$
--   The counts are $S(X)=\sum_j X_j$ and $S_{-i}(X)=\sum_{j\ne i}X_j$. These are functions of the same vector, so expressions involving both $X_j$ and $S_{-i}$ retain their dependence.
--
--   This interface supplies the online activation law throughout the acceptance calculation. The general success-set law is reused from the published Poisson-binomial definition rather than replaced with a paper-specific distribution. Empty products have value one and the empty count is zero; probability interpretations require all coordinates of $p$ to lie in $[0,1]$.
-- source:
--   Shaddin Dughmi, Vasilis Livanos, Pranav Nuti, STOC 2027 submission #686 (October 2026), §2, pp.5–6; Theorem 4.1 proof, pp.14,17

import Mathlib
import Definitions.Def_CommitteeVoting_SingleVoter_PoissonBinomial

namespace SampleCRS.AlmostGreedy

/-- The product Bernoulli law on online activation vectors (§2, p.5).
The published success-set weight supplies the independent trials. -/
noncomputable def activationWeight {n : ℕ} (p : Fin n → ℝ) (X : Fin n → Bool) : ℝ :=
  CommitteeVoting.SingleVoter.pbWeight p Finset.univ
    (Finset.univ.filter (fun j => X j = true))

/-- Expectation over the original independent online activations. -/
noncomputable def activationE {n : ℕ} (p : Fin n → ℝ) (f : (Fin n → Bool) → ℝ) : ℝ :=
  ∑ X : Fin n → Bool, activationWeight p X * f X

/-- The unconditioned number S of online-active elements (p.17). -/
def activeCount {n : ℕ} (X : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun j => X j = true)).card

/-- S_{−i}, the number of online-active elements other than i (p.14). -/
def otherCount {n : ℕ} (X : Fin n → Bool) (i : Fin n) : ℕ :=
  ((Finset.univ.erase i).filter (fun j => X j = true)).card

end SampleCRS.AlmostGreedy


