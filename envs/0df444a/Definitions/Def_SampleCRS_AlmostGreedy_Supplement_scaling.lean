-- Prove2me | Definitions.Def_SampleCRS_AlmostGreedy_Supplement_scaling
-- name    : SampleCRS_AlmostGreedy_Supplement_scaling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:34:06.130922+00:00
-- url     : https://prove2.me/theorems/88d5d6ee-efa3-43d2-a351-472103ae0056
-- title:
--   Conservative Scaling runs, experiments and Appendix B parameters
-- statement:
--   Given online bits $X$, sample bits $Y$, independent coin bits $Q$ and a permutation $\sigma$, the scaling run scans $\sigma$ and accepts the first $k$ elements satisfying $X_i=1$ and either $Y_i=0$ or $Q_i=1$. The run never reads $p$. Its experiment averages independent $X,Y$, independent per-element coins of common bias $a$, and an independent uniform permutation. Write $C_i$ for its acceptance probability divided by $p_i>0$.
--
--   Algorithm 1 uses $k=1$ and $a=1-1/e$. For Algorithm 6 define
--   $$\delta_k=E[\operatorname{AR}_k(\operatorname{Poi}(k-1))],\quad
--   \alpha_k=\gamma_k/\delta_k,\quad\beta_k=1-\alpha_k,\quad
--   \rho_i=p_i(1-\beta_kp_i).$$
--   Algorithm 6 uses $a=\alpha_k$. The competing candidate count uses independent biases $\rho_j$ for $j\ne i$. Also define $F_k(\lambda)=1/E[\operatorname{AR}_k(\operatorname{Poi}(\lambda))]$ on the nonnegative real parameter domain. The published acceptance-rate and Poisson expectation definitions are reused only for these bounded tests. Theorem B.4 asserts parameter validity, rather than assuming it.
-- source:
--   Shaddin Dughmi, Vasilis Livanos, Pranav Nuti, STOC 2027 submission #686 (October 2026), Algorithms 1,6, pp.7,40–41; Lemma B.2, p.42

import Mathlib
import Definitions.Def_SampleCRS_AlmostGreedy_Supplement_onlineKernel
import Definitions.Def_StaticProphetSec_AR
import Definitions.Def_StaticProphetSec_gamma
import Definitions.Def_StaticProphetSec_pbE
import Definitions.Def_StaticProphetSec_poisE

namespace SampleCRS.AlmostGreedy.Supplement

noncomputable def deltaScale (k : ℕ) : ℝ :=
  StaticProphetSec.poisE (StaticProphetSec.AR k) (Real.toNNReal ((k : ℝ) - 1))

noncomputable def alphaScale (k : ℕ) : ℝ := StaticProphetSec.gamma k / deltaScale k

noncomputable def betaScale (k : ℕ) : ℝ := 1 - alphaScale k

/-- Algorithms 1 and 6: scan the supplied permutation, accepting the first k
candidates. The candidate coin is used only when the sample is active. -/
def scalingRun {n : ℕ} (k : ℕ) (σ : Equiv.Perm (Fin n))
    (X Y Q : Fin n → Bool) : Finset (Fin n) :=
  (List.ofFn σ).foldl (fun A i =>
    if A.card < k ∧ X i = true ∧ (Y i = false ∨ Q i = true) then insert i A else A) ∅

/-- Independent online vector, sample vector, per-element coins and uniform order. -/
noncomputable def scalingE {n : ℕ} (k : ℕ) (a : ℝ) (p : Fin n → ℝ)
    (f : Finset (Fin n) → ℝ) : ℝ :=
  (∑ σ : Equiv.Perm (Fin n), ∑ X, ∑ Y, ∑ Q,
    activationWeight p X * activationWeight p Y * activationWeight (fun _ => a) Q *
      f (scalingRun k σ X Y Q)) / Fintype.card (Equiv.Perm (Fin n))

noncomputable def scalingC {n : ℕ} (k : ℕ) (a : ℝ) (p : Fin n → ℝ)
    (i : Fin n) : ℝ :=
  scalingE k a p (fun A => if i ∈ A then 1 else 0) / p i

def ScalingFeasible (n k : ℕ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (X Y Q : Fin n → Bool),
    (scalingRun k σ X Y Q).card ≤ k ∧ ∀ i ∈ scalingRun k σ X Y Q, X i = true

noncomputable def candidateBias {n : ℕ} (k : ℕ) (p : Fin n → ℝ) (i : Fin n) : ℝ :=
  p i * (1 - betaScale k * p i)

noncomputable def competingAR {n : ℕ} (k : ℕ) (p : Fin n → ℝ) (i : Fin n) : ℝ :=
  activationE (candidateBias k p) (fun Z => StaticProphetSec.AR k (otherCount Z i))

noncomputable def reciprocalAR (k : ℕ) (lam : ℝ) : ℝ :=
  1 / StaticProphetSec.poisE (StaticProphetSec.AR k) (Real.toNNReal lam)

end SampleCRS.AlmostGreedy.Supplement


