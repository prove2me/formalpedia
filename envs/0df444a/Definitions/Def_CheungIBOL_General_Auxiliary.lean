-- Prove2me | Definitions.Def_CheungIBOL_General_Auxiliary
-- name    : CheungIBOL_General_Auxiliary
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T22:14:40.396158+00:00
-- url     : https://prove2.me/theorems/8eef829d-b051-4846-9c2d-06bcf2d275da
-- title:
--   Dynamic best-action comparator and signed relaxed regret
-- statement:
--   At history $h$ and current context $x$, the auxiliary expected reward of action $a$ is
--   $$R(h,x,a)=\sum_i r_i(1-\Psi_\epsilon(N_i(h)/b_i))p_{x,a,i}.$$
--   Its comparator is $R_*(h,x)=\sup_{a\in A}R(h,x,a)$. For nonempty $A$ and $\epsilon\ge0$ this is the supremum of a nonempty bounded set in $[0,n]$. It equals the printed maximum whenever attained, and also covers unattained suprema. As a function of history it depends only on the finite set of possible inventory vectors, ensuring measurability.
--
--   For a realized history, sum $R_*(h_{<t},x_t)-(1+\epsilon)R(h_{<t},x_t,a_t)$ over its rounds. The relaxed regret $\mathrm{Reg}_\epsilon$ is the expectation of this signed sum under the same IBOL history law that defines revenue. It can be negative. The comparator uses the run's own inventory, not a separate optimal run or a fixed-action benchmark.
-- source:
--   Cheung, Ma, Simchi-Levi and Wang, Inventory Balancing with Online Learning, arXiv:1810.05640v2 (30 August 2021), PDF/printed pp. 14–16, auxiliary reward and equation (8), https://arxiv.org/abs/1810.05640v2

import Definitions.Def_CheungIBOL_General_Run

open MeasureTheory
open scoped BigOperators
noncomputable section

namespace CheungIBOL.General

/-- The auxiliary mean reward at the current realized inventory, evaluated at any action. -/
def auxiliaryReward {n c : ℕ} {A : Type*} [MeasurableSpace A]
    (M : Model n c A) (ε : ℝ) (h : History n c A) (x : Fin c) (a : A) : ℝ :=
  ∑ i : Fin n, discounted M ε h i * M.prob x a i

/-- The best-action value, also defined for a nonattained supremum. With A nonempty
and epsilon nonnegative, the range is nonempty and bounded in [0,n]. -/
def bestReward {n c : ℕ} {A : Type*} [MeasurableSpace A]
    (M : Model n c A) (ε : ℝ) (h : History n c A) (x : Fin c) : ℝ :=
  sSup (Set.range (auxiliaryReward M ε h x))

/-- Equation (8) before expectation, using the chosen actions in this very history. -/
def realizedRegret {n c : ℕ} {A : Type*} [MeasurableSpace A]
    (M : Model n c A) (ε : ℝ) (x : ℕ → Fin c) (h : History n c A) : ℝ :=
  (h.mapIdx fun t obs => bestReward M ε (h.take t) (x t) -
    (1 + ε) * auxiliaryReward M ε (h.take t) (x t) obs.2.1).sum

/-- Signed relaxed regret; it is not clipped to zero. -/
def relaxedRegret {n c : ℕ} {A : Type*} [MeasurableSpace A]
    (M : Model n c A) (O : Oracle n c A) (ε : ℝ) (x : ℕ → Fin c) (T : ℕ) : ℝ :=
  ∫ h, realizedRegret M ε x h ∂runLaw M O ε x T

end CheungIBOL.General


