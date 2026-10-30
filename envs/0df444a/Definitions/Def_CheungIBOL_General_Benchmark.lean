-- Prove2me | Definitions.Def_CheungIBOL_General_Benchmark
-- name    : CheungIBOL_General_Benchmark
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T22:16:07.983974+00:00
-- url     : https://prove2.me/theorems/3736dc6e-5178-4ce8-bc5a-11c2860c5fd1
-- title:
--   Primal benchmark and inventory-dependent dual certificate
-- statement:
--   The primal benchmark instantiates the separate probability-measure packing LP with cost $\sum_i r_i p_{x_t,a,i}$, resource use $p_{x_t,a,i}$ and budget $b_i$. Its value $\mathrm{OPT}$ is the extended-real supremum of feasible objectives. Probability allocations enforce total mass exactly one in every period; an empty feasible set has value $-\infty$.
--
--   The literal dual predicate requires, for every $t,a$,
--   $$\Gamma_t\ge\sum_i p_{x_t,a,i}(r_i-\Lambda_i),\qquad p_{x_t,a,i}\Lambda_i\ge0\quad\text{for every }i.$$
--   For a length-$T$ history the constructed certificate is
--   $$\Lambda_i=r_i\Psi_\epsilon(N_i^T/b_i),\qquad \Gamma_t=\sup_a R(h_{<t},x_t,a).$$
--   Its objective is $\sum_t\Gamma_t+\sum_i b_i\Lambda_i$. The formula for $\Lambda$ uses final consumed inventory; $\Gamma$ uses the prefix before the corresponding decision. No dual feasibility or benchmark inequality is built into the definitions.
-- source:
--   Cheung, Ma, Simchi-Levi and Wang, Inventory Balancing with Online Learning, arXiv:1810.05640v2 (30 August 2021), PDF/printed pp. 16–17 and 39–40, equations (9)–(12) and (31)–(35), https://arxiv.org/abs/1810.05640v2

import Definitions.Def_CheungIBOL_General_MeasureProgram
import Definitions.Def_CheungIBOL_General_Auxiliary

open MeasureTheory
open scoped BigOperators
noncomputable section

namespace CheungIBOL.General

/-- Equations (9)--(12), as an instance of the general probability-measure packing LP. -/
def primal {n c : ℕ} {A : Type*} [MeasurableSpace A]
    (M : Model n c A) (x : ℕ → Fin c) (T : ℕ) : MeasureProgram A T n where
  cost t a := ∑ i : Fin n, M.reward i * M.prob (x t.val) a i
  use t i a := M.prob (x t.val) a i
  budget i := (M.capacity i : ℕ)

def optimum {n c : ℕ} {A : Type*} [MeasurableSpace A]
    (M : Model n c A) (x : ℕ → Fin c) (T : ℕ) : EReal :=
  (primal M x T).value

/-- Literal dual constraints (32)--(33), with all the implicit action/time indices. -/
def DualFeasible {n c : ℕ} {A : Type*} [MeasurableSpace A]
    (M : Model n c A) (x : ℕ → Fin c) (T : ℕ)
    (Λ : Fin n → ℝ) (Γ : Fin T → ℝ) : Prop :=
  (∀ t a, (∑ i : Fin n, M.prob (x t.val) a i * (M.reward i - Λ i)) ≤ Γ t) ∧
  ∀ (t : Fin T) a i, 0 ≤ M.prob (x t.val) a i * Λ i

/-- Final inventory potential (34). -/
def certificateLambda {n c : ℕ} {A : Type*} [MeasurableSpace A]
    (M : Model n c A) (ε : ℝ) (h : History n c A) (i : Fin n) : ℝ :=
  M.reward i * potential ε ((inventory M.capacity h i : ℝ) / (M.capacity i : ℕ))

/-- Dynamic best-action value (35) from the prefix before period t+1. -/
def certificateGamma {n c : ℕ} {A : Type*} [MeasurableSpace A]
    (M : Model n c A) (ε : ℝ) (x : ℕ → Fin c) (T : ℕ)
    (h : History n c A) (t : Fin T) : ℝ :=
  bestReward M ε (h.take t.val) (x t.val)

def certificateObjective {n c : ℕ} {A : Type*} [MeasurableSpace A]
    (M : Model n c A) (ε : ℝ) (x : ℕ → Fin c) (T : ℕ) (h : History n c A) : ℝ :=
  (∑ t : Fin T, certificateGamma M ε x T h t) +
    ∑ i : Fin n, (M.capacity i : ℕ) * certificateLambda M ε h i

end CheungIBOL.General


