-- Prove2me | Definitions.Def_XuDRMDP_Finite_Robustness
-- name    : XuDRMDP_Finite_Robustness
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T05:29:33.19799+00:00
-- url     : https://prove2.me/theorems/3948c979-c8f6-4a49-8d52-ed43690e4fcb
-- title:
--   Backward S-robustness and distributional saddle predicates
-- statement:
--   Define $Q_s(q,x,v)=\sum_a q(a)[r_x(a)+\gamma\sum_jp_x(j\mid a)v(j)]$ and $L_s(q,v)=\inf_{x\in\widehat P_s}Q_s(q,x,v)$. Starting from zero with no decisions left, the backward recursion takes the supremum of $L_s(q,v)$ over the action simplex at nonterminal states and takes zero at terminal states. The robust value at $s$ uses exactly $T-1-t(s)$ steps. This is Definition 3.2's finite backward recursion. Compact nonempty reduction sets and compact nonempty simplices ensure that these real infima and suprema are finite and attained; this is not assumed as a model field.
--
--   A policy is S-robust when its mixed action maximizes $L_s(q,\widetilde v)$ after every structurally admissible nonterminal history. Terminal choices are unrestricted. The continuation vector is the statewise backward value; valid transition rows vanish outside the next stage.
--
--   The worst performance of a policy is $\inf_{\nu\in C_S}W(\pi,\nu)$. A distributionally robust policy dominates each other policy's own worst performance. A saddle pair consists of an admissible global law $\nu^*$ and a policy $\pi^*$ such that $W(\pi,\nu^*)\le W(\pi^*,\nu^*)\le W(\pi^*,\nu)$ for every policy $\pi$ and every admissible law $\nu$. Because the pair itself belongs to both optimization domains, these inequalities encode the two attained equalities in Theorem 3.1. The nonempty compact outer parameter supports uniformly bound all policy returns; real infimum defaults therefore do not enter admissible instances.
-- source:
--   Xu and Mannor (2012), Distributionally Robust Markov Decision Processes, Mathematics of Operations Research 37(2), 288–300, DOI:10.1287/moor.1120.0540. Published basis; printed page = PDF page + 287. Sections 2–3, printed pp. 289–293 (PDF pp. 2–6).

import Definitions.Def_XuDRMDP_Finite_Returns
open MeasureTheory
open scoped BigOperators

namespace XuDRMDP.Finite

noncomputable def actionValue {n : ℕ} {a : Fin n → ℕ}
    (G : Setup n a) (s : Fin n) (q : MixedAction a s) (x : Local n a s)
    (v : Fin n → ℝ) : ℝ :=
  ∑ b, q.val b * (x.2 b + G.discount * ∑ j, x.1 b j * v j)

noncomputable def lowerActionValue {n : ℕ} [NeZero n] {a : Fin n → ℕ}
    [∀ s, NeZero (a s)] {G : Setup n a} (U : Uncertainty G)
    (s : Fin n) (q : MixedAction a s) (v : Fin n → ℝ) : ℝ :=
  sInf ((fun x => actionValue G s q x v) '' reducedSet U s)

/-- Explicit finite backward recursion. Fuel is the number of remaining decisions. -/
noncomputable def backward {n : ℕ} [NeZero n] {a : Fin n → ℕ}
    [∀ s, NeZero (a s)] {G : Setup n a} (U : Uncertainty G) : ℕ → Fin n → ℝ
  | 0, _ => 0
  | k + 1, s => if G.stage s + 1 < G.horizon then
      sSup (Set.range fun q : MixedAction a s => lowerActionValue U s q (backward U k))
    else 0

noncomputable def robustValue {n : ℕ} [NeZero n] {a : Fin n → ℕ}
    [∀ s, NeZero (a s)] {G : Setup n a} (U : Uncertainty G) (s : Fin n) : ℝ :=
  backward U (G.horizon - 1 - G.stage s) s

/-- Definition 3.2: a local maximizer after every admissible nonterminal history. -/
def SRobust {n : ℕ} [NeZero n] {a : Fin n → ℕ} [∀ s, NeZero (a s)]
    {G : Setup n a} (U : Uncertainty G) (π : Policy a) : Prop :=
  ∀ h, Admissible G h → G.stage h.state + 1 < G.horizon →
    ∀ q : MixedAction a h.state,
      lowerActionValue U h.state q (robustValue U) ≤
        lowerActionValue U h.state (π h) (robustValue U)

noncomputable def worstPerformance {n : ℕ} [NeZero n] {a : Fin n → ℕ}
    [∀ s, NeZero (a s)] {G : Setup n a} (U : Uncertainty G) (π : Policy a) : ℝ :=
  sInf ((fun ν => performance G π ν) '' globalClass U)

/-- Definition 3.1; every competitor has its own worst law. -/
def DistributionallyRobust {n : ℕ} [NeZero n] {a : Fin n → ℕ}
    [∀ s, NeZero (a s)] {G : Setup n a} (U : Uncertainty G) (π : Policy a) : Prop :=
  ∀ π' : Policy a, worstPerformance U π' ≤ worstPerformance U π

/-- Membership and all-competitor inequalities encode the attained sup/inf saddle. -/
def Saddle {n : ℕ} [NeZero n] {a : Fin n → ℕ} [∀ s, NeZero (a s)]
    {G : Setup n a} (U : Uncertainty G) (π : Policy a)
    (ν : Measure (Parameters n a)) : Prop :=
  ν ∈ globalClass U ∧
  (∀ π' : Policy a, performance G π' ν ≤ performance G π ν) ∧
  (∀ ν' ∈ globalClass U, performance G π ν ≤ performance G π ν')

end XuDRMDP.Finite


