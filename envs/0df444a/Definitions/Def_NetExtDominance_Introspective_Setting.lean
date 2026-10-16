-- Prove2me | Definitions.Def_NetExtDominance_Introspective_Setting
-- name    : NetExtDominance_Introspective_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T08:02:36.816122+00:00
-- url     : https://prove2.me/theorems/e66b1164-1032-45d8-8fcb-b29951160582
-- title:
--   §2, footnote 7, Definition 1 — aggregate demand, In/Out demand, and introspective equilibrium
-- statement:
--   A **market** has aggregate demand $D(p,Q)$ for firm 1 at relative price $p=p_1-p_2$ and current quantity $Q\in[0,1]$, together with an inverse demand curve $P$. Demand takes values in $[0,1]$, is continuous in $(p,Q)$ on the feasible domain, weakly decreases as $p$ rises, and weakly increases as $Q$ rises. The inverse-demand identity is
--
--   $$D(P(Q),Q)=Q\qquad(0\le Q\le1).$$
--
--   At a feasible interior quantity, demand lies strictly above $Q$ when $p<P(Q)$ and strictly below $Q$ when $p>P(Q)$; these signs are required only away from the saturation boundaries $Q=1$ and $Q=0$, respectively.
--
--   **In/Out demand** has thresholds $0<Q_L<Q_H<1$. The curve $P$ is strictly decreasing and weakly convex on $[0,Q_L]$, strictly increasing on $[Q_L,Q_H]$, and strictly decreasing and weakly concave on $[Q_H,1]$. Set $p_{\min}=P(Q_L)$ and $p_{\max}=P(Q_H)$, with $p_{\max}<P(0)$ and $P(1)<p_{\min}$. For a price $p$, $Q^{\mathrm{out}}(p)$, $Q^{\mathrm{mid}}(p)$, and $Q^{\mathrm{in}}(p)$ mean intersections of $P(Q)=p$ on the three respective closed branches. The notation is represented by predicates that also give the branch membership.
--
--   An **equilibrium quantity** is $Q\in[0,1]$ satisfying $D(p,Q)=Q$. From an impulse $I_0\in[0,1]$, **level-$k$ consumption** is the $k$-fold iteration
--
--   $$I_k=D(p,\cdot)^{\circ k}(I_0),$$
--
--   and an **introspective equilibrium** at $Q$ means $I_k\to Q$ as $k\to\infty$.
--
--   These shared objects state the selection result and its supporting claims.
--
--   **Formalization Note** The market records the paper's continuity and monotonicity assumptions on feasible quantities. The paper says demand is decreasing in price; the strict signs at inverse-demand points make precise the use of that phrase in footnote 12. Its claim of strict increase in quantity is weakened to weak increase because the stated consumer model can have saturated demand. The consumer-type distribution and the firms' pricing game are outside this interface. One aggregate demand map covers both the one-firm convention and the two-firm relative-price case.
-- source:
--   Akerlof, Holden & Rayo, Network Externalities and Market Dominance, author's accepted manuscript (WRAP 178238, dated September 16, 2022), pp. 4–9, §2, (1)–(3), footnote 7, §2.1, Definition 1; http://wrap.warwick.ac.uk/178238

import Mathlib

open Filter Topology

namespace NetExtDominance.Introspective

/-- Aggregate and inverse demand, with the standing conditions of §2. -/
structure Market where
  D : ℝ → ℝ → ℝ
  P : ℝ → ℝ
  hD01 : ∀ p, ∀ Q ∈ Set.Icc (0 : ℝ) 1, 0 ≤ D p Q ∧ D p Q ≤ 1
  hDcont : ContinuousOn (Function.uncurry D) (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)
  hDanti : ∀ Q ∈ Set.Icc (0 : ℝ) 1, Antitone (fun p => D p Q)
  hDmono : ∀ p, MonotoneOn (D p) (Set.Icc (0 : ℝ) 1)
  hP : ∀ Q ∈ Set.Icc (0 : ℝ) 1, D (P Q) Q = Q
  hPabove : ∀ Q ∈ Set.Icc (0 : ℝ) 1, ∀ p, p < P Q → Q < 1 → Q < D p Q
  hPbelow : ∀ Q ∈ Set.Icc (0 : ℝ) 1, ∀ p, P Q < p → 0 < Q → D p Q < Q

/-- Figure 1(a)'s upper price threshold. -/
def pmax (P : ℝ → ℝ) (QH : ℝ) : ℝ := P QH

/-- Figure 1(a)'s lower price threshold. -/
def pmin (P : ℝ → ℝ) (QL : ℝ) : ℝ := P QL

/-- Footnote 7's In/Out shape and the endpoint price inequalities. -/
def IsInOut (P : ℝ → ℝ) (QL QH : ℝ) : Prop :=
  0 < QL ∧ QL < QH ∧ QH < 1 ∧
    StrictAntiOn P (Set.Icc 0 QL) ∧ ConvexOn ℝ (Set.Icc 0 QL) P ∧
    StrictMonoOn P (Set.Icc QL QH) ∧
    StrictAntiOn P (Set.Icc QH 1) ∧ ConcaveOn ℝ (Set.Icc QH 1) P ∧
    pmax P QH < P 0 ∧ P 1 < pmin P QL

/-- The out branch intersection of the inverse demand curve with price `p`. -/
def IsQout (P : ℝ → ℝ) (QL p q : ℝ) : Prop :=
  q ∈ Set.Icc 0 QL ∧ P q = p

/-- The middle branch intersection of the inverse demand curve with price `p`. -/
def IsQmid (P : ℝ → ℝ) (QL QH p q : ℝ) : Prop :=
  q ∈ Set.Icc QL QH ∧ P q = p

/-- The in branch intersection of the inverse demand curve with price `p`. -/
def IsQin (P : ℝ → ℝ) (QH p q : ℝ) : Prop :=
  q ∈ Set.Icc QH 1 ∧ P q = p

/-- Equilibrium equation (1), restricted to feasible quantities. -/
def IsEquilibriumQty (M : Market) (p Q : ℝ) : Prop :=
  Q ∈ Set.Icc 0 1 ∧ M.D p Q = Q

/-- Level-`k` consumption of Definition 1, starting from impulse `I0`. -/
def levelK (M : Market) (p I0 : ℝ) (k : ℕ) : ℝ :=
  (M.D p)^[k] I0

/-- Definition 1's limit of the actual level-`k` recursion. -/
def IsIntrospectiveEq (M : Market) (p I0 Q : ℝ) : Prop :=
  Tendsto (levelK M p I0) atTop (𝓝 Q)

end NetExtDominance.Introspective


