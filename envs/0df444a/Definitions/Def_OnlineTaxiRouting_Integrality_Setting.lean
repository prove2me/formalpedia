-- Prove2me | Definitions.Def_OnlineTaxiRouting_Integrality_Setting
-- name    : OnlineTaxiRouting_Integrality_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:27:27.353114+00:00
-- url     : https://prove2.me/theorems/f6cbf933-779a-474d-9866-5695887e638a
-- title:
--   §2.1, §3.2, pp. 7–13 — taxi routing instance, arc rule (1), acyclicity, the MIO (5)–(14), its LP relaxation, the flow system (6)–(11), integrality
-- statement:
--   This file fixes the objects of the offline taxi routing problem of Bertsimas, Jaillet and Martin.
--
--   **Instance.** Let $\mathcal C$ be a finite set of customers and $\mathcal K$ a finite set of taxis. Each customer $c$ has a pick-up time window $[t^{\min}_c, t^{\max}_c]$; each taxi $k$ becomes available at its initial time of service $t^{\mathrm{init}}_k$. For customers $c', c$ the number $T_{c',c}$ is the travel time from (serving) $c'$ to the pick-up of $c$, and $R_{c',c}$ the profit of serving $c$ right after $c'$; $T_{k,c}$ and $R_{k,c}$ are the travel time and profit when $c$ is the first customer of taxi $k$. No sign conditions are imposed on these data.
--
--   **Graph.** There is an arc $c \to c'$ between customers if and only if
--   $$t^{\min}_c + T_{c,c'} \le t^{\max}_{c'}. \qquad (1)$$
--   The instance is *acyclic* if this arc relation has no directed cycle (no customer reaches itself by a nonempty chain of arcs); taxi nodes have no incoming arcs, so this is acyclicity of the whole graph $\mathcal G$.
--
--   **Formulation.** A point is a quadruple $(x, y, p, t)$ with $x = (x_{c',c})_{c',c \in \mathcal C}$, $y = (y_{k,c})_{k\in\mathcal K, c \in \mathcal C}$, $p = (p_c)_{c\in\mathcal C}$ and $t = (t_c)_{c \in \mathcal C}$, all real. The objective (5) is $\sum_{k,c} R_{k,c} y_{k,c} + \sum_{c',c} R_{c',c} x_{c',c}$. The **LP relaxation** of the mixed-integer formulation (5)–(14) is the set of points satisfying
--   $$
--   \begin{aligned}
--   &p_c = \textstyle\sum_{k} y_{k,c} + \sum_{c'} x_{c',c} \ \ \forall c, \qquad \textstyle\sum_{c} x_{c',c} \le p_{c'} \ \ \forall c', \qquad \textstyle\sum_c y_{k,c} \le 1 \ \ \forall k,\\
--   &0 \le x_{c',c},\, y_{k,c},\, p_c \le 1,\\
--   &t^{\min}_c \le t_c \le t^{\max}_c, \\
--   &t_c - t_{c'} \ge (t^{\min}_c - t^{\max}_{c'}) + \big(T_{c',c} - (t^{\min}_c - t^{\max}_{c'})\big)\, x_{c',c} \ \ \forall c, c',\\
--   &t_c \ge t^{\min}_c + (t^{\mathrm{init}}_k + T_{k,c} - t^{\min}_c)\, y_{k,c} \ \ \forall c, k,
--   \end{aligned}
--   $$
--   that is, (6)–(8) and (12)–(14) as printed, with the binary constraints (9)–(11) replaced by the bounds $0 \le \cdot \le 1$. The feasible set of the MIO itself adds $x, y, p \in \{0,1\}$; the times $t$ stay continuous. A set of points is **integral** if each of its extreme points has $x, y, p \in \{0,1\}$; nothing is required of $t$.
--
--   **Flow system.** For arc subsets $A \subseteq \mathcal C \times \mathcal C$ and $B \subseteq \mathcal K \times \mathcal C$, the relaxed flow system on $A \cup B$ is the set of $(x, y, p)$ satisfying (6)–(8), the bounds $0 \le x, y, p \le 1$, and $x_{c',c} = 0$ for $(c',c) \notin A$, $y_{k,c} = 0$ for $(k,c) \notin B$ (the variable is removed). Finally, for a vector $t^*$ the **fixed-time instance** replaces both window ends of every customer $c$ by $t^*_c$.
--
--   These are the objects of Theorem 1 and of the steps of its proof.
--
--   **Formalization Note** Indices are arbitrary finite types; the variables $x$ and the time constraints (13) range over all ordered pairs $(c', c)$, the diagonal included, as printed, not only over the arcs of $\mathcal G$. A point is an element of the real vector space $(\mathcal C\times\mathcal C \to \mathbb R) \times (\mathcal K\times\mathcal C \to \mathbb R) \times (\mathcal C \to \mathbb R)\times(\mathcal C\to\mathbb R)$, so that extreme points are Mathlib's `Set.extremePoints ℝ`.
-- source:
--   Bertsimas–Jaillet–Martin, accepted manuscript (March 2018), §2.1 (pp. 7–8), §3.2 (pp. 11–13), displays (1), (5)–(14)

import Mathlib

namespace OnlineTaxiRouting.Integrality

/-- Data of an offline taxi routing instance (Bertsimas–Jaillet–Martin, §2.1, pp. 7–8):
customers `C`, taxis `K`, pick-up time windows `[tmin c, tmax c]`, the initial time of service
`tinit k` of taxi `k`, travel times `T c' c` = T_{c′,c} (customer `c'` to customer `c`) and
`Tk k c` = T_{k,c} (taxi `k` to its first customer `c`), and profits `R c' c` = R_{c′,c},
`Rk k c` = R_{k,c}. No sign or ordering conditions are imposed. -/
structure Instance (C K : Type*) where
  tmin : C → ℝ
  tmax : C → ℝ
  tinit : K → ℝ
  T : C → C → ℝ
  Tk : K → C → ℝ
  R : C → C → ℝ
  Rk : K → C → ℝ

variable {C K : Type*}

/-- Display (1), p. 7: there is an arc `c → c'` in the customer graph `G` iff
`t^min_c + T_{c,c'} ≤ t^max_{c'}`. -/
def Instance.Arc (I : Instance C K) (c c' : C) : Prop :=
  I.tmin c + I.T c c' ≤ I.tmax c'

/-- §2.1, p. 7, standing assumption: the graph `G` is acyclic. Taxi nodes have no incoming
arcs, so every cycle of `G` runs through customers only. -/
def Instance.Acyclic (I : Instance C K) : Prop :=
  ∀ c, ¬ Relation.TransGen I.Arc c c

/-- A point `(x, y, p, t)` of the formulation (5)–(14): `v.1 c' c = x_{c′,c}`,
`v.2.1 k c = y_{k,c}`, `v.2.2.1 c = p_c`, `v.2.2.2 c = t_c`. -/
abbrev Var (C K : Type*) := (C → C → ℝ) × (K → C → ℝ) × (C → ℝ) × (C → ℝ)

/-- A point `(x, y, p)` of the flow variables only. -/
abbrev FlowVar (C K : Type*) := (C → C → ℝ) × (K → C → ℝ) × (C → ℝ)

/-- The objective (5), p. 11: `∑_{k,c} R_{k,c} y_{k,c} + ∑_{c',c} R_{c',c} x_{c',c}`. -/
def objective [Fintype C] [Fintype K] (I : Instance C K) (v : Var C K) : ℝ :=
  (∑ k, ∑ c, I.Rk k c * v.2.1 k c) + ∑ c', ∑ c, I.R c' c * v.1 c' c

/-- The LP relaxation of (5)–(14), pp. 11–12: constraints (6)–(8) and (12)–(14) as printed,
with the binary constraints (9)–(11) replaced by `0 ≤ x, y, p ≤ 1`. -/
def relax [Fintype C] [Fintype K] (I : Instance C K) : Set (Var C K) :=
  {v |
    -- (6)
    (∀ c, v.2.2.1 c = (∑ k, v.2.1 k c) + ∑ c', v.1 c' c) ∧
    -- (7)
    (∀ c', ∑ c, v.1 c' c ≤ v.2.2.1 c') ∧
    -- (8)
    (∀ k, ∑ c, v.2.1 k c ≤ 1) ∧
    -- (9) relaxed
    (∀ c' c, 0 ≤ v.1 c' c ∧ v.1 c' c ≤ 1) ∧
    -- (10) relaxed
    (∀ k c, 0 ≤ v.2.1 k c ∧ v.2.1 k c ≤ 1) ∧
    -- (11) relaxed
    (∀ c, 0 ≤ v.2.2.1 c ∧ v.2.2.1 c ≤ 1) ∧
    -- (12)
    (∀ c, I.tmin c ≤ v.2.2.2 c ∧ v.2.2.2 c ≤ I.tmax c) ∧
    -- (13)
    (∀ c c', (I.tmin c - I.tmax c') + (I.T c' c - (I.tmin c - I.tmax c')) * v.1 c' c
        ≤ v.2.2.2 c - v.2.2.2 c') ∧
    -- (14)
    (∀ c k, I.tmin c + (I.tinit k + I.Tk k c - I.tmin c) * v.2.1 k c ≤ v.2.2.2 c)}

/-- Every `x_{c′,c}`, `y_{k,c}` and `p_c` of `v` is `0` or `1` (nothing is required of `t`). -/
def IsZeroOne (v : Var C K) : Prop :=
  (∀ c' c, v.1 c' c = 0 ∨ v.1 c' c = 1) ∧
  (∀ k c, v.2.1 k c = 0 ∨ v.2.1 k c = 1) ∧
  (∀ c, v.2.2.1 c = 0 ∨ v.2.2.1 c = 1)

/-- Every coordinate of the flow point `w = (x, y, p)` is `0` or `1`. -/
def IsZeroOneFlow (w : FlowVar C K) : Prop :=
  (∀ c' c, w.1 c' c = 0 ∨ w.1 c' c = 1) ∧
  (∀ k c, w.2.1 k c = 0 ∨ w.2.1 k c = 1) ∧
  (∀ c, w.2.2 c = 0 ∨ w.2.2 c = 1)

/-- The feasible set of the mixed-integer formulation (6)–(14). -/
def mio [Fintype C] [Fintype K] (I : Instance C K) : Set (Var C K) :=
  {v | v ∈ relax I ∧ IsZeroOne v}

/-- "Extreme points of the formulation are integral" (p. 13): every extreme point of `S` has
`x, y, p ∈ {0, 1}`. -/
def IsIntegral (S : Set (Var C K)) : Prop :=
  ∀ v ∈ Set.extremePoints ℝ S, IsZeroOne v

/-- The relaxed network-flow system (6)–(11) (pp. 11–12) on the arc subset `A ∪ B`: constraints
(6)–(8), the bounds `0 ≤ x, y, p ≤ 1`, and `x_{c′,c} = 0` for `¬ A c' c`, `y_{k,c} = 0` for
`¬ B k c` (the variable is removed). With `A = B = ⊤` it is (6)–(11) with (9)–(11) relaxed. -/
def flowRelax [Fintype C] [Fintype K] (A : C → C → Prop) (B : K → C → Prop) :
    Set (FlowVar C K) :=
  {w |
    (∀ c, w.2.2 c = (∑ k, w.2.1 k c) + ∑ c', w.1 c' c) ∧
    (∀ c', ∑ c, w.1 c' c ≤ w.2.2 c') ∧
    (∀ k, ∑ c, w.2.1 k c ≤ 1) ∧
    (∀ c' c, 0 ≤ w.1 c' c ∧ w.1 c' c ≤ 1) ∧
    (∀ k c, 0 ≤ w.2.1 k c ∧ w.2.1 k c ≤ 1) ∧
    (∀ c, 0 ≤ w.2.2 c ∧ w.2.2 c ≤ 1) ∧
    (∀ c' c, ¬ A c' c → w.1 c' c = 0) ∧
    (∀ k c, ¬ B k c → w.2.1 k c = 0)}

/-- The fixed-time instance of p. 13: both window ends of customer `c` are set to `ts c`. -/
def fixAt (I : Instance C K) (ts : C → ℝ) : Instance C K :=
  { I with tmin := ts, tmax := ts }

end OnlineTaxiRouting.Integrality


