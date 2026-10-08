-- Prove2me | Definitions.Def_FedergruenZhengRQ_OPT_Model
-- name    : FedergruenZhengRQ_OPT_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T11:38:04.609922+00:00
-- url     : https://prove2.me/theorems/4b6136e7-8ba7-4c6f-bb70-1094212e9889
-- title:
--   Eq. (1), the window sequence $y_Q$ of §2 and Algorithm OPT (Step 1)
-- statement:
--   This module fixes the model of Federgruen and Zheng (1992) and the objects their algorithm manipulates.
--
--   **Data.** A fixed order cost $\kappa$ and a function $G:\mathbb Z\to\mathbb R$ (the expected holding and backlogging cost rate at inventory position $y$). Inventory positions $y$, reorder points $r$ are integers; order quantities $Q$ are positive integers.
--
--   **Standing assumptions (as predicates).**
--
--   1. $-G$ is *unimodal*: there is an integer $m$ such that $G$ is nonincreasing on $\{y\le m\}$ and nondecreasing on $\{y\ge m\}$. Plateaus are allowed.
--   2. *Coercivity*: $\lim_{|y|\to\infty}G(y)=\infty$, i.e. $G(y)\to+\infty$ both as $y\to-\infty$ and as $y\to+\infty$.
--
--   **The cost (1).** For an integer reorder point $r$ and an order quantity $Q\ge1$, the long-run average cost of the $(r,Q)$ policy is
--   $$C(r,Q)=\Big[\kappa+\sum_{y=r+1}^{r+Q}G(y)\Big]\Big/Q.$$
--
--   **The sequence $y_Q$ (§2).** Given an integer $y_1$, define windows $[L(Q),R(Q)]$ and points $y_Q$ by $L(1)=R(1)=y_1$ and, for $Q\ge1$,
--   $$y_{Q+1}=\begin{cases}L(Q)-1 & \text{if } G(L(Q)-1)\le G(R(Q)+1),\\ R(Q)+1 & \text{otherwise,}\end{cases}$$
--   with the window extended on the side of $y_{Q+1}$: $L(Q+1)=L(Q)-1$, $R(Q+1)=R(Q)$ in the first case and $L(Q+1)=L(Q)$, $R(Q+1)=R(Q)+1$ in the second. Ties go to the left. Further,
--   $$C^*(Q)=\Big[\kappa+\sum_{i=1}^{Q}G(y_i)\Big]\Big/Q .$$
--
--   **Algorithm OPT, Step 1.** The state consists of $S$, $Q$, $C^*$, $r$, $R$. Starting from $S=\kappa+G(y_1)$, $Q=1$, $C^*=S$, $r=y_1-1$, $R=y_1+1$ (the state at the end of Step 0 when Step 0 has located $y_1$), each pass does: if $G(r)\le G(R)$ then stop with output $(r,Q)$ if $C^*\le G(r)$, else set $S:=S+G(r)$, $r:=r-1$; otherwise stop with output $(r,Q)$ if $C^*\le G(R)$, else set $S:=S+G(R)$, $R:=R+1$; after a non-stopping pass, $Q:=Q+1$ and $C^*:=S/Q$. The run with a budget of $n$ passes returns the output if the algorithm stops within $n$ passes, and nothing otherwise. An auxiliary state $\big(\kappa+\sum_{i\le Q}G(y_i),\,Q,\,C^*(Q),\,L(Q)-1,\,R(Q)+1\big)$ records what Step 1 should hold after $Q$ points.
--
--   These are the objects of Lemmas 1–2 and Theorem 1; the statements about them are separate items.
--
--   **Formalization Note.** `cost κ G r Q` divides by `Q`, so it is only meaningful for `Q ≥ 1` (Lean gives `cost κ G r 0 = 0`); every statement quantifies over `Q ≥ 1`. The window is defined by recursion on the pair $(L,R)$ (`window G y₁ n` is $(L(n+1),R(n+1))$); `L G y₁ 0`, `R G y₁ 0` and `y G y₁ 0` are junk values never used. That $L(Q),R(Q)$ are the minimum and maximum of $\{y_1,\dots,y_Q\}$, as the paper defines them, is a separate theorem. In Step 1, $G$ is evaluated directly; the page's $\Delta G$ bookkeeping ("evaluate $\Delta G(r)$ and $G(r):=G(r+1)-\Delta G(r)$") only computes these values. The run returns `none` when the budget is exhausted, never a default output.
-- source:
--   Federgruen and Zheng, An Efficient Algorithm for Computing an Optimal (r, Q) Policy in Continuous Review Stochastic Inventory Systems, Oper. Res. 40(4) (1992), (1) and the standing assumptions (p. 808), §2 preamble, the sequence y_Q, C*(Q) and Algorithm OPT (p. 811)

import Mathlib

namespace FedergruenZhengRQ.OPT

/-- `−G` is unimodal: `G` is nonincreasing up to some integer `m` and nondecreasing from `m` on.
Plateaus (equal consecutive values) are allowed. -/
def NegUnimodal (G : ℤ → ℝ) : Prop :=
  ∃ m : ℤ, AntitoneOn G (Set.Iic m) ∧ MonotoneOn G (Set.Ici m)

/-- `lim_{|y| → ∞} G(y) = ∞`: `G(y) → +∞` both as `y → −∞` and as `y → +∞`. -/
def Coercive (G : ℤ → ℝ) : Prop :=
  Filter.Tendsto G Filter.atBot Filter.atTop ∧ Filter.Tendsto G Filter.atTop Filter.atTop

/-- The long-run average cost (1) of the `(r, Q)` policy:
`C(r, Q) = [κ + ∑_{y = r+1}^{r+Q} G(y)] / Q`. Only meaningful for `Q ≥ 1`
(Lean's `x / 0 = 0` makes `cost κ G r 0 = 0`). -/
noncomputable def cost (κ : ℝ) (G : ℤ → ℝ) (r : ℤ) (Q : ℕ) : ℝ :=
  (κ + ∑ y ∈ Finset.Ioc r (r + (Q : ℤ)), G y) / (Q : ℝ)

/-- The window recursion of §2: `window G y₁ n = (L(n+1), R(n+1))`. It starts at `(y₁, y₁)` and
extends to the left when `G(L − 1) ≤ G(R + 1)` (ties go left), otherwise to the right. -/
noncomputable def window (G : ℤ → ℝ) (y₁ : ℤ) : ℕ → ℤ × ℤ
  | 0 => (y₁, y₁)
  | n + 1 =>
    if G ((window G y₁ n).1 - 1) ≤ G ((window G y₁ n).2 + 1) then
      ((window G y₁ n).1 - 1, (window G y₁ n).2)
    else
      ((window G y₁ n).1, (window G y₁ n).2 + 1)

/-- `L(Q)`, the left end of the window after `Q ≥ 1` points (`L 0` is a junk value, equal to `L 1`). -/
noncomputable def L (G : ℤ → ℝ) (y₁ : ℤ) (Q : ℕ) : ℤ := (window G y₁ (Q - 1)).1

/-- `R(Q)`, the right end of the window after `Q ≥ 1` points (`R 0` is a junk value, equal to `R 1`). -/
noncomputable def R (G : ℤ → ℝ) (y₁ : ℤ) (Q : ℕ) : ℤ := (window G y₁ (Q - 1)).2

/-- The sequence `y_1, y_2, …` of §2, 1-based: `y_1 = y₁` and
`y_{Q+1} = L(Q) − 1` if `G(L(Q) − 1) ≤ G(R(Q) + 1)`, else `R(Q) + 1`.
`y 0` is a junk value (set to `y₁`) and is never used. -/
noncomputable def y (G : ℤ → ℝ) (y₁ : ℤ) : ℕ → ℤ
  | 0 => y₁
  | 1 => y₁
  | Q + 2 =>
    if G (L G y₁ (Q + 1) - 1) ≤ G (R G y₁ (Q + 1) + 1) then L G y₁ (Q + 1) - 1
    else R G y₁ (Q + 1) + 1

/-- `C*(Q) = [κ + ∑_{i=1}^{Q} G(y_i)] / Q`, the page's formula (meaningful for `Q ≥ 1`). -/
noncomputable def Cstar (κ : ℝ) (G : ℤ → ℝ) (y₁ : ℤ) (Q : ℕ) : ℝ :=
  (κ + ∑ i ∈ Finset.Icc 1 Q, G (y G y₁ i)) / (Q : ℝ)

/-- The variables of Algorithm OPT: `S`, `Q`, `C*` (here `Cst`), `r` and `R`. -/
structure OPTState where
  S : ℝ
  Q : ℕ
  Cst : ℝ
  r : ℤ
  R : ℤ

/-- The state at the end of Step 0 when Step 0 has located the minimizer `L = y₁`:
`S := κ + G(L), Q := 1, C* := S, r := L − 1, R := L + 1`. -/
noncomputable def optInit (κ : ℝ) (G : ℤ → ℝ) (y₁ : ℤ) : OPTState :=
  ⟨κ + G y₁, 1, κ + G y₁, y₁ - 1, y₁ + 1⟩

/-- One pass of the `Repeat` body of Step 1. `Sum.inl (r, Q)` means "stop" with output `(r, Q)`;
`Sum.inr s'` is the state for the next pass. `G` is evaluated directly (the `ΔG` bookkeeping of the
page only computes `G(r)` and `G(R + 1)`). -/
noncomputable def optStep (G : ℤ → ℝ) (s : OPTState) : (ℤ × ℕ) ⊕ OPTState :=
  if G s.r ≤ G s.R then
    if s.Cst ≤ G s.r then Sum.inl (s.r, s.Q)
    else Sum.inr ⟨s.S + G s.r, s.Q + 1, (s.S + G s.r) / ((s.Q + 1 : ℕ) : ℝ), s.r - 1, s.R⟩
  else
    if s.Cst ≤ G s.R then Sum.inl (s.r, s.Q)
    else Sum.inr ⟨s.S + G s.R, s.Q + 1, (s.S + G s.R) / ((s.Q + 1 : ℕ) : ℝ), s.r, s.R + 1⟩

/-- Iterate Step 1 from a state with at most `n` passes; `none` if the fuel runs out first. -/
noncomputable def optLoop (G : ℤ → ℝ) : ℕ → OPTState → Option (ℤ × ℕ)
  | 0, _ => none
  | n + 1, s =>
    match optStep G s with
    | Sum.inl out => some out
    | Sum.inr s' => optLoop G n s'

/-- Algorithm OPT (Step 1 started from the minimizer `y₁`) with fuel `n`: `some (r, Q)` if it
stops within `n` passes with output `(r, Q)`, `none` otherwise. -/
noncomputable def optRun (κ : ℝ) (G : ℤ → ℝ) (y₁ : ℤ) (n : ℕ) : Option (ℤ × ℕ) :=
  optLoop G n (optInit κ G y₁)

/-- The state Step 1 should hold after `Q` points have been collected:
`S = κ + ∑_{i ≤ Q} G(y_i)`, `C* = C*(Q)`, `r = L(Q) − 1`, `R = R(Q) + 1`. -/
noncomputable def stateAt (κ : ℝ) (G : ℤ → ℝ) (y₁ : ℤ) (Q : ℕ) : OPTState :=
  ⟨κ + ∑ i ∈ Finset.Icc 1 Q, G (y G y₁ i), Q, Cstar κ G y₁ Q, L G y₁ Q - 1, R G y₁ Q + 1⟩

end FedergruenZhengRQ.OPT


