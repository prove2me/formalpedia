-- Prove2me | Definitions.Def_ConstrainedDirSep_STSep_Quadrant
-- name    : ConstrainedDirSep_STSep_Quadrant
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:04:58.170102+00:00
-- url     : https://prove2.me/theorems/757b0a5f-df58-4206-a537-bb054c14232d
-- title:
--   Quadrant constraints, windows, staircase boundaries L and U, increasing chains, min/max closure
-- statement:
--   For variables $X, Y$ with domains $[d_X]=\{1,\dots,d_X\}$ and $[d_Y]$, a **quadrant constraint** is
--   $$Q^{\searrow}_{a,b}(x,y):\ \neg(x\ge a\wedge y\le b),\qquad Q^{\nwarrow}_{a,b}(x,y):\ \neg(x\le a\wedge y\ge b),$$
--   with thresholds $a\in[d_X+1]$, $b\in\{0\}\cup[d_Y]$ for $Q^{\searrow}$ and $a\in\{0\}\cup[d_X]$, $b\in[d_Y+1]$ for $Q^{\nwarrow}$ (`WellRanged`). $Q^{\searrow}_{a,b}$ is **vacuous** when $a=d_X+1$ or $b=0$, $Q^{\nwarrow}_{a,b}$ when $a=0$ or $b=d_Y+1$; otherwise **nonvacuous**.
--
--   For a finite set $Q$ of quadrant constraints, the **window** $W$ is the set of $(p,q)\in[d_X]\times[d_Y]$ satisfying every constraint of $Q$. The staircase boundaries (7)–(8) are
--   $$L(p)=1+\max\big(\{b: Q^{\searrow}_{a,b}\in Q,\ a\le p\}\cup\{0\}\big),\qquad U(p)=-1+\min\big(\{b: Q^{\nwarrow}_{a,b}\in Q,\ p\le a\}\cup\{d_Y+1\}\big).$$
--   A set $T\subseteq\mathbb N^2$ is an **increasing chain** if any two of its points are comparable coordinatewise; it is **min-closed** (**min–max closed**) if it contains the coordinatewise minimum (and maximum) of any two of its points.
--
--   **Formalization Note.** $L$ and $U$ are integer-valued, so the $-1$ in $U$ is never truncated.
-- source:
--   Olkowski, Ramanujan, Constrained Directed Separation: Algorithms and Classifications, STOC 2027 submission (manuscript sha256 4dd06c29…), pp. 14–16 (PDF 17–19), §4, (1)–(3), (7)–(8)

import Mathlib

set_option autoImplicit false

namespace ConstrainedDirSep.STSep

/-- **Quadrant constraints.** Olkowski, Ramanujan, *Constrained Directed Separation*, STOC 2027
submission (manuscript sha256 4dd06c29…), §4, p. 14 (PDF 17), (1)–(2). A quadrant constraint on an
ordered pair of variables `(X, Y)` is either `se a b` (the paper's `Q↘_{a,b}`) or `nw a b` (the
paper's `Q↖_{a,b}`); `a` and `b` are its thresholds. -/
inductive Quadrant
  /-- `Q↘_{a,b}(x, y) : ¬(x ≥ a ∧ y ≤ b)` -/
  | se (a b : ℕ)
  /-- `Q↖_{a,b}(x, y) : ¬(x ≤ a ∧ y ≥ b)` -/
  | nw (a b : ℕ)
  deriving DecidableEq

/-- **The pair `(x, y)` satisfies the quadrant constraint.** §4, p. 14 (PDF 17), (1)–(2):
`Q↘_{a,b}(x, y) : ¬(x ≥ a ∧ y ≤ b)` and `Q↖_{a,b}(x, y) : ¬(x ≤ a ∧ y ≥ b)`. -/
def Quadrant.Holds : Quadrant → ℕ → ℕ → Prop
  | .se a b, x, y => ¬ (a ≤ x ∧ y ≤ b)
  | .nw a b, x, y => ¬ (x ≤ a ∧ b ≤ y)

/-- **Threshold ranges of a quadrant constraint on variables with domains `[dX]`, `[dY]`.** §4,
p. 14 (PDF 17), (1)–(2): `Q↘_{a,b}` has `a ∈ [dX + 1]`, `b ∈ {0} ∪ [dY]`; `Q↖_{a,b}` has
`a ∈ {0} ∪ [dX]`, `b ∈ [dY + 1]`. -/
def Quadrant.WellRanged (dX dY : ℕ) : Quadrant → Prop
  | .se a b => 1 ≤ a ∧ a ≤ dX + 1 ∧ b ≤ dY
  | .nw a b => a ≤ dX ∧ 1 ≤ b ∧ b ≤ dY + 1

/-- **Nonvacuous quadrant constraint.** §4, pp. 14–15 (PDF 17–18): "The constraint `Q↘_{a,b}`
forbids no pair when `a = dX + 1` or `b = 0`, and `Q↖_{a,b}` forbids no pair when `a = 0` or
`b = dY + 1`. We call a quadrant constraint vacuous in these cases and nonvacuous otherwise." -/
def Quadrant.Nonvacuous (dX dY : ℕ) : Quadrant → Prop
  | .se a b => a ≠ dX + 1 ∧ b ≠ 0
  | .nw a b => a ≠ 0 ∧ b ≠ dY + 1

/-- **Window.** §4, p. 15 (PDF 18): "For each i < j, let the window `W_ij` be the set of pairs
satisfying every constraint in `Q_ij`." The pairs range over `[dX] × [dY]`. -/
def window (Q : Finset Quadrant) (dX dY : ℕ) : Set (ℕ × ℕ) :=
  {pq | 1 ≤ pq.1 ∧ pq.1 ≤ dX ∧ 1 ≤ pq.2 ∧ pq.2 ≤ dY ∧ ∀ c ∈ Q, c.Holds pq.1 pq.2}

/-- The thresholds `b` of the constraints `Q↘_{a,b} ∈ Q` with `a ≤ p` (the set in (7)). -/
def seThresholds (Q : Finset Quadrant) (p : ℕ) : Finset ℕ :=
  Q.biUnion fun c =>
    match c with
    | .se a b => if a ≤ p then {b} else ∅
    | .nw _ _ => ∅

/-- The thresholds `b` of the constraints `Q↖_{a,b} ∈ Q` with `p ≤ a` (the set in (8)). -/
def nwThresholds (Q : Finset Quadrant) (p : ℕ) : Finset ℕ :=
  Q.biUnion fun c =>
    match c with
    | .nw a b => if p ≤ a then {b} else ∅
    | .se _ _ => ∅

/-- **Lower staircase boundary.** §4.1, p. 16 (PDF 19), (7):
`L(p) = 1 + max({b : Q↘_{a,b} ∈ Q_ij and a ≤ p} ∪ {0})`.

**Formalization Note.** `Finset.sup` over `ℕ` is the maximum of the set together with `0`. -/
def lowerL (Q : Finset Quadrant) (p : ℕ) : ℤ :=
  1 + ((seThresholds Q p).sup id : ℕ)

/-- **Upper staircase boundary.** §4.1, p. 16 (PDF 19), (8):
`U(p) = −1 + min({b : Q↖_{a,b} ∈ Q_ij and p ≤ a} ∪ {dj + 1})`.

**Formalization Note.** Integer-valued, so `−1` is never truncated. -/
def upperU (Q : Finset Quadrant) (dY p : ℕ) : ℤ :=
  (((insert (dY + 1) (nwThresholds Q p)).min' (Finset.insert_nonempty _ _) : ℕ) : ℤ) - 1

/-- **Increasing chain.** §4, p. 15 (PDF 18): "For points `(p, q), (p′, q′) ∈ [d] × [d′]`, write
`(p, q) ≤× (p′, q′)` when `p ≤ p′` and `q ≤ q′`. A subset of `[d] × [d′]` is an increasing chain if
every two of its points are comparable under `≤×`." -/
def IsIncreasingChain (T : Set (ℕ × ℕ)) : Prop :=
  ∀ x ∈ T, ∀ y ∈ T, (x.1 ≤ y.1 ∧ x.2 ≤ y.2) ∨ (y.1 ≤ x.1 ∧ y.2 ≤ x.2)

/-- **Closed under coordinatewise minimum and maximum.** §4.1, p. 16 (PDF 19), Lemma 4.3, and
App. A.1, p. 42 (PDF 45). -/
def MinMaxClosed (T : Set (ℕ × ℕ)) : Prop :=
  ∀ x ∈ T, ∀ y ∈ T, (min x.1 y.1, min x.2 y.2) ∈ T ∧ (max x.1 y.1, max x.2 y.2) ∈ T

/-- **Closed under coordinatewise minimum.** §4.2, p. 16 (PDF 19), Lemma 4.6. -/
def MinClosed (T : Set (ℕ × ℕ)) : Prop :=
  ∀ x ∈ T, ∀ y ∈ T, (min x.1 y.1, min x.2 y.2) ∈ T

end ConstrainedDirSep.STSep


