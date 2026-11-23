-- Prove2me | Definitions.Def_SingleMachinePrec_VariableCost_Supplement_OrderClasses
-- name    : SingleMachinePrec_VariableCost_Supplement_OrderClasses
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T17:46:20.947259+00:00
-- url     : https://prove2.me/theorems/74803ca0-0841-4100-ab68-ae0ea6e557ff
-- title:
--   Semiorders, interval orders, convex bipartite orders, interval dimension $\le 2$, $\Delta_D,\Delta_U$, and $k$-realizer inputs
-- statement:
--   Let $P$ be a reflexive relation on a finite set $N$, and write $x<y$ for $(x,y)\in P$, $x\neq y$.
--
--   1. $P$ is a **linear order** if any two elements are comparable (p. 655).
--   2. $P$ is an **interval order** (§6.1, p. 659) if it is a partial order and there are closed real intervals $[a_x,b_x]$, $a_x\le b_x$, with $x<y \iff b_x<a_y$; this is the published `AppliedComb.Posets.IsIntervalOrder`.
--   3. $P$ is a **semiorder** (§4.2, p. 658) if the intervals can be taken of unit length: there are reals $a_x$ with $x<y\iff a_x+1<a_y$.
--   4. $P$ on $\{0,\dots,n-1\}$ forms a **convex bipartite order** (§4.1, p. 657) if, after relabelling the jobs as minus jobs $j_1,\dots,j_a$ and plus jobs, it is the published `ConvexBipartiteOrder`: each plus job $k$ has indices $l(k)\le r(k)$ and $j_i<k$ exactly when $l(k)\le i\le r(k)$.
--   5. $P$ has **interval dimension at most 2** (§6.2, p. 660) if $P=Q_1\cap Q_2$ for two (possibly equal) interval orders $Q_1,Q_2$ on $N$.
--   6. $\deg_D(j)=|D(j)|$ and $\deg_U(j)=|U(j)|$ count the jobs strictly below and strictly above $j$ (§6.3, p. 660), and $\Delta_D=\max_j\deg_D(j)$, $\Delta_U=\max_j\deg_U(j)$ ($0$ when there are no jobs).
--   7. The input of Theorem 3.2 is an instance together with $k$ processing orders. They form a **$k$-realizer** (p. 655: a $1$-fold realizer of size $k$) if each is a permutation of the jobs whose order is a linear extension of $P$ and every incomparable pair is reversed by at least one of them (published `IsKFoldRealizer` with multiplicity $1$). Its code is the instance code, $k$ in unary, and the $k$ orders.
--
--   These are the classes of precedence constraints of Theorems 3.2–6.4.
--
--   **Formalization Note** A relation is turned into a Mathlib partial order by `relPartialOrder`, so the published interval-order predicate applies to it; its strict order is $(x,y)\in P\wedge(y,x)\notin P$, which equals $x<y$ above. Degrees count all comparable jobs, not only covering relations.
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 655, §2.1 (linear order, k-fold realizer, k-realizer); p. 657, §4.1 (convex bipartite order); p. 658, §4.2 (semiorder); p. 659, §6.1 (interval order); p. 660, §6.2 (interval dimension), §6.3 (deg_D, deg_U, Δ_D, Δ_U)

import Mathlib
import Definitions.Def_SingleMachinePrec_VariableCost_Supplement_Scheduling
import Definitions.Def_SingleMachinePrec_Framework_Poset
import Definitions.Def_SingleMachinePrec_ConvexBipartite_ConvexBipartiteOrder
import Definitions.Def_AppliedComb_Posets_intervalOrder

set_option autoImplicit false

namespace SingleMachinePrec.VariableCost.Supplement

open QAlgorithms.Complexity

variable {α : Type}

/-- The partial order (in Mathlib's sense) whose `≤` is the relation `r`; its strict order is
`x < y ↔ r x y ∧ ¬ r y x`, which under antisymmetry is `r x y ∧ x ≠ y` (p. 655). -/
abbrev relPartialOrder (r : α → α → Prop) (h : IsPartialOrder α r) : PartialOrder α where
  le := r
  le_refl := h.refl
  le_trans := fun _ _ _ => h.trans _ _ _
  le_antisymm := fun _ _ => h.antisymm _ _

/-- `r` is a linear order: any two elements are comparable (p. 655). -/
def IsLinearRel (r : α → α → Prop) : Prop := ∀ x y, r x y ∨ r y x

/-- `r` is an interval order (§6.1, p. 659): a partial order for which the published predicate
`AppliedComb.Posets.IsIntervalOrder` holds, i.e. there are closed real intervals `[a_x, b_x]`
with `x < y ↔ b_x < a_y`. -/
def IsIntervalOrderRel (r : α → α → Prop) : Prop :=
  ∃ h : IsPartialOrder α r, @AppliedComb.Posets.IsIntervalOrder α (relPartialOrder r h)

/-- `r` is a semiorder (unit interval order, §4.2, p. 658): a partial order with closed real
intervals `[a_x, a_x + 1]` of unit length such that `x < y ↔ a_x + 1 < a_y`. -/
def IsSemiorderRel (r : α → α → Prop) : Prop :=
  ∃ h : IsPartialOrder α r, ∃ a : α → ℝ, ∀ x y,
    @LT.lt α (relPartialOrder r h).toLT x y ↔ a x + 1 < a y

/-- A relation on `Fin n` forms a convex bipartite order (§4.1, p. 657) if, after relabelling
the jobs by a bijection with the minus and plus jobs, it is the precedence relation of a
published `ConvexBipartiteOrder`. -/
def IsConvexBipartiteRel {n : ℕ} (r : Fin n → Fin n → Prop) : Prop :=
  ∃ (a b : ℕ) (C : SingleMachinePrec.ConvexBipartite.ConvexBipartiteOrder a b)
    (e : Fin n ≃ SingleMachinePrec.ConvexBipartite.Job a b), ∀ i j, r i j ↔ C.prec (e i) (e j)

/-- Interval dimension at most 2 (§6.2, p. 660): `r` is the intersection of two (possibly equal)
extensions `Q₁, Q₂` of `r`, each of which is an interval order. -/
def IntervalDimLeTwo (r : α → α → Prop) : Prop :=
  ∃ Q₁ Q₂ : α → α → Prop, IsIntervalOrderRel Q₁ ∧ IsIntervalOrderRel Q₂ ∧
    ∀ x y, r x y ↔ Q₁ x y ∧ Q₂ x y

open Classical in
/-- `deg_D(j) = |D(j)|`, the number of jobs strictly below `j` (§6.3, p. 660). -/
noncomputable def degD [Fintype α] (r : α → α → Prop) (j : α) : ℕ :=
  (Finset.univ.filter (fun i => r i j ∧ i ≠ j)).card

open Classical in
/-- `deg_U(j) = |U(j)|`, the number of jobs strictly above `j` (§6.3, p. 660). -/
noncomputable def degU [Fintype α] (r : α → α → Prop) (j : α) : ℕ :=
  (Finset.univ.filter (fun i => r j i ∧ i ≠ j)).card

/-- `Δ_D(P) = max_j deg_D(j)` (§6.3, p. 660); `0` when there are no jobs. -/
noncomputable def maxDegD [Fintype α] (r : α → α → Prop) : ℕ := Finset.univ.sup (degD r)

/-- `Δ_U(P) = max_j deg_U(j)` (§6.3, p. 660); `0` when there are no jobs. -/
noncomputable def maxDegU [Fintype α] (r : α → α → Prop) : ℕ := Finset.univ.sup (degU r)

/-- The relation "`i` is at or before `j`" of a processing order `σ`. -/
def listLe {n : ℕ} (σ : List (Fin n)) (i j : Fin n) : Prop := σ.idxOf i ≤ σ.idxOf j

/-- `σ` lists every element of `Fin n` exactly once. -/
def IsPerm {n : ℕ} (σ : List (Fin n)) : Prop := σ.Nodup ∧ σ.length = n

/-- Input of Theorem 3.2: a scheduling instance together with `k` processing orders, meant to
be a `k`-realizer of its precedence constraints. -/
structure RealizerInput where
  inst : SchedInput
  k : ℕ
  orders : Fin k → List (Fin inst.n)

namespace RealizerInput

/-- Input code: the instance code, then `k` in unary, then the `k` orders. -/
def enc (R : RealizerInput) : Str :=
  R.inst.enc ++ encList (fun ℓ : Fin R.k => encSchedule (R.orders ℓ)) (List.finRange R.k)

/-- The supplied orders are a `k`-realizer (a `1`-fold realizer of size `k`, p. 655) of the
precedence constraints `P`: each is a permutation of the jobs whose order is a linear extension
of `P`, and every incomparable pair is reversed by at least one of them. -/
def IsRealizer (R : RealizerInput) : Prop :=
  (∀ ℓ, IsPerm (R.orders ℓ)) ∧
    ∃ L : Fin R.k → SingleMachinePrec.Framework.LinearExtension R.inst.Prec,
      SingleMachinePrec.Framework.IsKFoldRealizer R.inst.Prec 1 R.k L ∧
      ∀ ℓ, (L ℓ).le = listLe (R.orders ℓ)

end RealizerInput

end SingleMachinePrec.VariableCost.Supplement


