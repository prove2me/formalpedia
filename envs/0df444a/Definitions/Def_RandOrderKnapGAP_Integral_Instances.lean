-- Prove2me | Definitions.Def_RandOrderKnapGAP_Integral_Instances
-- name    : RandOrderKnapGAP_Integral_Instances
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:26:04.454179+00:00
-- url     : https://prove2.me/theorems/fdd220c6-9489-47b4-976d-a00b2372ed1e
-- title:
--   Integral knapsack, GAP and GPAP instances, feasible integral solutions, $\mathrm{OPT}_{\mathrm{int}}$ and resource deletion
-- statement:
--   An **integral knapsack instance** with $n$ items has a capacity $B>0$, sizes $s_i\ge 0$ and values $v_i\ge 0$ for $i\in[n]$; a set $S$ of items is feasible when $\sum_{i\in S}s_i\le B$, and
--   $$\mathrm{OPT}_{\mathrm{int}}=\max\Big\{\sum_{i\in S}v_i:\ \sum_{i\in S}s_i\le B\Big\}.$$
--   An **integral GAP instance** with $n$ items and $m$ machines has capacities $B_b>0$, sizes $s_{bi}\ge0$ and values $v_{bi}\ge0$. An integral assignment sends each item to one machine or rejects it; it is feasible when $\sum_{i\mapsto b}s_{bi}\le B_b$ for every machine $b$, and $\mathrm{OPT}_{\mathrm{int}}$ is the largest value $\sum_{i\mapsto b}v_{bi}$ of a feasible assignment.
--
--   A **multiple-choice packing instance** (§5) has $m$ resources with capacities $B_b>0$; item $i$ has a finite action set $\mathcal A_i$, each action $a$ with value $v_i(a)\ge0$ and consumptions $s_{bi}(a)\ge0$, and $\mathcal A_i$ contains a rejection action with zero value and zero consumption. A feasible integral allocation picks one action per item with $\sum_i s_{bi}(a_i)\le B_b$ for every $b$, and $\mathrm{OPT}_{\mathrm{int}}$ is (5.1), the largest $\sum_i v_i(a_i)$. **Resource deletion** (Definition 5.1): for every item $i$ and action $a$ there are fixed contributions $w_{bi}(a)\ge0$ with $\sum_b w_{bi}(a)=v_i(a)$ and, for every set $T$ of retained resources, an action $D_i(a,T)\in\mathcal A_i$ with $s_{bi}(D_i(a,T))\le s_{bi}(a)\mathbf 1\{b\in T\}$ for all $b$ and $v_i(D_i(a,T))\ge\sum_{b\in T}w_{bi}(a)$. An instance with this property is a **GPAP instance**.
--
--   The GPAP instance of a GAP instance (§5) has one resource per machine; action $0$ rejects and action $b+1$ assigns the item to machine $b$, consuming $s_{bi}$ of resource $b$ only and earning $v_{bi}$. A knapsack instance is a GAP instance with one machine.
--
--   **Formalization Note.** Items are `Fin n`, machines/resources `Fin m`, actions of item $i$ are `Fin (nA i)` with a designated rejection action. Sizes may exceed capacities. $\mathrm{OPT}_{\mathrm{int}}$ is `Finset.sup'` over the feasible solutions, a nonempty finite set because the empty solution is feasible. Resource deletion is a `Prop` about the instance (the witnesses $w$, $D$ exist); they are not data.
-- source:
--   Agrawal, Khan, Pareek, Improved Algorithms in the Random-Order Model: Knapsack, GAP, and Beyond, STOC 2027 submission (manuscript sha256 7825a05f…), pp. 1, 14 (PDF 3, 16), §1, §5, (5.1), Definition 5.1

import Mathlib

open scoped BigOperators

namespace RandOrderKnapGAP.Integral

/-!
# Integral knapsack, GAP and GPAP instances, feasible integral solutions and `OPT_int`

Agrawal, Khan, Pareek, *Improved Algorithms in the Random-Order Model: Knapsack, GAP, and
Beyond*, STOC 2027 submission, p. 1 (§1) and p. 14 (§5, (5.1), Definition 5.1).

Items are `Fin n`, machines / resources are `Fin m`. The standing conditions of the paper
(capacities `B_b > 0`, sizes / consumptions `≥ 0`, values `≥ 0`, a rejection action with zero
value and zero consumption) are fields of the structures. Sizes may exceed capacities.
`OPT_int` is a maximum over a finite nonempty set (the empty solution is feasible).
-/

/-- An integral knapsack instance with `n` items: capacity `B > 0`, sizes `s_i ≥ 0`,
values `v_i ≥ 0`. -/
structure KnapsackInstance (n : ℕ) where
  cap : ℝ
  size : Fin n → ℝ
  value : Fin n → ℝ
  cap_pos : 0 < cap
  size_nonneg : ∀ i, 0 ≤ size i
  value_nonneg : ∀ i, 0 ≤ value i

namespace KnapsackInstance

variable {n : ℕ} (I : KnapsackInstance n)

/-- A set `S` of items is a feasible integral packing: `∑_{i ∈ S} s_i ≤ B`. -/
def Feasible (S : Finset (Fin n)) : Prop := ∑ i ∈ S, I.size i ≤ I.cap

/-- The integral offline optimum `OPT_int = max {∑_{i∈S} v_i : ∑_{i∈S} s_i ≤ B}`. -/
noncomputable def OPT : ℝ := by
  classical
  exact (Finset.univ.filter (fun S : Finset (Fin n) => I.Feasible S)).sup'
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      simp only [Feasible, Finset.sum_empty]; exact le_of_lt I.cap_pos⟩⟩ (fun S => ∑ i ∈ S, I.value i)

end KnapsackInstance

/-- An integral GAP instance with `n` items and `m` machines: capacities `B_b > 0`, sizes
`s_{bi} ≥ 0` and values `v_{bi} ≥ 0` (here `size i b = s_{bi}`, `value i b = v_{bi}`). -/
structure GAPInstance (n m : ℕ) where
  cap : Fin m → ℝ
  size : Fin n → Fin m → ℝ
  value : Fin n → Fin m → ℝ
  cap_pos : ∀ b, 0 < cap b
  size_nonneg : ∀ i b, 0 ≤ size i b
  value_nonneg : ∀ i b, 0 ≤ value i b

namespace GAPInstance

variable {n m : ℕ} (I : GAPInstance n m)

/-- The load of machine `b` under an integral assignment `a` (`a i = none`: item `i` rejected,
`a i = some b`: item `i` assigned to machine `b`). -/
def load (a : Fin n → Option (Fin m)) (b : Fin m) : ℝ :=
  ∑ i, if a i = some b then I.size i b else 0

/-- The value `∑_{b,i} v_{bi} x_{bi}` of an integral assignment. -/
def assignValue (a : Fin n → Option (Fin m)) : ℝ :=
  ∑ i, match a i with
    | none => 0
    | some b => I.value i b

/-- Feasible integral assignment: `∑_i s_{bi} x_{bi} ≤ B_b` for every machine `b`. -/
def Feasible (a : Fin n → Option (Fin m)) : Prop := ∀ b, I.load a b ≤ I.cap b

/-- The integral offline optimum of the GAP instance. -/
noncomputable def OPT : ℝ := by
  classical
  exact (Finset.univ.filter (fun a : Fin n → Option (Fin m) => I.Feasible a)).sup'
    ⟨fun _ => none, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun b => by
      simp only [load, reduceCtorEq, if_false, Finset.sum_const_zero]; exact le_of_lt (I.cap_pos b)⟩⟩ I.assignValue

end GAPInstance

/-- One GPAP item over `m` resources: a finite action set `A_i = Fin nA`, values `v_i(a) ≥ 0`,
consumptions `s_{bi}(a) ≥ 0`, and a designated rejection action with zero value and zero
consumption. -/
structure GPAPItem (m : ℕ) where
  nA : ℕ
  val : Fin nA → ℝ
  cons : Fin nA → Fin m → ℝ
  rej : Fin nA
  val_nonneg : ∀ a, 0 ≤ val a
  cons_nonneg : ∀ a b, 0 ≤ cons a b
  val_rej : val rej = 0
  cons_rej : ∀ b, cons rej b = 0

/-- A multiple-choice packing instance (§5): `n` items over `m` resources with capacities
`B_b > 0`. It is a GPAP instance when it satisfies `ResourceDeletion` below. -/
structure GPAPInstance (n m : ℕ) where
  cap : Fin m → ℝ
  item : Fin n → GPAPItem m
  cap_pos : ∀ b, 0 < cap b

/-- Definition 5.1 (resource deletion) for one item: there are fixed nonnegative contributions
`w_b(a)` with `∑_b w_b(a) = v(a)`, and for every set `T` of retained resources an action
`D(a, T)` with `s_b(D(a,T)) ≤ s_b(a) 1{b ∈ T}` and `v(D(a,T)) ≥ ∑_{b ∈ T} w_b(a)`. -/
def GPAPItem.ResourceDeletion {m : ℕ} (x : GPAPItem m) : Prop :=
  ∃ (w : Fin x.nA → Fin m → ℝ) (D : Fin x.nA → Finset (Fin m) → Fin x.nA),
    (∀ a b, 0 ≤ w a b) ∧ (∀ a, ∑ b, w a b = x.val a) ∧
    (∀ a T b, x.cons (D a T) b ≤ x.cons a b * (if b ∈ T then 1 else 0)) ∧
    (∀ a T, ∑ b ∈ T, w a b ≤ x.val (D a T))

namespace GPAPInstance

variable {n m : ℕ} (I : GPAPInstance n m)

/-- Definition 5.1 for the instance: every item has the resource-deletion property. -/
def ResourceDeletion : Prop := ∀ i, (I.item i).ResourceDeletion

/-- Feasible integral allocation: one action per item, `∑_i s_{bi}(a_i) ≤ B_b` for every `b`. -/
def Feasible (a : (i : Fin n) → Fin (I.item i).nA) : Prop :=
  ∀ b, ∑ i, (I.item i).cons (a i) b ≤ I.cap b

/-- The integral offline optimum (5.1). -/
noncomputable def OPT : ℝ := by
  classical
  exact (Finset.univ.filter (fun a : (i : Fin n) → Fin (I.item i).nA => I.Feasible a)).sup'
    ⟨fun i => (I.item i).rej, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun b => by
      simp only [GPAPItem.cons_rej, Finset.sum_const_zero]; exact le_of_lt (I.cap_pos b)⟩⟩
    (fun a => ∑ i, (I.item i).val (a i))

end GPAPInstance

/-- §5: the GPAP instance of a GAP instance. One resource per machine; action `0` is rejection
and action `b + 1` assigns the item to machine `b`, consuming `s_{bi}` of resource `b` only and
earning `v_{bi}`. -/
def GAPInstance.toGPAP {n m : ℕ} (I : GAPInstance n m) : GPAPInstance n m where
  cap := I.cap
  item i :=
    { nA := m + 1
      val := fun a => if h : a.val = 0 then 0 else I.value i ⟨a.val - 1, by omega⟩
      cons := fun a b => if h : a.val = 0 then 0 else
        (if b = ⟨a.val - 1, by omega⟩ then I.size i b else 0)
      rej := 0
      val_nonneg := by
        intro a; split_ifs
        · exact le_rfl
        · exact I.value_nonneg _ _
      cons_nonneg := by
        intro a b; split_ifs
        · exact le_rfl
        · exact I.size_nonneg _ _
        · exact le_rfl
      val_rej := by simp
      cons_rej := by intro b; simp }
  cap_pos := I.cap_pos

/-- Knapsack as GAP with a single machine. -/
def KnapsackInstance.toGAP {n : ℕ} (I : KnapsackInstance n) : GAPInstance n 1 where
  cap := fun _ => I.cap
  size := fun i _ => I.size i
  value := fun i _ => I.value i
  cap_pos := fun _ => I.cap_pos
  size_nonneg := fun i _ => I.size_nonneg i
  value_nonneg := fun i _ => I.value_nonneg i

end RandOrderKnapGAP.Integral


