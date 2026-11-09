-- Prove2me | Definitions.Def_ChoresTIE197_Main_Setting
-- name    : ChoresTIE197_Main_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T02:14:40.68388+00:00
-- url     : https://prove2.me/theorems/a078f5e8-ec71-483a-8c4b-3d8e44555571
-- title:
--   Finite chores, allocation laws, incentives and cost MMS
-- statement:
--   There are $n$ agents and $m$ chores. A cost profile consists of nonnegative real singleton costs, extended additively to bundles. A complete allocation assigns each chore to one agent, and a lottery is a probability mass function on these assignments. For every subset $S$, the cost maximin share is
--   $$\mu_i(S)=-\operatorname{MMS}_{-c_i}(n,S)=\min_{A\in\Pi_n(S)}\max_j c_i(A_j).$$
--   The identity is used only for $n>0$, when all finite extrema are attained. Truthfulness compares the same true row against a unilateral alternative report with opponents fixed. Ex-ante envy-freeness compares two random bundles using the envious agent's row. Ex-post MMS bounds every allocation of nonzero mass. The domain predicate allows the source's positive-type internal statements and the unrestricted headline to share these definitions.
--
--   Public index ties determine ranks and top sets. Padding extends every report by forced zeros. A public first-zero-reporter wrapper and checked finite-weight constructor complete the interface. Failed weight checks return a fixed complete allocation, without asserting any fairness property. This is a total definition outside the intended algorithm domains, not an input hypothesis.
-- source:
--   Zehan Lin, Biaoshuai Tao, Xiaowei Wu, Yuhao Zhang, STOC 2027 submission #859 (October 2026), §2, Definitions 2.1–2.3, printed p.6, PDF p.6; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/859.pdf

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting

open Finset
open scoped NNReal ENNReal
noncomputable section

namespace ChoresTIE197.Main

/-- Section 2, PDF p.6. The row is its additive singleton costs. -/
abbrev Profile (n m : ℕ) := Fin n → Fin m → ℝ≥0
abbrev Allocation (n m : ℕ) := Fin m → Fin n
abbrev Law (n m : ℕ) := PMF (Allocation n m)
abbrev Mechanism (n m : ℕ) := Profile n m → Law n m

def cost {m : ℕ} (c : Fin m → ℝ≥0) (S : Finset (Fin m)) : ℝ :=
  ∑ e ∈ S, (c e : ℝ)

def bundle {n m : ℕ} (A : Allocation n m) (i : Fin n) : Finset (Fin m) :=
  univ.filter (fun e => A e = i)

/-- Sign dual of the published max-min share, without the goods sign predicate. -/
def mms {m : ℕ} (c : Fin m → ℝ≥0) (n : ℕ) (S : Finset (Fin m)) : ℝ :=
  -LittleCharity.MMS.mms (fun T => -cost c T) n S

def expectedCost {n m : ℕ} (p : Law n m) (c : Fin m → ℝ≥0) (j : Fin n) : ℝ :=
  ∑ A, (p A).toReal * cost c (bundle A j)

def marginal {n m : ℕ} (p : Law n m) (i : Fin n) (e : Fin m) : ℝ :=
  ∑ A, if A e = i then (p A).toReal else 0

def Positive {n m : ℕ} (c : Profile n m) : Prop := ∀ i, 0 < cost (c i) univ

def TIEOn {n m : ℕ} (D : Profile n m → Prop) (F : Mechanism n m) : Prop :=
  ∀ c, D c → ∀ i r, D (Function.update c i r) →
    expectedCost (F c) (c i) i ≤ expectedCost (F (Function.update c i r)) (c i) i

def EFOn {n m : ℕ} (D : Profile n m → Prop) (F : Mechanism n m) : Prop :=
  ∀ c, D c → ∀ i j, expectedCost (F c) (c i) i ≤ expectedCost (F c) (c i) j

def MMSOn {n m : ℕ} (D : Profile n m → Prop) (α : ℝ) (F : Mechanism n m) : Prop :=
  ∀ c, D c → ∀ A, F c A ≠ 0 → ∀ i, cost (c i) (bundle A i) ≤ α * mms (c i) n univ

def EqualOn {n m : ℕ} (D : Profile n m → Prop) (F : Mechanism n m) : Prop :=
  ∀ c, D c → ∀ i e, marginal (F c) i e = 1 / (n : ℝ)

/-- Public chore order is the index; a rank is zero based. -/
def rank {m : ℕ} (c : Fin m → ℝ≥0) (e : Fin m) : ℕ :=
  (univ.filter (fun f => c e < c f ∨ (c e = c f ∧ f.val < e.val))).card

def top {m : ℕ} (c : Fin m → ℝ≥0) (t : ℕ) : Finset (Fin m) :=
  univ.filter (fun e => rank c e < t)

/-- Source's empty maximum convention. Used only at valid ranks in theorems. -/
def maximum {m : ℕ} (c : Fin m → ℝ≥0) (S : Finset (Fin m)) : ℝ :=
  (S.sup c : ℝ≥0)

def kth {m : ℕ} (c : Fin m → ℝ≥0) (t : ℕ) : ℝ :=
  maximum c (univ.filter (fun e => rank c e + 1 = t))

/-- Forced zero dummy reports; originals are the first m indices. -/
def pad {n m : ℕ} (d : ℕ) (c : Profile n m) : Profile n (m + d) :=
  fun i e => if h : e.val < m then c i ⟨e.val, h⟩ else 0

def unpad {n m d : ℕ} (A : Allocation n (m + d)) : Allocation n m :=
  fun e => A ⟨e.val, Nat.lt_add_right d e.isLt⟩

def zeroWrap {n m : ℕ} [NeZero n] (F : Mechanism n m) : Mechanism n m := by
  classical
  exact fun c =>
    let Z := univ.filter (fun i => ∀ e, c i e = 0)
    if h : Z.Nonempty then PMF.pure (fun _ => Z.min' h) else F c

/-- Uniform finite choices, including a specified fallback outside the intended domain. -/
def uniformChoice {α : Type*} [DecidableEq α] (s : Finset α) (fallback : α) : PMF α :=
  if h : s.Nonempty then PMF.uniformOfFinset s h else PMF.pure fallback

/-- A finite weight table becomes a law only after its probability axioms are checked.
The failure branch is operational and supplies no fairness property. -/
def checkedLaw {n m : ℕ} [NeZero n] (w : Allocation n m → ℝ) : Law n m := by
  classical
  exact if h : (∀ A, 0 ≤ w A) ∧ (∑ A, w A) = 1 then
    PMF.ofFinset (fun A => ENNReal.ofReal (w A)) univ
      (by simpa using
        (ENNReal.ofReal_sum_of_nonneg (fun A _ => h.1 A)).symm.trans (by rw [h.2]; simp))
      (by simp)
    else PMF.pure (fun _ => 0)

abbrev Fraction (n m : ℕ) := Fin n → Fin m → ℝ

def Feasible {n m : ℕ} (x : Fraction n m) : Prop :=
  (∀ i e, 0 ≤ x i e) ∧ ∀ e, ∑ i, x i e = 1

def fractionalCost {n m : ℕ} (c : Profile n m) (x : Fraction n m) (i : Fin n)
    (S : Finset (Fin m)) : ℝ := ∑ e ∈ S, x i e * (c i e : ℝ)

end ChoresTIE197.Main


