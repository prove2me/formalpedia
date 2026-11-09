-- Prove2me | Definitions.Def_ChoresTIE197_Main_Rounding
-- name    : ChoresTIE197_Main_Rounding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T02:15:18.412715+00:00
-- url     : https://prove2.me/theorems/af9e5727-400a-4205-bf87-b9ea02388d79
-- title:
--   Multigraph decomposition and arbitrary real sorted-slot rounding
-- statement:
--   A finite multigraph has distinguished edge identities and two endpoint maps. Its operational decomposition successively chooses a matching covering the right vertices and all left vertices of current maximum degree, then removes it. Numeric keys fix public choices.
--
--   For a nonnegative fractional matrix, each agent's chore fractions are laid out in her own descending cost order and intersected with unit intervals. The resulting slot mass is
--   $$s_{ite}=\max\{0,\min(a_{ie}+x_{ie},t+1)-\max(a_{ie},t)\},$$
--   where $a_{ie}$ sums earlier fractions. Unused slots are filled by dummy chore rows in a square matrix. Greedy Birkhoff subtraction chooses a positive-support perfect matching, subtracts its minimum edge weight, and records that coefficient. The output law discards dummy chores. No cost bound or marginal-preservation conclusion is a condition for choosing a matching. Feasibility and correctness remain theorem obligations.
--
--   Each agent has $m+1$ slots, including unused slots, rather than deleting empty slots in advance; these extra slots are filled by dummies and have no effect on real assignments. Finite numeric keys specify increasing, reproducible choices.
--   The unrestricted published interval-length component ChoresEFX.slotMass is reused with each agent's own cost rank. Its separate capped-price IsSortedOrder predicate is never required or assumed.
-- source:
--   Zehan Lin, Biaoshuai Tao, Xiaowei Wu, Yuhao Zhang, STOC 2027 submission #859 (October 2026), §3.2, §4.1 and Appendix A, printed p.34, PDF p.34; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/859.pdf

import Mathlib
import Definitions.Def_ChoresTIE197_Main_Setting
import Definitions.Def_ProphetBipartite_IsMatching
import Definitions.Def_ChoresEFX_IsAdmissibleMatching

open Finset
open Classical
open scoped NNReal ENNReal
noncomputable section

namespace ChoresTIE197.Main

/-- A fixed numeric public choice. Its key is independent of cost magnitudes. -/
def firstBy {α : Type*} [DecidableEq α] (s : Finset α) (key : α → ℕ) (fallback : α) : α :=
  (s.toList.mergeSort (fun a b => key a ≤ key b)).headD fallback

/-- Increasing enumeration, avoiding an arbitrary classical choice of vertex labels. -/
def orderedFinEquiv (α : Type*) [Fintype α] [LinearOrder α] : α ≃ Fin (Fintype.card α) :=
  (Equiv.subtypeUnivEquiv (fun x : α => Finset.mem_univ x)).symm.trans
    ((Finset.univ : Finset α).orderIsoOfFin rfl).toEquiv.symm

def edgeKey {t : ℕ} (S : Finset (Fin t)) : ℕ := ∑ e ∈ S, 2 ^ e.val

def decomposition {l r t : ℕ} (left : Fin t → Fin l) (right : Fin t → Fin r) :
    ℕ → Finset (Fin t) → List (Finset (Fin t))
  | 0, _ => []
  | d + 1, E =>
    let candidates := E.powerset.filter (fun S =>
      ProphetBipartite.IsMatching left right S ∧
      (∀ v : Fin r, ∃ e ∈ S, right e = v) ∧
      (∀ v : Fin l, (E.filter (fun e => left e = v)).card = d + 1 →
        ∃ e ∈ S, left e = v))
    let S := firstBy candidates edgeKey ∅
    S :: decomposition left right d (E \ S)

/-- Fraction of e in the t-th (zero based) sorted unit slot of i. -/
def slotMass {n m : ℕ} (c : Profile n m) (x : Fraction n m)
    (i : Fin n) (t : Fin (m + 1)) (e : Fin m) : ℝ :=
  ChoresEFX.slotMass x (fun j f => rank (c j) f) i e t.val

/-- There are m+1 slots per agent, including unused slots. These extra slots receive dummies. -/
def slotCount (n m : ℕ) : ℕ := n * (m + 1)

def slotOwner {n m : ℕ} [NeZero n] (s : Fin (slotCount n m)) : Fin n :=
  ⟨s.val / (m + 1), (Nat.div_lt_iff_lt_mul (Nat.succ_pos m)).mpr
    (by simpa [slotCount, Nat.mul_comm] using s.isLt)⟩

def slotIndex {n m : ℕ} (s : Fin (slotCount n m)) : Fin (m + 1) :=
  ⟨s.val % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩

/-- Dummy rows cover the slot deficits in fixed public order. -/
def slotMatrix {n m : ℕ} [NeZero n] (c : Profile n m) (x : Fraction n m) :
    Matrix (Fin (slotCount n m)) (Fin (slotCount n m)) ℝ :=
  fun a s =>
    let deficit := fun t : Fin (slotCount n m) =>
      1 - ∑ e, slotMass c x (slotOwner t) (slotIndex t) e
    if h : a.val < m then slotMass c x (slotOwner s) (slotIndex s) ⟨a.val, h⟩
    else
      let start := ∑ t ∈ univ.filter (fun t => t.val < s.val), deficit t
      let j := (a.val - m : ℕ)
      max 0 (min (start + deficit s) (j + 1 : ℝ) - max start (j : ℝ))

def permKey {k : ℕ} (p : Equiv.Perm (Fin k)) : ℕ :=
  ∑ a, (p a).val * (k + 1) ^ a.val

/-- Greedy Birkhoff subtraction. Only positive edges determine the matching;
no cost/fairness bound enters this procedure. At most k² positive entries can be removed. -/
def birkhoff {k : ℕ} : ℕ → Matrix (Fin k) (Fin k) ℝ → List (ℝ × Equiv.Perm (Fin k))
  | 0, _ => []
  | fuel + 1, w =>
    let good := univ.filter (fun p : Equiv.Perm (Fin k) => ∀ a, 0 < w a (p a))
    if _h : good.Nonempty then
      let p := firstBy good permKey (Equiv.refl _)
      let v := univ.image (fun a => w a (p a))
      let δ := if hv : v.Nonempty then v.min' hv else 0
      (δ, p) :: birkhoff fuel (fun a s => w a s - if p a = s then δ else 0)
    else []

def slotAllocation {n m : ℕ} [NeZero n] (p : Equiv.Perm (Fin (slotCount n m))) :
    Allocation n m :=
  fun e => if h : e.val < slotCount n m then slotOwner (p ⟨e.val, h⟩) else 0

/-- Appendix A: sample a Birkhoff coefficient and discard the dummy chore rows. -/
def roundSlots {n m : ℕ} [NeZero n] (c : Profile n m) (x : Fraction n m) : Law n m :=
  let terms := birkhoff (slotCount n m ^ 2 + 1) (slotMatrix c x)
  checkedLaw (fun A => (terms.map (fun z => if slotAllocation z.2 = A then z.1 else 0)).sum)

end ChoresTIE197.Main


