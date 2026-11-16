-- Prove2me | Definitions.Def_SublinearChoresMMS_Disposal_Supplement_FixedBundles
-- name    : SublinearChoresMMS_Disposal_Supplement_FixedBundles
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:59:32.141755+00:00
-- url     : https://prove2.me/theorems/d15ee05a-0a11-4803-bb6c-9fa63c287b7b
-- title:
--   Opposite pairs and operational fixed-bundle completion
-- statement:
--   The **opposite pairs** are $Q_j=\{e_j,e_{2n+1-j}\}$ for $1\le j\le n$, and $V=\{e_{2n+1},\ldots,e_m\}$. A completion records an assigned pair label and a fraction $t_i$ of every tail chore for each agent.
--
--   Algorithm 1 starts with all agents and fixed bundles active and remaining tail fraction $b=1$. For each agent it computes her cheapest remaining bundle and the largest feasible tail fraction at cost at most $c_i(M)/n$. If the largest offer is below $b$, it assigns that agent her cheapest bundle and offer and repeats. Otherwise it samples uniformly among agents whose offer equals $b$, gives the selected agent her cheapest bundle and the whole remaining tail, and samples a uniform bijection of the remaining agents and fixed bundles. Numeric ties are broken deterministically by index. No fairness condition selects any action.
--
--   **Formalization Note** The procedure returns a finite real weighted list. Its normalization and complete-output properties are conclusions of Lemma 4.2, rather than fields of the algorithm. The recursion has fuel $n$. Unreachable invalid states return the current partial record; a zero-cost tail has maximum feasible fraction $b$.
-- source:
--   Zehan Lin, Xiaowei Wu, Shengwei Zhou, STOC 2027 submission #845 (October 2026), Section 4 opposite pairs, printed p. 14 / PDF p. 15. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/845.pdf Algorithm 1, printed p. 15 / PDF p. 16.

import Mathlib
import Definitions.Def_SublinearChoresMMS_Disposal_Setting

noncomputable section

namespace SublinearChoresMMS.Disposal.Supplement

open Finset
attribute [local instance] Classical.propDecidable

/-- Section 4, printed 14 / PDF 15: zero-based opposite pairs. Used with 2*n ≤ m. -/
def oppositePairs (n m : ℕ) (j : Fin n) : Finset (Fin m) :=
  univ.filter (fun e => e.val = j.val ∨ e.val = 2 * n - 1 - j.val)

def oppositeTail (n m : ℕ) : Finset (Fin m) :=
  univ.filter (fun e => 2 * n ≤ e.val)

/-- Algorithm 1 records assigned fixed-bundle labels and fractions of the common tail.
Unassigned entries occur only during the computation, not in its completed outputs. -/
structure Completion (n : ℕ) where
  assigned : Fin n → Option (Fin n)
  tail : Fin n → ℝ

def assignedBundle {n m : ℕ} (Q : Fin n → Finset (Fin m))
    (z : Completion n) (i : Fin n) : Finset (Fin m) :=
  match z.assigned i with
  | none => ∅
  | some j => Q j

def completionFraction {n m : ℕ} (Q : Fin n → Finset (Fin m))
    (V : Finset (Fin m)) (z : Completion n) (i : Fin n) (e : Fin m) : ℝ :=
  (if e ∈ assignedBundle Q z i then 1 else 0) + (if e ∈ V then z.tail i else 0)

/-- The actual output shape, with no cost or fairness condition. -/
def Complete {n : ℕ} (z : Completion n) : Prop :=
  (∃ σ : Equiv.Perm (Fin n), ∀ i, z.assigned i = some (σ i)) ∧
  (∀ i, 0 ≤ z.tail i ∧ z.tail i ≤ 1) ∧ ∑ i, z.tail i = 1

/-- Fixed deterministic tie breaking: sort a finite set by its score and take the first.
The empty-set value is none. No fairness property enters the choice. -/
def leastScore {n : ℕ} (S : Finset (Fin n)) (score : Fin n → ℝ) : Option (Fin n) :=
  ((S.sort (· ≤ ·)).mergeSort (fun a b => score a ≤ score b)).head?

def cheapest {n m : ℕ} (c : Cost n m) (Q : Fin n → Finset (Fin m))
    (B : Finset (Fin n)) (i : Fin n) : Option (Fin n) :=
  leastScore B (fun j => cost c i (Q j))

def cheapestCost {n m : ℕ} (c : Cost n m) (Q : Fin n → Finset (Fin m))
    (B : Finset (Fin n)) (i : Fin n) : ℝ :=
  match cheapest c Q B i with
  | none => 0
  | some j => cost c i (Q j)

/-- Algorithm 1 line 3. On reachable states a≤PROP and b≥0, so this is precisely
max {t∈[0,b] : a+t*c(V)≤PROP}. If c(V)=0 the maximum is b. -/
def tailOffer {n m : ℕ} (c : Cost n m) (Q : Fin n → Finset (Fin m))
    (V : Finset (Fin m)) (B : Finset (Fin n)) (b : ℝ) (i : Fin n) : ℝ :=
  if cost c i V = 0 then b
  else max 0 (min b ((propShare c i - cheapestCost c Q B i) / cost c i V))

/-- All permutations extending the previously assigned labels and the current choice.
They enumerate exactly the remaining bijections in Algorithm 1 line 12. -/
def extensions {n : ℕ} (z : Completion n) (i j : Fin n) : Finset (Equiv.Perm (Fin n)) :=
  univ.filter (fun σ => σ i = j ∧ ∀ a t, z.assigned a = some t → σ a = t)

/-- Algorithm 1, lines 1–14, as a finite weighted list. The only random branch first
chooses uniformly from E and then uniformly among remaining bijections. The fuel n
is an operational bound on the number of strict-removal rounds, not a fairness test.
Invalid states terminate with their current partial record; Lemma 4.2 rules them out
for the initialized algorithm. Probability normalization is a theorem conclusion. -/
def completeRun {n m : ℕ} (c : Cost n m) (Q : Fin n → Finset (Fin m))
    (V : Finset (Fin m)) : ℕ → Finset (Fin n) → Finset (Fin n) → ℝ →
      Completion n → OAI.CliqueFreeIndependence.Lottery.Law (Completion n)
  | 0, _, _, _, z => [(1, z)]
  | fuel + 1, A, B, b, z =>
    let offer := tailOffer c Q V B b
    match leastScore A (fun i => -offer i) with
    | none => [(1, z)]
    | some i =>
      match cheapest c Q B i with
      | none => [(1, z)]
      | some j =>
        if offer i < b then
          completeRun c Q V fuel (A.erase i) (B.erase j) (b - offer i)
            ⟨Function.update z.assigned i (some j), Function.update z.tail i (offer i)⟩
        else
          let E := A.filter (fun a => offer a = b)
          (E.sort (· ≤ ·)).flatMap (fun a =>
            match cheapest c Q B a with
            | none => []
            | some t =>
              let T := extensions z a t
              T.toList.map (fun σ =>
                ((1 / (E.card : ℝ)) * (1 / (T.card : ℝ)),
                  (⟨fun u => some (σ u), Function.update z.tail a b⟩ : Completion n))))

def algorithm1 {n m : ℕ} (c : Cost n m) (Q : Fin n → Finset (Fin m))
    (V : Finset (Fin m)) : OAI.CliqueFreeIndependence.Lottery.Law (Completion n) :=
  completeRun c Q V n univ univ 1 ⟨fun _ => none, fun _ => 0⟩

end SublinearChoresMMS.Disposal.Supplement


