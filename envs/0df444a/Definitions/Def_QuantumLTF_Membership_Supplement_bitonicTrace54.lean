-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
-- name    : QuantumLTF_Membership_Supplement_bitonicTrace54
-- status  : Definition
-- author  : @Robin Kothari
-- created : 2026-11-25T01:47:24.601732+00:00
-- url     : https://prove2.me/theorems/d205ba61-4d5d-4023-8d21-073d9794f92f
-- title:
--   Bitonic sort with trace replay, keyed circuit suite, and classical-$m$ uniform prefix state preparation ($\mathrm{BitonicRouting54}$)
-- statement:
--   Defines the pure bitonic sorting network with recorded comparator-swap traces (`Cslib.BitonicSort`) and the `BitonicRouting54` reversible `gates12` circuit-suite interface for quantum second-to-first-quantization routing and uniform prefix state preparation.
--
--   1. **Bitonic Sorting Network & Trace Replay:** On length $2^d$ arrays `Fin (arity d) -> alpha` with key map `key : alpha -> kappa`, `sort key d asc x` recursively sorts the left half ascending and right half descending before running a depth-`(d+1)` bitonic `merge`. At each compare-and-exchange wire pair, `layerFlags` records the swap decision as a Boolean bit, producing total trace lengths `mergeTraceSize d` and `sortTraceSize d` (satisfying $4 \cdot \mathrm{sortTraceSize}(d) = d(d+1)2^d$). Given an arbitrary Boolean trace vector `flags`, `routeSort d flags` and `unrouteSort d flags` define inverse payload-routing permutations on `Fin (arity d) -> alpha`.
--
--   2. **Reversible Sorting, Routing, and Uniform Prefix Circuits (`BitonicRouting54`):** Bundles a suite of elementary $1$- and $2$-qubit `gates12` (`LayeredCircuit`) primitives with explicit size and unitary-action specifications:
--      - An integer comparator toggle `ltBitsCircuit w` of size $\le 20w + 1$ and controlled-swap circuit `cswapRegCircuit w` of size $7w$.
--      - Trace-controlled routing and unrouting circuits `routeSortCircuit d w` and `unrouteSortCircuit d w` (its adjoint) of size $O(2^d (d+1)^2 (w+1))$.
--      - Reversible generic and keyed record-sorting circuits `sortWithTraceCircuit` and `bitonicSortKeyCircuit d w_k w_p asc` on `2^d` records of `(w_k + w_p)` qubits (where keys occupy the leading `w_k` bits via `recKey54`), mapping clean trace and ancilla wires $|x, 0^T, 0^{w_k}\rangle$ to $|\mathrm{sort}(x), \mathrm{sortTrace}(x), 0^{w_k}\rangle$ in $O(2^d (d+1)^2 (w_k + w_p + 1))$ `gates12` gates, whose adjoint simultaneously unroutes a sorted payload array and uncomputes the saved sorting trace back to $|0^T\rangle$.
--      - A controlled classical-$m$ uniform prefix state-preparation circuit `unifPrefixCircuit b m` ($1 \le m \le 2^b$) of size $O((b+1)^2)$ acting as the identity when the control wire is `false` and mapping $|\mathrm{true}, 0^b, 0^b\rangle \mapsto \frac{1}{\sqrt{m}} \sum_{j=0}^{m-1} |\mathrm{true}, \mathrm{bin}_b(j), 0^b\rangle$ when `true`.
-- source:
--   Batcher (1968), Sorting Networks and Their Applications; cslib-frontier Bitonic Sort & Trace (CslibFrontier/Algorithms/Lean/Sort/Bitonic/{Basic,ZeroOne,Correctness,Trace}.lean, Apache-2.0); Liu, Childs, Gottesman [LCG26] (arXiv:2411.04019, Section IV); Krivcenko, Nguyen, de Wolf [KNW26] (arXiv:2609.40331, Theorem 5.4).

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks

set_option autoImplicit false

/-
# Bitonic Sort with Trace Replay & Uniform Prefix State Prep (Definitions)

Ported from `cslib-frontier` (`CslibFrontier/Algorithms/Lean/Sort/Bitonic/{Basic,Trace}.lean`,
Apache-2.0) together with helper functions and the `BitonicRouting54` circuit-suite interface for
Milestone #16 (`QuantumLTF.Membership.Supplement.theorem_5_4`).
-/

namespace Cslib.BitonicSort

section Basic
variable {α κ : Type*}

def arity : ℕ → ℕ
  | 0 => 1
  | depth + 1 => arity depth + arity depth

@[simp] theorem arity_eq_two_pow (depth : ℕ) : arity depth = 2 ^ depth := by
  induction depth with
  | zero => rfl
  | succ depth ih => simp [arity, ih, Nat.pow_succ, Nat.mul_two]

def IsBitonic [LinearOrder κ] {n : ℕ} (input : Fin n → κ) : Prop :=
  ∀ i j k l, i < j → j < k → k < l →
    min (input i) (input k) ≤ max (input j) (input l) ∧
      min (input j) (input l) ≤ max (input i) (input k)

def compareLayer [LinearOrder κ] (key : α → κ) {n : ℕ} (ascending : Bool)
    (input : Fin (n + n) → α) : Fin (n + n) → α :=
  input ∘ source key ascending input
where
  source (key : α → κ) {n : ℕ} (ascending : Bool)
      (input : Fin (n + n) → α) :
      Fin (n + n) → Fin (n + n) :=
    let exchange (i : Fin n) :=
      let outOfOrder := key (input (Fin.natAdd n i)) < key (input (Fin.castAdd n i))
      if ascending then outOfOrder else ¬outOfOrder
    Fin.addCases
      (fun i => if exchange i then Fin.natAdd n i else Fin.castAdd n i)
      (fun i => if exchange i then Fin.castAdd n i else Fin.natAdd n i)

def merge [LinearOrder κ] (key : α → κ) : (depth : ℕ) → Bool →
    (Fin (arity depth) → α) → Fin (arity depth) → α
  | 0, _, input => input
  | depth + 1, ascending, input =>
    let compared := compareLayer key (n := arity depth) ascending input
    Fin.append
      (merge key depth ascending (compared ∘ Fin.castAdd (arity depth)))
      (merge key depth ascending (compared ∘ Fin.natAdd (arity depth)))

def sort [LinearOrder κ] (key : α → κ) : (depth : ℕ) → Bool →
    (Fin (arity depth) → α) → Fin (arity depth) → α
  | 0, _, input => input
  | depth + 1, ascending, input =>
    merge key (depth + 1) ascending (Fin.append
      (sort key depth true (input ∘ Fin.castAdd (arity depth)))
      (sort key depth false (input ∘ Fin.natAdd (arity depth))))

end Basic

section Trace
variable {α κ : Type*}

def routeLayer {n : ℕ} (flags : Fin n → Bool) (x : Fin (n + n) → α) : Fin (n + n) → α :=
  Fin.append
    (fun i => if flags i then x (Fin.natAdd n i) else x (Fin.castAdd n i))
    (fun i => if flags i then x (Fin.castAdd n i) else x (Fin.natAdd n i))

def layerFlags [LinearOrder κ] (key : α → κ) {n : ℕ} (ascending : Bool)
    (x : Fin (n + n) → α) : Fin n → Bool :=
  fun i => decide (if ascending then key (x (Fin.natAdd n i)) < key (x (Fin.castAdd n i))
    else ¬key (x (Fin.natAdd n i)) < key (x (Fin.castAdd n i)))

def mergeTraceSize : ℕ → ℕ
  | 0 => 0
  | d + 1 => arity d + (mergeTraceSize d + mergeTraceSize d)

def sortTraceSize : ℕ → ℕ
  | 0 => 0
  | d + 1 => (sortTraceSize d + sortTraceSize d) + mergeTraceSize (d + 1)

def mergeTrace [LinearOrder κ] (key : α → κ) : (d : ℕ) → Bool →
    (Fin (arity d) → α) → Fin (mergeTraceSize d) → Bool
  | 0, _, _ => Fin.elim0
  | d + 1, ascending, x =>
    let compared := compareLayer key ascending x
    Fin.append (layerFlags key ascending x) (Fin.append
      (mergeTrace key d ascending (compared ∘ Fin.castAdd (arity d)))
      (mergeTrace key d ascending (compared ∘ Fin.natAdd (arity d))))

def sortTrace [LinearOrder κ] (key : α → κ) : (d : ℕ) → Bool →
    (Fin (arity d) → α) → Fin (sortTraceSize d) → Bool
  | 0, _, _ => Fin.elim0
  | d + 1, ascending, x =>
    let left := x ∘ Fin.castAdd (arity d)
    let right := x ∘ Fin.natAdd (arity d)
    Fin.append (Fin.append (sortTrace key d true left) (sortTrace key d false right))
      (mergeTrace key (d + 1) ascending
        (Fin.append (sort key d true left) (sort key d false right)))

def routeMerge : (d : ℕ) → (Fin (mergeTraceSize d) → Bool) →
    (Fin (arity d) → α) → Fin (arity d) → α
  | 0, _, x => x
  | d + 1, flags, x =>
    let compared := routeLayer (flags ∘ Fin.castAdd (mergeTraceSize d + mergeTraceSize d)) x
    let children := flags ∘ Fin.natAdd (arity d)
    Fin.append
      (routeMerge d (children ∘ Fin.castAdd (mergeTraceSize d)) (compared ∘ Fin.castAdd (arity d)))
      (routeMerge d (children ∘ Fin.natAdd (mergeTraceSize d)) (compared ∘ Fin.natAdd (arity d)))

def unrouteMerge : (d : ℕ) → (Fin (mergeTraceSize d) → Bool) →
    (Fin (arity d) → α) → Fin (arity d) → α
  | 0, _, x => x
  | d + 1, flags, x =>
    let children := flags ∘ Fin.natAdd (arity d)
    routeLayer (flags ∘ Fin.castAdd (mergeTraceSize d + mergeTraceSize d)) (Fin.append
      (unrouteMerge d (children ∘ Fin.castAdd (mergeTraceSize d)) (x ∘ Fin.castAdd (arity d)))
      (unrouteMerge d (children ∘ Fin.natAdd (mergeTraceSize d)) (x ∘ Fin.natAdd (arity d))))

def routeSort : (d : ℕ) → (Fin (sortTraceSize d) → Bool) →
    (Fin (arity d) → α) → Fin (arity d) → α
  | 0, _, x => x
  | d + 1, flags, x =>
    let children := flags ∘ Fin.castAdd (mergeTraceSize (d + 1))
    routeMerge (d + 1) (flags ∘ Fin.natAdd (sortTraceSize d + sortTraceSize d)) (Fin.append
      (routeSort d (children ∘ Fin.castAdd (sortTraceSize d)) (x ∘ Fin.castAdd (arity d)))
      (routeSort d (children ∘ Fin.natAdd (sortTraceSize d)) (x ∘ Fin.natAdd (arity d))))

def unrouteSort : (d : ℕ) → (Fin (sortTraceSize d) → Bool) →
    (Fin (arity d) → α) → Fin (arity d) → α
  | 0, _, x => x
  | d + 1, flags, x =>
    let merged := unrouteMerge (d + 1) (flags ∘ Fin.natAdd (sortTraceSize d + sortTraceSize d)) x
    let children := flags ∘ Fin.castAdd (mergeTraceSize (d + 1))
    Fin.append
      (unrouteSort d (children ∘ Fin.castAdd (sortTraceSize d)) (merged ∘ Fin.castAdd (arity d)))
      (unrouteSort d (children ∘ Fin.natAdd (sortTraceSize d)) (merged ∘ Fin.natAdd (arity d)))

end Trace

end Cslib.BitonicSort

namespace QuantumLTF.Membership.Supplement

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router Cslib.BitonicSort

/-- Classical integer comparison toggle on `(w + w + 1)` bits: XORs the target bit `(w + w)` with
`decide (bitsToNat a < bitsToNat b)`. -/
def ltBitsFn54 (w : ℕ) (x : Qubits (w + w + 1)) : Qubits (w + w + 1) :=
  let a : Qubits w := fun i => x ⟨i.1, by omega⟩
  let b : Qubits w := fun i => x ⟨w + i.1, by omega⟩
  Function.update x ⟨w + w, by omega⟩
    (xor (x ⟨w + w, by omega⟩) (decide (bitsToNat a < bitsToNat b)))

/-- Classical controlled-SWAP on `(1 + w + w)` bits: swaps the two `w`-bit registers iff wire `0`
is `true`. -/
def cswapRegFn54 (w : ℕ) (x : Qubits (1 + w + w)) : Qubits (1 + w + w) :=
  fun k =>
    if _h0 : k.1 = 0 then x k
    else if x ⟨0, by omega⟩ then
      if _hw : k.1 ≤ w then x ⟨k.1 + w, by have := k.isLt; omega⟩
      else x ⟨k.1 - w, by have := k.isLt; omega⟩
    else x k

/-- Project the leading `w_k`-bit key from a `(w_k + w_p)`-bit record. -/
def recKey54 {w_k w_p : ℕ} (r : Qubits (w_k + w_p)) : Qubits w_k :=
  fun i => r (Fin.castAdd w_p i)

/-- Project the trailing `w_p`-bit payload from a `(w_k + w_p)`-bit record. -/
def recPay54 {w_k w_p : ℕ} (r : Qubits (w_k + w_p)) : Qubits w_p :=
  fun j => r (Fin.natAdd w_k j)

/-- Classical generic key-comparator toggle on `(w_r + w_r + 1)` bits: XORs wire `(w_r + w_r)` with
`decide (key a < key b)`. -/
def cmpLtFn54 {κ : Type} [LinearOrder κ] (w_r : ℕ) (key : Qubits w_r → κ)
    (z : Qubits (w_r + w_r + 1)) : Qubits (w_r + w_r + 1) :=
  let a : Qubits w_r := fun i => z ⟨i.1, by omega⟩
  let b : Qubits w_r := fun i => z ⟨w_r + i.1, by omega⟩
  Function.update z ⟨w_r + w_r, by omega⟩
    (xor (z ⟨w_r + w_r, by omega⟩) (decide (key a < key b)))

/-- Pack `N` records of width `w`, a `T`-bit trace register, and `anc` zeroed ancilla qubits into a
flat `((N * w + T) + anc)`-qubit computational basis string. -/
def packDTA54 (N w T anc : ℕ) (arr : Fin N → Qubits w) (tr : Qubits T) : Qubits ((N * w + T) + anc) :=
  padZero (N * w + T) anc (Fin.append (flatReg N w arr) tr)

/-- Bundled pure bitonic-sort / trace-replay laws together with exact `gates12` circuits for
reversible keyed record sorting, trace-controlled routing/unrouting, and classical-`m` uniform
prefix state preparation. -/
structure BitonicRouting54 where
  C_sort : ℝ
  hC_sort_pos : 0 < C_sort
  C_unif : ℝ
  hC_unif_pos : 0 < C_unif
  sort_perm : ∀ {κ α : Type} [LinearOrder κ] (key : α → κ) (d : ℕ) (asc : Bool)
      (x : Fin (arity d) → α),
    (List.ofFn (sort key d asc x)).Perm (List.ofFn x)
  sort_sorted : ∀ {κ α : Type} [LinearOrder κ] (key : α → κ) (d : ℕ) (asc : Bool)
      (x : Fin (arity d) → α),
    if asc then Monotone (key ∘ sort key d asc x) else Antitone (key ∘ sort key d asc x)
  monotone_sort : ∀ {κ α : Type} [LinearOrder κ] (key : α → κ) (d : ℕ)
      (x : Fin (arity d) → α),
    Monotone (key ∘ sort key d true x)
  antitone_sort : ∀ {κ α : Type} [LinearOrder κ] (key : α → κ) (d : ℕ)
      (x : Fin (arity d) → α),
    Antitone (key ∘ sort key d false x)
  unrouteSort_routeSort : ∀ {α : Type} (d : ℕ) (flags : Fin (sortTraceSize d) → Bool)
      (x : Fin (arity d) → α),
    unrouteSort d flags (routeSort d flags x) = x
  routeSort_unrouteSort : ∀ {α : Type} (d : ℕ) (flags : Fin (sortTraceSize d) → Bool)
      (x : Fin (arity d) → α),
    routeSort d flags (unrouteSort d flags x) = x
  routeSort_sortTrace : ∀ {κ α : Type} [LinearOrder κ] (key : α → κ) (d : ℕ) (asc : Bool)
      (x : Fin (arity d) → α),
    routeSort d (sortTrace key d asc x) x = sort key d asc x
  routeSort_comp : ∀ {α β : Type} (d : ℕ) (flags : Fin (sortTraceSize d) → Bool)
      (f : α → β) (x : Fin (arity d) → α),
    routeSort d flags (f ∘ x) = f ∘ routeSort d flags x
  unrouteSort_comp : ∀ {α β : Type} (d : ℕ) (flags : Fin (sortTraceSize d) → Bool)
      (f : α → β) (x : Fin (arity d) → α),
    unrouteSort d flags (f ∘ x) = f ∘ unrouteSort d flags x
  unrouteSort_comp_sort : ∀ {κ α β : Type} [LinearOrder κ] (key : α → κ) (d : ℕ)
      (asc : Bool) (f : α → β) (x : Fin (arity d) → α),
    unrouteSort d (sortTrace key d asc x) (f ∘ sort key d asc x) = f ∘ x
  routeSort_apply : ∀ {α : Type} (d : ℕ) (flags : Fin (sortTraceSize d) → Bool)
      (x : Fin (arity d) → α) (i : Fin (arity d)),
    routeSort d flags x i = x (routeSort d flags id i)
  unrouteSort_apply : ∀ {α : Type} (d : ℕ) (flags : Fin (sortTraceSize d) → Bool)
      (x : Fin (arity d) → α) (i : Fin (arity d)),
    unrouteSort d flags x i = x (unrouteSort d flags id i)
  unrouteSort_rel_sort : ∀ {κ α β : Type} [LinearOrder κ] (key : α → κ) (d : ℕ) (asc : Bool)
      (x : Fin (arity d) → α) (y : Fin (arity d) → β) (R : α → β → Prop),
    (∀ i, R (sort key d asc x i) (y i)) → ∀ i, R (x i) (unrouteSort d (sortTrace key d asc x) y i)
  two_mul_mergeTraceSize : ∀ d : ℕ, 2 * mergeTraceSize d = d * 2 ^ d
  four_mul_sortTraceSize : ∀ d : ℕ, 4 * sortTraceSize d = d * (d + 1) * 2 ^ d
  sort_of_key_comp : ∀ {κ α β : Type} [LinearOrder κ] (key0 : β → κ) (f : α → β) (d : ℕ)
      (asc : Bool) (x : Fin (arity d) → α),
    f ∘ sort (key0 ∘ f) d asc x = sort key0 d asc (f ∘ x)
  sortTrace_of_key_comp : ∀ {κ α β : Type} [LinearOrder κ] (key0 : β → κ) (f : α → β) (d : ℕ)
      (asc : Bool) (x : Fin (arity d) → α),
    sortTrace (key0 ∘ f) d asc x = sortTrace key0 d asc (f ∘ x)
  ltBitsCircuit : (w : ℕ) → LayeredCircuit ((w + w + 1) + w)
  ltBitsCircuit_size : ∀ w : ℕ, (ltBitsCircuit w).size ≤ 20 * w + 1
  ltBitsCircuit_implements : ∀ w : ℕ,
    (ltBitsCircuit w).ImplementsOnClean (permMat (ltBitsFn54 w))
  cswapRegCircuit : (w : ℕ) → LayeredCircuit ((1 + w + w) + 0)
  cswapRegCircuit_size : ∀ w : ℕ, (cswapRegCircuit w).size = 7 * w
  cswapRegCircuit_implements : ∀ w : ℕ,
    (cswapRegCircuit w).ImplementsOnClean (permMat (cswapRegFn54 w))
  routeSortCircuit : (d w : ℕ) → LayeredCircuit (arity d * w + sortTraceSize d)
  routeSortCircuit_size_nat : ∀ d w : ℕ, (routeSortCircuit d w).size = 7 * w * sortTraceSize d
  routeSortCircuit_size : ∀ d w : ℕ,
    ((routeSortCircuit d w).size : ℝ) ≤ C_sort * (2 ^ d : ℝ) * ((d + 1 : ℝ) ^ 2) * (w + 1 : ℝ)
  act_routeSortCircuit_ket : ∀ (d w : ℕ) (x : Fin (arity d) → Qubits w)
      (flags : Fin (sortTraceSize d) → Bool),
    act (routeSortCircuit d w).unitary (ket (Fin.append (flatReg (arity d) w x) flags)) =
      ket (Fin.append (flatReg (arity d) w (routeSort d flags x)) flags)
  unrouteSortCircuit : (d w : ℕ) → LayeredCircuit (arity d * w + sortTraceSize d)
  unrouteSortCircuit_eq_adj : ∀ d w : ℕ, unrouteSortCircuit d w = (routeSortCircuit d w).adj
  unrouteSortCircuit_size_nat : ∀ d w : ℕ, (unrouteSortCircuit d w).size = 7 * w * sortTraceSize d
  unrouteSortCircuit_size : ∀ d w : ℕ,
    ((unrouteSortCircuit d w).size : ℝ) ≤ C_sort * (2 ^ d : ℝ) * ((d + 1 : ℝ) ^ 2) * (w + 1 : ℝ)
  act_unrouteSortCircuit_ket : ∀ (d w : ℕ) (x : Fin (arity d) → Qubits w)
      (flags : Fin (sortTraceSize d) → Bool),
    act (unrouteSortCircuit d w).unitary (ket (Fin.append (flatReg (arity d) w x) flags)) =
      ket (Fin.append (flatReg (arity d) w (unrouteSort d flags x)) flags)
  sortWithTraceCircuit : (d w_r anc_cmp : ℕ) →
    LayeredCircuit ((w_r + w_r + 1) + anc_cmp) → Bool →
    LayeredCircuit ((arity d * w_r + sortTraceSize d) + anc_cmp)
  sortWithTraceCircuit_size_nat : ∀ (d w_r anc_cmp : ℕ)
      (cmp : LayeredCircuit ((w_r + w_r + 1) + anc_cmp)) (asc : Bool),
    (sortWithTraceCircuit d w_r anc_cmp cmp asc).size ≤ sortTraceSize d * (cmp.size + 7 * w_r + 1)
  act_sortWithTraceCircuit_ket : ∀ {κ : Type} [LinearOrder κ] (d w_r anc_cmp : ℕ)
      (key : Qubits w_r → κ) (cmp : LayeredCircuit ((w_r + w_r + 1) + anc_cmp))
      (_hcmp : cmp.ImplementsOnClean (permMat (cmpLtFn54 w_r key)))
      (asc : Bool) (x : Fin (arity d) → Qubits w_r),
    act (sortWithTraceCircuit d w_r anc_cmp cmp asc).unitary
        (ket (packDTA54 (arity d) w_r (sortTraceSize d) anc_cmp x (fun _ => false))) =
      ket (packDTA54 (arity d) w_r (sortTraceSize d) anc_cmp (sort key d asc x) (sortTrace key d asc x))
  sortWithTraceCircuit_adj_unroute : ∀ {κ : Type} [LinearOrder κ] (d w_k w_p anc_cmp : ℕ)
      (key0 : Qubits w_k → κ)
      (cmp : LayeredCircuit (((w_k + w_p) + (w_k + w_p) + 1) + anc_cmp))
      (_hcmp : cmp.ImplementsOnClean (permMat (cmpLtFn54 (w_k + w_p) (key0 ∘ recKey54))))
      (asc : Bool) (k_in : Fin (arity d) → Qubits w_k) (y_p : Fin (arity d) → Qubits w_p),
    act (sortWithTraceCircuit d (w_k + w_p) anc_cmp cmp asc).adj.unitary
        (ket (packDTA54 (arity d) (w_k + w_p) (sortTraceSize d) anc_cmp
          (fun i => Fin.append (sort key0 d asc k_in i) (y_p i))
          (sortTrace key0 d asc k_in))) =
      ket (packDTA54 (arity d) (w_k + w_p) (sortTraceSize d) anc_cmp
        (fun i => Fin.append (k_in i) (unrouteSort d (sortTrace key0 d asc k_in) y_p i))
        (fun _ => false))
  bitonicSortKeyCircuit : (d w_k w_p : ℕ) → Bool →
    LayeredCircuit ((arity d * (w_k + w_p) + sortTraceSize d) + w_k)
  bitonicSortKeyCircuit_size : ∀ (d w_k w_p : ℕ) (asc : Bool),
    ((bitonicSortKeyCircuit d w_k w_p asc).size : ℝ) ≤
      C_sort * (2 ^ d : ℝ) * ((d + 1 : ℝ) ^ 2) * (w_k + w_p + 1 : ℝ)
  act_bitonicSortKeyCircuit_ket : ∀ (d w_k w_p : ℕ) (asc : Bool)
      (x : Fin (arity d) → Qubits (w_k + w_p)),
    act (bitonicSortKeyCircuit d w_k w_p asc).unitary
        (ket (packDTA54 (arity d) (w_k + w_p) (sortTraceSize d) w_k x (fun _ => false))) =
      ket (packDTA54 (arity d) (w_k + w_p) (sortTraceSize d) w_k
        (sort (fun r => bitsToNat (recKey54 r)) d asc x)
        (sortTrace (fun r => bitsToNat (recKey54 r)) d asc x))
  act_bitonicSortKeyCircuit_adj_unroute : ∀ (d w_k w_p : ℕ) (asc : Bool)
      (k_in : Fin (arity d) → Qubits w_k) (y_p : Fin (arity d) → Qubits w_p),
    act (bitonicSortKeyCircuit d w_k w_p asc).adj.unitary
        (ket (packDTA54 (arity d) (w_k + w_p) (sortTraceSize d) w_k
          (fun i => Fin.append (sort bitsToNat d asc k_in i) (y_p i))
          (sortTrace bitsToNat d asc k_in))) =
      ket (packDTA54 (arity d) (w_k + w_p) (sortTraceSize d) w_k
        (fun i => Fin.append (k_in i) (unrouteSort d (sortTrace bitsToNat d asc k_in) y_p i))
        (fun _ => false))
  unifPrefixCircuit : (b m : ℕ) → 1 ≤ m → m ≤ 2 ^ b → LayeredCircuit ((1 + b) + b)
  unifPrefixCircuit_size : ∀ (b m : ℕ) (hm1 : 1 ≤ m) (hm2 : m ≤ 2 ^ b),
    ((unifPrefixCircuit b m hm1 hm2).size : ℝ) ≤ C_unif * ((b + 1 : ℝ) ^ 2)
  act_unifPrefixCircuit_false : ∀ (b m : ℕ) (hm1 : 1 ≤ m) (hm2 : m ≤ 2 ^ b) (v : Qubits b),
    act (unifPrefixCircuit b m hm1 hm2).unitary
        (ket (padZero (1 + b) b (Fin.append (fun _ : Fin 1 => false) v))) =
      ket (padZero (1 + b) b (Fin.append (fun _ : Fin 1 => false) v))
  act_unifPrefixCircuit_true : ∀ (b m : ℕ) (hm1 : 1 ≤ m) (hm2 : m ≤ 2 ^ b),
    act (unifPrefixCircuit b m hm1 hm2).unitary
        (ket (padZero (1 + b) b (Fin.append (fun _ : Fin 1 => true) (fun _ : Fin b => false)))) =
      ((1 / Real.sqrt (m : ℝ) : ℝ) : ℂ) •
        ∑ d : Fin m, ket (padZero (1 + b) b (Fin.append (fun _ : Fin 1 => true) (natToBits b d.val)))
  act_unifPrefixCircuit_adj_false : ∀ (b m : ℕ) (hm1 : 1 ≤ m) (hm2 : m ≤ 2 ^ b) (v : Qubits b),
    act (unifPrefixCircuit b m hm1 hm2).adj.unitary
        (ket (padZero (1 + b) b (Fin.append (fun _ : Fin 1 => false) v))) =
      ket (padZero (1 + b) b (Fin.append (fun _ : Fin 1 => false) v))
  act_unifPrefixCircuit_adj_true : ∀ (b m : ℕ) (hm1 : 1 ≤ m) (hm2 : m ≤ 2 ^ b),
    act (unifPrefixCircuit b m hm1 hm2).adj.unitary
        (((1 / Real.sqrt (m : ℝ) : ℝ) : ℂ) •
          ∑ d : Fin m, ket (padZero (1 + b) b (Fin.append (fun _ : Fin 1 => true) (natToBits b d.val)))) =
      ket (padZero (1 + b) b (Fin.append (fun _ : Fin 1 => true) (fun _ : Fin b => false)))

end QuantumLTF.Membership.Supplement


