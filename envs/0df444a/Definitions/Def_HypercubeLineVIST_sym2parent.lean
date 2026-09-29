-- Prove2me | Definitions.Def_HypercubeLineVIST_sym2parent
-- name    : HypercubeLineVIST_sym2parent
-- status  : Definition
-- author  : @undercat
-- created : 2026-09-27T14:40:52.166294+00:00
-- url     : https://prove2.me/theorems/df0cbd4e-7780-4a43-b70a-e36289b0795d
-- title:
--   Sym2 parent functions for 2n-2 VISTs in L(Q_n)
-- statement:
--   Defines 2n-2 parent functions on unordered vertex pairs $Sym2((Fin n) \to Bool)$ for the line graph of the hypercube. Each tree targets an endpoint and dimension, routing pairs towards the target via Hamming-distance steps.

import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

open Classical

namespace HypercubeLineVISTSym2

/-! ## Parent functions on Sym2 (public types only, no private imports) -/

/-- Hamming distance between hypercube vertices. -/
def hamDist (n : Nat) (a b : Fin n → Bool) : Nat :=
  Finset.card (Finset.univ.filter (fun i => a i ≠ b i))

/-- Extract a representative pair from a Sym2. -/
noncomputable def sym2Rep (n : Nat) (s : Sym2 (Fin n → Bool)) : (Fin n → Bool) × (Fin n → Bool) :=
  Classical.choose (Quot.exists_rep s)

/-- Flip bit `c` of `z`. -/
def flipAt (n : Nat) (z : Fin n → Bool) (c : Fin n) : Fin n → Bool :=
  Function.update z c (!z c)

/-- The `i`-th dimension except `d`. -/
def dimExcept (n : Nat) (d : Fin n) (i : Fin (n - 1)) : Fin n :=
  if h : i.val < d.val then ⟨i.val, lt_trans h d.isLt⟩
  else ⟨i.val + 1, by have hi := i.isLt; have hd := d.isLt; omega⟩

/-- `dimExcept` never returns `d`. -/
lemma dimExcept_ne (n : Nat) (d : Fin n) (i : Fin (n - 1)) :
    dimExcept n d i ≠ d := by
  unfold dimExcept
  split
  · next h =>
    intro heq
    have hval : (⟨i.val, lt_trans h d.isLt⟩ : Fin n).val = d.val := congrArg Fin.val heq
    simp at hval
    omega
  · next h =>
    intro heq
    have hval : (⟨i.val + 1, by have hi := i.isLt; have hd := d.isLt; omega⟩ : Fin n).val = d.val :=
      congrArg Fin.val heq
    simp at hval
    omega

/-- Tree index. -/
abbrev TreeIdx (n : Nat) := Fin (2 * n - 2)

/-- Which endpoint-bit for tree `k`. -/
def treeEndpoint (n : Nat) (k : TreeIdx n) : Bool :=
  decide (k.val / (n - 1) = 1)

/-- Which dimension-index for tree `k`. -/
def treeDimIdx (n : Nat) (hn : 2 ≤ n) (k : TreeIdx n) : Fin (n - 1) :=
  ⟨k.val % (n - 1), Nat.mod_lt _ (by omega)⟩

/-- A coordinate where `z` differs from `t`. -/
noncomputable def diffCoord (n : Nat) (z t : Fin n → Bool) (h : z ≠ t) : Fin n :=
  Classical.choose (by
    by_contra hc
    push_neg at hc
    apply h
    funext i
    by_contra hne
    exact hc i hne)

/-- The parent function on Sym2 for tree `k`. -/
noncomputable def sym2Parent (n : Nat) (r : Sym2 (Fin n → Bool))
    (tgtRep : Fin n → Bool) (via : Sym2 (Fin n → Bool))
    (k : TreeIdx n) (s : Sym2 (Fin n → Bool)) : Sym2 (Fin n → Bool) :=
  if s = r then r
  else if s = via then r
  else
    let (x, y) := sym2Rep n s
    if h : x = tgtRep ∨ y = tgtRep then via
    else
      have hx : x ≠ tgtRep := fun heq => h (Or.inl heq)
      have hy : y ≠ tgtRep := fun heq => h (Or.inr heq)
      have hz : (if hamDist n x tgtRep ≤ hamDist n y tgtRep then x else y) ≠ tgtRep := by
        by_cases hc : hamDist n x tgtRep ≤ hamDist n y tgtRep
        · simp only [hc, if_true]; exact hx
        · simp only [hc, if_false]; exact hy
      let z := if hamDist n x tgtRep ≤ hamDist n y tgtRep then x else y
      let c := diffCoord n z tgtRep hz
      Sym2.mk z (flipAt n z c)

end HypercubeLineVISTSym2


