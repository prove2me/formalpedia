-- Prove2me | Definitions.Def_TwoMasterRoommates_Capped_NormalForm
-- name    : TwoMasterRoommates_Capped_NormalForm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:38:18.14157+00:00
-- url     : https://prove2.me/theorems/d3edbf0e-36e7-407d-9d63-ca9f4e6ddbe9
-- title:
--   Per-tier consecutive pairing, activity at cuts, and entering targets
-- statement:
--   A retained edge is cross-class or has unequal endpoint ranks in its own master. In each $A$ $a$-tier, gather the identities whose mates are also in that same tier and observer class, and sort them by $(b,\mathrm{ID})$. Use $(a,\mathrm{ID})$ for a $B$ $b$-tier. Consecutive pairing means an even list length and the first–second, third–fourth, and subsequent consecutive pairs actually matched. Normal form imposes this separately in every tier.
--
--   At cuts $(i,j)$, an $A$ identity is own-active if $a(v)\le i<Q_v$, and wrong-active if $a(v)>i$, $b(v)\le j$, and $Q_v>i$. Exchange the two classes and masters for the $B$ notions. For $L_A=\{v\in A:a(v)=t,b(v)>j\}$, the entering-target set consists of those identities with an $A$ mate of smaller $a$ rank, or of the same $a$ rank and $b$ rank at most $j$.
--
--   $$L_A=\{v\in A:a(v)=t,\ b(v)>j\}.$$
--
--   This captures the per-tier normalization and the precise two-target boundary bound, rather than a global sort of all internal identities.
-- source:
--   Bin Yu, STOC 2027 submission #225 (October 2026), pp. 4–6 (PDF pp. 5–7), Lemmas 3.1 and 4.1; p. 13 (PDF p. 14), Lemma B.2 and equation (8)

import Mathlib
import Definitions.Def_TwoMasterRoommates_Capped_Compression

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TwoMasterRoommates.Capped

def Keep {R : Type} [LinearOrder R] {n : ℕ} (I : Instance R n)
    (M : Fin n → Fin n) (v : Fin n) : Prop :=
  I.isA v ≠ I.isA (M v) ∨ I.r v v ≠ I.r v (M v)

noncomputable def tierList {R : Type} [LinearOrder R] {n : ℕ} (I : Instance R n)
    (M : Fin n → Fin n) (cls : Bool) (t : R) : List (Fin n) := by
  classical
  let own := if cls then I.a else I.b
  let foreign := if cls then I.b else I.a
  exact ((List.finRange n).filter fun v => I.isA v = cls ∧ own v = t ∧
      I.isA (M v) = cls ∧ own (M v) = t).mergeSort
    (fun x y => decide (foreign x < foreign y ∨ (foreign x = foreign y ∧ x ≤ y)))

def Consecutive {α : Type} (M : α → α) (xs : List α) : Prop :=
  Even xs.length ∧ ∀ k : ℕ, 2 * k + 1 < xs.length →
    ∃ u v, xs[2*k]? = some u ∧ xs[2*k+1]? = some v ∧ M u = v

noncomputable def NormalForm {R : Type} [LinearOrder R] {n : ℕ}
    (I : Instance R n) (M : Fin n → Fin n) : Prop :=
  ∀ cls t, Consecutive M (tierList I M cls t)

def OwnActive {R : Type} [LinearOrder R] {n : ℕ} (I : Instance R n)
    (M : Fin n → Fin n) (i j : R) (v : Fin n) : Prop :=
  if I.isA v then I.a v ≤ i ∧ i < Q I M v else I.b v ≤ j ∧ j < Q I M v

def WrongActive {R : Type} [LinearOrder R] {n : ℕ} (I : Instance R n)
    (M : Fin n → Fin n) (i j : R) (v : Fin n) : Prop :=
  if I.isA v then i < I.a v ∧ I.b v ≤ j ∧ i < Q I M v
  else j < I.b v ∧ I.a v ≤ i ∧ j < Q I M v

noncomputable def enteringTargets {R : Type} [LinearOrder R] {n : ℕ}
    (I : Instance R n) (M : Fin n → Fin n) (t j : R) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun v => I.isA v = true ∧ I.a v = t ∧ j < I.b v ∧
    I.isA (M v) = true ∧ (I.a (M v) < t ∨ (I.a (M v) = t ∧ I.b (M v) ≤ j))

end TwoMasterRoommates.Capped


