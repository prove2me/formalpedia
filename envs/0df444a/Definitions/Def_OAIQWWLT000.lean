-- Prove2me | Definitions.Def_OAIQWWLT000
-- name    : OAIQWWLT000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-23T21:49:59.381203+00:00
-- url     : https://prove2.me/theorems/f8727215-4d81-4a80-93d9-f9ebfc184a8c
-- title:
--   OpenAI Weisfeiler–Leman time lower bound split: definitions bundle
-- statement:
--   The definitions bundle of the split of OpenAI's proof of the unconditional time lower bound for deciding Weisfeiler–Leman equivalence (`OAI.WLTime.unconditional_time_lower_bound`, the paper's Theorem 1.1). It holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Computability/WeisfeilerLeman` (OpenAI, *Unconditional time lower bounds for Weisfeiler–Leman equivalence*, OpenAI Math Release, September 25, 2026, result family 133, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. Among them are the pebble-game positions and invariants (`Position`, `GameInvariant`, `Wins`), the consistency gadgets and their graphs (`ConsistencyData`, `TypeLink`, `ArcConsistent`, `ArcWitness`), the circuit and machine encodings, the one-tape writer programs and universal machine, the word-RAM simulation, and the consumers of the diagonal argument together with their budgets. The bundle also contains the lemmas those definitions use in their bodies.
--
--   The definitions of the published statement (`Graph`, `Convention`, `InputClass`, `Model`, `Decides`, `worstTime`, `MainClaim` and the rest) are not repeated: the bundle imports them from the published bundle `Def_WeisfeilerLeman`. It imports no other bundle of this split.
--
--   Modules: `Arithmetic`, `BoundedRun`, `Circuits`, `Colors`, `Consistency`, `Consumer`, `Diagonal`, `Digits`, `Enumeration`, `Expressions`, `Extension`, `Frames`, `Gadgets`, `GraphFormula`, `Interpreter`, `Marking`, `MatrixBounds`, `MatrixWriter`, `Offsets`, `Padding`, `Pebbles`, `Predicates`, `Programs`, `RAMBounds`, `RAMInstruction`, `RAMMemory`, `RAMSimulation`, `Readouts`, `Simulation`, `SparseSearch`, `SparseStore`, `Stacks`, `Sweep`, `Tableau`, `TapeCompiler`, `TapePair`, `Transducer`, `Turing`, `Universal`, `Wrapping`, `Writer`.
--
--   The theorems of the development that the definitions do not need are proved in the three solutions of this split. Two prove the published intermediate statements `OAI.WLTime.OneTape.Symbolic.FullWriter.consumer_correct` and `OAI.WLTime.OneTape.Symbolic.RAMWriter.correct`, and the third proves `OAI.WLTime.unconditional_time_lower_bound` from both. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, Unconditional time lower bounds for Weisfeiler–Leman equivalence, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 133; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Unconditional-time-lower-bounds-for-Weisfeiler-Leman-equivalence-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability/WeisfeilerLeman at commit adc7f12

import Mathlib
import Definitions.Def_WeisfeilerLeman

section
-- module Solutions.OAIQW_WLTime.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Colors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα uβ uC uγ

namespace WLTime

def Stable {n : ℕ} (c : Convention) (k : ℕ) (G H : Graph n)
    (v w : Fin k → Fin n) : Prop := ∀ t, tupleColor c k G t v = tupleColor c k H t w

end WLTime

namespace WLTime

def permuteColor (c : Convention) (k : ℕ) (π : Equiv.Perm (Fin k)) :
    (t : ℕ) → Color c k t → Color c k t
  | 0, col => (fun i j => col.1 (π i) (π j), fun i j => col.2 (π i) (π j))
  | t + 1, col => match c with
    | .joint => (permuteColor .joint k π t col.1,
        col.2.map (fun vector i => permuteColor .joint k π t (vector (π i))))
    | .separate => (permuteColor .separate k π t col.1,
        fun i => (col.2 (π i)).map (permuteColor .separate k π t))

end WLTime

namespace WLTime

abbrev Position (K n : ℕ) := Fin K → Option (Fin n × Fin n)

def Position.Sub {K n : ℕ} (P Q : Position K n) : Prop :=
  ∀ i, P i = none ∨ P i = Q i

def Position.PartialIso {K n : ℕ} (G H : Graph n) (P : Position K n) : Prop :=
  ∀ i j x y u v, P i = some (x, y) → P j = some (u, v) →
    (x = u ↔ y = v) ∧ G.adj x u = H.adj y v

structure GameInvariant {n : ℕ} (G H : Graph n) (K : ℕ) where
  safe : Position K n → Prop
  forget : ∀ {P Q}, safe Q → P.Sub Q → safe P
  atomic : ∀ {P}, safe P → P.PartialIso G H
  extend : ∀ {P}, safe P → ∀ i, P i = none →
    ∃ e : Fin n ≃ Fin n, ∀ z, safe (Function.update P i (some (z, e z)))

def Wins {n K : ℕ} (G H : Graph n) (P : Position K n) : Prop :=
  ∃ I : GameInvariant G H K, I.safe P

def Marks {n K k : ℕ} (P : Position K n) (slot : Fin k → Fin K)
    (v w : Fin k → Fin n) : Prop := ∀ i, P (slot i) = some (v i, w i)

end WLTime

namespace WLTime

def completePosition {n K : ℕ} (v w : Fin K → Fin n) : Position K n :=
  fun i => some (v i, w i)

end WLTime

namespace WLTime

def JointFull {n k : ℕ} (G H : Graph n) (v w : Fin (k + 1) → Fin n) : Prop :=
  ∀ τ : Fin k ↪ Fin (k + 1), Stable .joint k G H (v ∘ τ) (w ∘ τ)

end WLTime

namespace WLTime

def sparePosition {n k : ℕ} (v w : Fin k → Fin n) : Position (k + 1) n :=
  Fin.snoc (fun i => some (v i, w i)) none

end WLTime

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Offsets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV uE uF

namespace WLTime.Compression

abbrev F₂ := ZMod 2

variable {V : Type uV} {G : SimpleGraph V}

def walkWeight (mark : V → V → F₂) : {u v : V} → G.Walk u v → F₂
  | _, _, .nil => 0
  | _, _, @SimpleGraph.Walk.cons _ _ u v _ _ p => mark u v + walkWeight mark p

@[simp] theorem walkWeight_nil (mark : V → V → F₂) (v : V) :
    walkWeight mark (G := G) (.nil : G.Walk v v) = 0 := rfl

@[simp] theorem walkWeight_cons (mark : V → V → F₂) {u v w : V}
    (h : G.Adj u v) (p : G.Walk v w) :
    walkWeight mark (.cons h p) = mark u v + walkWeight mark p := rfl

@[simp] theorem walkWeight_append (mark : V → V → F₂) {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) :
    walkWeight mark (p.append q) = walkWeight mark p + walkWeight mark q := by
  induction p with
  | nil => simp [walkWeight]
  | @cons u v w h p ih => simp [walkWeight, ih, add_assoc]

@[simp] theorem walkWeight_reverse (mark : V → V → F₂)
    (hsymm : ∀ u v, G.Adj u v → mark u v = mark v u)
    {u v : V} (p : G.Walk u v) :
    walkWeight mark p.reverse = walkWeight mark p := by
  induction p with
  | nil => rfl
  | @cons u v w h p ih =>
    simp [SimpleGraph.Walk.reverse_cons, ih, hsymm u v h, add_comm]

theorem walkWeight_independent (mark : V → V → F₂)
    (hsymm : ∀ u v, G.Adj u v → mark u v = mark v u)
    (hclosed : ∀ v (p : G.Walk v v), walkWeight mark p = 0)
    {u v : V} (p q : G.Walk u v) : walkWeight mark p = walkWeight mark q := by
  have h := hclosed u (p.append q.reverse)
  simp only [walkWeight_append, walkWeight_reverse mark hsymm] at h
  have hz := CharTwo.add_self_eq_zero (walkWeight mark q)
  exact add_right_cancel (h.trans hz.symm)

theorem walkWeight_congr (mark mark' : V → V → F₂)
    (h : ∀ u v, G.Adj u v → mark u v = mark' u v)
    {u v : V} (p : G.Walk u v) : walkWeight mark p = walkWeight mark' p := by
  induction p with
  | nil => rfl
  | cons e p ih => simp only [walkWeight_cons, h _ _ e, ih]

@[simp] theorem walkWeight_zero {u v : V} (p : G.Walk u v) :
    walkWeight (fun _ _ => 0) p = 0 := by
  induction p with
  | nil => rfl
  | cons e p ih => simp only [walkWeight_cons, zero_add, ih]

@[simp] theorem walkWeight_add (a b : V → V → F₂) {u v : V} (p : G.Walk u v) :
    walkWeight (fun u v => a u v + b u v) p = walkWeight a p + walkWeight b p := by
  induction p with
  | nil => simp
  | cons e p ih => simp only [walkWeight_cons, ih]; abel

@[simp] theorem walkWeight_mul (a : V → V → F₂) (c : F₂)
    {u v : V} (p : G.Walk u v) :
    walkWeight (fun u v => c * a u v) p = c * walkWeight a p := by
  induction p with
  | nil => simp
  | cons e p ih => simp only [walkWeight_cons, ih, mul_add]

@[simp] theorem walkWeight_coboundary (s : V → F₂) {u v : V} (p : G.Walk u v) :
    walkWeight (fun u v => s u + s v) p = s u + s v := by
  induction p with
  | nil => simp [CharTwo.add_self_eq_zero]
  | @cons a b c e p ih =>
    simp only [walkWeight_cons, ih]
    calc
      _ = s a + (s b + s b) + s c := by abel
      _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]

noncomputable def potentialFrom (mark : V → V → F₂) (root v : V) : F₂ := by
  classical
  exact if h : G.Reachable root v then walkWeight mark h.some else 0

theorem potentialFrom_edge (mark : V → V → F₂)
    (hsymm : ∀ u v, G.Adj u v → mark u v = mark v u)
    (hclosed : ∀ v (p : G.Walk v v), walkWeight mark p = 0)
    {root u v : V} (hu : G.Reachable root u) (h : G.Adj u v) :
    potentialFrom (G := G) mark root u + potentialFrom (G := G) mark root v = mark u v := by
  classical
  have hv := hu.trans h.reachable
  simp only [potentialFrom, dite_eq_left hu, dite_eq_left hv]
  have hp := walkWeight_independent mark hsymm hclosed
    (hu.some.append (.cons h .nil)) hv.some
  simp only [walkWeight_append, walkWeight_cons, walkWeight_nil, add_zero] at hp
  rw [← hp, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

theorem exists_seam_potential (mark : V → V → F₂)
    (hsymm : ∀ u v, G.Adj u v → mark u v = mark v u)
    (hclosed : ∀ v (p : G.Walk v v), walkWeight mark p = 0) :
    ∃ s : V → F₂, ∀ u v, G.Adj u v → s u + s v = mark u v := by
  classical
  let root (v : V) : V := (G.connectedComponentMk v).out
  have hroot (v : V) : G.Reachable (root v) v :=
    SimpleGraph.ConnectedComponent.eq.mp (Quot.out_eq (G.connectedComponentMk v))
  refine ⟨fun v => potentialFrom (G := G) mark (root v) v, ?_⟩
  intro u v huv
  have heq : root u = root v :=
    congrArg Quot.out (SimpleGraph.ConnectedComponent.eq.mpr huv.reachable)
  change potentialFrom mark (root u) u + potentialFrom mark (root v) v = mark u v
  rw [← heq]
  exact potentialFrom_edge mark hsymm hclosed (hroot u) huv

section ReadoutAlgebra

variable {E : Type uE} {F : Type uF} [AddCommGroup E] [Module F₂ E]
  [AddCommGroup F] [Module F₂ F]

def horizontalReadout (left right shift : E) (seam : F₂) : E :=
  left + right + seam • shift

def verticalReadout (L : E →ₗ[F₂] F₂) (R : F →ₗ[F₂] F₂)
    (left : E) (right : F) : F₂ := L left + R right

theorem horizontal_adjustment (left right oldShift newShift : E)
    (s t seam : F₂) (hst : s + t = seam) :
    horizontalReadout (left + s • (oldShift - newShift))
      (right + t • (oldShift - newShift)) newShift seam =
        horizontalReadout left right oldShift seam := by
  unfold horizontalReadout
  calc
    _ = left + right + (s + t) • (oldShift - newShift) + seam • newShift := by
      module
    _ = _ := by rw [hst, smul_sub]; abel

theorem homogeneous_shift_difference (L : E →ₗ[F₂] F₂) (R : F →ₗ[F₂] F₂)
    (oldLeft newLeft : E) (oldRight newRight : F) (b : F₂)
    (ho : L oldLeft + R oldRight = b) (hn : L newLeft + R newRight = b) :
    L (oldLeft - newLeft) + R (oldRight - newRight) = 0 := by
  simp only [map_sub]
  linear_combination ho - hn

theorem vertical_adjustment (L : E →ₗ[F₂] F₂) (R : F →ₗ[F₂] F₂)
    (left gLeft : E) (right gRight : F) (s : F₂)
    (hg : L gLeft + R gRight = 0) :
    verticalReadout L R (left + s • gLeft) (right + s • gRight) =
      verticalReadout L R left right := by
  simp only [verticalReadout, map_add, map_smul, smul_eq_mul]
  linear_combination s * hg

theorem square_readouts_legal (L : E →ₗ[F₂] F₂) (R : F →ₗ[F₂] F₂)
    (left₀ left₁ shiftLeft : E) (right₀ right₁ shiftRight : F) (seam b : F₂)
    (hlink : L shiftLeft + R shiftRight = b) :
    L (horizontalReadout left₀ left₁ shiftLeft seam) +
      R (horizontalReadout right₀ right₁ shiftRight seam) +
      verticalReadout L R left₀ right₀ + verticalReadout L R left₁ right₁ =
        seam * b := by
  simp only [horizontalReadout, verticalReadout, map_add, map_smul, smul_eq_mul]
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) seam * hlink

end ReadoutAlgebra

end WLTime.Compression

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Wrapping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV uB uLabel uI

namespace WLTime.Compression

variable {V : Type uV} {G : SimpleGraph V}

theorem walkWeight_ne_zero_edge (mark : V → V → F₂) {u v : V} (p : G.Walk u v)
    (h : walkWeight mark p ≠ 0) :
    ∃ a b, G.Adj a b ∧ mark a b ≠ 0 := by
  induction p with
  | nil => exact (h rfl).elim
  | @cons a b c e p ih =>
    by_cases hab : mark a b = 0
    · apply ih
      simpa only [walkWeight_cons, hab, zero_add] using h
    · exact ⟨a, b, e, hab⟩

theorem closed_row_weights_eq {r : ℕ} (mark : Fin (r + 1) → V → V → F₂)
    (boundary : Fin r → V → F₂)
    (balance : ∀ i u v, G.Adj u v →
      mark i.castSucc u v + mark i.succ u v = boundary i u + boundary i v)
    {v : V} (p : G.Walk v v) (i j : Fin (r + 1)) :
    walkWeight (mark i) p = walkWeight (mark j) p := by
  have hstep (i : Fin r) :
      walkWeight (mark i.castSucc) p = walkWeight (mark i.succ) p := by
    have h := walkWeight_congr _ _ (balance i) p
    rw [walkWeight_add, walkWeight_coboundary, CharTwo.add_self_eq_zero] at h
    exact add_right_cancel (h.trans (CharTwo.add_self_eq_zero _).symm)
  have hzero (i : Fin (r + 1)) : walkWeight (mark i) p = walkWeight (mark 0) p :=
    Fin.induction rfl (fun i ih => (hstep i).symm.trans ih) i
  exact (hzero i).trans (hzero j).symm

theorem wrapping_all_rows {r : ℕ} {B : Type uB} (U : Finset B) (row : B → Fin (r + 1))
    (mark : Fin (r + 1) → V → V → F₂) (boundary : Fin r → V → F₂)
    (balance : ∀ i u v, G.Adj u v →
      mark i.castSucc u v + mark i.succ u v = boundary i u + boundary i v)
    (support : ∀ i u v, G.Adj u v → mark i u v ≠ 0 → ∃ b ∈ U, row b = i)
    {v : V} (p : G.Walk v v) (seam : Fin (r + 1))
    (wraps : walkWeight (mark seam) p ≠ 0) :
    ∀ i, ∃ b ∈ U, row b = i := by
  intro i
  have hi : walkWeight (mark i) p ≠ 0 := by
    rwa [closed_row_weights_eq mark boundary balance p i seam]
  obtain ⟨u, v, huv, hmark⟩ := walkWeight_ne_zero_edge _ p hi
  exact support i u v huv hmark

theorem wrapping_card_lower {r : ℕ} {B : Type uB} (U : Finset B) (row : B → Fin (r + 1))
    (mark : Fin (r + 1) → V → V → F₂) (boundary : Fin r → V → F₂)
    (balance : ∀ i u v, G.Adj u v →
      mark i.castSucc u v + mark i.succ u v = boundary i u + boundary i v)
    (support : ∀ i u v, G.Adj u v → mark i u v ≠ 0 → ∃ b ∈ U, row b = i)
    {v : V} (p : G.Walk v v) (seam : Fin (r + 1))
    (wraps : walkWeight (mark seam) p ≠ 0) : r + 1 ≤ U.card := by
  classical
  have hall := wrapping_all_rows U row mark boundary balance support p seam wraps
  have heq : U.image row = Finset.univ := by
    ext i
    simp only [Finset.mem_image, Finset.mem_univ, iff_true]
    exact hall i
  calc
    r + 1 = (U.image row).card := by rw [heq]; simp
    _ ≤ U.card := Finset.card_image_le

theorem unique_block_per_row {r : ℕ} {B : Type uB} (U : Finset B) (row : B → Fin (r + 1))
    (hall : ∀ i, ∃ b ∈ U, row b = i) (hcard : U.card = r + 1) :
    ∀ i, ∃! b, b ∈ U ∧ row b = i := by
  classical
  have heq : U.image row = Finset.univ := by
    ext i
    simp only [Finset.mem_image, Finset.mem_univ, iff_true]
    exact hall i
  have hinj : Set.InjOn row U := Finset.injOn_of_card_image_eq (by rw [heq, hcard]; simp)
  intro i
  obtain ⟨b, hb, hbi⟩ := hall i
  refine ⟨b, ⟨hb, hbi⟩, ?_⟩
  intro c hc
  exact hinj hc.1 hb (hc.2.trans hbi.symm)

end WLTime.Compression

namespace WLTime.Compression

variable {V : Type uV} {G : SimpleGraph V}

theorem boundary_label_recovery {Label : Type uLabel} [DecidableEq Label]
    (leftRow rightRow : V → V → F₂) (leftLabel rightLabel : Label)
    (boundary : Label → V → F₂)
    (balance : ∀ label u v, G.Adj u v →
      (if leftLabel = label then leftRow u v else 0) +
        (if rightLabel = label then rightRow u v else 0) =
          boundary label u + boundary label v)
    {v : V} (p : G.Walk v v) (wraps : walkWeight leftRow p ≠ 0) :
    leftLabel = rightLabel := by
  classical
  by_contra hne
  have h := walkWeight_congr _ _ (balance leftLabel) p
  simp only [ite_eq_right (Ne.symm hne), add_zero] at h
  rw [walkWeight_coboundary, CharTwo.add_self_eq_zero] at h
  exact wraps h

theorem difference_card_le_one {B : Type uB} [DecidableEq B]
    (U A B' : Finset B) (hA : A ⊆ U) (hB : B' ⊆ U) (d : ℕ)
    (hcardB : B'.card = d) (hcardU : U.card ≤ d + 1) : (A \ B').card ≤ 1 := by
  have hun : A ∪ B' ⊆ U := Finset.union_subset hA hB
  have hsize := Finset.card_le_card hun
  have hsum := Finset.card_sdiff_add_card A B'
  omega

theorem recovered_addresses_agree {B : Type uB} {I : Type uI} {Label : Type uLabel} [DecidableEq B]
    (next : Equiv.Perm I) (next_ne : ∀ i, next i ≠ i)
    (row : B → I) (leftLabel rightLabel : B → Label)
    (U A B' : Finset B) (hA : A ⊆ U) (hB : B' ⊆ U) (d : ℕ)
    (hcardB : B'.card = d) (hcardU : U.card ≤ d + 1)
    (rowsA : ∀ i, ∃ b ∈ A, row b = i)
    (addressA addressB : I → Label)
    (readsA : ∀ b ∈ A, addressA (row b) = leftLabel b ∧
      addressA (next (row b)) = rightLabel b)
    (readsB : ∀ b ∈ B', addressB (row b) = leftLabel b ∧
      addressB (next (row b)) = rightLabel b) : addressA = addressB := by
  have hdiff := difference_card_le_one U A B' hA hB d hcardB hcardU
  funext i
  obtain ⟨b, hb, hbi⟩ := rowsA i
  obtain ⟨c, hc, hci⟩ := rowsA (next.symm i)
  have hbc : b ≠ c := by
    intro heq
    have hi : i = next.symm i := hbi.symm.trans ((congrArg row heq).trans hci)
    have hh := congrArg next hi
    rw [next.apply_symm_apply] at hh
    exact next_ne i hh
  have hcommon : b ∈ B' ∨ c ∈ B' := by
    by_contra! hn
    have hsub : {b, c} ⊆ A \ B' := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_sdiff.mpr ⟨hb, hn.1⟩
      · exact Finset.mem_sdiff.mpr ⟨hc, hn.2⟩
    have htwo := Finset.card_le_card hsub
    rw [Finset.card_pair hbc] at htwo
    omega
  rcases hcommon with hb' | hc'
  · rw [← hbi, (readsA b hb).1, (readsB b hb').1]
  · have hi : next (row c) = i := by rw [hci, next.apply_symm_apply]
    rw [← hi, (readsA c hc).2, (readsB c hc').2]

end WLTime.Compression

namespace WLTime.Compression

@[simp] theorem rotate_castSucc {r : ℕ} (i : Fin r) :
    finRotate (r + 1) i.castSucc = i.succ := finRotate_of_lt i.isLt

theorem rotate_ne_self {r : ℕ} (hr : 1 ≤ r) (i : Fin (r + 1)) :
    finRotate (r + 1) i ≠ i := by
  intro he
  have hv := congrArg Fin.val he
  rw [coe_finRotate] at hv
  split_ifs at hv with h
  · have hi := congrArg Fin.val h
    simp only [Fin.val_last] at hi
    omega
  · omega

theorem rotate_no_two_cycle {r : ℕ} (hr : 2 ≤ r) (i j : Fin (r + 1)) :
    ¬(finRotate (r + 1) i = j ∧ finRotate (r + 1) j = i) := by
  rintro ⟨hij, hji⟩
  have hv := congrArg Fin.val hij
  have hw := congrArg Fin.val hji
  rw [coe_finRotate] at hv hw
  by_cases hi : i = Fin.last r <;> by_cases hj : j = Fin.last r
  all_goals simp [hi, hj] at hv hw
  all_goals omega

structure BlockDrawing (r : ℕ) (B : Type uB) (V : Type uV) where
  boundary : V → Fin (r + 1)
  row : B → Fin (r + 1)
  low : B → Bool → V
  high : B → Bool → V
  low_boundary : ∀ b s, boundary (low b s) = row b
  high_boundary : ∀ b s, boundary (high b s) = finRotate (r + 1) (row b)

namespace BlockDrawing

variable {r : ℕ} {B : Type uB} {V : Type uV} (D : BlockDrawing r B V)

def Edge (b : B) (x y : V) : Prop :=
  (∃ s, x = D.low b s ∧ y = D.high b s) ∨
  (x = D.low b false ∧ y = D.low b true) ∨
  (x = D.high b false ∧ y = D.high b true)

def graph (U : Finset B) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ∃ b ∈ U, D.Edge b x y ∨ D.Edge b y x
  symm := ⟨by
    rintro x y ⟨h, b, hb, he⟩
    exact ⟨h.symm, b, hb, he.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def rowMark (i : Fin (r + 1)) (x y : V) : F₂ :=
  if (D.boundary x = i ∧ D.boundary y = finRotate (r + 1) i) ∨
      (D.boundary y = i ∧ D.boundary x = finRotate (r + 1) i) then 1 else 0

@[simp] theorem rowMark_symm (i : Fin (r + 1)) (x y : V) :
    D.rowMark i x y = D.rowMark i y x := by
  simp only [rowMark, or_comm]

@[simp] theorem rowMark_horizontal (hr : 2 ≤ r) (i : Fin (r + 1)) (b : B) (s : Bool) :
    D.rowMark i (D.low b s) (D.high b s) = if i = D.row b then 1 else 0 := by
  simp only [rowMark, D.low_boundary, D.high_boundary]
  have hrev : ¬(finRotate (r + 1) (D.row b) = i ∧
      D.row b = finRotate (r + 1) i) := by
    rintro ⟨h1, h2⟩
    exact rotate_no_two_cycle hr (D.row b) i ⟨h1, h2.symm⟩
  simp only [hrev, or_false, Equiv.apply_eq_iff_eq, and_self, eq_comm (a := D.row b) (b := i)]

theorem rowMark_zero_of_boundary_eq (hr : 1 ≤ r) (i : Fin (r + 1))
    {x y : V} (hxy : D.boundary x = D.boundary y) : D.rowMark i x y = 0 := by
  rw [rowMark, ite_eq_right]
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact rotate_ne_self hr i (h2.symm.trans (hxy.symm.trans h1))
  · exact rotate_ne_self hr i (h2.symm.trans (hxy.trans h1))

def boundaryMark (i : Fin (r + 1)) (x : V) : F₂ :=
  if D.boundary x = i then 1 else 0

theorem row_balance_horizontal (hr : 2 ≤ r) (i : Fin r) (b : B) (s : Bool) :
    D.rowMark i.castSucc (D.low b s) (D.high b s) +
      D.rowMark i.succ (D.low b s) (D.high b s) =
    D.boundaryMark i.succ (D.low b s) + D.boundaryMark i.succ (D.high b s) := by
  rw [D.rowMark_horizontal hr, D.rowMark_horizontal hr]
  simp only [boundaryMark, D.low_boundary, D.high_boundary,
    ← rotate_castSucc i, Equiv.apply_eq_iff_eq]
  simp only [eq_comm (a := D.row b) (b := i.castSucc), eq_comm (a := D.row b) (b := ((finRotate (r + 1)) i.castSucc))]
  exact add_comm _ _

theorem row_balance_vertical (hr : 2 ≤ r) (i : Fin r) {x y : V}
    (hxy : D.boundary x = D.boundary y) :
    D.rowMark i.castSucc x y + D.rowMark i.succ x y =
      D.boundaryMark i.succ x + D.boundaryMark i.succ y := by
  rw [D.rowMark_zero_of_boundary_eq (by omega) _ hxy,
    D.rowMark_zero_of_boundary_eq (by omega) _ hxy, zero_add]
  unfold boundaryMark
  rw [hxy, CharTwo.add_self_eq_zero]

theorem row_balance_edge (hr : 2 ≤ r) (i : Fin r) {b : B} {x y : V}
    (h : D.Edge b x y) :
    D.rowMark i.castSucc x y + D.rowMark i.succ x y =
      D.boundaryMark i.succ x + D.boundaryMark i.succ y := by
  rcases h with ⟨s, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact D.row_balance_horizontal hr i b s
  · exact D.row_balance_vertical hr i ((D.low_boundary b false).trans (D.low_boundary b true).symm)
  · exact D.row_balance_vertical hr i ((D.high_boundary b false).trans (D.high_boundary b true).symm)

theorem row_balance (hr : 2 ≤ r) (U : Finset B) (i : Fin r) {x y : V}
    (h : (D.graph U).Adj x y) :
    D.rowMark i.castSucc x y + D.rowMark i.succ x y =
      D.boundaryMark i.succ x + D.boundaryMark i.succ y := by
  obtain ⟨_, b, _, h | h⟩ := h
  · exact D.row_balance_edge hr i h
  · simpa only [D.rowMark_symm _ y x, add_comm (D.boundaryMark i.succ y)] using
      D.row_balance_edge hr i h

theorem row_support_edge (hr : 2 ≤ r) (i : Fin (r + 1)) {b : B} {x y : V}
    (h : D.Edge b x y) (hm : D.rowMark i x y ≠ 0) : D.row b = i := by
  rcases h with ⟨s, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [D.rowMark_horizontal hr] at hm
    by_contra hne
    exact hm (ite_eq_right (Ne.symm hne))
  · exact (hm (D.rowMark_zero_of_boundary_eq (by omega) _
      ((D.low_boundary b false).trans (D.low_boundary b true).symm))).elim
  · exact (hm (D.rowMark_zero_of_boundary_eq (by omega) _
      ((D.high_boundary b false).trans (D.high_boundary b true).symm))).elim

theorem row_support (hr : 2 ≤ r) (U : Finset B) (i : Fin (r + 1)) {x y : V}
    (h : (D.graph U).Adj x y) (hm : D.rowMark i x y ≠ 0) : ∃ b ∈ U, D.row b = i := by
  obtain ⟨_, b, hb, h | h⟩ := h
  · exact ⟨b, hb, D.row_support_edge hr i h hm⟩
  · exact ⟨b, hb, D.row_support_edge hr i h (by rwa [D.rowMark_symm])⟩

def Wraps (U : Finset B) : Prop :=
  ∃ v, ∃ p : (D.graph U).Walk v v, walkWeight (D.rowMark (Fin.last r)) p ≠ 0

theorem wraps_card (hr : 2 ≤ r) (U : Finset B) (h : D.Wraps U) : r + 1 ≤ U.card := by
  obtain ⟨v, p, hp⟩ := h
  exact wrapping_card_lower U D.row D.rowMark (fun i => D.boundaryMark i.succ)
    (fun i x y h => D.row_balance hr U i h)
    (fun i x y h hm => D.row_support hr U i h hm) p (Fin.last r) hp

theorem wraps_unique_row (hr : 2 ≤ r) (U : Finset B) (h : D.Wraps U)
    (hc : U.card = r + 1) : ∀ i, ∃! b, b ∈ U ∧ D.row b = i := by
  obtain ⟨v, p, hp⟩ := h
  apply unique_block_per_row U D.row ?_ hc
  exact wrapping_all_rows U D.row D.rowMark (fun i => D.boundaryMark i.succ)
    (fun i x y h => D.row_balance hr U i h)
    (fun i x y h hm => D.row_support hr U i h hm) p (Fin.last r) hp

end BlockDrawing
end WLTime.Compression

namespace WLTime.Compression
namespace BlockDrawing
variable {r : ℕ} {B : Type uB} {V : Type uV} {Label : Type uLabel} (D : BlockDrawing r B V)

theorem edge_reachable (U : Finset B) {b : B} (hb : b ∈ U) {x y : V}
    (h : D.Edge b x y) : (D.graph U).Reachable x y := by
  by_cases he : x = y
  · subst y; exact SimpleGraph.Reachable.refl _
  · exact (show (D.graph U).Adj x y from ⟨he, b, hb, Or.inl h⟩).reachable

theorem low_reachable (U : Finset B) {b : B} (hb : b ∈ U) (s : Bool) :
    (D.graph U).Reachable (D.low b false) (D.low b s) := by
  cases s
  · exact SimpleGraph.Reachable.refl _
  · exact D.edge_reachable U hb (Or.inr (Or.inl ⟨rfl, rfl⟩))

theorem high_reachable (U : Finset B) {b : B} (hb : b ∈ U) (s : Bool) :
    (D.graph U).Reachable (D.low b false) (D.high b s) :=
  (D.low_reachable U hb s).trans (D.edge_reachable U hb (Or.inl ⟨s, rfl, rfl⟩))

theorem edge_left_reachable (U : Finset B) {b : B} (hb : b ∈ U) {x y : V}
    (h : D.Edge b x y) : (D.graph U).Reachable (D.low b false) x := by
  rcases h with ⟨s, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact D.low_reachable U hb s
  · exact D.low_reachable U hb false
  · exact D.high_reachable U hb false

theorem edge_right_reachable (U : Finset B) {b : B} (hb : b ∈ U) {x y : V}
    (h : D.Edge b x y) : (D.graph U).Reachable (D.low b false) y :=
  (D.edge_left_reachable U hb h).trans (D.edge_reachable U hb h)

theorem row_weight_nonzero_has_block (hr : 2 ≤ r) (U : Finset B)
    {v w : V} (p : (D.graph U).Walk v w) (i : Fin (r + 1))
    (h : walkWeight (D.rowMark i) p ≠ 0) :
    ∃ b ∈ U, D.row b = i ∧ (D.graph U).Reachable v (D.low b false) := by
  induction p with
  | nil => exact (h rfl).elim
  | @cons x y z hxy p ih =>
    by_cases hm : D.rowMark i x y = 0
    · have hp : walkWeight (D.rowMark i) p ≠ 0 := by
        simpa only [walkWeight_cons, hm, zero_add] using h
      obtain ⟨b, hb, hbi, hrch⟩ := ih hp
      exact ⟨b, hb, hbi, hxy.reachable.trans hrch⟩
    · obtain ⟨_, b, hb, he | he⟩ := hxy
      · exact ⟨b, hb, D.row_support_edge hr i he hm, (D.edge_left_reachable U hb he).symm⟩
      · exact ⟨b, hb, D.row_support_edge hr i he (by rwa [D.rowMark_symm]),
          (D.edge_right_reachable U hb he).symm⟩

theorem wraps_connected (hr : 2 ≤ r) (U : Finset B) (h : D.Wraps U)
    (hc : U.card = r + 1) : ∀ b ∈ U, ∀ c ∈ U,
    (D.graph U).Reachable (D.low b false) (D.low c false) := by
  have hu := D.wraps_unique_row hr U h hc
  obtain ⟨v, p, hp⟩ := h
  have hreach : ∀ b ∈ U, (D.graph U).Reachable v (D.low b false) := by
    intro b hb
    have hrow : walkWeight (D.rowMark (D.row b)) p ≠ 0 := by
      rwa [closed_row_weights_eq D.rowMark (fun i => D.boundaryMark i.succ)
        (fun i x y h => D.row_balance hr U i h) p (D.row b) (Fin.last r)]
    obtain ⟨c, hc', he, hreach⟩ := D.row_weight_nonzero_has_block hr U p (D.row b) hrow
    obtain ⟨d, hd, huniq⟩ := hu (D.row b)
    have hcb : c = b := (huniq c ⟨hc', he⟩).trans (huniq b ⟨hb, rfl⟩).symm
    simpa only [hcb] using hreach
  exact fun b hb c hc => (hreach b hb).symm.trans (hreach c hc)

variable [DecidableEq Label]

def labeledBoundary (label : V → Label) (i : Fin (r + 1)) (a : Label) (x : V) : F₂ :=
  if D.boundary x = i ∧ label x = a then 1 else 0

omit [DecidableEq Label] in
theorem side_label_low (label : V → Label) {b : B}
    (h : label (D.low b false) = label (D.low b true)) (s : Bool) :
    label (D.low b s) = label (D.low b false) := by cases s <;> simp_all

omit [DecidableEq Label] in
theorem side_label_high (label : V → Label) {b : B}
    (h : label (D.high b false) = label (D.high b true)) (s : Bool) :
    label (D.high b s) = label (D.high b false) := by cases s <;> simp_all

theorem labeled_balance_horizontal (hr : 2 ≤ r) (U : Finset B) (label : V → Label)
    (lo hi : Fin (r + 1) → Label)
    (labels : ∀ b ∈ U, ∀ s, label (D.low b s) = lo (D.row b) ∧
      label (D.high b s) = hi (D.row b))
    (i : Fin (r + 1)) (a : Label) {b : B} (hb : b ∈ U) (s : Bool) :
    (if hi i = a then D.rowMark i (D.low b s) (D.high b s) else 0) +
    (if lo (finRotate (r + 1) i) = a then
      D.rowMark (finRotate (r + 1) i) (D.low b s) (D.high b s) else 0) =
    D.labeledBoundary label (finRotate (r + 1) i) a (D.low b s) +
      D.labeledBoundary label (finRotate (r + 1) i) a (D.high b s) := by
  rw [D.rowMark_horizontal hr, D.rowMark_horizontal hr]
  simp only [labeledBoundary, D.low_boundary, D.high_boundary, (labels b hb s).1,
    (labels b hb s).2, Equiv.apply_eq_iff_eq]
  by_cases hbi : D.row b = i
  · have hni := rotate_ne_self (by omega : 1 ≤ r) i
    simp only [hbi, hni, Ne.symm hni, ↓reduceIte, false_and, true_and, ite_self, zero_add, add_zero]
  · by_cases hbn : D.row b = finRotate (r + 1) i
    · have hni := rotate_ne_self (by omega : 1 ≤ r) i
      simp only [hbn, hni, Ne.symm hni, ↓reduceIte, false_and, true_and, ite_self, zero_add, add_zero]
    · simp only [hbi, hbn, Ne.symm hbi, Ne.symm hbn, ↓reduceIte, false_and, ite_self, zero_add]

theorem labeled_balance_vertical (hr : 2 ≤ r) (label : V → Label)
    (lo hi : Fin (r + 1) → Label) (i : Fin (r + 1)) (a : Label) {x y : V}
    (hxy : D.boundary x = D.boundary y) (hl : label x = label y) :
    (if hi i = a then D.rowMark i x y else 0) +
      (if lo (finRotate (r + 1) i) = a then D.rowMark (finRotate (r + 1) i) x y else 0) =
    D.labeledBoundary label (finRotate (r + 1) i) a x +
      D.labeledBoundary label (finRotate (r + 1) i) a y := by
  rw [D.rowMark_zero_of_boundary_eq (by omega) _ hxy,
    D.rowMark_zero_of_boundary_eq (by omega) _ hxy]
  simp only [ite_self, labeledBoundary, hxy, hl, CharTwo.add_self_eq_zero]

theorem labeled_balance_edge (hr : 2 ≤ r) (U : Finset B) (label : V → Label)
    (lo hi : Fin (r + 1) → Label)
    (labels : ∀ b ∈ U, ∀ s, label (D.low b s) = lo (D.row b) ∧
      label (D.high b s) = hi (D.row b))
    (i : Fin (r + 1)) (a : Label) {b : B} (hb : b ∈ U) {x y : V}
    (h : D.Edge b x y) :
    (if hi i = a then D.rowMark i x y else 0) +
      (if lo (finRotate (r + 1) i) = a then D.rowMark (finRotate (r + 1) i) x y else 0) =
    D.labeledBoundary label (finRotate (r + 1) i) a x +
      D.labeledBoundary label (finRotate (r + 1) i) a y := by
  rcases h with ⟨s, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact D.labeled_balance_horizontal hr U label lo hi labels i a hb s
  · exact D.labeled_balance_vertical hr label lo hi i a
      ((D.low_boundary b false).trans (D.low_boundary b true).symm)
      ((labels b hb false).1.trans (labels b hb true).1.symm)
  · exact D.labeled_balance_vertical hr label lo hi i a
      ((D.high_boundary b false).trans (D.high_boundary b true).symm)
      ((labels b hb false).2.trans (labels b hb true).2.symm)

theorem labeled_balance (hr : 2 ≤ r) (U : Finset B) (label : V → Label)
    (lo hi : Fin (r + 1) → Label)
    (labels : ∀ b ∈ U, ∀ s, label (D.low b s) = lo (D.row b) ∧
      label (D.high b s) = hi (D.row b))
    (i : Fin (r + 1)) (a : Label) {x y : V} (h : (D.graph U).Adj x y) :
    (if hi i = a then D.rowMark i x y else 0) +
      (if lo (finRotate (r + 1) i) = a then D.rowMark (finRotate (r + 1) i) x y else 0) =
    D.labeledBoundary label (finRotate (r + 1) i) a x +
      D.labeledBoundary label (finRotate (r + 1) i) a y := by
  obtain ⟨_, b, hb, h | h⟩ := h
  · exact D.labeled_balance_edge hr U label lo hi labels i a hb h
  · simpa only [D.rowMark_symm _ y x, add_comm (D.labeledBoundary label _ a y)] using
      D.labeled_balance_edge hr U label lo hi labels i a hb h

theorem wrapping_labels_join (hr : 2 ≤ r) (U : Finset B) (label : V → Label)
    (lo hi : Fin (r + 1) → Label)
    (labels : ∀ b ∈ U, ∀ s, label (D.low b s) = lo (D.row b) ∧
      label (D.high b s) = hi (D.row b)) (h : D.Wraps U) :
    ∀ i, hi i = lo (finRotate (r + 1) i) := by
  obtain ⟨v, p, hp⟩ := h
  intro i
  apply boundary_label_recovery (D.rowMark i) (D.rowMark (finRotate (r + 1) i))
    (hi i) (lo (finRotate (r + 1) i)) (D.labeledBoundary label (finRotate (r + 1) i))
    (fun a x y h => D.labeled_balance hr U label lo hi labels i a h) p
  rwa [closed_row_weights_eq D.rowMark (fun i => D.boundaryMark i.succ)
    (fun i x y h => D.row_balance hr U i h) p i (Fin.last r)]

end BlockDrawing
end WLTime.Compression

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Frames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uB uV uLabel uP uE uΛ

namespace WLTime.Compression
namespace BlockDrawing
variable {r : ℕ} {B : Type uB} {V : Type uV} {Label : Type uLabel} [DecidableEq Label] (D : BlockDrawing r B V)

theorem address_exists (hr : 2 ≤ r) (U : Finset B) (label : V → Label)
    (align : ∀ b ∈ U, label (D.low b false) = label (D.low b true) ∧
      label (D.high b false) = label (D.high b true))
    (h : D.Wraps U) (hc : U.card = r + 1) :
    ∃ a : Fin (r + 1) → Label, ∀ b ∈ U, ∀ s,
      label (D.low b s) = a (D.row b) ∧
      label (D.high b s) = a (finRotate (r + 1) (D.row b)) := by
  classical
  have hex := D.wraps_unique_row hr U h hc
  choose f hf huniq using hex
  let lo := fun i => label (D.low (f i) false)
  let hi := fun i => label (D.high (f i) false)
  have hlabels : ∀ b ∈ U, ∀ s, label (D.low b s) = lo (D.row b) ∧
      label (D.high b s) = hi (D.row b) := by
    intro b hb s
    have hbf := huniq (D.row b) b ⟨hb, rfl⟩
    constructor
    · exact (D.side_label_low label (align b hb).1 s).trans (congrArg (fun b => label (D.low b false)) hbf)
    · exact (D.side_label_high label (align b hb).2 s).trans (congrArg (fun b => label (D.high b false)) hbf)
  have hjoin := D.wrapping_labels_join hr U label lo hi hlabels h
  exact ⟨lo, fun b hb s => ⟨(hlabels b hb s).1, (hlabels b hb s).2.trans (hjoin (D.row b))⟩⟩

omit [DecidableEq Label] in

theorem addresses_agree [DecidableEq B] (hr : 2 ≤ r) (U A C : Finset B)
    (hA : A ⊆ U) (hC : C ⊆ U) (hcard : U.card ≤ r + 2)
    (hwrap : D.Wraps A) (hsizeA : A.card = r + 1) (hsizeC : C.card = r + 1)
    (label : V → Label) (a c : Fin (r + 1) → Label)
    (ha : ∀ b ∈ A, ∀ s, label (D.low b s) = a (D.row b) ∧
      label (D.high b s) = a (finRotate (r + 1) (D.row b)))
    (hc : ∀ b ∈ C, ∀ s, label (D.low b s) = c (D.row b) ∧
      label (D.high b s) = c (finRotate (r + 1) (D.row b))) : a = c := by
  apply recovered_addresses_agree (finRotate (r + 1)) (rotate_ne_self (by omega)) D.row
    (fun b => label (D.low b false)) (fun b => label (D.high b false))
    U A C hA hC (r + 1) hsizeC (by omega)
  · intro i
    obtain ⟨b, hb, _⟩ := D.wraps_unique_row hr A hwrap hsizeA i
    exact ⟨b, hb⟩
  · exact fun b hb => ⟨(ha b hb false).1.symm, (ha b hb false).2.symm⟩
  · exact fun b hb => ⟨(hc b hb false).1.symm, (hc b hb false).2.symm⟩

end BlockDrawing
end WLTime.Compression

namespace WLTime.Compression

variable {P : Type uP} {E : Type uE}

abbrev TypeNode (K : ℕ) (P : Type uP) (E : Type uE) := P ⊕ (E × Fin (4 * K))
abbrev TypeLink (K : ℕ) (E : Type uE) := E × Fin (4 * K + 1)

def linkLeft (K : ℕ) (src : E → P) (l : TypeLink K E) : TypeNode K P E :=
  if h : l.2.val = 0 then Sum.inl (src l.1)
  else Sum.inr (l.1, ⟨l.2.val - 1, by have := l.2.isLt; omega⟩)

def linkRight (K : ℕ) (dst : E → P) (l : TypeLink K E) : TypeNode K P E :=
  if h : l.2.val = 4 * K then Sum.inl (dst l.1)
  else Sum.inr (l.1, ⟨l.2.val, by have := l.2.isLt; omega⟩)

def typeDepth (K : ℕ) : TypeNode K P E → ℕ
  | .inl _ => 0
  | .inr (_, j) => min (j.val + 1) (4 * K - j.val)

def linkDepth (K : ℕ) (src dst : E → P) (l : TypeLink K E) : ℕ :=
  min (typeDepth K (linkLeft K src l)) (typeDepth K (linkRight K dst l))

theorem link_depth_near (K : ℕ) (src dst : E → P) (l : TypeLink K E) :
    typeDepth K (linkLeft K src l) ≤ typeDepth K (linkRight K dst l) + 1 ∧
    typeDepth K (linkRight K dst l) ≤ typeDepth K (linkLeft K src l) + 1 := by
  have hj := l.2.isLt
  dsimp only [linkLeft, linkRight]
  split_ifs <;> simp only [typeDepth] <;> omega

theorem link_midpoint_depth (K : ℕ) (src dst : E → P) (hK : 0 < K)
    (l : TypeLink K E) (hl : l.2.val = 2 * K) :
    typeDepth K (linkLeft K src l) = 2 * K ∧
    typeDepth K (linkRight K dst l) = 2 * K := by
  have h0 : l.2.val ≠ 0 := by omega
  have h4 : l.2.val ≠ 4 * K := by omega
  simp only [linkLeft, linkRight, dite_eq_right h0, dite_eq_right h4, typeDepth]
  omega

theorem exists_missing_depth [DecidableEq E] (K : ℕ) (src dst : E → P) (hK : 0 < K)
    (S : Finset (TypeLink K E)) (hS : S.card ≤ K) :
    ∃ h, h < 2 * K ∧ ∀ l ∈ S, linkDepth K src dst l ≠ h := by
  classical
  by_contra! h
  have hsub : Finset.range (2 * K) ⊆ S.image (linkDepth K src dst) := by
    intro a ha
    obtain ⟨l, hl, heq⟩ := h a (Finset.mem_range.mp ha)
    exact Finset.mem_image.mpr ⟨l, hl, heq⟩
  have hc := (Finset.card_le_card hsub).trans (Finset.card_image_le)
  simp only [Finset.card_range] at hc
  omega

def typeSupportGraph (K : ℕ) (src dst : E → P) (S : Finset (TypeLink K E)) :
    SimpleGraph (TypeNode K P E) where
  Adj x y := x ≠ y ∧ ∃ l ∈ S,
    (x = linkLeft K src l ∧ y = linkRight K dst l) ∨
    (x = linkRight K dst l ∧ y = linkLeft K src l)
  symm := ⟨by
    rintro x y ⟨hxy, l, hl, h | h⟩
    · exact ⟨hxy.symm, l, hl, Or.inr ⟨h.2, h.1⟩⟩
    · exact ⟨hxy.symm, l, hl, Or.inl ⟨h.2, h.1⟩⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

theorem equal_cut_of_near {a b h : ℕ} (hab : a ≤ b + 1) (hba : b ≤ a + 1)
    (hh : min a b ≠ h) : (a ≤ h ↔ b ≤ h) := by omega

theorem support_cut_preserved (K : ℕ) (src dst : E → P) (S : Finset (TypeLink K E))
    (h : ℕ) (hh : ∀ l ∈ S, linkDepth K src dst l ≠ h)
    {x y : TypeNode K P E} (hxy : (typeSupportGraph K src dst S).Adj x y) :
    (typeDepth K x ≤ h ↔ typeDepth K y ≤ h) := by
  obtain ⟨_, l, hl, he | he⟩ := hxy
  · obtain ⟨rfl, rfl⟩ := he
    exact equal_cut_of_near (link_depth_near K src dst l).1
      (link_depth_near K src dst l).2 (hh l hl)
  · obtain ⟨rfl, rfl⟩ := he
    exact (equal_cut_of_near (link_depth_near K src dst l).1
      (link_depth_near K src dst l).2 (hh l hl)).symm

theorem support_walk_cut (K : ℕ) (src dst : E → P) (S : Finset (TypeLink K E))
    (h : ℕ) (hh : ∀ l ∈ S, linkDepth K src dst l ≠ h)
    {x y : TypeNode K P E} (w : (typeSupportGraph K src dst S).Walk x y) :
    (typeDepth K x ≤ h ↔ typeDepth K y ≤ h) := by
  induction w with
  | nil => rfl
  | cons hxy w ih => exact (support_cut_preserved K src dst S h hh hxy).trans ih

theorem reachable_real_depth [DecidableEq E] (K : ℕ) (src dst : E → P) (hK : 0 < K)
    (S : Finset (TypeLink K E)) (hS : S.card ≤ K) (p : P)
    {t : TypeNode K P E} (ht : (typeSupportGraph K src dst S).Reachable (.inl p) t) :
    typeDepth K t < 2 * K := by
  obtain ⟨h, hh, hmissing⟩ := exists_missing_depth K src dst hK S hS
  obtain ⟨w⟩ := ht
  have hd := (support_walk_cut K src dst S h hmissing w).mp (Nat.zero_le h)
  exact lt_of_le_of_lt hd hh

end WLTime.Compression

namespace WLTime.Compression

variable {P : Type uP} {E : Type uE}

def nodeWire (K : ℕ) : TypeNode K P E → Option E
  | .inl _ => none
  | .inr (e, _) => some e

theorem link_internal_same_wire (K : ℕ) (src dst : E → P) (l : TypeLink K E)
    (hl : ∀ p, linkLeft K src l ≠ Sum.inl p)
    (hr : ∀ p, linkRight K dst l ≠ Sum.inl p) :
    nodeWire K (linkLeft K src l) = nodeWire K (linkRight K dst l) := by
  have h0 : l.2.val ≠ 0 := by
    intro h
    exact hl (src l.1) (dite_eq_left h)
  have h4 : l.2.val ≠ 4 * K := by
    intro h
    exact hr (dst l.1) (dite_eq_left h)
  simp only [linkLeft, linkRight, dite_eq_right h0, dite_eq_right h4, nodeWire]

theorem support_edge_wire (K : ℕ) (src dst : E → P) (S : Finset (TypeLink K E))
    {x y : TypeNode K P E} (hxy : (typeSupportGraph K src dst S).Adj x y)
    (hx : ∀ p, x ≠ Sum.inl p) (hy : ∀ p, y ≠ Sum.inl p) :
    nodeWire K x = nodeWire K y := by
  obtain ⟨_, l, _, he | he⟩ := hxy
  · obtain ⟨rfl, rfl⟩ := he
    exact link_internal_same_wire K src dst l hx hy
  · obtain ⟨rfl, rfl⟩ := he
    exact (link_internal_same_wire K src dst l hy hx).symm

theorem support_walk_wire (K : ℕ) (src dst : E → P) (S : Finset (TypeLink K E))
    {x y : TypeNode K P E} (w : (typeSupportGraph K src dst S).Walk x y)
    (hreal : ∀ p, ¬(typeSupportGraph K src dst S).Reachable x (.inl p)) :
    nodeWire K x = nodeWire K y := by
  induction w with
  | nil => rfl
  | @cons x z y hxz w ih =>
    have hz : ∀ p, ¬(typeSupportGraph K src dst S).Reachable z (.inl p) :=
      fun p h => hreal p (hxz.reachable.trans h)
    apply (support_edge_wire K src dst S hxz
      (fun p h => hreal p (h ▸ SimpleGraph.Reachable.refl x))
      (fun p h => hz p (h ▸ SimpleGraph.Reachable.refl z))).trans
    exact ih hz

noncomputable def extendCoordinate {Λ : Type uΛ} [Fintype Λ] (A : Finset Λ)
    (f : A → Λ) (hf : Function.Injective f) : Equiv.Perm Λ :=
  Classical.choose (Equiv.Perm.exists_extending_pair Subtype.val f Subtype.val_injective hf)

theorem extendCoordinate_apply {Λ : Type uΛ} [Fintype Λ] (A : Finset Λ)
    (f : A → Λ) (hf : Function.Injective f) (a : A) :
    extendCoordinate A f hf a = f a :=
  Classical.choose_spec (Equiv.Perm.exists_extending_pair Subtype.val f Subtype.val_injective hf) a

def typeFrame {Λ : Type uΛ} (K : ℕ) (perm : E → Equiv.Perm Λ) :
    TypeNode K P E → Equiv.Perm Λ
  | .inl _ => Equiv.refl Λ
  | .inr (e, j) => if j.val < 2 * K then Equiv.refl Λ else perm e

def linkMatch {Λ : Type uΛ} (K : ℕ) (perm : E → Equiv.Perm Λ)
    (l : TypeLink K E) : Equiv.Perm Λ :=
  if l.2.val = 4 * K then perm l.1 else Equiv.refl Λ

theorem frame_match {Λ : Type uΛ} (K : ℕ) (src dst : E → P) (hK : 0 < K)
    (perm : E → Equiv.Perm Λ) (l : TypeLink K E) (hmid : l.2.val ≠ 2 * K) (a : Λ) :
    typeFrame K perm (linkLeft K src l) a =
      typeFrame K perm (linkRight K dst l) (linkMatch K perm l a) := by
  have hj := l.2.isLt
  dsimp only [linkLeft, linkRight]
  split_ifs <;> simp only [typeFrame, linkMatch]
  all_goals (try split_ifs) <;> first | rfl | omega

end WLTime.Compression

namespace WLTime.Compression
variable {P : Type uP} {E : Type uE}

theorem support_link_reachable (K : ℕ) (src dst : E → P)
    (S : Finset (TypeLink K E)) {l : TypeLink K E} (hl : l ∈ S) :
    (typeSupportGraph K src dst S).Reachable (linkLeft K src l) (linkRight K dst l) := by
  by_cases h : linkLeft K src l = linkRight K dst l
  · rw [h]
  · exact SimpleGraph.Adj.reachable ⟨h, l, hl, Or.inl ⟨rfl, rfl⟩⟩

def HasReal (K : ℕ) (src dst : E → P) (S : Finset (TypeLink K E))
    (t : TypeNode K P E) : Prop :=
  ∃ p, (typeSupportGraph K src dst S).Reachable (Sum.inl p) t

theorem hasReal_of_reachable (K : ℕ) (src dst : E → P)
    (S : Finset (TypeLink K E)) {x y : TypeNode K P E}
    (hxy : (typeSupportGraph K src dst S).Reachable x y) :
    HasReal K src dst S x ↔ HasReal K src dst S y := by
  constructor
  · rintro ⟨p, hp⟩; exact ⟨p, hp.trans hxy⟩
  · rintro ⟨p, hp⟩; exact ⟨p, hp.trans hxy.symm⟩

theorem hasReal_inl (K : ℕ) (src dst : E → P) (S : Finset (TypeLink K E)) (p : P) :
    HasReal K src dst S (.inl p) := ⟨p, SimpleGraph.Reachable.refl _⟩

noncomputable def supportFrame {Λ : Type uΛ} (K : ℕ) (src dst : E → P)
    (perm : E → Equiv.Perm Λ) (S : Finset (TypeLink K E)) (t : TypeNode K P E) :
    Equiv.Perm Λ := by
  classical
  exact if HasReal K src dst S t then typeFrame K perm t else Equiv.refl Λ

theorem supportFrame_match [DecidableEq E] {Λ : Type uΛ} (K : ℕ) (src dst : E → P)
    (hK : 0 < K) (perm : E → Equiv.Perm Λ) (S : Finset (TypeLink K E)) (hS : S.card ≤ K)
    (l : TypeLink K E) (hl : l ∈ S) (a : Λ) :
    supportFrame K src dst perm S (linkLeft K src l) a =
      supportFrame K src dst perm S (linkRight K dst l) (linkMatch K perm l a) := by
  classical
  have heq := hasReal_of_reachable K src dst S (support_link_reachable K src dst S hl)
  by_cases hreal : HasReal K src dst S (linkLeft K src l)
  · have hreal' := heq.mp hreal
    simp only [supportFrame, ite_eq_left hreal, ite_eq_left hreal']
    apply frame_match K src dst hK
    intro hmid
    obtain ⟨p, hp⟩ := hreal
    have hd := reachable_real_depth K src dst hK S hS p hp
    have hm := (link_midpoint_depth K src dst hK l hmid).1
    omega
  · have hreal' : ¬HasReal K src dst S (linkRight K dst l) := mt heq.mpr hreal
    have h4 : l.2.val ≠ 4 * K := by
      intro h
      apply hreal'
      simpa only [linkRight, dite_eq_left h] using hasReal_inl K src dst S (dst l.1)
    simp only [supportFrame, ite_eq_right hreal, ite_eq_right hreal', linkMatch, ite_eq_right h4,
      Equiv.refl_apply]

theorem support_graph_mono (K : ℕ) (src dst : E → P)
    {S R : Finset (TypeLink K E)} (h : S ⊆ R) :
    typeSupportGraph K src dst S ≤ typeSupportGraph K src dst R := by
  rintro x y ⟨hne, l, hl, he⟩
  exact ⟨hne, l, h hl, he⟩

end WLTime.Compression

namespace WLTime.Compression
variable {P : Type uP} {E : Type uE} {Λ : Type uΛ}

theorem hasReal_mono (K : ℕ) (src dst : E → P) {S R : Finset (TypeLink K E)}
    (hSR : S ⊆ R) {t : TypeNode K P E} (h : HasReal K src dst S t) : HasReal K src dst R t := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, hp.mono (support_graph_mono K src dst hSR)⟩

end WLTime.Compression

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Consistency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uP uE uΛ uT uLabel uL uB uV

namespace WLTime.Compression
variable {P : Type uP} {E : Type uE} {Λ : Type uΛ}

def frameTransition {K : ℕ} (old new : TypeNode K P E → Equiv.Perm Λ)
    (t : TypeNode K P E) : Equiv.Perm Λ := (old t).symm.trans (new t)

theorem frameTransition_link (K : ℕ) (src dst : E → P)
    (perm : E → Equiv.Perm Λ) (l : TypeLink K E)
    (old new : TypeNode K P E → Equiv.Perm Λ)
    (ho : ∀ a, old (linkLeft K src l) a =
      old (linkRight K dst l) (linkMatch K perm l a))
    (hn : ∀ a, new (linkLeft K src l) a =
      new (linkRight K dst l) (linkMatch K perm l a)) :
    frameTransition old new (linkLeft K src l) =
      frameTransition old new (linkRight K dst l) := by
  ext a
  change new (linkLeft K src l) ((old (linkLeft K src l)).symm a) =
    new (linkRight K dst l) ((old (linkRight K dst l)).symm a)
  rw [hn]
  congr 1
  apply (old (linkRight K dst l)).injective
  rw [← ho, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem frameTransition_walk (K : ℕ) (src dst : E → P)
    (perm : E → Equiv.Perm Λ) (S : Finset (TypeLink K E))
    (old new : TypeNode K P E → Equiv.Perm Λ)
    (ho : ∀ l ∈ S, ∀ a, old (linkLeft K src l) a =
      old (linkRight K dst l) (linkMatch K perm l a))
    (hn : ∀ l ∈ S, ∀ a, new (linkLeft K src l) a =
      new (linkRight K dst l) (linkMatch K perm l a))
    {x y : TypeNode K P E} (w : (typeSupportGraph K src dst S).Walk x y) :
    frameTransition old new x = frameTransition old new y := by
  induction w with
  | nil => rfl
  | @cons x z y hxz w ih =>
    apply Eq.trans (b := frameTransition old new z) _ ih
    obtain ⟨_, l, hl, he | he⟩ := hxz
    · obtain ⟨rfl, rfl⟩ := he
      exact frameTransition_link K src dst perm l old new (ho l hl) (hn l hl)
    · obtain ⟨rfl, rfl⟩ := he
      exact (frameTransition_link K src dst perm l old new (ho l hl) (hn l hl)).symm

end WLTime.Compression

namespace WLTime.Compression

structure ConsistencyData (r m : ℕ) (P : Type uP) (E : Type uE) where
  dim : P → ℕ
  src : E → P
  dst : E → P
  domain : E → Fin r → Finset (Fin m)
  coord : (e : E) → (i : Fin r) → domain e i → Fin m
  coord_inj : ∀ e i, Function.Injective (coord e i)
  linearSrc : (e : E) → (Fin (dim (src e)) → F₂) →ₗ[F₂] F₂
  linearDst : (e : E) → (Fin (dim (dst e)) → F₂) →ₗ[F₂] F₂
  biasSrc : E → F₂
  biasDst : E → F₂

namespace ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} (I : ConsistencyData r m P E)

abbrev RealValue (p : P) := Fin (I.dim p) → F₂
abbrev Address (_I : ConsistencyData r m P E) := Fin r → Fin m

def Allowed (e : E) (a : I.Address) : Prop := ∀ i, a i ∈ I.domain e i

def transmit (e : E) (a : I.Address) (ha : I.Allowed e a) : I.Address :=
  fun i => I.coord e i ⟨a i, ha i⟩

def affineSrc (e : E) (x : I.RealValue (I.src e)) : F₂ := I.linearSrc e x + I.biasSrc e

def affineDst (e : E) (x : I.RealValue (I.dst e)) : F₂ := I.linearDst e x + I.biasDst e

def ArcConsistent : Prop :=
  ∃ Q : (p : P) → I.Address → Set (I.RealValue p),
    (∀ p a, (Q p a).Nonempty) ∧
    ∀ e a (ha : I.Allowed e a),
      I.affineSrc e '' Q (I.src e) a =
        I.affineDst e '' Q (I.dst e) (I.transmit e a ha)

noncomputable def coordinatePerm (e : E) (i : Fin r) : Equiv.Perm (Fin m) :=
  extendCoordinate (I.domain e i) (I.coord e i) (I.coord_inj e i)

theorem coordinatePerm_apply (e : E) (i : Fin r) (a : I.domain e i) :
    I.coordinatePerm e i a = I.coord e i a :=
  extendCoordinate_apply (I.domain e i) (I.coord e i) (I.coord_inj e i) a

noncomputable def permuteAddress (e : E) (a : I.Address) : I.Address := fun i => I.coordinatePerm e i (a i)

theorem permuteAddress_eq (e : E) (a : I.Address) (ha : I.Allowed e a) :
    I.permuteAddress e a = I.transmit e a ha := by
  funext i
  exact I.coordinatePerm_apply e i ⟨a i, ha i⟩

abbrev Value (K : ℕ) : TypeNode K P E → Type
  | .inl p => I.RealValue p
  | .inr _ => F₂

instance instAddCommGroupValue (K : ℕ) (t : TypeNode K P E) : AddCommGroup (I.Value K t) := by
  cases t <;> dsimp [Value] <;> infer_instance

instance instModuleF₂Value (K : ℕ) (t : TypeNode K P E) : Module F₂ (I.Value K t) := by
  cases t <;> dsimp [Value] <;> infer_instance

instance instFintypeValue (K : ℕ) (t : TypeNode K P E) : Fintype (I.Value K t) := by
  cases t <;> dsimp [Value] <;> infer_instance

noncomputable def transportForm (K : ℕ) {s t : TypeNode K P E} (hst : s = t)
    (f : I.Value K t →ₗ[F₂] F₂) : I.Value K s →ₗ[F₂] F₂ := hst.symm ▸ f

theorem transportForm_apply (K : ℕ) {s t : TypeNode K P E} (hst : s = t)
    (f : I.Value K t →ₗ[F₂] F₂) (x : (t : TypeNode K P E) → I.Value K t) :
    I.transportForm K hst f (x s) = f (x t) := by
  subst t
  rfl

noncomputable def leftForm (K : ℕ) (l : TypeLink K E) :
    I.Value K (linkLeft K I.src l) →ₗ[F₂] F₂ :=
  if h : l.2.val = 0 then
    I.transportForm K (t := .inl (I.src l.1)) (by simp only [linkLeft, dite_eq_left h]) (I.linearSrc l.1)
  else
    I.transportForm K (show linkLeft K I.src l = Sum.inr
      (l.1, ⟨l.2.val - 1, by have := l.2.isLt; omega⟩) by simp only [linkLeft, dite_eq_right h])
      LinearMap.id

noncomputable def rightForm (K : ℕ) (l : TypeLink K E) :
    I.Value K (linkRight K I.dst l) →ₗ[F₂] F₂ :=
  if h : l.2.val = 4 * K then
    I.transportForm K (t := .inl (I.dst l.1)) (by simp only [linkRight, dite_eq_left h]) (I.linearDst l.1)
  else
    I.transportForm K (show linkRight K I.dst l = Sum.inr
      (l.1, ⟨l.2.val, by have := l.2.isLt; omega⟩) by simp only [linkRight, dite_eq_right h])
      LinearMap.id

def linkBias (K : ℕ) (l : TypeLink K E) : F₂ :=
  if l.2.val = 0 then I.biasSrc l.1 else
    if l.2.val = 4 * K then I.biasDst l.1 else 0

def ShiftSolves (K : ℕ) (S : Finset (TypeLink K E))
    (h : (t : TypeNode K P E) → I.Value K t) : Prop :=
  ∀ l ∈ S, I.leftForm K l (h (linkLeft K I.src l)) +
    I.rightForm K l (h (linkRight K I.dst l)) = I.linkBias K l

def rootedShift (K : ℕ) (h : (p : P) → I.RealValue p) :
    (t : TypeNode K P E) → I.Value K t
  | .inl p => h p
  | .inr (e, j) => if j.val < 2 * K then I.affineSrc e (h (I.src e))
      else I.affineDst e (h (I.dst e))

theorem rootedShift_link (K : ℕ) (hK : 0 < K) (h : (p : P) → I.RealValue p)
    (l : TypeLink K E) (hmid : l.2.val ≠ 2 * K) :
    I.leftForm K l (I.rootedShift K h (linkLeft K I.src l)) +
      I.rightForm K l (I.rootedShift K h (linkRight K I.dst l)) = I.linkBias K l := by
  have hj := l.2.isLt
  by_cases h0 : l.2.val = 0
  · have h4 : l.2.val ≠ 4 * K := by omega
    simp only [leftForm, rightForm, dite_eq_left h0, dite_eq_right h4]
    rw [transportForm_apply, transportForm_apply]
    simp only [rootedShift, LinearMap.id_coe, id_eq, h0, show 0 < 2 * K by omega, ite_true,
      affineSrc, linkBias]
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  · by_cases h4 : l.2.val = 4 * K
    · have hhalf : ¬l.2.val - 1 < 2 * K := by omega
      simp only [leftForm, rightForm, dite_eq_right h0, dite_eq_left h4]
      rw [transportForm_apply, transportForm_apply]
      simp only [rootedShift, LinearMap.id_coe, id_eq, ite_eq_right hhalf, affineDst, linkBias,
        ite_eq_right h0, ite_eq_left h4]
      rw [add_right_comm, CharTwo.add_self_eq_zero, zero_add]
    · have heq : l.2.val - 1 < 2 * K ↔ l.2.val < 2 * K := by omega
      simp only [leftForm, rightForm, dite_eq_right h0, dite_eq_right h4]
      rw [transportForm_apply, transportForm_apply]
      simp only [rootedShift, LinearMap.id_coe, id_eq, linkBias, ite_eq_right h0, ite_eq_right h4,
        heq, CharTwo.add_self_eq_zero]

theorem leftForm_section_internal (K : ℕ) (l : TypeLink K E) (h0 : l.2.val ≠ 0)
    (h : (t : TypeNode K P E) → I.Value K t) :
    I.leftForm K l (h (linkLeft K I.src l)) =
      h (.inr (l.1, ⟨l.2.val - 1, by have := l.2.isLt; omega⟩)) := by
  simp only [leftForm, dite_eq_right h0]
  exact I.transportForm_apply K _ _ h

theorem rightForm_section_internal (K : ℕ) (l : TypeLink K E) (h4 : l.2.val ≠ 4 * K)
    (h : (t : TypeNode K P E) → I.Value K t) :
    I.rightForm K l (h (linkRight K I.dst l)) =
      h (.inr (l.1, ⟨l.2.val, by have := l.2.isLt; omega⟩)) := by
  simp only [rightForm, dite_eq_right h4]
  exact I.transportForm_apply K _ _ h

noncomputable def canonicalShift (K : ℕ) (S : Finset (TypeLink K E))
    (x : (p : P) → I.RealValue p) (z : E → F₂) (t : TypeNode K P E) : I.Value K t := by
  classical
  exact if HasReal K I.src I.dst S t then I.rootedShift K x t else
    match t with
    | .inl p => x p
    | .inr (e, _) => z e

theorem canonicalShift_solves [DecidableEq E] (K : ℕ) (hK : 0 < K)
    (S : Finset (TypeLink K E)) (hS : S.card ≤ K)
    (x : (p : P) → I.RealValue p) (z : E → F₂) :
    I.ShiftSolves K S (I.canonicalShift K S x z) := by
  classical
  intro l hl
  have hreach := support_link_reachable K I.src I.dst S hl
  have heq := hasReal_of_reachable K I.src I.dst S hreach
  by_cases hreal : HasReal K I.src I.dst S (linkLeft K I.src l)
  · have hreal' := heq.mp hreal
    simp only [canonicalShift, ite_eq_left hreal, ite_eq_left hreal']
    apply I.rootedShift_link K hK
    intro hmid
    obtain ⟨p, hp⟩ := hreal
    have hd := reachable_real_depth K I.src I.dst hK S hS p hp
    have hm := (link_midpoint_depth K I.src I.dst hK l hmid).1
    omega
  · have hreal' := mt heq.mpr hreal
    have h0 : l.2.val ≠ 0 := by
      intro h
      apply hreal
      simpa only [linkLeft, dite_eq_left h] using hasReal_inl K I.src I.dst S (I.src l.1)
    have h4 : l.2.val ≠ 4 * K := by
      intro h
      apply hreal'
      simpa only [linkRight, dite_eq_left h] using hasReal_inl K I.src I.dst S (I.dst l.1)
    rw [I.leftForm_section_internal K l h0, I.rightForm_section_internal K l h4]
    have hlreal : ¬ HasReal K I.src I.dst S
        (.inr (l.1, ⟨l.2.val - 1, by have := l.2.isLt; omega⟩)) := by
      simpa only [linkLeft, dite_eq_right h0] using hreal
    have hrreal : ¬ HasReal K I.src I.dst S
        (.inr (l.1, ⟨l.2.val, by have := l.2.isLt; omega⟩)) := by
      simpa only [linkRight, dite_eq_right h4] using hreal'
    simp only [canonicalShift, ite_eq_right hlreal, ite_eq_right hrreal, linkBias,
      ite_eq_right h0, ite_eq_right h4, CharTwo.add_self_eq_zero]

structure ArcWitness where
  sets : (p : P) → I.Address → Set (I.RealValue p)
  nonempty : ∀ p a, (sets p a).Nonempty
  images : ∀ e a (ha : I.Allowed e a),
    I.affineSrc e '' sets (I.src e) a =
      I.affineDst e '' sets (I.dst e) (I.transmit e a ha)

namespace ArcWitness
variable {I} (Q : I.ArcWitness)

def internalSet (e : E) (a : I.Address) : Set F₂ := I.affineSrc e '' Q.sets (I.src e) a

theorem internal_nonempty (e : E) (a : I.Address) : (Q.internalSet e a).Nonempty :=
  (Q.nonempty (I.src e) a).image _

theorem src_preimage (e : E) (a : I.Address) {s : F₂} (hs : s ∈ Q.internalSet e a) :
    ∃ h ∈ Q.sets (I.src e) a, I.affineSrc e h = s := hs

theorem dst_preimage (e : E) (a : I.Address) (ha : I.Allowed e a)
    {s : F₂} (hs : s ∈ Q.internalSet e a) :
    ∃ h ∈ Q.sets (I.dst e) (I.permuteAddress e a), I.affineDst e h = s := by
  rw [I.permuteAddress_eq e a ha]
  change s ∈ I.affineDst e '' Q.sets (I.dst e) (I.transmit e a ha)
  rw [← Q.images e a ha]
  exact hs

theorem src_mem_internal (e : E) (a : I.Address) {h : I.RealValue (I.src e)}
    (hh : h ∈ Q.sets (I.src e) a) : I.affineSrc e h ∈ Q.internalSet e a :=
  ⟨h, hh, rfl⟩

theorem dst_mem_internal (e : E) (a : I.Address) (ha : I.Allowed e a)
    {h : I.RealValue (I.dst e)} (hh : h ∈ Q.sets (I.dst e) (I.permuteAddress e a)) :
    I.affineDst e h ∈ Q.internalSet e a := by
  rw [I.permuteAddress_eq e a ha] at hh
  rw [internalSet, Q.images e a ha]
  exact ⟨h, hh, rfl⟩

end ArcWitness

def scalarOf (K : ℕ) (h : (t : TypeNode K P E) → I.Value K t) : TypeNode K P E → F₂
  | .inl _ => 0
  | .inr ej => h (.inr ej)

theorem scalar_eq_on_internal_link (K : ℕ) (l : TypeLink K E)
    (h : (t : TypeNode K P E) → I.Value K t)
    (hl : I.leftForm K l (h (linkLeft K I.src l)) +
      I.rightForm K l (h (linkRight K I.dst l)) = I.linkBias K l)
    (h0 : l.2.val ≠ 0) (h4 : l.2.val ≠ 4 * K) :
    I.scalarOf K h (linkLeft K I.src l) = I.scalarOf K h (linkRight K I.dst l) := by
  rw [I.leftForm_section_internal K l h0, I.rightForm_section_internal K l h4] at hl
  simp only [linkBias, ite_eq_right h0, ite_eq_right h4] at hl
  simp only [linkLeft, linkRight, dite_eq_right h0, dite_eq_right h4, scalarOf]
  calc
    _ = _ + (h (.inr (l.1, ⟨l.2.val - 1, by have := l.2.isLt; omega⟩)) +
      h (.inr (l.1, ⟨l.2.val, by have := l.2.isLt; omega⟩))) := by rw [hl, add_zero]
    _ = _ := by rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

theorem scalar_eq_on_internal_edge (K : ℕ) (S : Finset (TypeLink K E))
    (h : (t : TypeNode K P E) → I.Value K t) (hs : I.ShiftSolves K S h)
    {x y : TypeNode K P E} (hxy : (typeSupportGraph K I.src I.dst S).Adj x y)
    (hx : ∀ p, x ≠ Sum.inl p) (hy : ∀ p, y ≠ Sum.inl p) :
    I.scalarOf K h x = I.scalarOf K h y := by
  have aux : ∀ l ∈ S, (∀ p, linkLeft K I.src l ≠ Sum.inl p) →
      (∀ p, linkRight K I.dst l ≠ Sum.inl p) →
      I.scalarOf K h (linkLeft K I.src l) = I.scalarOf K h (linkRight K I.dst l) := by
    intro l hl hleft hright
    apply I.scalar_eq_on_internal_link K l h (hs l hl)
    · intro hz; exact hleft (I.src l.1) (dite_eq_left hz)
    · intro hz; exact hright (I.dst l.1) (dite_eq_left hz)
  obtain ⟨_, l, hl, he | he⟩ := hxy
  · obtain ⟨rfl, rfl⟩ := he; exact aux l hl hx hy
  · obtain ⟨rfl, rfl⟩ := he; exact (aux l hl hy hx).symm

theorem scalar_eq_on_rootfree_walk (K : ℕ) (S : Finset (TypeLink K E))
    (h : (t : TypeNode K P E) → I.Value K t) (hs : I.ShiftSolves K S h)
    {x y : TypeNode K P E} (w : (typeSupportGraph K I.src I.dst S).Walk x y)
    (hreal : ¬HasReal K I.src I.dst S x) : I.scalarOf K h x = I.scalarOf K h y := by
  induction w with
  | nil => rfl
  | @cons x z y hxz w ih =>
    have hz : ¬HasReal K I.src I.dst S z :=
      mt (hasReal_of_reachable K I.src I.dst S hxz.reachable).mpr hreal
    apply (I.scalar_eq_on_internal_edge K S h hs hxz
      (fun p he => hreal (he.symm ▸ hasReal_inl K I.src I.dst S p))
      (fun p he => hz (he.symm ▸ hasReal_inl K I.src I.dst S p))).trans
    exact ih hz

end ConsistencyData
end WLTime.Compression

namespace WLTime.Compression

structure Corner (r : ℕ) (T : Type uT) (Label : Type uLabel) where
  boundary : Fin (r + 1)
  type : T
  label : Label
  deriving DecidableEq, Fintype

inductive BlockName (r : ℕ) (T : Type uT) (L : Type uL) (Label : Type uLabel) where
  | site (row : Fin (r + 1)) (type : T) (lowLabel highLabel : Label)
  | square (row : Fin (r + 1)) (link : L) (lowLabel highLabel : Label)
  deriving DecidableEq, Fintype

namespace BlockName
variable {r : ℕ} {T : Type uT} {L : Type uL} {Label : Type uLabel}

def row : BlockName r T L Label → Fin (r + 1)
  | .site i _ _ _ => i
  | .square i _ _ _ => i

def low (left right : L → T) (matchLabel : L → Fin (r + 1) → Equiv.Perm Label) :
    BlockName r T L Label → Bool → Corner r T Label
  | .site i t a _, _ => ⟨i, t, a⟩
  | .square i l a _, false => ⟨i, left l, a⟩
  | .square i l a _, true => ⟨i, right l, matchLabel l i a⟩

def high (left right : L → T) (matchLabel : L → Fin (r + 1) → Equiv.Perm Label) :
    BlockName r T L Label → Bool → Corner r T Label
  | .site i t _ b, _ => ⟨finRotate (r + 1) i, t, b⟩
  | .square i l _ b, false => ⟨finRotate (r + 1) i, left l, b⟩
  | .square i l _ b, true => ⟨finRotate (r + 1) i, right l, matchLabel l (finRotate (r + 1) i) b⟩

def drawing (left right : L → T) (matchLabel : L → Fin (r + 1) → Equiv.Perm Label) :
    BlockDrawing r (BlockName r T L Label) (Corner r T Label) where
  boundary := Corner.boundary
  row := row
  low := low left right matchLabel
  high := high left right matchLabel
  low_boundary := by intro b s; cases b <;> cases s <;> rfl
  high_boundary := by intro b s; cases b <;> cases s <;> rfl

noncomputable def blockLinks [DecidableEq L] : BlockName r T L Label → Finset L
  | .site _ _ _ _ => ∅
  | .square _ l _ _ => {l}

noncomputable def links [DecidableEq L] (U : Finset (BlockName r T L Label)) : Finset L :=
  U.biUnion blockLinks

theorem links_card [DecidableEq L] (U : Finset (BlockName r T L Label)) :
    (links U).card ≤ U.card := by
  calc
    _ ≤ ∑ b ∈ U, (blockLinks b).card := Finset.card_biUnion_le
    _ ≤ ∑ _ ∈ U, 1 := Finset.sum_le_sum (fun b _ => by cases b <;> simp [blockLinks])
    _ = _ := by simp

theorem square_link_mem [DecidableEq L] {U : Finset (BlockName r T L Label)}
    {i : Fin (r + 1)} {l : L} {a b : Label} (h : .square i l a b ∈ U) : l ∈ links U := by
  exact Finset.mem_biUnion.mpr ⟨.square i l a b, h, Finset.mem_singleton_self _⟩

theorem links_mono [DecidableEq L] {U W : Finset (BlockName r T L Label)} (h : U ⊆ W) :
    links U ⊆ links W := by
  intro l hl
  obtain ⟨b, hb, hlb⟩ := Finset.mem_biUnion.mp hl
  exact Finset.mem_biUnion.mpr ⟨b, h hb, hlb⟩

theorem drawing_aligned (left right : L → T)
    (matchLabel : L → Fin (r + 1) → Equiv.Perm Label)
    (frame : T → Fin (r + 1) → Equiv.Perm Label)
    (U : Finset (BlockName r T L Label))
    (hframe : ∀ i l a b, .square i l a b ∈ U → ∀ j p,
      frame (left l) j p = frame (right l) j (matchLabel l j p)) :
    let D := drawing left right matchLabel
    let label := fun c : Corner r T Label => frame c.type c.boundary c.label
    ∀ b ∈ U, label (D.low b false) = label (D.low b true) ∧
      label (D.high b false) = label (D.high b true) := by
  intro D label b hb
  cases b with
  | site i t a b => exact ⟨rfl, rfl⟩
  | square i l a b => exact ⟨hframe i l a b hb i a, hframe i l a b hb _ b⟩

end BlockName

namespace BlockDrawing
variable {r : ℕ} {B : Type uB} {V : Type uV} {T : Type uT} (D : BlockDrawing r B V)

theorem graph_mono {U W : Finset B} (h : U ⊆ W) : D.graph U ≤ D.graph W := by
  rintro x y ⟨hne, b, hb, he⟩
  exact ⟨hne, b, h hb, he⟩

theorem map_reachable (U : Finset B) (H : SimpleGraph T) (f : V → T)
    (hhor : ∀ b ∈ U, ∀ s, f (D.low b s) = f (D.high b s))
    (hlow : ∀ b ∈ U, H.Reachable (f (D.low b false)) (f (D.low b true)))
    (hhigh : ∀ b ∈ U, H.Reachable (f (D.high b false)) (f (D.high b true)))
    {x y : V} (h : (D.graph U).Reachable x y) : H.Reachable (f x) (f y) := by
  have hedge : ∀ b ∈ U, ∀ x y, D.Edge b x y → H.Reachable (f x) (f y) := by
    intro b hb x y he
    rcases he with ⟨s, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hhor b hb s]
    · exact hlow b hb
    · exact hhigh b hb
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c hab w ih =>
    obtain ⟨_, d, hd, he | he⟩ := hab
    · exact (hedge d hd a b he).trans ih
    · exact (hedge d hd b a he).symm.trans ih

end BlockDrawing
end WLTime.Compression

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Extension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uP uE

namespace WLTime.Compression
namespace ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} (I : ConsistencyData (r+1) m P E)

abbrev RawBlock (K : ℕ) := BlockName r (TypeNode K P E) (TypeLink K E) (Fin m)
abbrev RawCorner (K : ℕ) := Corner r (TypeNode K P E) (Fin m)

noncomputable def drawing (K : ℕ) : BlockDrawing r (RawBlock (r := r) (m := m) (P := P) (E := E) K)
    (RawCorner (r := r) (m := m) (P := P) (E := E) K) :=
  BlockName.drawing (linkLeft K I.src) (linkRight K I.dst)
    (fun l i => linkMatch K (fun e => I.coordinatePerm e i) l)

def LabelAllowed (K : ℕ) : TypeNode K P E → Fin (r+1) → Fin m → Prop
  | .inl _, _, _ => True
  | .inr (e, _), i, a => a ∈ I.domain e i

def ValidBlock (K : ℕ) : RawBlock (r := r) (m := m) (P := P) (E := E) K → Prop
  | .site i t a b => I.LabelAllowed K t i a ∧ I.LabelAllowed K t (finRotate (r+1) i) b
  | .square i l a b => a ∈ I.domain l.1 i ∧ b ∈ I.domain l.1 (finRotate (r+1) i)

theorem linkLeft_allowed (K : ℕ) (l : TypeLink K E) (i : Fin (r+1)) (a : Fin m)
    (ha : a ∈ I.domain l.1 i) : I.LabelAllowed K (linkLeft K I.src l) i a := by
  dsimp only [linkLeft]
  split_ifs <;> simp_all only [LabelAllowed]

theorem linkRight_allowed (K : ℕ) (l : TypeLink K E) (i : Fin (r+1)) (a : Fin m)
    (ha : a ∈ I.domain l.1 i) :
    I.LabelAllowed K (linkRight K I.dst l) i (linkMatch K (fun e => I.coordinatePerm e i) l a) := by
  dsimp only [linkRight]
  split_ifs with h
  · trivial
  · simpa only [LabelAllowed, linkMatch, ite_eq_right h, Equiv.refl_apply] using ha

theorem low_allowed (K : ℕ) (b : RawBlock (r := r) (m := m) (P := P) (E := E) K)
    (hb : I.ValidBlock K b) (s : Bool) :
    I.LabelAllowed K ((I.drawing K).low b s).type ((I.drawing K).low b s).boundary
      ((I.drawing K).low b s).label := by
  cases b with
  | site i t a b => exact hb.1
  | square i l a b =>
    cases s
    · exact I.linkLeft_allowed K l i a hb.1
    · exact I.linkRight_allowed K l i a hb.1

noncomputable def alignedLabel [DecidableEq E] (K : ℕ)
    (U : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K))
    (c : RawCorner (r := r) (m := m) (P := P) (E := E) K) : Fin m :=
  supportFrame K I.src I.dst (fun e => I.coordinatePerm e c.boundary)
    (BlockName.links U) c.type c.label

theorem alignedLabel_sides [DecidableEq E] (K : ℕ) (hK : 0 < K)
    (U : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K)) (hU : U.card ≤ K) :
    ∀ b ∈ U, I.alignedLabel K U ((I.drawing K).low b false) =
        I.alignedLabel K U ((I.drawing K).low b true) ∧
      I.alignedLabel K U ((I.drawing K).high b false) =
        I.alignedLabel K U ((I.drawing K).high b true) := by
  exact BlockName.drawing_aligned (linkLeft K I.src) (linkRight K I.dst)
    (fun l i => linkMatch K (fun e => I.coordinatePerm e i) l)
    (fun t i => supportFrame K I.src I.dst (fun e => I.coordinatePerm e i) (BlockName.links U) t) U
    (fun _ l _ _ hb _ p => supportFrame_match K I.src I.dst hK _ _
      ((BlockName.links_card U).trans hU) l (BlockName.square_link_mem hb) p)

theorem corner_type_reachable [DecidableEq E] (K : ℕ)
    (U : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K))
    {x y : RawCorner (r := r) (m := m) (P := P) (E := E) K}
    (h : ((I.drawing K).graph U).Reachable x y) :
    (typeSupportGraph K I.src I.dst (BlockName.links U)).Reachable x.type y.type := by
  apply (I.drawing K).map_reachable U _ Corner.type _ _ _ h
  · intro b _ s; cases b <;> cases s <;> rfl
  · intro b hb
    cases b with
    | site => exact SimpleGraph.Reachable.refl _
    | square => exact support_link_reachable K I.src I.dst _ (BlockName.square_link_mem hb)
  · intro b hb
    cases b with
    | site => exact SimpleGraph.Reachable.refl _
    | square => exact support_link_reachable K I.src I.dst _ (BlockName.square_link_mem hb)

structure WrapData [DecidableEq E] (K : ℕ)
    (U : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K)) where
  blocks : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K)
  subset : blocks ⊆ U
  card : blocks.card = r+1
  wraps : (I.drawing K).Wraps blocks
  address : I.Address
  reads : ∀ b ∈ blocks, ∀ s,
    I.alignedLabel K U ((I.drawing K).low b s) = address ((I.drawing K).row b) ∧
    I.alignedLabel K U ((I.drawing K).high b s) = address (finRotate (r+1) ((I.drawing K).row b))
  anchor : RawBlock (r := r) (m := m) (P := P) (E := E) K
  anchor_mem : anchor ∈ blocks

theorem wrapData_exists [DecidableEq E] (K : ℕ) (hK : 0 < K) (hr : 2 ≤ r)
    (U A : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K))
    (hU : U.card ≤ K) (hA : A ⊆ U) (hc : A.card = r+1) (hw : (I.drawing K).Wraps A) :
    Nonempty (I.WrapData K U) := by
  obtain ⟨a, ha⟩ := (I.drawing K).address_exists hr A (I.alignedLabel K U)
    (fun b hb => I.alignedLabel_sides K hK U hU b (hA hb)) hw hc
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (show 0 < A.card by omega)
  exact ⟨⟨A, hA, hc, hw, a, ha, b, hb⟩⟩

namespace WrapData
variable [DecidableEq E] {I} {K : ℕ}
    {U : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K)}

noncomputable abbrev rootType (d : I.WrapData K U) : TypeNode K P E := ((I.drawing K).low d.anchor false).type

theorem address_unique [DecidableEq P] (hr : 2 ≤ r) (hU : U.card ≤ r+2)
    (d f : I.WrapData K U) : d.address = f.address :=
  (I.drawing K).addresses_agree hr U d.blocks f.blocks d.subset f.subset hU
    d.wraps d.card f.card (I.alignedLabel K U) d.address f.address d.reads f.reads

theorem type_reachable (hr : 2 ≤ r) (d : I.WrapData K U)
    (b : RawBlock (r := r) (m := m) (P := P) (E := E) K) (hb : b ∈ d.blocks) (s : Bool) :
    (typeSupportGraph K I.src I.dst (BlockName.links U)).Reachable d.rootType
      ((I.drawing K).low b s).type := by
  apply I.corner_type_reachable K U
  apply SimpleGraph.Reachable.mono ((I.drawing K).graph_mono d.subset)
  exact ((I.drawing K).wraps_connected hr d.blocks d.wraps d.card d.anchor d.anchor_mem b hb).trans
    ((I.drawing K).low_reachable d.blocks hb s)

theorem rootfree_allowed (hr : 2 ≤ r) (d : I.WrapData K U)
    (hvalid : ∀ b ∈ U, I.ValidBlock K b) (e : E) (j : Fin (4*K))
    (he : d.rootType = .inr (e,j))
    (hreal : ¬HasReal K I.src I.dst (BlockName.links U) d.rootType) :
    I.Allowed e d.address := by
  intro i
  obtain ⟨b, ⟨hb, hrow⟩, _⟩ := (I.drawing K).wraps_unique_row hr d.blocks d.wraps d.card i
  have hrch := d.type_reachable hr b hb false
  have hreal' : ¬HasReal K I.src I.dst (BlockName.links U) ((I.drawing K).low b false).type :=
    mt (hasReal_of_reachable K I.src I.dst _ hrch).mpr hreal
  have hw : nodeWire K d.rootType = nodeWire K ((I.drawing K).low b false).type := by
    obtain ⟨w⟩ := hrch
    exact support_walk_wire K I.src I.dst _ w (fun p h => hreal ⟨p, h.symm⟩)
  have hallowed := I.low_allowed K b (hvalid b (d.subset hb)) false
  have hlabel := (d.reads b hb false).1
  simp only [alignedLabel, supportFrame, ite_eq_right hreal', Equiv.refl_apply] at hlabel
  have hboundary := (I.drawing K).low_boundary b false
  rw [hrow] at hboundary
  change ((I.drawing K).low b false).boundary = i at hboundary
  rw [hrow] at hlabel
  rw [he] at hw
  cases ht : ((I.drawing K).low b false).type with
  | inl p =>
    simp only [ht, nodeWire] at hw
    contradiction
  | inr ej =>
    rcases ej with ⟨e',j'⟩
    simp only [ht, nodeWire, Option.some.injEq] at hw
    subst e'
    simpa only [ht, LabelAllowed, hlabel, hboundary] using hallowed

omit [DecidableEq E] in

theorem type_low_high (b : RawBlock (r := r) (m := m) (P := P) (E := E) K) (s : Bool) :
    ((I.drawing K).low b s).type = ((I.drawing K).high b s).type := by
  cases b <;> cases s <;> rfl

theorem type_reachable_blocks (hr : 2 ≤ r) (d : I.WrapData K U)
    (b : RawBlock (r := r) (m := m) (P := P) (E := E) K) (hb : b ∈ d.blocks) (s : Bool) :
    (typeSupportGraph K I.src I.dst (BlockName.links d.blocks)).Reachable d.rootType
      ((I.drawing K).low b s).type := by
  apply I.corner_type_reachable K d.blocks
  exact ((I.drawing K).wraps_connected hr d.blocks d.wraps d.card d.anchor d.anchor_mem b hb).trans
    ((I.drawing K).low_reachable d.blocks hb s)

noncomputable def changedAddress (d : I.WrapData K U)
    (W : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K)) : I.Address :=
  fun i => frameTransition
    (supportFrame K I.src I.dst (fun e => I.coordinatePerm e i) (BlockName.links U))
    (supportFrame K I.src I.dst (fun e => I.coordinatePerm e i) (BlockName.links W))
    d.rootType (d.address i)

theorem changedAddress_reads (hK : 0 < K) (hr : 2 ≤ r) (d : I.WrapData K U)
    (W : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K))
    (hU : U.card ≤ K) (hW : W.card ≤ K) (hdW : d.blocks ⊆ W)
    (b : RawBlock (r := r) (m := m) (P := P) (E := E) K) (hb : b ∈ d.blocks) (s : Bool) :
    I.alignedLabel K W ((I.drawing K).low b s) = d.changedAddress W ((I.drawing K).row b) ∧
    I.alignedLabel K W ((I.drawing K).high b s) =
      d.changedAddress W (finRotate (r+1) ((I.drawing K).row b)) := by
  have aux (c : RawCorner (r := r) (m := m) (P := P) (E := E) K)
      (hc : (typeSupportGraph K I.src I.dst (BlockName.links d.blocks)).Reachable d.rootType c.type) :
      I.alignedLabel K W c = frameTransition
        (supportFrame K I.src I.dst (fun e => I.coordinatePerm e c.boundary) (BlockName.links U))
        (supportFrame K I.src I.dst (fun e => I.coordinatePerm e c.boundary) (BlockName.links W))
        d.rootType (I.alignedLabel K U c) := by
    obtain ⟨w⟩ := hc
    have heq := frameTransition_walk K I.src I.dst (fun e => I.coordinatePerm e c.boundary)
      (BlockName.links d.blocks)
      (supportFrame K I.src I.dst (fun e => I.coordinatePerm e c.boundary) (BlockName.links U))
      (supportFrame K I.src I.dst (fun e => I.coordinatePerm e c.boundary) (BlockName.links W))
      (fun l hl a => supportFrame_match K I.src I.dst hK _ _ ((BlockName.links_card U).trans hU)
        l (BlockName.links_mono d.subset hl) a)
      (fun l hl a => supportFrame_match K I.src I.dst hK _ _ ((BlockName.links_card W).trans hW)
        l (BlockName.links_mono hdW hl) a) w
    rw [heq]
    simp only [frameTransition, Equiv.trans_apply, alignedLabel, Equiv.symm_apply_apply]
  have hlo := aux ((I.drawing K).low b s) (d.type_reachable_blocks hr b hb s)
  have hhi := aux ((I.drawing K).high b s)
    ((type_low_high (I := I) b s) ▸ d.type_reachable_blocks hr b hb s)
  have hbl : ((I.drawing K).low b s).boundary = ((I.drawing K).row b) :=
    (I.drawing K).low_boundary b s
  have hbh : ((I.drawing K).high b s).boundary = finRotate (r+1) ((I.drawing K).row b) :=
    (I.drawing K).high_boundary b s
  rw [(d.reads b hb s).1, hbl] at hlo
  rw [(d.reads b hb s).2, hbh] at hhi
  exact ⟨hlo, hhi⟩

noncomputable def reframe (hK : 0 < K) (hr : 2 ≤ r) (d : I.WrapData K U)
    (W : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K))
    (hU : U.card ≤ K) (hW : W.card ≤ K) (hdW : d.blocks ⊆ W) : I.WrapData K W where
  blocks := d.blocks
  subset := hdW
  card := d.card
  wraps := d.wraps
  address := d.changedAddress W
  reads := d.changedAddress_reads hK hr W hU hW hdW
  anchor := d.anchor
  anchor_mem := d.anchor_mem

end WrapData
end ConsistencyData
end WLTime.Compression

namespace WLTime.Compression
namespace ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} (I : ConsistencyData (r+1) m P E)

structure ShiftChoice where
  real : (p : P) → I.RealValue p
  scalar : E → F₂

namespace ShiftChoice
variable {I}
noncomputable def values (q : I.ShiftChoice) (K : ℕ) (S : Finset (TypeLink K E)) :=
  I.canonicalShift K S q.real q.scalar

def AtAddress (q : I.ShiftChoice) (Q : I.ArcWitness) (a : I.Address) : Prop :=
  (∀ p, q.real p ∈ Q.sets p a) ∧ (∀ e, q.scalar e ∈ Q.internalSet e a)

noncomputable def atAddress (Q : I.ArcWitness) (a : I.Address) : I.ShiftChoice where
  real := fun p => (Q.nonempty p a).choose
  scalar := fun e => (Q.internal_nonempty e a).choose

theorem atAddress_mem (Q : I.ArcWitness) (a : I.Address) :
    (atAddress Q a).AtAddress Q a :=
  ⟨fun p => (Q.nonempty p a).choose_spec, fun e => (Q.internal_nonempty e a).choose_spec⟩

noncomputable def withReal [DecidableEq P] (q : I.ShiftChoice) (p : P) (h : I.RealValue p) :
    I.ShiftChoice := ⟨Function.update q.real p h, q.scalar⟩

noncomputable def withScalar [DecidableEq E] (q : I.ShiftChoice) (e : E) (s : F₂) :
    I.ShiftChoice := ⟨q.real, Function.update q.scalar e s⟩

theorem withReal_mem [DecidableEq P] (q : I.ShiftChoice) (Q : I.ArcWitness) (a : I.Address)
    (hq : q.AtAddress Q a) (p : P) (h : I.RealValue p) (hh : h ∈ Q.sets p a) :
    (q.withReal p h).AtAddress Q a := by
  constructor
  · intro t
    by_cases ht : t = p
    · subst t; simpa only [withReal, Function.update_self] using hh
    · simpa only [withReal, Function.update_of_ne ht] using hq.1 t
  · exact hq.2

theorem withScalar_mem [DecidableEq E] (q : I.ShiftChoice) (Q : I.ArcWitness) (a : I.Address)
    (hq : q.AtAddress Q a) (e : E) (s : F₂) (hs : s ∈ Q.internalSet e a) :
    (q.withScalar e s).AtAddress Q a := by
  constructor
  · exact hq.1
  · intro t
    by_cases ht : t = e
    · subst t; simpa only [withScalar, Function.update_self] using hs
    · simpa only [withScalar, Function.update_of_ne ht] using hq.2 t

def Admissible [DecidableEq E] (q : I.ShiftChoice) (Q : I.ArcWitness) (K : ℕ)
    (U : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K)) : Prop :=
  ∀ d : I.WrapData K U, q.AtAddress Q d.address

theorem admissible_of_one [DecidableEq P] [DecidableEq E]
    (q : I.ShiftChoice) (Q : I.ArcWitness) (K : ℕ) (hr : 2 ≤ r)
    (U : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K)) (hU : U.card ≤ r+2)
    (d : I.WrapData K U) (hq : q.AtAddress Q d.address) : q.Admissible Q K U := by
  intro f
  rw [← d.address_unique hr hU f]
  exact hq

theorem admissible_exists [DecidableEq P] [DecidableEq E] (Q : I.ArcWitness)
    (K : ℕ) (hr : 2 ≤ r)
    (U : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K)) (hU : U.card ≤ r+2) :
    ∃ q : I.ShiftChoice, q.Admissible Q K U := by
  classical
  by_cases h : Nonempty (I.WrapData K U)
  · obtain ⟨d⟩ := h
    exact ⟨atAddress Q d.address, admissible_of_one _ Q K hr U hU d (atAddress_mem Q _)⟩
  · exact ⟨⟨fun _ => 0, fun _ => 0⟩, fun d => False.elim (h ⟨d⟩)⟩

end ShiftChoice

namespace WrapData
variable [DecidableEq E] {I} {K : ℕ}
    {U W : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K)}

theorem changedAddress_both_real (d : I.WrapData K U)
    (h : HasReal K I.src I.dst (BlockName.links U) d.rootType)
    (h' : HasReal K I.src I.dst (BlockName.links W) d.rootType) :
    d.changedAddress W = d.address := by
  funext i
  simp only [changedAddress, frameTransition, supportFrame, ite_eq_left h, ite_eq_left h',
    Equiv.trans_apply, Equiv.apply_symm_apply]

theorem changedAddress_neither_real (d : I.WrapData K U)
    (h : ¬HasReal K I.src I.dst (BlockName.links U) d.rootType)
    (h' : ¬HasReal K I.src I.dst (BlockName.links W) d.rootType) :
    d.changedAddress W = d.address := by
  funext i
  simp only [changedAddress, frameTransition, supportFrame, ite_eq_right h, ite_eq_right h',
    Equiv.trans_apply, Equiv.apply_symm_apply]

theorem changedAddress_new_real (d : I.WrapData K U)
    (h : ¬HasReal K I.src I.dst (BlockName.links U) d.rootType)
    (h' : HasReal K I.src I.dst (BlockName.links W) d.rootType)
    (e : E) (j : Fin (4*K)) (he : d.rootType = .inr (e,j)) :
    d.changedAddress W = if j.val < 2*K then d.address else I.permuteAddress e d.address := by
  funext i
  simp only [changedAddress, frameTransition, supportFrame, ite_eq_right h, ite_eq_left h',
    Equiv.trans_apply, Equiv.refl_symm, Equiv.refl_apply, he, typeFrame]
  split_ifs <;> rfl

end WrapData

theorem shifts_eq_on_rootfree_component (K : ℕ) (S : Finset (TypeLink K E))
    (h g : (t : TypeNode K P E) → I.Value K t)
    (hh : I.ShiftSolves K S h) (hg : I.ShiftSolves K S g)
    {x y : TypeNode K P E}
    (hreal : ¬HasReal K I.src I.dst S x)
    (hxy : (typeSupportGraph K I.src I.dst S).Reachable x y) (heq : h x = g x) : h y = g y := by
  have hy : ¬HasReal K I.src I.dst S y := mt (hasReal_of_reachable K I.src I.dst S hxy).mpr hreal
  obtain ⟨w⟩ := hxy
  have hxscalar : I.scalarOf K h x = I.scalarOf K g x := by
    cases x with
    | inl p => exact (hreal (hasReal_inl K I.src I.dst S p)).elim
    | inr ej => exact heq
  have hyscalar := (I.scalar_eq_on_rootfree_walk K S h hh w hreal).symm.trans
    (hxscalar.trans (I.scalar_eq_on_rootfree_walk K S g hg w hreal))
  cases y with
  | inl p => exact (hy (hasReal_inl K I.src I.dst S p)).elim
  | inr ej => exact hyscalar

namespace ShiftChoice
variable {I}

open scoped Classical in
theorem values_internal (q : I.ShiftChoice) (K : ℕ) (S : Finset (TypeLink K E))
    (e : E) (j : Fin (4*K)) :
    q.values K S (.inr (e,j)) =
      if HasReal K I.src I.dst S (.inr (e,j)) then
        (if j.val < 2*K then I.affineSrc e (q.real (I.src e)) else I.affineDst e (q.real (I.dst e)))
      else q.scalar e := by
  classical
  rfl

theorem values_solves [DecidableEq E] (q : I.ShiftChoice) (K : ℕ) (hK : 0 < K)
    (S : Finset (TypeLink K E)) (hS : S.card ≤ K) : I.ShiftSolves K S (q.values K S) :=
  I.canonicalShift_solves K hK S hS q.real q.scalar

theorem newly_rooted_preimage [DecidableEq E] [DecidableEq P]
    (Q : I.ArcWitness) (K : ℕ) (hr : 2 ≤ r)
    {V U : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K)}
    (d : I.WrapData K V) (hvalid : ∀ b ∈ V, I.ValidBlock K b)
    (hV : ¬HasReal K I.src I.dst (BlockName.links V) d.rootType)
    (hU : HasReal K I.src I.dst (BlockName.links U) d.rootType)
    (e : E) (j : Fin (4*K)) (he : d.rootType = .inr (e,j))
    (s : F₂) (hs : s ∈ Q.internalSet e d.address) :
    ∃ q : I.ShiftChoice, q.AtAddress Q (d.changedAddress U) ∧
      q.values K (BlockName.links U) (.inr (e,j)) = s := by
  classical
  have ha := d.changedAddress_new_real hV hU e j he
  have hU' : HasReal K I.src I.dst (BlockName.links U) (.inr (e,j)) := he ▸ hU
  by_cases hj : j.val < 2*K
  · rw [ite_eq_left hj] at ha
    obtain ⟨x, hx, hxs⟩ := Q.src_preimage e d.address hs
    let q := (atAddress Q (d.changedAddress U)).withReal (I.src e) x
    refine ⟨q, withReal_mem _ _ _ (atAddress_mem _ _) _ _ ?_, ?_⟩
    · rwa [ha]
    · rw [q.values_internal, ite_eq_left hU', ite_eq_left hj]
      simpa only [q, withReal, Function.update_self] using hxs
  · rw [ite_eq_right hj] at ha
    obtain ⟨x, hx, hxs⟩ := Q.dst_preimage e d.address (d.rootfree_allowed hr hvalid e j he hV) hs
    let q := (atAddress Q (d.changedAddress U)).withReal (I.dst e) x
    refine ⟨q, withReal_mem _ _ _ (atAddress_mem _ _) _ _ ?_, ?_⟩
    · rwa [ha]
    · rw [q.values_internal, ite_eq_left hU', ite_eq_right hj]
      simpa only [q, withReal, Function.update_self] using hxs

theorem newly_rooted_image [DecidableEq E]
    (Q : I.ArcWitness) (K : ℕ) (hr : 2 ≤ r)
    {V U : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K)}
    (d : I.WrapData K V) (hvalid : ∀ b ∈ V, I.ValidBlock K b)
    (hV : ¬HasReal K I.src I.dst (BlockName.links V) d.rootType)
    (hU : HasReal K I.src I.dst (BlockName.links U) d.rootType)
    (e : E) (j : Fin (4*K)) (he : d.rootType = .inr (e,j))
    (q : I.ShiftChoice) (hq : q.AtAddress Q (d.changedAddress U)) :
    q.values K (BlockName.links U) (.inr (e,j)) ∈ Q.internalSet e d.address := by
  have ha := d.changedAddress_new_real hV hU e j he
  have hU' : HasReal K I.src I.dst (BlockName.links U) (.inr (e,j)) := he ▸ hU
  rw [q.values_internal, ite_eq_left hU']
  by_cases hj : j.val < 2*K
  · rw [ite_eq_left hj] at ha ⊢
    apply Q.src_mem_internal e d.address
    rw [← ha]
    exact hq.1 _
  · rw [ite_eq_right hj] at ha ⊢
    apply Q.dst_mem_internal e d.address (d.rootfree_allowed hr hvalid e j he hV)
    rw [← ha]
    exact hq.1 _

theorem extend_on_wrapping [DecidableEq E] [DecidableEq P]
    (Q : I.ArcWitness) (K : ℕ) (hK : 0 < K) (hr : 2 ≤ r)
    {V U : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K)}
    (hVU : V ⊆ U) (hUK : U.card ≤ K) (hUr : U.card ≤ r+2)
    (d : I.WrapData K V) (hvalid : ∀ b ∈ V, I.ValidBlock K b)
    (q : I.ShiftChoice) (hq : q.Admissible Q K V) :
    ∃ q' : I.ShiftChoice, q'.Admissible Q K U ∧
      ∀ t, (typeSupportGraph K I.src I.dst (BlockName.links V)).Reachable d.rootType t →
        q'.values K (BlockName.links U) t = q.values K (BlockName.links V) t := by
  classical
  have hVK : V.card ≤ K := (Finset.card_le_card hVU).trans hUK
  let f := d.reframe hK hr U hVK hUK (d.subset.trans hVU)
  have hqAt := hq d
  have hsub := BlockName.links_mono hVU
  by_cases hVr : HasReal K I.src I.dst (BlockName.links V) d.rootType
  · have hUrt := hasReal_mono K I.src I.dst hsub hVr
    have ha := d.changedAddress_both_real hVr hUrt
    refine ⟨q, admissible_of_one q Q K hr U hUr f ?_, ?_⟩
    · change q.AtAddress Q (d.changedAddress U)
      rwa [ha]
    · intro t ht
      have htV := (hasReal_of_reachable K I.src I.dst _ ht).mp hVr
      have htU := hasReal_mono K I.src I.dst hsub htV
      simp only [values, canonicalShift, ite_eq_left htV, ite_eq_left htU]
  · by_cases hUr' : HasReal K I.src I.dst (BlockName.links U) d.rootType
    · obtain ⟨e,j,he⟩ : ∃ e j, d.rootType = Sum.inr (e,j) := by
        cases he : d.rootType with
        | inl p => exact (hVr (he.symm ▸ hasReal_inl K I.src I.dst _ p)).elim
        | inr ej => exact ⟨ej.1, ej.2, rfl⟩
      obtain ⟨q', hq', heq⟩ := newly_rooted_preimage Q K hr d hvalid hVr hUr'
        e j he (q.scalar e) (hqAt.2 e)
      refine ⟨q', admissible_of_one q' Q K hr U hUr f hq', ?_⟩
      intro t ht
      apply I.shifts_eq_on_rootfree_component K (BlockName.links V)
        (q'.values K (BlockName.links U)) (q.values K (BlockName.links V))
        (fun l hl => q'.values_solves K hK _ ((BlockName.links_card U).trans hUK) l (hsub hl))
        (q.values_solves K hK _ ((BlockName.links_card V).trans hVK)) hVr ht
      have hVr' : ¬HasReal K I.src I.dst (BlockName.links V) (.inr (e,j)) := he ▸ hVr
      rw [he, q.values_internal, ite_eq_right hVr']
      exact heq
    · have ha := d.changedAddress_neither_real hVr hUr'
      refine ⟨q, admissible_of_one q Q K hr U hUr f ?_, ?_⟩
      · change q.AtAddress Q (d.changedAddress U)
        rwa [ha]
      · intro t ht
        have htV : ¬HasReal K I.src I.dst (BlockName.links V) t :=
          mt (hasReal_of_reachable K I.src I.dst _ ht).mpr hVr
        have htU : ¬HasReal K I.src I.dst (BlockName.links U) t :=
          mt (hasReal_of_reachable K I.src I.dst _ (ht.mono (support_graph_mono K I.src I.dst hsub))).mpr hUr'
        simp only [values, canonicalShift, ite_eq_right htV, ite_eq_right htU]

theorem restrict_on_wrapping [DecidableEq E] [DecidableEq P]
    (Q : I.ArcWitness) (K : ℕ) (hK : 0 < K) (hr : 2 ≤ r)
    {V U : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K)}
    (hVU : V ⊆ U) (hUK : U.card ≤ K) (hVr : V.card ≤ r+2)
    (d : I.WrapData K V) (hvalid : ∀ b ∈ V, I.ValidBlock K b)
    (q : I.ShiftChoice) (hq : q.Admissible Q K U) :
    ∃ q' : I.ShiftChoice, q'.Admissible Q K V ∧
      ∀ t, (typeSupportGraph K I.src I.dst (BlockName.links V)).Reachable d.rootType t →
        q'.values K (BlockName.links V) t = q.values K (BlockName.links U) t := by
  classical
  have hVK : V.card ≤ K := (Finset.card_le_card hVU).trans hUK
  let f := d.reframe hK hr U hVK hUK (d.subset.trans hVU)
  have hqAt : q.AtAddress Q (d.changedAddress U) := hq f
  have hsub := BlockName.links_mono hVU
  by_cases hVreal : HasReal K I.src I.dst (BlockName.links V) d.rootType
  · have hUrt := hasReal_mono K I.src I.dst hsub hVreal
    have ha := d.changedAddress_both_real hVreal hUrt
    refine ⟨q, admissible_of_one q Q K hr V hVr d ?_, ?_⟩
    · rwa [ha] at hqAt
    · intro t ht
      have htV := (hasReal_of_reachable K I.src I.dst _ ht).mp hVreal
      have htU := hasReal_mono K I.src I.dst hsub htV
      simp only [values, canonicalShift, ite_eq_left htV, ite_eq_left htU]
  · by_cases hUr' : HasReal K I.src I.dst (BlockName.links U) d.rootType
    · obtain ⟨e,j,he⟩ : ∃ e j, d.rootType = Sum.inr (e,j) := by
        cases he : d.rootType with
        | inl p => exact (hVreal (he.symm ▸ hasReal_inl K I.src I.dst _ p)).elim
        | inr ej => exact ⟨ej.1, ej.2, rfl⟩
      let s := q.values K (BlockName.links U) (.inr (e,j))
      have hs : s ∈ Q.internalSet e d.address := newly_rooted_image Q K hr d hvalid hVreal hUr' e j he q hqAt
      let q' := (atAddress Q d.address).withScalar e s
      have hq' := withScalar_mem _ Q d.address (atAddress_mem Q _) e s hs
      refine ⟨q', admissible_of_one q' Q K hr V hVr d hq', ?_⟩
      intro t ht
      apply I.shifts_eq_on_rootfree_component K (BlockName.links V)
        (q'.values K (BlockName.links V)) (q.values K (BlockName.links U))
        (q'.values_solves K hK _ ((BlockName.links_card V).trans hVK))
        (fun l hl => q.values_solves K hK _ ((BlockName.links_card U).trans hUK) l (hsub hl)) hVreal ht
      have hVr' : ¬HasReal K I.src I.dst (BlockName.links V) (.inr (e,j)) := he ▸ hVreal
      rw [he, q'.values_internal, ite_eq_right hVr']
      exact Function.update_self e s (atAddress Q d.address).scalar
    · have ha := d.changedAddress_neither_real hVreal hUr'
      refine ⟨q, admissible_of_one q Q K hr V hVr d ?_, ?_⟩
      · rwa [ha] at hqAt
      · intro t ht
        have htV : ¬HasReal K I.src I.dst (BlockName.links V) t :=
          mt (hasReal_of_reachable K I.src I.dst _ ht).mpr hVreal
        have htU : ¬HasReal K I.src I.dst (BlockName.links U) t :=
          mt (hasReal_of_reachable K I.src I.dst _ (ht.mono (support_graph_mono K I.src I.dst hsub))).mpr hUr'
        simp only [values, canonicalShift, ite_eq_right htV, ite_eq_right htU]

end ShiftChoice
end ConsistencyData
end WLTime.Compression

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Readouts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uB uV uT uL uLabel uP uE

namespace WLTime.Compression

namespace BlockDrawing
variable {r : ℕ} {B : Type uB} {V : Type uV} (D : BlockDrawing r B V)

theorem seam_potential_exists (hr : 2 ≤ r) (U : Finset B) (hw : ¬D.Wraps U) :
    ∃ s : V → F₂, ∀ b ∈ U, ∀ x y, D.Edge b x y →
      s x + s y = D.rowMark (Fin.last r) x y := by
  have hclosed : ∀ v (p : (D.graph U).Walk v v),
      walkWeight (D.rowMark (Fin.last r)) p = 0 := by
    intro v p
    by_contra h
    exact hw ⟨v,p,h⟩
  obtain ⟨s, hs⟩ := exists_seam_potential (D.rowMark (Fin.last r))
    (fun x y _ => D.rowMark_symm _ x y) hclosed
  refine ⟨s, ?_⟩
  intro b hb x y hxy
  by_cases he : x = y
  · subst y
    rw [CharTwo.add_self_eq_zero, D.rowMark_zero_of_boundary_eq (by omega) _ rfl]
  · exact hs x y ⟨he,b,hb,Or.inl hxy⟩

end BlockDrawing

inductive ReadoutName (r : ℕ) (T : Type uT) (L : Type uL) (Label : Type uLabel) where
  | horizontal (row : Fin (r+1)) (type : T) (low high : Label)
  | vertical (boundary : Fin (r+1)) (link : L) (label : Label)
  deriving DecidableEq, Fintype

abbrev RawName {r m : ℕ} {P : Type uP} {E : Type uE} (K : ℕ) :=
  ReadoutName r (TypeNode K P E) (TypeLink K E) (Fin m)

namespace ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} (I : ConsistencyData (r+1) m P E)

abbrev ReadValue (K : ℕ) : RawName (r := r) (m := m) (P := P) (E := E) K → Type
  | .horizontal _ t _ _ => I.Value K t
  | .vertical _ _ _ => F₂

abbrev Readouts (K : ℕ) := (n : RawName (r := r) (m := m) (P := P) (E := E) K) → I.ReadValue K n
abbrev Potentials (K : ℕ) := (c : RawCorner (r := r) (m := m) (P := P) (E := E) K) → I.Value K c.type

def seam (i : Fin (r+1)) : F₂ := if i = Fin.last r then 1 else 0

noncomputable def footprint (K : ℕ) : RawBlock (r := r) (m := m) (P := P) (E := E) K →
    Finset (RawName (r := r) (m := m) (P := P) (E := E) K) := by
  classical
  exact fun b => match b with
    | .site i t a b => {.horizontal i t a b}
    | .square i l a b => {
        .horizontal i (linkLeft K I.src l) a b,
        .horizontal i (linkRight K I.dst l)
          (linkMatch K (fun e => I.coordinatePerm e i) l a)
          (linkMatch K (fun e => I.coordinatePerm e (finRotate (r+1) i)) l b),
        .vertical i l a, .vertical (finRotate (r+1) i) l b}

def AgreeOn (K : ℕ) (U : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K))
    (R S : I.Readouts K) : Prop :=
  ∀ b ∈ U, ∀ n ∈ I.footprint K b, R n = S n

namespace AgreeOn
variable {I} {K : ℕ} {U V : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K)}
    {R S T : I.Readouts K}
theorem refl (R : I.Readouts K) : I.AgreeOn K U R R := fun _ _ _ _ => rfl
theorem symm (h : I.AgreeOn K U R S) : I.AgreeOn K U S R := fun b hb n hn => (h b hb n hn).symm
theorem trans (h : I.AgreeOn K U R S) (h' : I.AgreeOn K U S T) : I.AgreeOn K U R T :=
  fun b hb n hn => (h b hb n hn).trans (h' b hb n hn)
theorem mono (h : I.AgreeOn K U R S) (hVU : V ⊆ U) : I.AgreeOn K V R S :=
  fun b hb n hn => h b (hVU hb) n hn
end AgreeOn

noncomputable def fromPotentials (K : ℕ) (M : I.Potentials K)
    (h : (t : TypeNode K P E) → I.Value K t) : I.Readouts K
  | .horizontal i t a b => horizontalReadout (M ⟨i,t,a⟩) (M ⟨finRotate (r+1) i,t,b⟩) (h t) (seam i)
  | .vertical i l a => verticalReadout (I.leftForm K l) (I.rightForm K l)
      (M ⟨i,linkLeft K I.src l,a⟩)
      (M ⟨i,linkRight K I.dst l,linkMatch K (fun e => I.coordinatePerm e i) l a⟩)

noncomputable def adjustPotentials (K : ℕ) (M : I.Potentials K)
    (s : RawCorner (r := r) (m := m) (P := P) (E := E) K → F₂)
    (old new : (t : TypeNode K P E) → I.Value K t) : I.Potentials K :=
  fun c => M c + s c • (old c.type - new c.type)

theorem adjust_horizontal (K : ℕ) (M : I.Potentials K)
    (s : RawCorner (r := r) (m := m) (P := P) (E := E) K → F₂)
    (old new : (t : TypeNode K P E) → I.Value K t)
    (i : Fin (r+1)) (t : TypeNode K P E) (a b : Fin m)
    (hs : s ⟨i,t,a⟩ + s ⟨finRotate (r+1) i,t,b⟩ = seam i) :
    I.fromPotentials K (I.adjustPotentials K M s old new) new (.horizontal i t a b) =
      I.fromPotentials K M old (.horizontal i t a b) :=
  horizontal_adjustment _ _ _ _ _ _ _ hs

theorem adjust_vertical (K : ℕ) (M : I.Potentials K)
    (s : RawCorner (r := r) (m := m) (P := P) (E := E) K → F₂)
    (old new : (t : TypeNode K P E) → I.Value K t)
    (i : Fin (r+1)) (l : TypeLink K E) (a : Fin m)
    (hs : s ⟨i,linkLeft K I.src l,a⟩ =
      s ⟨i,linkRight K I.dst l,linkMatch K (fun e => I.coordinatePerm e i) l a⟩)
    (ho : I.leftForm K l (old (linkLeft K I.src l)) + I.rightForm K l (old (linkRight K I.dst l)) = I.linkBias K l)
    (hn : I.leftForm K l (new (linkLeft K I.src l)) + I.rightForm K l (new (linkRight K I.dst l)) = I.linkBias K l) :
    I.fromPotentials K (I.adjustPotentials K M s old new) new (.vertical i l a) =
      I.fromPotentials K M old (.vertical i l a) := by
  dsimp only [fromPotentials, adjustPotentials]
  rw [hs]
  apply vertical_adjustment
  exact homogeneous_shift_difference _ _ _ _ _ _ _ ho hn

theorem adjust_nonwrapping [DecidableEq E] (K : ℕ) (hr : 2 ≤ r)
    (V : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K))
    (hw : ¬(I.drawing K).Wraps V) (M : I.Potentials K)
    (old new : (t : TypeNode K P E) → I.Value K t)
    (ho : I.ShiftSolves K (BlockName.links V) old) (hn : I.ShiftSolves K (BlockName.links V) new) :
    ∃ M' : I.Potentials K, I.AgreeOn K V (I.fromPotentials K M' new) (I.fromPotentials K M old) := by
  classical
  obtain ⟨s, hs⟩ := (I.drawing K).seam_potential_exists hr V hw
  have hhor (b : RawBlock (r := r) (m := m) (P := P) (E := E) K) (hb : b ∈ V) (side : Bool) :
      s ((I.drawing K).low b side) + s ((I.drawing K).high b side) = seam ((I.drawing K).row b) := by
    rw [hs b hb _ _ (Or.inl ⟨side,rfl,rfl⟩), (I.drawing K).rowMark_horizontal hr]
    simp only [seam, eq_comm (a := Fin.last r)]
  have hver (b : RawBlock (r := r) (m := m) (P := P) (E := E) K) (hb : b ∈ V) :
      s ((I.drawing K).low b false) = s ((I.drawing K).low b true) ∧
      s ((I.drawing K).high b false) = s ((I.drawing K).high b true) := by
    constructor
    · apply CharTwo.add_eq_zero.mp
      rw [hs b hb _ _ (Or.inr (Or.inl ⟨rfl,rfl⟩))]
      exact (I.drawing K).rowMark_zero_of_boundary_eq (by omega) _
        (((I.drawing K).low_boundary b false).trans ((I.drawing K).low_boundary b true).symm)
    · apply CharTwo.add_eq_zero.mp
      rw [hs b hb _ _ (Or.inr (Or.inr ⟨rfl,rfl⟩))]
      exact (I.drawing K).rowMark_zero_of_boundary_eq (by omega) _
        (((I.drawing K).high_boundary b false).trans ((I.drawing K).high_boundary b true).symm)
  refine ⟨I.adjustPotentials K M s old new, ?_⟩
  intro b hb n hnmem
  cases b with
  | site i t a b =>
    simp only [footprint, Finset.mem_singleton] at hnmem
    subst n
    exact I.adjust_horizontal K M s old new i t a b (hhor _ hb false)
  | square i l a b =>
    have hl := BlockName.square_link_mem hb
    simp only [footprint, Finset.mem_insert, Finset.mem_singleton] at hnmem
    rcases hnmem with rfl | rfl | rfl | rfl
    · exact I.adjust_horizontal K M s old new i _ _ _ (hhor _ hb false)
    · exact I.adjust_horizontal K M s old new i _ _ _ (hhor _ hb true)
    · exact I.adjust_vertical K M s old new i l a (hver _ hb).1 (ho l hl) (hn l hl)
    · exact I.adjust_vertical K M s old new _ l b (hver _ hb).2 (ho l hl) (hn l hl)

theorem fromPotentials_agree [DecidableEq E] (K : ℕ)
    (V : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K)) (M : I.Potentials K)
    (old new : (t : TypeNode K P E) → I.Value K t)
    (heq : ∀ b ∈ V, ∀ side, old ((I.drawing K).low b side).type = new ((I.drawing K).low b side).type) :
    I.AgreeOn K V (I.fromPotentials K M old) (I.fromPotentials K M new) := by
  classical
  intro b hb n hn
  cases b with
  | site i t a b =>
    simp only [footprint, Finset.mem_singleton] at hn
    subst n
    have ht := heq _ hb false
    change old t = new t at ht
    simp only [fromPotentials, ht]
  | square i l a b =>
    have ht := heq _ hb false
    have hu := heq _ hb true
    change old (linkLeft K I.src l) = new (linkLeft K I.src l) at ht
    change old (linkRight K I.dst l) = new (linkRight K I.dst l) at hu
    simp only [footprint, Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl | rfl
    · simp only [fromPotentials, ht]
    · simp only [fromPotentials, hu]
    · rfl
    · rfl

def OffsetFamily [DecidableEq E] (Q : I.ArcWitness) (K : ℕ)
    (U : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K)) (R : I.Readouts K) : Prop :=
  ∃ q : I.ShiftChoice, ∃ M : I.Potentials K,
    q.Admissible Q K U ∧ I.AgreeOn K U R (I.fromPotentials K M (q.values K (BlockName.links U)))

theorem offset_nonempty [DecidableEq E] [DecidableEq P] (Q : I.ArcWitness)
    (K : ℕ) (hr : 2 ≤ r)
    (U : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K)) (hU : U.card ≤ r+2) :
    ∃ R, I.OffsetFamily Q K U R := by
  obtain ⟨q, hq⟩ := ShiftChoice.admissible_exists Q K hr U hU
  exact ⟨I.fromPotentials K (fun _ => 0) (q.values K (BlockName.links U)), q, fun _ => 0,
    hq, AgreeOn.refl _⟩

theorem offset_extend [DecidableEq E] [DecidableEq P] (Q : I.ArcWitness)
    (K : ℕ) (hK : 0 < K) (hr : 2 ≤ r)
    {V U : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K)}
    (hVU : V ⊆ U) (hUK : U.card ≤ K) (hUr : U.card ≤ r+2)
    (hvalid : ∀ b ∈ U, I.ValidBlock K b)
    (R : I.Readouts K) (hR : I.OffsetFamily Q K V R) :
    ∃ R', I.OffsetFamily Q K U R' ∧ I.AgreeOn K V R R' := by
  classical
  by_cases he : V = U
  · subst V
    exact ⟨R,hR,AgreeOn.refl R⟩
  have hproper : V ⊂ U := Finset.ssubset_iff_subset_ne.mpr ⟨hVU,he⟩
  have hVr : V.card ≤ r+1 := by have := Finset.card_lt_card hproper; omega
  have hVK : V.card ≤ K := (Finset.card_le_card hVU).trans hUK
  obtain ⟨q,M,hq,hRM⟩ := hR
  by_cases hw : (I.drawing K).Wraps V
  · have hcard : V.card = r+1 := Nat.le_antisymm hVr ((I.drawing K).wraps_card hr V hw)
    obtain ⟨d⟩ := I.wrapData_exists K hK hr V V hVK (Finset.Subset.refl _) hcard hw
    have hd : d.blocks = V := Finset.eq_of_subset_of_card_le d.subset (by rw [d.card]; exact hVr)
    obtain ⟨q',hq',hshift⟩ := q.extend_on_wrapping Q K hK hr hVU hUK hUr d
      (fun b hb => hvalid b (hVU hb)) hq
    let R' := I.fromPotentials K M (q'.values K (BlockName.links U))
    refine ⟨R', ⟨q',M,hq',AgreeOn.refl _⟩, hRM.trans ?_⟩
    apply I.fromPotentials_agree K V M
    intro b hb side
    exact (hshift _ (d.type_reachable hr b (hd.symm ▸ hb) side)).symm
  · obtain ⟨q',hq'⟩ := ShiftChoice.admissible_exists Q K hr U hUr
    obtain ⟨M',hM'⟩ := I.adjust_nonwrapping K hr V hw M
      (q.values K (BlockName.links V)) (q'.values K (BlockName.links U))
      (q.values_solves K hK _ ((BlockName.links_card V).trans hVK))
      (fun l hl => q'.values_solves K hK _ ((BlockName.links_card U).trans hUK) l (BlockName.links_mono hVU hl))
    exact ⟨I.fromPotentials K M' (q'.values K (BlockName.links U)),
      ⟨q',M',hq',AgreeOn.refl _⟩, hRM.trans hM'.symm⟩

theorem offset_restrict [DecidableEq E] [DecidableEq P] (Q : I.ArcWitness)
    (K : ℕ) (hK : 0 < K) (hr : 2 ≤ r)
    {V U : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K)}
    (hVU : V ⊆ U) (hUK : U.card ≤ K) (hUr : U.card ≤ r+2)
    (hvalid : ∀ b ∈ U, I.ValidBlock K b)
    (R : I.Readouts K) (hR : I.OffsetFamily Q K U R) : I.OffsetFamily Q K V R := by
  classical
  by_cases he : V = U
  · subst V; exact hR
  have hproper : V ⊂ U := Finset.ssubset_iff_subset_ne.mpr ⟨hVU,he⟩
  have hVr : V.card ≤ r+1 := by have := Finset.card_lt_card hproper; omega
  have hVK : V.card ≤ K := (Finset.card_le_card hVU).trans hUK
  have hVr' : V.card ≤ r+2 := by omega
  obtain ⟨q,M,hq,hRM⟩ := hR
  have hRM' := hRM.mono hVU
  by_cases hw : (I.drawing K).Wraps V
  · have hcard : V.card = r+1 := Nat.le_antisymm hVr ((I.drawing K).wraps_card hr V hw)
    obtain ⟨d⟩ := I.wrapData_exists K hK hr V V hVK (Finset.Subset.refl _) hcard hw
    have hd : d.blocks = V := Finset.eq_of_subset_of_card_le d.subset (by rw [d.card]; exact hVr)
    obtain ⟨q',hq',hshift⟩ := q.restrict_on_wrapping Q K hK hr hVU hUK hVr' d
      (fun b hb => hvalid b (hVU hb)) hq
    refine ⟨q',M,hq',hRM'.trans ?_⟩
    apply I.fromPotentials_agree K V M
    intro b hb side
    exact (hshift _ (d.type_reachable hr b (hd.symm ▸ hb) side)).symm
  · obtain ⟨q',hq'⟩ := ShiftChoice.admissible_exists Q K hr V hVr'
    obtain ⟨M',hM'⟩ := I.adjust_nonwrapping K hr V hw M
      (q.values K (BlockName.links U)) (q'.values K (BlockName.links V))
      (fun l hl => q.values_solves K hK _ ((BlockName.links_card U).trans hUK) l (BlockName.links_mono hVU hl))
      (q'.values_solves K hK _ ((BlockName.links_card V).trans hVK))
    exact ⟨q',M',hq',hRM'.trans hM'.symm⟩

end ConsistencyData
end WLTime.Compression

namespace WLTime.Compression
namespace ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} (I : ConsistencyData (r+1) m P E)

instance instAddCommGroupReadValue (K : ℕ) (n : RawName (r := r) (m := m) (P := P) (E := E) K) :
    AddCommGroup (I.ReadValue K n) := by cases n <;> dsimp [ReadValue] <;> infer_instance
instance instModuleF₂ReadValue (K : ℕ) (n : RawName (r := r) (m := m) (P := P) (E := E) K) :
    Module F₂ (I.ReadValue K n) := by cases n <;> dsimp [ReadValue] <;> infer_instance
instance instFintypeReadValue (K : ℕ) (n : RawName (r := r) (m := m) (P := P) (E := E) K) :
    Fintype (I.ReadValue K n) := by cases n <;> dsimp [ReadValue] <;> infer_instance

noncomputable def blockForm (K : ℕ)
    (b : RawBlock (r := r) (m := m) (P := P) (E := E) K) : I.Readouts K →ₗ[F₂] F₂ where
  toFun R := match b with
    | .site _ _ _ _ => 0
    | .square i l a b =>
      I.leftForm K l (R (.horizontal i (linkLeft K I.src l) a b)) +
      I.rightForm K l (R (.horizontal i (linkRight K I.dst l)
        (linkMatch K (fun e => I.coordinatePerm e i) l a)
        (linkMatch K (fun e => I.coordinatePerm e (finRotate (r+1) i)) l b))) +
      R (.vertical i l a) + R (.vertical (finRotate (r+1) i) l b)
  map_add' R S := by cases b <;> simp only [Pi.add_apply, map_add] <;> abel
  map_smul' c R := by cases b <;> simp only [Pi.smul_apply, map_smul, smul_add, smul_zero, RingHom.id_apply]

noncomputable def blockBias (K : ℕ) : RawBlock (r := r) (m := m) (P := P) (E := E) K → F₂
  | .site _ _ _ _ => 0
  | .square i l _ _ => seam i * I.linkBias K l

noncomputable def blockSpace (K : ℕ)
    (b : RawBlock (r := r) (m := m) (P := P) (E := E) K) : Submodule F₂ (I.Readouts K) where
  carrier := {R | ∀ n, n ∉ I.footprint K b → R n = 0}
  zero_mem' := by intro n _; rfl
  add_mem' := by intro R S hR hS n hn; simp only [Pi.add_apply, hR n hn, hS n hn, add_zero]
  smul_mem' := by intro c R hR n hn; simp only [Pi.smul_apply, hR n hn, smul_zero]

noncomputable def atBlock (K : ℕ)
    (b : RawBlock (r := r) (m := m) (P := P) (E := E) K) (R : I.Readouts K) : I.blockSpace K b := by
  classical
  exact ⟨fun n => if n ∈ I.footprint K b then R n else 0,
    fun n hn => ite_eq_right hn⟩

@[simp] theorem atBlock_apply (K : ℕ)
    (b : RawBlock (r := r) (m := m) (P := P) (E := E) K) (R : I.Readouts K)
    (n : RawName (r := r) (m := m) (P := P) (E := E) K) (hn : n ∈ I.footprint K b) :
    (I.atBlock K b R).val n = R n := by
  classical
  exact ite_eq_left hn

theorem blockForm_congr (K : ℕ)
    (b : RawBlock (r := r) (m := m) (P := P) (E := E) K) (R S : I.Readouts K)
    (h : ∀ n ∈ I.footprint K b, R n = S n) : I.blockForm K b R = I.blockForm K b S := by
  classical
  cases b with
  | site => rfl
  | square i l a b =>
    have h₁ := h (.horizontal i (linkLeft K I.src l) a b) (by simp [footprint])
    have h₂ := h (.horizontal i (linkRight K I.dst l)
        (linkMatch K (fun e => I.coordinatePerm e i) l a)
        (linkMatch K (fun e => I.coordinatePerm e (finRotate (r+1) i)) l b)) (by simp [footprint])
    have h₃ := h (.vertical i l a) (by simp [footprint])
    have h₄ := h (.vertical (finRotate (r+1) i) l b) (by simp [footprint])
    simp only [blockForm, LinearMap.coe_mk, AddHom.coe_mk]
    rw [h₁,h₂,h₃,h₄]

@[simp] theorem blockForm_atBlock (K : ℕ)
    (b : RawBlock (r := r) (m := m) (P := P) (E := E) K) (R : I.Readouts K) :
    I.blockForm K b (I.atBlock K b R).val = I.blockForm K b R :=
  I.blockForm_congr K b _ _ (fun n hn => I.atBlock_apply K b R n hn)

abbrev Legal (K : ℕ) (ε : F₂)
    (b : RawBlock (r := r) (m := m) (P := P) (E := E) K) :=
  {R : I.blockSpace K b // I.blockForm K b R.val = ε * I.blockBias K b}

noncomputable def zeroValuation (K : ℕ)
    (b : RawBlock (r := r) (m := m) (P := P) (E := E) K) : I.Legal K 0 b :=
  ⟨0, by simp⟩

noncomputable def translate (K : ℕ)
    (b : RawBlock (r := r) (m := m) (P := P) (E := E) K) (a : I.Legal K 1 b) :
    I.Legal K 0 b ≃ I.Legal K 1 b where
  toFun z := ⟨z.val + a.val, by simp only [Submodule.coe_add, map_add, z.property,
    a.property, zero_mul, zero_add, one_mul]⟩
  invFun z := ⟨z.val - a.val, by simp only [Submodule.coe_sub, map_sub, z.property,
    a.property, sub_self, zero_mul]⟩
  left_inv z := by apply Subtype.ext; exact add_sub_cancel_right _ _
  right_inv z := by apply Subtype.ext; exact sub_add_cancel _ _

theorem fromPotentials_legal [DecidableEq E] (K : ℕ)
    (U : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K))
    (M : I.Potentials K) (h : (t : TypeNode K P E) → I.Value K t)
    (hh : I.ShiftSolves K (BlockName.links U) h)
    (b : RawBlock (r := r) (m := m) (P := P) (E := E) K) (hb : b ∈ U) :
    I.blockForm K b (I.fromPotentials K M h) = I.blockBias K b := by
  cases b with
  | site => rfl
  | square i l a b =>
    exact square_readouts_legal _ _ _ _ _ _ _ _ _ _ (hh l (BlockName.square_link_mem hb))

theorem offset_legal [DecidableEq E] [DecidableEq P] (Q : I.ArcWitness)
    (K : ℕ) (hK : 0 < K)
    (U : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K)) (hU : U.card ≤ K)
    (R : I.Readouts K) (hR : I.OffsetFamily Q K U R)
    (b : RawBlock (r := r) (m := m) (P := P) (E := E) K) (hb : b ∈ U) :
    I.blockForm K b R = I.blockBias K b := by
  obtain ⟨q,M,hq,heq⟩ := hR
  rw [I.blockForm_congr K b R _ (heq b hb)]
  exact I.fromPotentials_legal K U M _
    (q.values_solves K hK _ ((BlockName.links_card U).trans hU)) b hb

theorem legal_nonempty (K : ℕ) (hr : 1 ≤ r) (ε : F₂)
    (b : RawBlock (r := r) (m := m) (P := P) (E := E) K) : Nonempty (I.Legal K ε b) := by
  classical
  cases b with
  | site i t a b => exact ⟨⟨0, by simp [blockForm, blockBias]⟩⟩
  | square i l a b =>
    let n : RawName (r := r) (m := m) (P := P) (E := E) K := .vertical i l a
    let R : I.Readouts K := Function.update (fun _ => 0) n (ε * (seam i * I.linkBias K l))
    refine ⟨⟨I.atBlock K (.square i l a b) R, ?_⟩⟩
    rw [I.blockForm_atBlock]
    have hv : ReadoutName.vertical (finRotate (r+1) i) l b ≠ n := by
      intro h
      have hi := ReadoutName.vertical.inj h
      exact rotate_ne_self hr i hi.1
    simp [blockForm, blockBias, R, n, Function.update_of_ne hv]

end ConsistencyData
end WLTime.Compression

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Pebbles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uB uD uState

namespace WLTime.Pebble

abbrev Position (K : ℕ) (A : Type uA) (B : Type uB) := Fin K → Option (A × B)

def Position.Sub {K : ℕ} {A : Type uA} {B : Type uB} (P Q : Position K A B) : Prop :=
  ∀ i, P i = none ∨ P i = Q i

def Position.PartialIso {K : ℕ} {A : Type uA} {B : Type uB} (G : SimpleGraph A) (H : SimpleGraph B)
    (C : A → B → Prop) (P : Position K A B) : Prop :=
  (∀ i x y, P i = some (x,y) → C x y) ∧
  ∀ i j x y u v, P i = some (x,y) → P j = some (u,v) →
    (x = u ↔ y = v) ∧ (G.Adj x u ↔ H.Adj y v)

structure Invariant {A : Type uA} {B : Type uB} (G : SimpleGraph A) (H : SimpleGraph B)
    (C : A → B → Prop) (K : ℕ) where
  safe : Position K A B → Prop
  forget : ∀ {P Q}, safe Q → P.Sub Q → safe P
  atomic : ∀ {P}, safe P → P.PartialIso G H C
  extend : ∀ {P}, safe P → ∀ i, P i = none →
    ∃ e : A ≃ B, ∀ z, safe (Function.update P i (some (z,e z)))

def Wins {K : ℕ} {A : Type uA} {B : Type uB} (G : SimpleGraph A) (H : SimpleGraph B)
    (C : A → B → Prop) (P : Position K A B) : Prop :=
  ∃ I : Invariant G H C K, I.safe P

namespace Position
variable {K : ℕ} {A : Type uA} {B : Type uB}

theorem Sub.trans {P Q R : Position K A B} (hPQ : P.Sub Q) (hQR : Q.Sub R) : P.Sub R := by
  intro i
  rcases hPQ i with h | h
  · exact Or.inl h
  · rcases hQR i with h' | h'
    · exact Or.inl (h.trans h')
    · exact Or.inr (h.trans h')

theorem Sub.mark {P Q : Position K A B} (h : P.Sub Q) {i : Fin K} {x : A} {y : B}
    (hi : P i = some (x,y)) : Q i = some (x,y) := by
  rcases h i with h | h
  · simp only [hi, Option.some_ne_none] at h
  · exact h.symm.trans hi

end Position

noncomputable def active {K : ℕ} {A : Type uA} {B : Type uB} {D : Type uD} (tag : A → Option D)
    (P : Position K A B) : Finset D := by
  classical
  exact Finset.univ.biUnion fun i => match P i with
    | none => ∅
    | some (x,_) => (tag x).toFinset

open scoped Classical in
theorem mem_active {K : ℕ} {A : Type uA} {B : Type uB} {D : Type uD} (tag : A → Option D) (P : Position K A B) (d : D) :
    d ∈ active tag P ↔ ∃ i x y, P i = some (x,y) ∧ tag x = some d := by
  simp only [active, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i,hi⟩
    cases hp : P i with
    | none => simp only [hp, Finset.notMem_empty] at hi
    | some xy =>
      rcases xy with ⟨x,y⟩
      simp only [hp, Option.mem_toFinset] at hi
      exact ⟨i,x,y,hp,hi⟩
  · rintro ⟨i,x,y,hp,ht⟩
    exact ⟨i,by simp [hp,ht]⟩

theorem active_mono {K : ℕ} {A : Type uA} {B : Type uB} {D : Type uD} (tag : A → Option D)
    {P Q : Position K A B} (h : P.Sub Q) : active tag P ⊆ active tag Q := by
  intro d hd
  obtain ⟨i,x,y,hi,ht⟩ := (mem_active tag P d).mp hd
  exact (mem_active tag Q d).mpr ⟨i,x,y,h.mark hi,ht⟩

theorem active_card_le {K : ℕ} {A : Type uA} {B : Type uB} {D : Type uD} (tag : A → Option D) (P : Position K A B)
    (S : Finset (Fin K)) (hS : ∀ i, P i ≠ none → i ∈ S) : (active tag P).card ≤ S.card := by
  classical
  have heq : active tag P = S.biUnion (fun i => match P i with
      | none => ∅
      | some (x,_) => (tag x).toFinset) := by
    ext d
    simp only [mem_active, Finset.mem_biUnion]
    constructor
    · rintro ⟨i,x,y,hi,ht⟩
      exact ⟨i,hS i (by simp [hi]),by simp [hi,ht]⟩
    · rintro ⟨i,_,hi⟩
      cases hp : P i with
      | none => simp only [hp,Finset.notMem_empty] at hi
      | some xy =>
        rcases xy with ⟨x,y⟩
        exact ⟨i,x,y,hp,by simpa only [hp,Option.mem_toFinset,Option.mem_def] using hi⟩
  rw [heq]
  calc
    _ ≤ ∑ i ∈ S, (match P i with | none => ∅ | some (x,_) => (tag x).toFinset).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ S, 1 := by
      apply Finset.sum_le_sum
      intro i _
      cases P i with
      | none => simp
      | some xy => cases hh : tag xy.1 <;> simp [hh]
    _ = S.card := by simp

theorem active_card {K : ℕ} {A : Type uA} {B : Type uB} {D : Type uD} (tag : A → Option D) (P : Position K A B) :
    (active tag P).card ≤ K := by
  simpa using active_card_le tag P Finset.univ (fun i _ => Finset.mem_univ i)

theorem active_card_free {K : ℕ} {A : Type uA} {B : Type uB} {D : Type uD} (tag : A → Option D) (P : Position K A B)
    (i : Fin K) (hi : P i = none) : (active tag P).card < K := by
  have h := active_card_le tag P (Finset.univ.erase i) (by
    intro j hj
    simp only [Finset.mem_erase,Finset.mem_univ,and_true]
    intro he; subst j; exact hj hi)
  have hcard : (Finset.univ.erase i).card = K-1 := by simp
  rw [hcard] at h
  have := i.isLt
  omega

open scoped Classical in
theorem active_update {K : ℕ} {A : Type uA} {B : Type uB} {D : Type uD} (tag : A → Option D) (P : Position K A B)
    (i : Fin K) (hi : P i = none) (x : A) (y : B) :
    active tag (Function.update P i (some (x,y))) = active tag P ∪ (tag x).toFinset := by
  ext d
  simp only [mem_active,Finset.mem_union,Option.mem_toFinset]
  constructor
  · rintro ⟨j,u,v,hj,ht⟩
    by_cases he : j = i
    · subst j
      simp only [Function.update_self,Option.some.injEq,Prod.mk.injEq] at hj
      exact Or.inr (hj.1 ▸ ht)
    · rw [Function.update_of_ne he] at hj
      exact Or.inl ⟨j,u,v,hj,ht⟩
  · rintro (⟨j,u,v,hj,ht⟩ | ht)
    · have he : j ≠ i := by intro he; subst j; simp [hi] at hj
      exact ⟨j,u,v,by simpa only [Function.update_of_ne he] using hj,ht⟩
    · exact ⟨i,x,y,Function.update_self _ _ _,ht⟩

end WLTime.Pebble

namespace WLTime.Pebble

structure ExactLocalSystem {A : Type uA} {B : Type uB} {D : Type uD} (G : SimpleGraph A) (H : SimpleGraph B)
    (C : A → B → Prop) (tag : A → Option D) (K : ℕ) where
  State : Type uState
  family : Finset D → State → Prop
  agree : Finset D → State → State → Prop
  maps : State → A → B → Prop
  empty : ∃ R, family ∅ R
  restrict : ∀ {U V}, V ⊆ U → U.card ≤ K → ∀ {R}, family U R → family V R
  extend : ∀ {U V}, V ⊆ U → U.card ≤ K → ∀ {R}, family V R →
    ∃ R', family U R' ∧ agree V R R'
  transfer : ∀ {U R S x y}, agree U R S → maps R x y →
    (∀ d, tag x = some d → d ∈ U) → maps S x y
  color : ∀ {R x y}, maps R x y → C x y
  atomic : ∀ {R x y u v}, maps R x y → maps R u v →
    (x = u ↔ y = v) ∧ (G.Adj x u ↔ H.Adj y v)
  assemble : (a : D → State) → (∀ d, family {d} (a d)) → A ≃ B
  assemble_some : ∀ a ha x d, tag x = some d → maps (a d) x (assemble a ha x)
  assemble_none : ∀ a ha x, tag x = none → ∀ R, maps R x (assemble a ha x)

namespace ExactLocalSystem
variable {K : ℕ} {A : Type uA} {B : Type uB} {D : Type uD} {G : SimpleGraph A} {H : SimpleGraph B}
    {C : A → B → Prop} {tag : A → Option D}
    (S : ExactLocalSystem.{uA, uB, uD, uState} G H C tag K)

def Safe (P : Position K A B) : Prop :=
  ∃ R, S.family (active tag P) R ∧ ∀ i x y, P i = some (x,y) → S.maps R x y

noncomputable def invariant : Invariant G H C K where
  safe := S.Safe
  forget := by
    intro P Q hQ hPQ
    obtain ⟨R,hR,heq⟩ := hQ
    exact ⟨R,S.restrict (active_mono tag hPQ) (active_card tag Q) hR,
      fun i x y hi => heq i x y (hPQ.mark hi)⟩
  atomic := by
    intro P hP
    obtain ⟨R,hR,heq⟩ := hP
    exact ⟨fun i x y hi => S.color (heq i x y hi),
      fun i j x y u v hi hj => S.atomic (heq i x y hi) (heq j u v hj)⟩
  extend := by
    classical
    intro P hP i hi
    obtain ⟨R,hR,heq⟩ := hP
    let U := active tag P
    have hcard : U.card < K := active_card_free tag P i hi
    have hext (d : D) : ∃ R', S.family (insert d U) R' ∧ S.agree U R R' :=
      S.extend (Finset.subset_insert d U)
        ((Finset.card_insert_le d U).trans (by omega)) hR
    choose a ha hkeep using hext
    have hsingle (d : D) : S.family {d} (a d) :=
      S.restrict (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self d U))
        ((Finset.card_insert_le d U).trans (by omega)) (ha d)
    refine ⟨S.assemble a hsingle, fun z => ?_⟩
    cases ht : tag z with
    | none =>
      refine ⟨R, ?_, ?_⟩
      · simpa only [active_update tag P i hi,ht,Option.toFinset_none,Finset.union_empty] using hR
      · intro j x y hj
        by_cases hji : j = i
        · subst j
          simp only [Function.update_self,Option.some.injEq,Prod.mk.injEq] at hj
          rcases hj with ⟨rfl,rfl⟩
          exact S.assemble_none a hsingle z ht R
        · rw [Function.update_of_ne hji] at hj
          exact heq j x y hj
    | some d =>
      refine ⟨a d, ?_, ?_⟩
      · simpa only [active_update tag P i hi,ht,Option.toFinset_some,Finset.union_singleton] using ha d
      · intro j x y hj
        by_cases hji : j = i
        · subst j
          simp only [Function.update_self,Option.some.injEq,Prod.mk.injEq] at hj
          rcases hj with ⟨rfl,rfl⟩
          exact S.assemble_some a hsingle z d ht
        · rw [Function.update_of_ne hji] at hj
          exact S.transfer (hkeep d) (heq j x y hj)
            (fun b hb => (mem_active tag P b).mpr ⟨j,x,y,hj,hb⟩)

end ExactLocalSystem
end WLTime.Pebble

namespace WLTime.Pebble

noncomputable def degree {A : Type uA} [Fintype A] (G : SimpleGraph A) (x : A) : ℕ :=
  by classical exact Fintype.card {z : A // G.Adj x z}

end WLTime.Pebble

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Gadgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uB uA' uB' uP uE

namespace WLTime.Pebble
namespace Position
variable {K : ℕ} {A : Type uA} {B : Type uB} {A' : Type uA'} {B' : Type uB'}

def map (f : A ≃ A') (g : B ≃ B') (P : Position K A B) : Position K A' B' :=
  fun i => (P i).map (fun xy => (f xy.1,g xy.2))

@[simp] theorem map_none (f : A ≃ A') (g : B ≃ B') :
    map f g (fun _ : Fin K => none) = fun _ => none := rfl

@[simp] theorem map_update (f : A ≃ A') (g : B ≃ B') (P : Position K A B)
    (i : Fin K) (x : A) (y : B) :
    map f g (Function.update P i (some (x,y))) =
      Function.update (map f g P) i (some (f x,g y)) := by
  funext j
  by_cases h : j=i
  · subst j; simp [map]
  · simp [map,h]

@[simp] theorem map_inverse (f : A ≃ A') (g : B ≃ B') (P : Position K A B) :
    map f.symm g.symm (map f g P) = P := by
  funext i
  cases h : P i <;> simp [map,h]

@[simp] theorem map_apply_eq_some (f : A ≃ A') (g : B ≃ B') (P : Position K A B)
    (i : Fin K) (x : A') (y : B') :
    map f g P i = some (x,y) ↔ P i = some (f.symm x,g.symm y) := by
  cases h : P i with
  | none => simp [map,h]
  | some xy =>
    rcases xy with ⟨a,b⟩
    simp [map,h,f.eq_symm_apply,g.eq_symm_apply]

@[simp] theorem map_apply_eq_none (f : A ≃ A') (g : B ≃ B') (P : Position K A B)
    (i : Fin K) : map f g P i = none ↔ P i = none := by simp [map]

end Position

end WLTime.Pebble

namespace WLTime.Compression
namespace ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} (I : ConsistencyData (r+1) m P E)

abbrev Block (K : ℕ) := {b : RawBlock (r := r) (m := m) (P := P) (E := E) K // I.ValidBlock K b}
abbrev Vertex (K : ℕ) (ε : F₂) := (b : I.Block K) × I.Legal K ε b.val

noncomputable instance instFintypeBlock [Fintype P] [Fintype E] (K : ℕ) : Fintype (I.Block K) := by
  classical
  dsimp [Block]
  infer_instance
noncomputable instance instFintypeLegalValRawBlockValidBlock [Fintype P] [Fintype E] (K : ℕ) (ε : F₂) (b : I.Block K) :
    Fintype (I.Legal K ε b.val) := by
  classical
  dsimp [Legal]
  infer_instance

namespace Vertex
variable {I} {K : ℕ} {ε : F₂}
abbrev read (x : I.Vertex K ε) : I.Readouts K := x.2.val.val

theorem ext {x y : I.Vertex K ε} (hb : x.1 = y.1) (hr : x.read = y.read) : x = y := by
  rcases x with ⟨b,x⟩
  rcases y with ⟨c,y⟩
  dsimp at hb
  subst c
  apply congrArg (Sigma.mk b)
  apply Subtype.ext
  exact Subtype.ext hr
end Vertex

open scoped Classical in

noncomputable def valuationGraph (K : ℕ) (ε : F₂) : SimpleGraph (I.Vertex K ε) where
  Adj x y := x.1 ≠ y.1 ∧ (I.footprint K x.1.val ∩ I.footprint K y.1.val).Nonempty ∧
    ∀ n ∈ I.footprint K x.1.val, n ∈ I.footprint K y.1.val → x.read n = y.read n
  symm := ⟨by
    intro x y h
    exact ⟨Ne.symm h.1,by simpa only [Finset.inter_comm] using h.2.1,
      fun n hn hm => (h.2.2 n hm hn).symm⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

def Maps (K : ℕ) (R : I.Readouts K) (x : I.Vertex K 0) (y : I.Vertex K 1) : Prop :=
  x.1 = y.1 ∧ y.read = x.read + (I.atBlock K x.1.val R).val

theorem atBlock_congr (K : ℕ)
    (b : RawBlock (r := r) (m := m) (P := P) (E := E) K) (R S : I.Readouts K)
    (h : ∀ n ∈ I.footprint K b, R n = S n) : I.atBlock K b R = I.atBlock K b S := by
  classical
  apply Subtype.ext
  funext n
  by_cases hn : n ∈ I.footprint K b
  · simpa only [I.atBlock_apply K b R n hn,I.atBlock_apply K b S n hn] using h n hn
  · simp only [atBlock,ite_eq_right hn]

theorem maps_read (K : ℕ) {R : I.Readouts K} {x : I.Vertex K 0} {y : I.Vertex K 1}
    (h : I.Maps K R x y) (n : RawName (r := r) (m := m) (P := P) (E := E) K)
    (hn : n ∈ I.footprint K x.1.val) : y.read n = x.read n + R n := by
  rw [h.2]
  simp only [Pi.add_apply,I.atBlock_apply K _ R n hn]

theorem maps_atomic (K : ℕ) {R : I.Readouts K}
    {x u : I.Vertex K 0} {y v : I.Vertex K 1} (hx : I.Maps K R x y) (hu : I.Maps K R u v) :
    (x = u ↔ y = v) ∧ ((I.valuationGraph K 0).Adj x u ↔ (I.valuationGraph K 1).Adj y v) := by
  classical
  have hb : x.1 = u.1 ↔ y.1 = v.1 := by rw [hx.1,hu.1]
  constructor
  · constructor
    · intro h
      have hyv := hb.mp (congrArg Sigma.fst h)
      apply Vertex.ext hyv
      rw [hx.2,hu.2,h]
    · intro h
      have hxu := hb.mpr (congrArg Sigma.fst h)
      apply Vertex.ext hxu
      have he : x.read + (I.atBlock K x.1.val R).val = u.read + (I.atBlock K u.1.val R).val := by
        rw [← hx.2,← hu.2,h]
      rw [hxu] at he
      exact add_right_cancel he
  · change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
    have hs : (I.footprint K x.1.val ∩ I.footprint K u.1.val).Nonempty ↔
        (I.footprint K y.1.val ∩ I.footprint K v.1.val).Nonempty := by rw [hx.1,hu.1]
    refine and_congr (not_congr hb) (and_congr hs ?_)
    constructor
    · intro h n hn hm
      rw [← hx.1] at hn
      rw [← hu.1] at hm
      rw [I.maps_read K hx n hn,I.maps_read K hu n hm,h n hn hm]
    · intro h n hn hm
      have he := h n (hx.1 ▸ hn) (hu.1 ▸ hm)
      rw [I.maps_read K hx n hn,I.maps_read K hu n hm] at he
      exact add_right_cancel he

open scoped Classical in
noncomputable def rawSet (K : ℕ) (U : Finset (I.Block K)) := U.image Subtype.val

@[simp] theorem rawSet_card (K : ℕ) (U : Finset (I.Block K)) : (I.rawSet K U).card = U.card := by
  classical
  exact Finset.card_image_of_injective U Subtype.val_injective

theorem rawSet_mono (K : ℕ) {U V : Finset (I.Block K)} (h : V ⊆ U) : I.rawSet K V ⊆ I.rawSet K U := by
  classical
  exact Finset.image_subset_image h

@[simp] theorem mem_rawSet (K : ℕ) (U : Finset (I.Block K)) (b : I.Block K) :
    b.val ∈ I.rawSet K U ↔ b ∈ U := by
  classical
  constructor
  · intro h
    obtain ⟨c,hc,hcb⟩ := Finset.mem_image.mp h
    have he : c = b := Subtype.ext hcb
    exact he ▸ hc
  · intro h
    exact Finset.mem_image.mpr ⟨b,h,rfl⟩

theorem rawSet_valid (K : ℕ) (U : Finset (I.Block K)) :
    ∀ b ∈ I.rawSet K U, I.ValidBlock K b := by
  classical
  intro b hb
  obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hb
  exact c.property

noncomputable def localOffset [DecidableEq E] [DecidableEq P] (Q : I.ArcWitness)
    (K : ℕ) (hK : 0 < K) (b : I.Block K) (R : I.Readouts K)
    (hR : I.OffsetFamily Q K (I.rawSet K {b}) R) : I.Legal K 1 b.val := by
  classical
  refine ⟨I.atBlock K b.val R, ?_⟩
  rw [I.blockForm_atBlock, one_mul]
  exact I.offset_legal Q K hK _ (by simp; omega) R hR b.val (by simp)

noncomputable def assembleTranslations [DecidableEq E] [DecidableEq P] (Q : I.ArcWitness)
    (K : ℕ) (hK : 0 < K) (a : I.Block K → I.Readouts K)
    (ha : ∀ b, I.OffsetFamily Q K (I.rawSet K {b}) (a b)) : I.Vertex K 0 ≃ I.Vertex K 1 :=
  Equiv.sigmaCongrRight (fun b => I.translate K b.val (I.localOffset Q K hK b (a b) (ha b)))

theorem assembleTranslations_maps [DecidableEq E] [DecidableEq P] (Q : I.ArcWitness)
    (K : ℕ) (hK : 0 < K) (a : I.Block K → I.Readouts K)
    (ha : ∀ b, I.OffsetFamily Q K (I.rawSet K {b}) (a b)) (x : I.Vertex K 0) :
    I.Maps K (a x.1) x (I.assembleTranslations Q K hK a ha x) := by
  exact ⟨rfl,rfl⟩

noncomputable def valuationSystem [DecidableEq E] [DecidableEq P] (Q : I.ArcWitness)
    (K : ℕ) (hK : 0 < K) (hr : 2 ≤ r) (hKr : K ≤ r+2) :
    Pebble.ExactLocalSystem (I.valuationGraph K 0) (I.valuationGraph K 1)
      (fun x y => x.1 = y.1) (fun x => some x.1) K where
  State := I.Readouts K
  family U R := I.OffsetFamily Q K (I.rawSet K U) R
  agree U R S := I.AgreeOn K (I.rawSet K U) R S
  maps := I.Maps K
  empty := by
    have h := I.offset_nonempty Q K hr (I.rawSet K ∅) (by simp)
    exact h
  restrict := by
    intro U V hVU hU R hR
    exact I.offset_restrict Q K hK hr (I.rawSet_mono K hVU)
      (by simpa using hU) (by simpa using hU.trans hKr) (I.rawSet_valid K U) R hR
  extend := by
    intro U V hVU hU R hR
    exact I.offset_extend Q K hK hr (I.rawSet_mono K hVU)
      (by simpa using hU) (by simpa using hU.trans hKr) (I.rawSet_valid K U) R hR
  transfer := by
    intro U R S x y hag hxy hxU
    have hx := hxU x.1 rfl
    have hab := I.atBlock_congr K x.1.val R S (hag x.1.val ((I.mem_rawSet K U x.1).mpr hx))
    exact ⟨hxy.1,by rw [← hab]; exact hxy.2⟩
  color := fun h => h.1
  atomic := I.maps_atomic K
  assemble := I.assembleTranslations Q K hK
  assemble_some := by
    intro a ha x b hb
    have he : x.1 = b := Option.some.inj hb
    rw [← he]
    exact I.assembleTranslations_maps Q K hK a ha x
  assemble_none := by intro a ha x h; cases h

end ConsistencyData
end WLTime.Compression

namespace WLTime.Compression
namespace ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} (I : ConsistencyData (r+1) m P E)

noncomputable def zeroVertex (K : ℕ) (b : I.Block K) : I.Vertex K 0 := ⟨b,I.zeroValuation K b.val⟩

@[simp] theorem zeroVertex_read (K : ℕ) (b : I.Block K) : (I.zeroVertex K b).read = 0 := rfl

noncomputable def queryPosition (K : ℕ) {s : ℕ} (f : Fin s → I.Block K) (y : Fin s → I.Vertex K 1) :
    Pebble.Position (s+1) (I.Vertex K 0) (I.Vertex K 1) :=
  Fin.lastCases none (fun i => some (I.zeroVertex K (f i),y i))

def Queried (K : ℕ) {s : ℕ} (f : Fin s → I.Block K) (y : Fin s → I.Vertex K 1) : Prop :=
  Pebble.Wins (I.valuationGraph K 0) (I.valuationGraph K 1)
    (fun x y => x.1 = y.1) (I.queryPosition K f y)

end ConsistencyData
end WLTime.Compression

namespace WLTime.Compression
namespace ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} (I : ConsistencyData (r+1) m P E)

def AddressAllowed (K : ℕ) (t : TypeNode K P E) (a : I.Address) : Prop :=
  ∀ i, I.LabelAllowed K t i (a i)

abbrev horizontalName (K : ℕ) (t : TypeNode K P E) (a : I.Address) (i : Fin (r+1)) :
    RawName (r := r) (m := m) (P := P) (E := E) K :=
  .horizontal i t (a i) (a (finRotate (r+1) i))

abbrev verticalName (K : ℕ) (l : TypeLink K E) (a : I.Address) (i : Fin (r+1)) :
    RawName (r := r) (m := m) (P := P) (E := E) K := .vertical i l (a i)

noncomputable def matchedAddress (K : ℕ) (l : TypeLink K E) (a : I.Address) : I.Address :=
  fun i => linkMatch K (fun e => I.coordinatePerm e i) l (a i)

noncomputable def siteRing (K : ℕ) (t : TypeNode K P E) (a : I.Address) (ha : I.AddressAllowed K t a) :
    Fin (r+1) → I.Block K := fun i =>
  ⟨.site i t (a i) (a (finRotate (r+1) i)),ha i,ha (finRotate (r+1) i)⟩

noncomputable def squareRing (K : ℕ) (l : TypeLink K E) (a : I.Address) (ha : I.Allowed l.1 a) :
    Fin (r+1) → I.Block K := fun i =>
  ⟨.square i l (a i) (a (finRotate (r+1) i)),ha i,ha (finRotate (r+1) i)⟩

theorem leftAddress_allowed (K : ℕ) (l : TypeLink K E) (a : I.Address) (ha : I.Allowed l.1 a) :
    I.AddressAllowed K (linkLeft K I.src l) a :=
  fun i => I.linkLeft_allowed K l i (a i) (ha i)

theorem rightAddress_allowed (K : ℕ) (l : TypeLink K E) (a : I.Address) (ha : I.Allowed l.1 a) :
    I.AddressAllowed K (linkRight K I.dst l) (I.matchedAddress K l a) :=
  fun i => I.linkRight_allowed K l i (a i) (ha i)

noncomputable def horizontalSum (K : ℕ) (t : TypeNode K P E) (a : I.Address)
    (ys : Fin (r+1) → I.Vertex K 1) : I.Value K t := ∑ i, (ys i).read (I.horizontalName K t a i)

end ConsistencyData
end WLTime.Compression

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Marking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uP uE uV uW uD uS uState

namespace WLTime.Compression
namespace ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} (I : ConsistencyData (r+1) m P E)

def Attainable (K : ℕ) (t : TypeNode K P E) (a : I.Address) : Set (I.Value K t) :=
  {v | ∃ ha ys, I.Queried K (I.siteRing K t a ha) ys ∧ I.horizontalSum K t a ys = v}

end ConsistencyData
end WLTime.Compression

namespace WLTime.Marking

inductive Vertex (V : Type uV) (count : V → ℕ) (q : ℕ) where
  | base : V → Vertex V count q
  | mark : (v : V) → Fin (count v) → Vertex V count q
  | hub : Vertex V count q
  | pad : Fin q → Vertex V count q
  deriving DecidableEq, Fintype

variable {V : Type uV} {W : Type uW} {D : Type uD} {count : V → ℕ} {count' : W → ℕ} {q : ℕ}

def Adj (G : SimpleGraph V) : Vertex V count q → Vertex V count q → Prop
  | .base x, .base y => G.Adj x y
  | .base x, .mark y _ => x = y
  | .mark x _, .base y => x = y
  | .hub, .hub => False
  | .hub, _ => True
  | _, .hub => True
  | _, _ => False

def graph (G : SimpleGraph V) (count : V → ℕ) (q : ℕ) : SimpleGraph (Vertex V count q) where
  Adj := Adj G
  symm := ⟨by intro x y h; cases x <;> cases y <;> simp only [Adj] at h ⊢ <;> first | exact G.symm h | exact h.symm⟩
  loopless := ⟨by intro x; cases x <;> simp only [Adj,SimpleGraph.irrefl,not_false_eq_true]⟩

@[simp] theorem mark_eq_iff (v w : V) (i : Fin (count v)) (j : Fin (count w)) :
    (Vertex.mark v i : Vertex V count q) = .mark w j ↔ v=w ∧ i.val=j.val := by
  constructor
  · intro h
    cases h
    exact ⟨rfl,rfl⟩
  · rintro ⟨rfl,h⟩
    exact congrArg (Vertex.mark v) (Fin.ext h)

noncomputable def liftEquiv (e : V ≃ W) (hc : ∀ v, count v = count' (e v)) :
    Vertex V count q ≃ Vertex W count' q where
  toFun
    | .base v => .base (e v)
    | .mark v i => .mark (e v) ⟨i.val,by rw [← hc v]; exact i.isLt⟩
    | .hub => .hub
    | .pad i => .pad i
  invFun
    | .base w => .base (e.symm w)
    | .mark w i => .mark (e.symm w) ⟨i.val,by rw [hc (e.symm w),e.apply_symm_apply]; exact i.isLt⟩
    | .hub => .hub
    | .pad i => .pad i
  left_inv x := by cases x <;> simp only [e.symm_apply_apply,mark_eq_iff,and_self]
  right_inv x := by cases x <;> simp only [e.apply_symm_apply,mark_eq_iff,and_self]

def tag (c : V → D) : Vertex V count q → Option D
  | .base x => some (c x)
  | .mark x _ => some (c x)
  | .hub => none
  | .pad _ => none

def Maps {S : Type uS} (maps : S → V → W → Prop) (s : S) :
    Vertex V count q → Vertex W count' q → Prop
  | .base v, .base w => maps s v w
  | .mark v i, .mark w j => maps s v w ∧ i.val=j.val
  | .hub, .hub => True
  | .pad i, .pad j => i=j
  | _, _ => False

theorem maps_atomic {S : Type uS} {G : SimpleGraph V} {H : SimpleGraph W}
    {maps : S → V → W → Prop} (s : S)
    (ha : ∀ {x u y v}, maps s x y → maps s u v →
      (x=u ↔ y=v) ∧ (G.Adj x u ↔ H.Adj y v))
    {x u : Vertex V count q} {y v : Vertex W count' q}
    (hx : Maps maps s x y) (hu : Maps maps s u v) :
    (x=u ↔ y=v) ∧ ((graph G count q).Adj x u ↔ (graph H count' q).Adj y v) := by
  cases x <;> cases y <;> simp only [Maps] at hx <;> try contradiction
  all_goals cases u <;> cases v <;> simp only [Maps] at hu <;> try contradiction
  all_goals simp only [graph,Adj,Vertex.base.injEq,Vertex.pad.injEq,mark_eq_iff,
    reduceCtorEq,and_true,true_and]
  · exact ha hx hu
  · exact (ha hx hu.1).1
  · exact (ha hx.1 hu).1
  · exact and_congr (ha hx.1 hu.1).1 (by rw [hx.2,hu.2])
  · rw [hx,hu]

noncomputable def liftSystem {G : SimpleGraph V} {H : SimpleGraph W}
    (c : V → D) (d : W → D) (n : D → ℕ) (q K : ℕ)
    (L : Pebble.ExactLocalSystem.{uV, uW, uD, uState}
      G H (fun v w => c v = d w) (fun v => some (c v)) K) :
    Pebble.ExactLocalSystem (graph G (n ∘ c) q) (graph H (n ∘ d) q)
      (fun _ _ => True) (tag c) K where
  State := L.State
  family := L.family
  agree := L.agree
  maps := Maps L.maps
  empty := L.empty
  restrict := L.restrict
  extend := L.extend
  transfer := by
    intro U R S x y hag hxy hxU
    cases x <;> cases y <;> simp only [Maps] at hxy ⊢ <;> try contradiction
    · exact L.transfer hag hxy (fun b hb => hxU b hb)
    · exact ⟨L.transfer hag hxy.1 (fun b hb => hxU b hb),hxy.2⟩
    · exact hxy
  color := by intro R x y h; trivial
  atomic := fun hx hu => maps_atomic _ (fun h₁ h₂ => L.atomic h₁ h₂) hx hu
  assemble a ha := liftEquiv (L.assemble a ha) (fun x => congrArg n
    (L.color (L.assemble_some a ha x (c x) rfl)))
  assemble_some := by
    intro a ha x b hb
    cases x with
    | base x => exact L.assemble_some a ha x b hb
    | mark x i => exact ⟨L.assemble_some a ha x b hb,rfl⟩
    | hub => cases hb
    | pad i => cases hb
  assemble_none := by
    intro a ha x hb R
    cases x with
    | base x => cases hb
    | mark x i => cases hb
    | hub => trivial
    | pad i => rfl

end WLTime.Marking

namespace WLTime.Marking
variable {V : Type uV} (count : V → ℕ) (q : ℕ)

def equivSum : Vertex V count q ≃ (V ⊕ (Σ v,Fin (count v))) ⊕ (Unit ⊕ Fin q) where
  toFun
    | .base v => .inl (.inl v)
    | .mark v i => .inl (.inr ⟨v,i⟩)
    | .hub => .inr (.inl ())
    | .pad i => .inr (.inr i)
  invFun
    | .inl (.inl v) => .base v
    | .inl (.inr ⟨v,i⟩) => .mark v i
    | .inr (.inl _) => .hub
    | .inr (.inr i) => .pad i
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with (x | ⟨v,i⟩) | (_ | i) <;> rfl

end WLTime.Marking

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Padding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV uW uD uP uE uT uL uA uB

namespace WLTime.Marking
variable {V : Type uV} {W : Type uW} {D : Type uD} [Fintype V] [Fintype W]

def basePosition {K : ℕ} {count : V → ℕ} {count' : W → ℕ} {q : ℕ}
    (P : Pebble.Position K V W) : Pebble.Position K (Vertex V count q) (Vertex W count' q) :=
  fun i => (P i).map (fun xy => (.base xy.1,.base xy.2))

omit [Fintype V] [Fintype W] in
@[simp] theorem basePosition_update {K : ℕ} {count : V → ℕ} {count' : W → ℕ} {q : ℕ}
    (P : Pebble.Position K V W) (i : Fin K) (x : V) (y : W) :
    (basePosition (count := count) (count' := count') (q := q) (Function.update P i (some (x,y)))) =
      Function.update (basePosition P) i (some (.base x,.base y)) := by
  funext j
  by_cases h : j=i
  · subst j; simp [basePosition]
  · simp [basePosition,h]

end WLTime.Marking

namespace WLTime.Compression
namespace ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} [Fintype P] [Fintype E]
    (I : ConsistencyData (r+1) m P E)

noncomputable def baseEquiv (K : ℕ) (hr : 1 ≤ r) : I.Vertex K 0 ≃ I.Vertex K 1 :=
  Equiv.sigmaCongrRight (fun b => I.translate K b.val
    (Classical.choice (I.legal_nonempty K hr 1 b.val)))

omit [Fintype P] [Fintype E] in
@[simp] theorem baseEquiv_block (K : ℕ) (hr : 1 ≤ r) (x : I.Vertex K 0) :
    (I.baseEquiv K hr x).1 = x.1 := rfl

end ConsistencyData
end WLTime.Compression

namespace WLTime.Compression

noncomputable def BlockName.equivProduct {r : ℕ} {T : Type uT} {L : Type uL} {A : Type uA} :
    BlockName r T L A ≃ Fin (r+1) × (T ⊕ L) × A × A where
  toFun
    | .site i t a b => (i,.inl t,a,b)
    | .square i l a b => (i,.inr l,a,b)
  invFun
    | (i,.inl t,a,b) => .site i t a b
    | (i,.inr l,a,b) => .square i l a b
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨i,t | l,a,b⟩ <;> rfl

theorem BlockName.card {r : ℕ} {T : Type uT} {L : Type uL} {A : Type uA} [Fintype T] [Fintype L] [Fintype A] :
    Fintype.card (BlockName r T L A) =
      (r+1)*(Fintype.card T+Fintype.card L)*(Fintype.card A)^2 := by
  rw [Fintype.card_congr BlockName.equivProduct]
  simp only [Fintype.card_prod,Fintype.card_sum,Fintype.card_fin]
  ring

end WLTime.Compression

namespace WLTime

noncomputable def Graph.ofSimple {V : Type uV} {n : ℕ} (G : SimpleGraph V) (e : V ≃ Fin n) : Graph n := by
  classical
  exact ⟨fun x y => decide (G.Adj (e.symm x) (e.symm y)),
    (by intro x y; simp only [decide_eq_decide]; exact G.adj_comm _ _),fun x => by simp⟩

def Graph.simple {n : ℕ} (G : Graph n) : SimpleGraph (Fin n) where
  Adj x y := G.adj x y = true
  symm := ⟨fun x y h => (G.property.1 y x).trans h⟩
  loopless := ⟨fun x h => Bool.false_ne_true ((G.property.2 x).symm.trans h)⟩

@[simp] theorem Graph.ofSimple_adj {V : Type uV} {n : ℕ} (G : SimpleGraph V)
    (e : V ≃ Fin n) (x y : V) :
    ((Graph.ofSimple G e).simple).Adj (e x) (e y) ↔ G.Adj x y := by
  simp [Graph.ofSimple,Graph.simple,Graph.adj]

@[simp] theorem Graph.ofSimple_diameter {V : Type uV} {n : ℕ} (G : SimpleGraph V)
    (e : V ≃ Fin n) (hn : 0 < n)
    (h : ∀ x y, x=y ∨ G.Adj x y ∨ ∃ z, G.Adj x z ∧ G.Adj z y) :
    (Graph.ofSimple G e).diameterTwo := by
  refine ⟨hn,fun x y => ?_⟩
  rcases h (e.symm x) (e.symm y) with he | he | ⟨z,hz,hz'⟩
  · exact Or.inl (e.symm.injective he)
  · exact Or.inr (Or.inl (by simpa [Graph.ofSimple,Graph.adj] using he))
  · exact Or.inr (Or.inr ⟨e z,by simpa [Graph.ofSimple,Graph.adj] using hz,
      by simpa [Graph.ofSimple,Graph.adj] using hz'⟩)

end WLTime

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Enumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uT uL uA uP uE uV uW uD uU

namespace WLTime.Compression

inductive NameTag (r : ℕ) (T : Type uT) (L : Type uL) where
  | horizontal (row : Fin (r+1)) (type : T)
  | vertical (row : Fin (r+1)) (link : L)
  deriving DecidableEq, Fintype

namespace ReadoutName
variable {r : ℕ} {T : Type uT} {L : Type uL} {A : Type uA}
def tag : ReadoutName r T L A → NameTag r T L
  | .horizontal i t _ _ => .horizontal i t
  | .vertical i l _ => .vertical i l
end ReadoutName

theorem link_endpoints_ne {P : Type uP} {E : Type uE} (K : ℕ) (hK : 0<K)
    (src dst : E → P) (l : TypeLink K E) : linkLeft K src l ≠ linkRight K dst l := by
  intro h
  by_cases h0 : l.2.val=0
  · have h4 : l.2.val≠4*K := by omega
    simp only [linkLeft,linkRight,dite_eq_left h0,dite_eq_right h4,reduceCtorEq] at h
  · by_cases h4 : l.2.val=4*K
    · simp only [linkLeft,linkRight,dite_eq_right h0,dite_eq_left h4,reduceCtorEq] at h
    · simp only [linkLeft,linkRight,dite_eq_right h0,dite_eq_right h4,Sum.inr.injEq,Prod.mk.injEq,
        true_and,Fin.mk.injEq] at h
      omega

namespace ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} (I : ConsistencyData (r+1) m P E)

abbrev Tag (K : ℕ) := NameTag r (TypeNode K P E) (TypeLink K E)
abbrev TagValue (K : ℕ) : Tag (r:=r) (P:=P) (E:=E) K → Type
  | .horizontal _ t => I.Value K t
  | .vertical _ _ => F₂
abbrev TagValues (K : ℕ) := (v : Tag (r:=r) (P:=P) (E:=E) K) → I.TagValue K v

instance instZeroTagValue (K : ℕ) (n : Tag (r:=r) (P:=P) (E:=E) K) : Zero (I.TagValue K n) := by
  cases n <;> dsimp [TagValue] <;> infer_instance
instance instFintypeTagValue (K : ℕ) (n : Tag (r:=r) (P:=P) (E:=E) K) : Fintype (I.TagValue K n) := by
  cases n <;> dsimp [TagValue] <;> infer_instance

def tagRead (K : ℕ) (v : I.TagValues K) : I.Readouts K
  | .horizontal i t _ _ => v (.horizontal i t)
  | .vertical i l _ => v (.vertical i l)

theorem tag_injective_on_footprint (K : ℕ) (hK : 0<K) (hr : 1≤r)
    (b : RawBlock (r:=r) (m:=m) (P:=P) (E:=E) K) :
    Set.InjOn ReadoutName.tag {x | x ∈ I.footprint K b} := by
  classical
  intro x hx y hy hxy
  cases b with
  | site i t a b =>
    simp only [footprint,Finset.mem_singleton] at hx hy
    exact hx.trans hy.symm
  | square i l a b =>
    simp only [footprint,Finset.mem_insert,Finset.mem_singleton] at hx hy
    rcases hx with rfl|rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl|rfl <;>
      simp only [ReadoutName.tag,NameTag.horizontal.injEq,NameTag.vertical.injEq,
        reduceCtorEq,true_and,and_true] at hxy <;> try rfl
    · exact False.elim (link_endpoints_ne K hK I.src I.dst l hxy)
    · exact False.elim (link_endpoints_ne K hK I.src I.dst l hxy.symm)
    · exact False.elim (rotate_ne_self hr i hxy.symm)
    · exact False.elim (rotate_ne_self hr i hxy)

def TagSupported (K : ℕ) (b : RawBlock (r:=r) (m:=m) (P:=P) (E:=E) K)
    (v : I.TagValues K) : Prop :=
  ∀ t, (∀ n ∈ I.footprint K b, ReadoutName.tag n ≠ t) → v t=0

 theorem tagRead_injective (K : ℕ) (b : RawBlock (r:=r) (m:=m) (P:=P) (E:=E) K)
    {v w : I.TagValues K} (hv : I.TagSupported K b v) (hw : I.TagSupported K b w)
    (h : I.atBlock K b (I.tagRead K v)=I.atBlock K b (I.tagRead K w)) : v=w := by
  classical
  funext t
  by_cases ht : ∃ n ∈ I.footprint K b, ReadoutName.tag n=t
  · obtain ⟨n,hn,hnv⟩ := ht
    have he := congrArg (fun z : I.blockSpace K b => z.val n) h
    rw [I.atBlock_apply K b _ n hn,I.atBlock_apply K b _ n hn] at he
    cases n <;> cases hnv <;> exact he
  · have hn : ∀ n ∈ I.footprint K b, ReadoutName.tag n≠t := by simpa using ht
    exact (hv t hn).trans (hw t hn).symm

def toTag (K : ℕ) (n : RawName (r:=r) (m:=m) (P:=P) (E:=E) K)
    (x : I.ReadValue K n) : I.TagValue K (ReadoutName.tag n) := by
  cases n <;> exact x

noncomputable def encodeTags (K : ℕ) (b : RawBlock (r:=r) (m:=m) (P:=P) (E:=E) K)
    (v : I.blockSpace K b) : I.TagValues K := by
  classical
  intro t
  exact if h : ∃ n ∈ I.footprint K b, ReadoutName.tag n=t then
    h.choose_spec.2 ▸ I.toTag K h.choose (v.val h.choose)
  else 0

theorem encodeTags_supported (K : ℕ)
    (b : RawBlock (r:=r) (m:=m) (P:=P) (E:=E) K) (v : I.blockSpace K b) :
    I.TagSupported K b (I.encodeTags K b v) := by
  classical
  intro t ht
  have hn : ¬∃ n ∈ I.footprint K b,ReadoutName.tag n=t := by
    rintro ⟨n,hn,he⟩; exact ht n hn he
  simp only [encodeTags,dite_eq_right hn]

theorem encodeTags_apply (K : ℕ) (hK : 0<K) (hr : 1≤r)
    (b : RawBlock (r:=r) (m:=m) (P:=P) (E:=E) K) (v : I.blockSpace K b)
    (n : RawName (r:=r) (m:=m) (P:=P) (E:=E) K) (hn : n∈I.footprint K b) :
    I.encodeTags K b v (ReadoutName.tag n)=I.toTag K n (v.val n) := by
  classical
  let h : ∃ j ∈ I.footprint K b, ReadoutName.tag j=ReadoutName.tag n := ⟨n,hn,rfl⟩
  have he : h.choose=n := I.tag_injective_on_footprint K hK hr b h.choose_spec.1 hn h.choose_spec.2
  simp only [encodeTags,dite_eq_left h]
  have hh : ∀ (j : RawName (r:=r) (m:=m) (P:=P) (E:=E) K) (_ : j=n)
      (ht : ReadoutName.tag j=ReadoutName.tag n),
      ht ▸ I.toTag K j (v.val j)=I.toTag K n (v.val n) := by
    intro j hj ht; subst j; rfl
  exact hh _ he _

theorem tagRead_encodeTags (K : ℕ) (hK : 0<K) (hr : 1≤r)
    (b : RawBlock (r:=r) (m:=m) (P:=P) (E:=E) K) (v : I.blockSpace K b) :
    I.atBlock K b (I.tagRead K (I.encodeTags K b v))=v := by
  classical
  apply Subtype.ext
  funext n
  by_cases hn : n∈I.footprint K b
  · rw [I.atBlock_apply K b _ n hn]
    have he := I.encodeTags_apply K hK hr b v n hn
    cases n <;> exact he
  · change (if n∈I.footprint K b then _ else 0)=v.val n
    rw [ite_eq_right hn,v.property n hn]

abbrev Descriptor (K : ℕ) := RawBlock (r:=r) (m:=m) (P:=P) (E:=E) K × I.TagValues K

def DescriptorValid (K : ℕ) (ε : F₂) (v : I.Descriptor K) : Prop :=
  I.ValidBlock K v.1 ∧ I.TagSupported K v.1 v.2 ∧
    I.blockForm K v.1 (I.tagRead K v.2)=ε*I.blockBias K v.1

noncomputable def descriptorEquiv (K : ℕ) (hK : 0<K) (hr : 1≤r) (ε : F₂) :
    {v : I.Descriptor K // I.DescriptorValid K ε v} ≃ I.Vertex K ε where
  toFun v := ⟨⟨v.val.1,v.property.1⟩,⟨I.atBlock K v.val.1 (I.tagRead K v.val.2),
    by rw [I.blockForm_atBlock]; exact v.property.2.2⟩⟩
  invFun v := ⟨(v.1.val,I.encodeTags K v.1.val v.2.val),v.1.property,
    I.encodeTags_supported K v.1.val v.2.val,by
      rw [← I.blockForm_atBlock,I.tagRead_encodeTags K hK hr]; exact v.2.property⟩
  left_inv v := by
    apply Subtype.ext
    dsimp
    congr 1
    exact I.tagRead_injective K v.val.1 (I.encodeTags_supported K _ _) v.property.2.1
      (I.tagRead_encodeTags K hK hr _ _)
  right_inv v := by
    apply Vertex.ext
    · rfl
    · exact congrArg Subtype.val (I.tagRead_encodeTags K hK hr _ _)

end ConsistencyData
end WLTime.Compression

namespace WLTime.Marking

abbrev Slot (V : Type uV) (count : V → ℕ) := V ⊕ ((v : V) × Fin (count v))

variable {V : Type uV} {U : Type uU} {count : V → ℕ}

def slotAdj (G : SimpleGraph V) : Slot V count → Slot V count → Prop
  | .inl x,.inl y => G.Adj x y
  | .inl x,.inr y => x=y.1
  | .inr x,.inl y => x.1=y
  | .inr _,.inr _ => False

def rawAdj (G : SimpleGraph V) (decode : U → Option (Slot V count)) : Option U → Option U → Prop
  | none,none => False
  | none,some _ => True
  | some _,none => True
  | some x,some y => match decode x,decode y with
    | some a,some b => slotAdj G a b
    | _,_ => False

def rawGraph (G : SimpleGraph V) (decode : U → Option (Slot V count)) : SimpleGraph (Option U) where
  Adj := rawAdj G decode
  symm := ⟨by
    intro x y h; cases x <;> cases y <;> simp only [rawAdj] at h ⊢; try exact h
    split at h <;> try contradiction
    rename_i a b hx hy
    rw [hy,hx]
    cases a <;> cases b <;> simp only [slotAdj] at h ⊢ <;>
      first | exact G.symm h | exact h.symm⟩
  loopless := ⟨by
    intro x; cases x with
    | none => simp only [rawAdj,not_false_eq_true]
    | some x =>
      cases h : decode x with
      | none => simp only [rawAdj,h,not_false_eq_true]
      | some v => cases v <;> simp only [rawAdj,h,slotAdj,G.irrefl,not_false_eq_true]⟩

noncomputable def rawEquiv [Fintype U] (decode : U → Option (Slot V count))
    (h : ∀ v, ∃!u,decode u=some v) :
    Option U ≃ Vertex V count (Fintype.card {u // decode u=none}) := by
  classical
  let pre : Slot V count → U := fun v => (h v).exists.choose
  have hp (v) : decode (pre v)=some v := (h v).exists.choose_spec
  have hi (v) (u) (hu : decode u=some v) : pre v=u := (h v).unique (hp v) hu
  let holes := Fintype.equivFin {u // decode u=none}
  let enc : Option U → Vertex V count (Fintype.card {u // decode u=none}) := fun x =>
    match x with
    | none => .hub
    | some u => if he : decode u=none then .pad (holes ⟨u,he⟩) else
        match decode u with
        | none => .hub
        | some (.inl v) => .base v
        | some (.inr v) => .mark v.1 v.2
  let dec : Vertex V count (Fintype.card {u // decode u=none}) → Option U := fun v =>
    match v with
    | .base v => some (pre (.inl v))
    | .mark v i => some (pre (.inr ⟨v,i⟩))
    | .hub => none
    | .pad i => some (holes.symm i).val
  exact {
    toFun := enc
    invFun := dec
    left_inv := by
      intro x; cases x with
      | none => rfl
      | some u =>
        cases he : decode u with
        | none => simp only [enc,he,↓reduceDIte,dec,Equiv.symm_apply_apply]
        | some v =>
          cases v with
          | inl v => simp only [enc,he,reduceCtorEq,↓reduceDIte,dec,hi _ _ he]
          | inr v => simp only [enc,he,reduceCtorEq,↓reduceDIte,dec,hi _ _ he]
    right_inv := by
      intro v; cases v with
      | hub => rfl
      | base v => simp only [dec,enc,hp,reduceCtorEq,↓reduceDIte]
      | mark v i => simp only [dec,enc,hp,reduceCtorEq,↓reduceDIte]
      | pad i =>
        have he := (holes.symm i).property
        simp only [dec,enc,he,↓reduceDIte]
        congr 1
        exact holes.apply_symm_apply i }

end WLTime.Marking

namespace WLTime.Marking

variable {D : Type uD} {V : Type uV} {p : D → Prop} {count : V → ℕ}

noncomputable def decodeSlots (e : {d // p d} ≃ V) (L q : ℕ) :
    (D × Fin L) ⊕ Fin q → Option (Slot V count) := by
  classical
  exact fun u => match u with
    | .inr _ => none
    | .inl (d,j) => if hd : p d then
        if j.val=0 then some (.inl (e ⟨d,hd⟩)) else
        if hj : j.val-1<count (e ⟨d,hd⟩) then some (.inr ⟨e ⟨d,hd⟩,⟨j.val-1,hj⟩⟩)
        else none
      else none

end WLTime.Marking

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Circuits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uB uG uE uAlphabet uJ

namespace WLTime.CircuitEncoding
abbrev Bit := ZMod 2

def zeroSet {d : ℕ} (f : Fin d → Prop) : Set (Fin d → Bit) :=
  {x | ∀ i, f i → x i = 0}

theorem zeroSet_nonempty {d : ℕ} (f : Fin d → Prop) : (zeroSet f).Nonempty :=
  ⟨0,fun _ _ => rfl⟩

theorem image_singleton_of_forall {A : Type uA} {B : Type uB} {S : Set A} (hS : S.Nonempty)
    (f : A → B) (b : B) (h : ∀ x ∈ S, f x=b) : f '' S = {b} := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact h x hx
  · rintro _ rfl
    obtain ⟨x,hx⟩ := hS
    exact ⟨x,hx,h x hx⟩

open scoped Classical in
theorem zeroSet_coord_image {d : ℕ} (f : Fin d → Prop) (i : Fin d) :
    (fun x : Fin d → Bit => x i) '' zeroSet f = if f i then {0} else Set.univ := by
  by_cases hi : f i
  · rw [ite_eq_left hi]
    exact image_singleton_of_forall (zeroSet_nonempty f) _ _ (fun _ hx => hx i hi)
  · rw [ite_eq_right hi]
    apply Set.eq_univ_of_forall
    intro b
    refine ⟨Function.update (fun _ => 0) i b,?_,Function.update_self _ _ _⟩
    intro j hj
    apply Function.update_of_ne
    intro h
    exact hi (h ▸ hj)

open scoped Classical in
theorem zeroSet_sum_image {d : ℕ} (f : Fin d → Prop) :
    (fun x : Fin d → Bit => ∑ i,x i) '' zeroSet f =
      if ∀ i,f i then {0} else Set.univ := by
  by_cases hf : ∀ i,f i
  · rw [ite_eq_left hf]
    apply image_singleton_of_forall (zeroSet_nonempty f)
    intro x hx
    simp only [hx _ (hf _),Finset.sum_const_zero]
  · rw [ite_eq_right hf]
    push Not at hf
    obtain ⟨i,hi⟩ := hf
    apply Set.eq_univ_of_forall
    intro b
    refine ⟨Function.update (fun _ => 0) i b,?_,?_⟩
    · intro j hj
      apply Function.update_of_ne
      intro h
      exact hi (h ▸ hj)
    · simp [Finset.sum_update_of_mem]

def diode (D : Set Bit) : Set (Fin 2 → Bit) := {z | z 0 + z 1 ∈ D}

theorem diode_nonempty {D : Set Bit} (hD : D.Nonempty) : (diode D).Nonempty := by
  obtain ⟨d,hd⟩ := hD
  exact ⟨![0,d],by simpa [diode] using hd⟩

theorem diode_coord_image {D : Set Bit} (hD : D.Nonempty) (i : Fin 2) :
    (fun z : Fin 2 → Bit => z i) '' diode D = Set.univ := by
  obtain ⟨d,hd⟩ := hD
  apply Set.eq_univ_of_forall
  intro a
  fin_cases i
  · refine ⟨![a,d-a],?_,by simp⟩
    simpa [diode,add_sub_cancel_left] using hd
  · refine ⟨![d-a,a],?_,by simp⟩
    simpa [diode] using hd

theorem diode_sum_image {D : Set Bit} :
    (fun z : Fin 2 → Bit => z 0+z 1) '' diode D = D := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z,hz,rfl⟩; exact hz
  · intro a ha
    exact ⟨![0,a],by simpa [diode] using ha,by simp⟩

inductive Kind where
  | scalar | both
  deriving DecidableEq

def Kind.dim : Kind → ℕ
  | .scalar => 1
  | .both => 2

theorem Kind.dim_pos (k : Kind) : 0 < k.dim := by cases k <;> decide

structure Circuit (G : Type uG) (E : Type uE) where
  kind : G → Kind
  src : E → G
  dst : E → G
  port : (e : E) → Fin (kind (dst e)).dim
  rank : G → ℕ
  forward : ∀ e, rank (src e) < rank (dst e)
  seed : G → Bool
  test : G → Bool
  seed_scalar : ∀ g, seed g = true → kind g = .scalar
  test_scalar : ∀ g, test g = true → kind g = .scalar
  test_terminal : ∀ e, test (src e) = false

namespace Circuit
variable {G : Type uG} {E : Type uE} (C : Circuit G E)

def TrueAt (g : G) : Prop :=
  if C.kind g = .scalar then C.seed g = true ∨ ∃ (e : E) (_h : C.dst e=g), TrueAt (C.src e)
  else ∀ p : Fin (C.kind g).dim,
    ∃ (e : E) (_h : C.dst e=g), (C.port e).val = p.val ∧ TrueAt (C.src e)
termination_by C.rank g
decreasing_by
  all_goals
    subst g
    exact C.forward _

def PortTrue (g : G) (p : ℕ) : Prop :=
  ∃ e, C.dst e=g ∧ (C.port e).val=p ∧ C.TrueAt (C.src e)

def Forced (g : G) (i : Fin (C.kind g).dim) : Prop :=
  if C.kind g = .scalar then C.TrueAt g else C.PortTrue g i.val

abbrev Value (g : G) := Fin (C.kind g).dim → Bit

def output (g : G) (x : C.Value g) : Bit := ∑ i,x i

structure Witness where
  gate : (g : G) → Set (C.Value g)
  buffer : E → Set (Fin 2 → Bit)
  gate_nonempty : ∀ g, (gate g).Nonempty
  buffer_nonempty : ∀ e, (buffer e).Nonempty
  first : ∀ e, C.output (C.src e) '' gate (C.src e) = (fun z => z 0) '' buffer e
  second : ∀ e, C.output (C.src e) '' gate (C.src e) = (fun z => z 1) '' buffer e
  third : ∀ e, (fun z => z 0+z 1) '' buffer e = (fun x => x (C.port e)) '' gate (C.dst e)
  seeds : ∀ g, C.seed g = true → C.output g '' gate g = {0}
  tests : ∀ g, C.test g = true → C.output g '' gate g = {1}

end Circuit
end WLTime.CircuitEncoding

namespace WLTime.CircuitEncoding.Circuit
variable {G : Type uG} {E : Type uE} (C : Circuit G E)

theorem all_forced_iff (g : G) : (∀ i,C.Forced g i) ↔ C.TrueAt g := by
  by_cases hs : C.kind g = .scalar
  · simp only [Forced,ite_eq_left hs]
    exact ⟨fun h => h ⟨0,(C.kind g).dim_pos⟩,fun h _ => h⟩
  · rw [TrueAt]
    simp only [hs,ite_false,Forced,PortTrue,exists_prop]

theorem port_true_forced (g : G) (p : Fin (C.kind g).dim)
    (h : C.PortTrue g p.val) : C.Forced g p := by
  by_cases hs : C.kind g = .scalar
  · simp only [Forced,ite_eq_left hs]
    rw [TrueAt,ite_eq_left hs]
    obtain ⟨e,he,_,ht⟩ := h
    exact Or.inr ⟨e,he,ht⟩
  · simpa only [Forced,ite_eq_right hs] using h

theorem true_of_seed (g : G) (h : C.seed g = true) : C.TrueAt g := by
  rw [TrueAt,ite_eq_left (C.seed_scalar g h)]
  exact Or.inl h

theorem output_scalar_eq_port (g : G) (hs : C.kind g = .scalar)
    (p : Fin (C.kind g).dim) (x : C.Value g) : C.output g x = x p := by
  classical
  apply Finset.sum_eq_single p
  · intro i _ hip
    exfalso
    apply hip
    apply Fin.ext
    have hi := i.isLt
    have hp := p.isLt
    simp only [hs,Kind.dim] at hi hp
    omega
  · simp

open scoped Classical in
noncomputable def canonicalGate (g : G) : Set (C.Value g) :=
  if C.test g = true then {fun _ => 1} else zeroSet (C.Forced g)

theorem canonicalGate_nonempty (g : G) : (C.canonicalGate g).Nonempty := by
  classical
  unfold canonicalGate
  split_ifs
  · exact Set.singleton_nonempty _
  · exact zeroSet_nonempty _

open scoped Classical in
theorem canonicalGate_output (g : G) :
    C.output g '' C.canonicalGate g =
      if C.test g = true then {1} else if C.TrueAt g then {0} else Set.univ := by
  by_cases ht : C.test g = true
  · rw [canonicalGate,ite_eq_left ht,ite_eq_left ht,Set.image_singleton]
    congr 1
    exact C.output_scalar_eq_port g (C.test_scalar g ht) ⟨0,(C.kind g).dim_pos⟩ _
  · rw [canonicalGate,ite_eq_right ht,ite_eq_right ht]
    exact (zeroSet_sum_image (C.Forced g)).trans (by simp only [C.all_forced_iff])

theorem canonicalGate_port_true
    (hT : ∀ g, C.test g = true → ¬C.TrueAt g) (g : G) (p : Fin (C.kind g).dim)
    (hp : C.PortTrue g p.val) :
    (fun x => x p) '' C.canonicalGate g = {0} := by
  classical
  have hf := C.port_true_forced g p hp
  have ht : C.test g ≠ true := by
    intro ht
    have hs := C.test_scalar g ht
    simp only [Forced,ite_eq_left hs] at hf
    exact hT g ht hf
  rw [canonicalGate,ite_eq_right ht,zeroSet_coord_image,ite_eq_left hf]

open scoped Classical in
noncomputable def canonicalBuffer (e : E) : Set (Fin 2 → Bit) :=
  if C.TrueAt (C.src e) then {0}
  else diode ((fun x => x (C.port e)) '' C.canonicalGate (C.dst e))

theorem canonicalBuffer_nonempty (e : E) : (C.canonicalBuffer e).Nonempty := by
  classical
  unfold canonicalBuffer
  split_ifs
  · exact Set.singleton_nonempty _
  · exact diode_nonempty ((C.canonicalGate_nonempty _).image _)

theorem canonicalBuffer_coord (e : E) (i : Fin 2) :
    (fun z => z i) '' C.canonicalBuffer e = C.output (C.src e) '' C.canonicalGate (C.src e) := by
  classical
  rw [C.canonicalGate_output,C.test_terminal]
  simp only [Bool.false_eq_true,ite_false]
  by_cases ht : C.TrueAt (C.src e)
  · simp [canonicalBuffer,ht]
  · rw [canonicalBuffer,ite_eq_right ht,ite_eq_right ht]
    exact diode_coord_image ((C.canonicalGate_nonempty _).image _) i

theorem canonicalBuffer_sum (hT : ∀ g, C.test g = true → ¬C.TrueAt g) (e : E) :
    (fun z => z 0+z 1) '' C.canonicalBuffer e =
      (fun x => x (C.port e)) '' C.canonicalGate (C.dst e) := by
  classical
  by_cases ht : C.TrueAt (C.src e)
  · rw [canonicalBuffer,ite_eq_left ht]
    rw [C.canonicalGate_port_true hT _ _ ⟨e,rfl,rfl,ht⟩]
    simp
  · rw [canonicalBuffer,ite_eq_right ht,diode_sum_image]

noncomputable def canonicalWitness (hT : ∀ g, C.test g = true → ¬C.TrueAt g) : C.Witness where
  gate := C.canonicalGate
  buffer := C.canonicalBuffer
  gate_nonempty := C.canonicalGate_nonempty
  buffer_nonempty := C.canonicalBuffer_nonempty
  first e := (C.canonicalBuffer_coord e 0).symm
  second e := (C.canonicalBuffer_coord e 1).symm
  third := C.canonicalBuffer_sum hT
  seeds := by
    intro g hg
    rw [C.canonicalGate_output]
    have htrue := C.true_of_seed g hg
    have htest : C.test g ≠ true := fun h => hT g h htrue
    rw [ite_eq_right htest,ite_eq_left htrue]
  tests := by intro g hg; rw [C.canonicalGate_output,ite_eq_left hg]

end WLTime.CircuitEncoding.Circuit

namespace WLTime.CircuitEncoding.Tableau
variable {Alphabet : Type uAlphabet} {J : Type uJ} (F : Alphabet → Alphabet → Alphabet → Alphabet) (shift : Equiv.Perm J) (initial : J → Alphabet)

def update (x : J → Alphabet) : J → Alphabet := fun j => F (x (shift.symm j)) (x j) (x (shift j))
def run : ℕ → J → Alphabet
  | 0 => initial
  | t+1 => update F shift (run t)

@[simp] theorem run_zero : run F shift initial 0 = initial := rfl
@[simp] theorem run_succ (t : ℕ) (j : J) : run F shift initial (t+1) j =
    F (run F shift initial t (shift.symm j)) (run F shift initial t j)
      (run F shift initial t (shift j)) := rfl

inductive Gate (Alphabet : Type uAlphabet) where
  | scalar (f : Alphabet)
  | first (a b c : Alphabet)
  | second (a b c : Alphabet)
  deriving DecidableEq, Fintype

abbrev Node (Alphabet : Type uAlphabet) (J : Type uJ) (H : ℕ) := Gate Alphabet × Fin H × J

def Gate.kind : Gate Alphabet → Kind
  | .scalar _ => .scalar
  | _ => .both

def Gate.phase : Gate Alphabet → ℕ
  | .scalar _ => 2
  | .first _ _ _ => 0
  | .second _ _ _ => 1

def prevTime {H : ℕ} (t : Fin H) (ht : 0<t.val) : Fin H := ⟨t.val-1,by omega⟩

inductive Connection (Alphabet : Type uAlphabet) (J : Type uJ) (H : ℕ) where
  | left (a b c : Alphabet) (t : Fin H) (ht : 0<t.val) (j : J)
  | center (a b c : Alphabet) (t : Fin H) (ht : 0<t.val) (j : J)
  | bridge (a b c : Alphabet) (t : Fin H) (j : J)
  | right (a b c : Alphabet) (t : Fin H) (ht : 0<t.val) (j : J)
  | out (a b c : Alphabet) (t : Fin H) (j : J)

variable {H : ℕ}

def source : Connection Alphabet J H → Node Alphabet J H
  | .left a _ _ t ht j => (.scalar a,prevTime t ht,shift.symm j)
  | .center _ b _ t ht j => (.scalar b,prevTime t ht,j)
  | .bridge a b c t j => (.first a b c,t,j)
  | .right _ _ c t ht j => (.scalar c,prevTime t ht,shift j)
  | .out a b c t j => (.second a b c,t,j)

def target : Connection Alphabet J H → Node Alphabet J H
  | .left a b c t _ j => (.first a b c,t,j)
  | .center a b c t _ j => (.first a b c,t,j)
  | .bridge a b c t j => (.second a b c,t,j)
  | .right a b c t _ j => (.second a b c,t,j)
  | .out a b c t j => (.scalar (F a b c),t,j)

def port : (e : Connection Alphabet J H) → Fin (target F e).1.kind.dim
  | .left _ _ _ _ _ _ => (0 : Fin 2)
  | .center _ _ _ _ _ _ => (1 : Fin 2)
  | .bridge _ _ _ _ _ => (0 : Fin 2)
  | .right _ _ _ _ _ _ => (1 : Fin 2)
  | .out _ _ _ _ _ => (0 : Fin 1)

def rank (g : Node Alphabet J H) : ℕ := 3*g.2.1.val+g.1.phase

theorem forward (e : Connection Alphabet J H) : rank (source shift e) < rank (target F e) := by
  cases e <;> simp only [source,target,rank,Gate.phase,prevTime] <;> omega

open scoped Classical in
noncomputable def seed (g : Node Alphabet J H) : Bool := match g.1 with
  | .scalar f => decide (g.2.1.val=0 ∧ f=initial g.2.2)
  | _ => false

open scoped Classical in
noncomputable def test (accepting : Alphabet → Prop) (g : Node Alphabet J H) : Bool := match g.1 with
  | .scalar f => decide (g.2.1.val+1=H ∧ accepting f)
  | _ => false

open scoped Classical in
noncomputable def circuit (accepting : Alphabet → Prop) : Circuit (Node Alphabet J H) (Connection Alphabet J H) where
  kind g := g.1.kind
  src := source shift
  dst := target F
  port := port F
  rank := rank
  forward := forward F shift
  seed := seed initial
  test := test accepting
  seed_scalar := by rintro ⟨g,t,j⟩; cases g <;> simp [seed,Gate.kind]
  test_scalar := by rintro ⟨g,t,j⟩; cases g <;> simp [test,Gate.kind]
  test_terminal := by
    intro e
    cases e <;> simp [source,test,prevTime]
    all_goals
      apply decide_eq_false
      rintro ⟨he,_⟩
      omega

def expected (g : Node Alphabet J H) : Prop := match g.1 with
  | .scalar f => f=run F shift initial g.2.1.val g.2.2
  | .first a b _ => 0<g.2.1.val ∧
      a=run F shift initial (g.2.1.val-1) (shift.symm g.2.2) ∧
      b=run F shift initial (g.2.1.val-1) g.2.2
  | .second a b c => 0<g.2.1.val ∧
      a=run F shift initial (g.2.1.val-1) (shift.symm g.2.2) ∧
      b=run F shift initial (g.2.1.val-1) g.2.2 ∧
      c=run F shift initial (g.2.1.val-1) (shift g.2.2)

end WLTime.CircuitEncoding.Tableau

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Turing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uJ

namespace WLTime

structure OneTape where
  states : ℕ
  symbols : ℕ
  states_ge : 3  ≤  states
  symbols_ge : 3  ≤  symbols
  transition : Fin states → Fin symbols → Fin states × Fin symbols × Move

namespace OneTape
variable (M : OneTape)
open scoped Classical

abbrev Cell := Fin M.symbols × Option (Fin M.states)

def action (q : Fin M.states) (s : Fin M.symbols) : Fin M.states × Fin M.symbols × Move :=
  if q.val=1 ∨ q.val=2 then (q,s,.stay) else M.transition q s

structure Config (J : Type uJ) where
  state : Fin M.states
  head : J
  tape : J → Fin M.symbols

def moveAt {J : Type uJ} (shift : Equiv.Perm J) : Move → J → J
  | .left => shift.symm
  | .stay => id
  | .right => shift

open scoped Classical in
noncomputable def step {J : Type uJ} (shift : Equiv.Perm J) (C : M.Config J) : M.Config J :=
  let a := M.action C.state (C.tape C.head)
  { state := a.1
    head := moveAt shift a.2.2 C.head
    tape := Function.update C.tape C.head a.2.1 }

open scoped Classical in
noncomputable def snapshot {J : Type uJ} (C : M.Config J) (j : J) : M.Cell :=
  (C.tape j,if j=C.head then some C.state else none)

def written (c : M.Cell) : Fin M.symbols := match c.2 with
  | none => c.1
  | some q => (M.action q c.1).2.1

def arrival (d : Move) (c : M.Cell) : Option (Fin M.states) := match c.2 with
  | none => none
  | some q => if (M.action q c.1).2.2=d then some (M.action q c.1).1 else none

def localRule (l c r : M.Cell) : M.Cell :=
  (M.written c,(M.arrival .stay c).or (M.arrival .right l) |>.or (M.arrival .left r))

variable {J : Type uJ}

noncomputable def run {J : Type uJ} (shift : Equiv.Perm J) (C : M.Config J) (t : ℕ) : M.Config J :=
  (M.step shift)^[t] C

def toTM : TM where
  tapes := 1
  states := M.states
  symbols := M.symbols
  tapes_pos := by decide
  states_ge := M.states_ge
  symbols_ge := M.symbols_ge
  transition q a := let b := M.transition q (a 0)
    (b.1,fun _ => b.2.1,fun _ => b.2.2)

def embed (C : M.Config ℤ) : M.toTM.Config where
  state := C.state
  head := fun _ => C.head
  tape := fun _ => C.tape

def lineShift : Equiv.Perm ℤ := Equiv.addRight 1

def initial (w : List Bool) : M.Config ℤ where
  state := ⟨0,by have := M.states_ge; omega⟩
  head := 0
  tape z := if 0 ≤ z ∧ z.toNat< w.length then
    M.toTM.symbol (w.getD z.toNat false) else ⟨0,by have := M.symbols_ge; omega⟩

@[simp] theorem embed_initial (w : List Bool) : M.embed (M.initial w)=M.toTM.initial w := by
  unfold embed initial TM.initial
  congr 1
  funext a z
  have ha : a.val=0 := Fin.eq_zero a ▸ rfl
  simp only [ha,true_and]
  split <;> rename_i hz <;> simp [hz] <;> rfl

def Agrees {J : Type uJ} (π : ℤ → J) (I : Set ℤ) (C : M.Config ℤ) (D : M.Config J) : Prop :=
  D.state=C.state ∧ D.head=π C.head ∧ ∀ z∈I,D.tape (π z)=C.tape z

def protectedInterval (m T : ℕ) : Set ℤ := Set.Icc (-(T:ℤ)-1) ((m:ℤ)+T)

def ringShift (L : ℕ) : Equiv.Perm (ZMod L) := Equiv.addRight 1

noncomputable def ringInitial (L : ℕ) (w : List Bool) : M.Config (ZMod L) where
  state := ⟨0,by have := M.states_ge; omega⟩
  head := 0
  tape j := if j.val< w.length then M.toTM.symbol (w.getD j.val false)
    else ⟨0,by have := M.symbols_ge; omega⟩

def letterAccepting (c : M.Cell) : Prop := ∃ q,c.2=some q ∧ q.val=1

end OneTape
end WLTime

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Stacks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uS uA

namespace WLTime.StackMachine

inductive Command (K a q : ℕ) where
  | next (state : Fin q)
  | push (stack : Fin K) (letter : Fin a) (state : Fin q)
  | pop (stack : Fin K) (state : Fin q)
  | halt (answer : Bool)

structure Machine where
  count : ℕ
  alphabet : ℕ
  states : ℕ
  count_pos : 0< count
  alphabet_ge : 2 ≤ alphabet
  initial : Fin states
  transition : Fin states → (Fin count → Option (Fin alphabet)) →
    Command count alphabet states

namespace Machine
variable (M : Machine)

structure Config where
  state : Bool ⊕ Fin M.states
  stack : Fin M.count → List (Fin M.alphabet)

 def inputLetter (b : Bool) : Fin M.alphabet := ⟨if b then 1 else 0,by have := M.alphabet_ge; split <;> omega⟩

 def initialConfig (w : List Bool) : M.Config where
  state := .inr M.initial
  stack k := if k.val=0 then w.map M.inputLetter else []

 def perform (C : M.Config) (a : Command M.count M.alphabet M.states) : M.Config := match a with
  | .next q => { C with state := .inr q }
  | .push k x q => { state := .inr q,stack := Function.update C.stack k (x::C.stack k) }
  | .pop k q => { state := .inr q,stack := Function.update C.stack k (C.stack k).tail }
  | .halt b => {C with state := .inl b}

 def step (C : M.Config) : M.Config := match C.state with
  | .inl _ => C
  | .inr q => M.perform C (M.transition q (fun k => (C.stack k).head?))

 def run (w : List Bool) (t : ℕ) : M.Config := M.step^[t] (M.initialConfig w)

 def encodeLetter : Option (Fin M.alphabet) → Fin (M.alphabet+1)
  | none => 0
  | some x => x.succ

 def decodeLetter (x : Fin (M.alphabet+1)) : Option (Fin M.alphabet) :=
   Fin.cases none some x

@[simp] theorem decode_encode (x : Option (Fin M.alphabet)) : M.decodeLetter (M.encodeLetter x)=x := by
  cases x <;> rfl

 def contents (s : List (Fin M.alphabet)) (h z : ℤ) : Fin (M.alphabet+1) :=
  if z<h then 0 else M.encodeLetter s[(z-h).toNat]?

@[simp] theorem contents_empty (h z : ℤ) : M.contents [] h z=0 := by
  simp only [contents,List.getElem?_nil,encodeLetter,ite_self]

@[simp] theorem contents_head (s : List (Fin M.alphabet)) (h : ℤ) :
    M.contents s h h=M.encodeLetter s.head? := by
  simp only [contents,lt_self_iff_false,ite_false,sub_self,Int.toNat_zero]
  exact congrArg M.encodeLetter (List.head?_eq_getElem? (l:=s)).symm

abbrev Micro := Fin 3 ⊕ (Fin M.states ⊕ (Fin M.count × Fin M.alphabet × Fin M.states))

noncomputable def microEquiv : M.Micro ≃ Fin (3+Fintype.card (Fin M.states ⊕
    (Fin M.count × Fin M.alphabet × Fin M.states))) :=
  (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFin _)).trans finSumFinEquiv

@[simp] theorem micro_left (i : Fin 3) : (M.microEquiv (.inl i)).val=i.val := rfl

 def microTransition (p : M.Micro) (read : Fin M.count → Fin (M.alphabet+1)) :
    M.Micro × (Fin M.count → Fin (M.alphabet+1)) × (Fin M.count → Move) := match p with
  | .inl i => ((if i.val=0 then .inr (.inl M.initial) else .inl i),read,fun _ => .stay)
  | .inr (.inr (k,x,q)) => (.inr (.inl q),Function.update read k x.succ,fun _ => .stay)
  | .inr (.inl q) => match M.transition q (fun k => M.decodeLetter (read k)) with
    | .next q' => (.inr (.inl q'),read,fun _ => .stay)
    | .push k x q' => (.inr (.inr (k,x,q')),read,Function.update (fun _ => .stay) k .left)
    | .pop k q' => (.inr (.inl q'),Function.update read k 0,Function.update (fun _ => .stay) k .right)
    | .halt b => (.inl (if b then 1 else 2),read,fun _ => .stay)

noncomputable abbrev compile : TM where
  tapes := M.count
  states := 3+Fintype.card (Fin M.states ⊕ (Fin M.count × Fin M.alphabet × Fin M.states))
  symbols := M.alphabet+1
  tapes_pos := M.count_pos
  states_ge := by omega
  symbols_ge := by have := M.alphabet_ge; omega
  transition q read := let a := M.microTransition (M.microEquiv.symm q) read
    (M.microEquiv a.1,a.2)

noncomputable def stateCode : Bool ⊕ Fin M.states → Fin M.compile.states
  | .inl b => M.microEquiv (.inl (if b then 1 else 2))
  | .inr q => M.microEquiv (.inr (.inl q))

noncomputable def embed (C : M.Config) (h : Fin M.count → ℤ) : M.compile.Config where
  state := M.stateCode C.state
  head := h
  tape k := M.contents (C.stack k) (h k)

end Machine
end WLTime.StackMachine

namespace WLTime.TypedTape

abbrev State (S : Type uS) := Fin 3 ⊕ S
abbrev Symbol (A : Type uA) := Fin 3 ⊕ A

structure Machine (S : Type uS) (A : Type uA) where
  transition : State S → Symbol A → State S × Symbol A × Move

structure Config (S : Type uS) (A : Type uA) where
  state : State S
  head : ℤ
  tape : ℤ → Symbol A

namespace Machine
variable {S : Type uS} {A : Type uA} (M : Machine S A)

 def halted (_M : Machine S A) (p : State S) : Prop := p = .inl 1 ∨ p = .inl 2

instance instDecidableHalted (p : State S) : Decidable (M.halted p) := by
  cases p with
  | inl i => exact decidable_of_iff (i=1 ∨ i=2) (by simp [halted])
  | inr q => exact isFalse (by simp [halted])

 def action (p : State S) (x : Symbol A) : State S × Symbol A × Move :=
  if M.halted p then (p,x,.stay) else M.transition p x

 def step (C : Config S A) : Config S A :=
  let a := M.action C.state (C.tape C.head)
  { state := a.1
    head := C.head+a.2.2.displacement
    tape := Function.update C.tape C.head a.2.1 }

 def initial (_M : Machine S A) (w : List Bool) : Config S A where
  state := .inl 0
  head := 0
  tape z := if 0 ≤ z ∧ z.toNat<w.length then
    .inl (if w.getD z.toNat false then 2 else 1) else .inl 0

 def run (w : List Bool) (t : ℕ) := M.step^[t] (M.initial w)

variable [Fintype S] [Fintype A]

noncomputable def stateEquiv (_M : Machine S A) : State S ≃ Fin (3+Fintype.card S) :=
  (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFin S)).trans finSumFinEquiv

noncomputable def symbolEquiv (_M : Machine S A) : Symbol A ≃ Fin (3+Fintype.card A) :=
  (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFin A)).trans finSumFinEquiv

omit [Fintype A] in
@[simp] theorem state_left (i : Fin 3) : (M.stateEquiv (.inl i)).val=i.val := rfl
omit [Fintype S] in
@[simp] theorem symbol_left (i : Fin 3) : (M.symbolEquiv (.inl i)).val=i.val := rfl

noncomputable abbrev compile : OneTape where
  states := 3+Fintype.card S
  symbols := 3+Fintype.card A
  states_ge := by omega
  symbols_ge := by omega
  transition p x := let a := M.transition (M.stateEquiv.symm p) (M.symbolEquiv.symm x)
    (M.stateEquiv a.1,M.symbolEquiv a.2.1,a.2.2)

noncomputable def embed (C : Config S A) : M.compile.Config ℤ where
  state := M.stateEquiv C.state
  head := C.head
  tape z := M.symbolEquiv (C.tape z)

end Machine
end WLTime.TypedTape

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Sweep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLTime.StackMachine
namespace Machine
variable (M : Machine)

abbrev Tops := Fin M.count → Option (Fin M.alphabet)
abbrev TrackSymbol := Bool × M.Tops

inductive Purpose (K a q : ℕ) where
  | peek (k : Fin K) (state : Fin q) (tops : Fin K → Option (Fin a))
  | push (k : Fin K) (letter : Fin a) (state : Fin q)
  | pop (k : Fin K) (state : Fin q)
  deriving Fintype, DecidableEq

inductive SweepControl (K a q : ℕ) where
  | mark
  | seekEnd
  | take
  | bring (letter : Fin a)
  | append (letter : Fin a)
  | back
  | start (state : Fin q)
  | seek (purpose : Purpose K a q)
  | read (k : Fin K) (state : Fin q) (tops : Fin K → Option (Fin a))
  | returnPeek (k : Fin K) (state : Fin q) (tops : Fin K → Option (Fin a))
  | erase (k : Fin K) (state : Fin q)
  | ret (state : Fin q)
  deriving Fintype, DecidableEq

abbrev Control := SweepControl M.count M.alphabet M.states
abbrev Purpose' := Purpose M.count M.alphabet M.states
abbrev TapeSymbol := TypedTape.Symbol M.TrackSymbol
abbrev TapeState := TypedTape.State M.Control
abbrev TapeConfig := TypedTape.Config M.Control M.TrackSymbol

 def symbolTracks (_M : Machine) : _M.TapeSymbol → _M.Tops
  | .inl _ => fun _ => none
  | .inr x => x.2

 def symbolBottom (_M : Machine) : _M.TapeSymbol → Bool
  | .inl _ => false
  | .inr x => x.1

 def trackSymbol (bottom : Bool) (v : M.Tops) : M.TapeSymbol :=
  if bottom=false ∧ v=fun _ => none then .inl 0 else .inr (bottom,v)

@[simp] theorem tracks_trackSymbol (b : Bool) (v : M.Tops) :
    M.symbolTracks (M.trackSymbol b v)=v := by
  unfold trackSymbol
  split_ifs with h
  · simp only [symbolTracks,h.2]
  · rfl

@[simp] theorem bottom_trackSymbol (b : Bool) (v : M.Tops) :
    M.symbolBottom (M.trackSymbol b v)=b := by
  unfold trackSymbol
  split_ifs with h
  · exact h.1.symm
  · rfl

 def purposeStack (_M : Machine) : _M.Purpose' → Fin _M.count
  | .peek k _ _ => k
  | .push k _ _ => k
  | .pop k _ => k

 def dispatch (a : Command M.count M.alphabet M.states) (s : M.TapeSymbol) :
    M.TapeState × M.TapeSymbol × Move := match a with
  | .next q => (.inr (.start q),s,.stay)
  | .push k x q => (.inr (.seek (.push k x q)),s,.left)
  | .pop k q => (.inr (.seek (.pop k q)),s,.left)
  | .halt b => (.inl (if b then 1 else 2),s,.stay)

 def finishPeek (k : Fin M.count) (q : Fin M.states) (v : M.Tops) (s : M.TapeSymbol) :
    M.TapeState × M.TapeSymbol × Move :=
  if h : k.val+1<M.count then (.inr (.seek (.peek ⟨k.val+1,h⟩ q v)),s,.left)
  else M.dispatch (M.transition q v) s

 def sweepTransition (p : M.TapeState) (s : M.TapeSymbol) :
    M.TapeState × M.TapeSymbol × Move := match p with
  | .inl i => if i.val=0 then (.inr .mark,s,.left) else (.inl i,s,.stay)
  | .inr .mark => (.inr .seekEnd,M.trackSymbol true (fun _ => none),.right)
  | .inr .seekEnd => if s=.inl 1 ∨ s=.inl 2 then (.inr .seekEnd,s,.right)
      else (.inr .take,s,.left)
  | .inr .take => if M.symbolBottom s then (.inr (.start M.initial),s,.stay)
      else (.inr (.bring (M.inputLetter (s=.inl 2))),.inl 0,.left)
  | .inr (.bring x) => if M.symbolBottom s then (.inr (.append x),s,.left)
      else (.inr (.bring x),s,.left)
  | .inr (.append x) => if (M.symbolTracks s ⟨0,M.count_pos⟩).isSome then
      (.inr (.append x),s,.left)
      else (.inr .back,M.trackSymbol (M.symbolBottom s)
        (Function.update (M.symbolTracks s) ⟨0,M.count_pos⟩ (some x)),.right)
  | .inr .back => if M.symbolBottom s then (.inr .seekEnd,s,.right)
      else (.inr .back,s,.right)
  | .inr (.start q) => (.inr (.seek (.peek ⟨0,M.count_pos⟩ q (fun _ => none))),s,.left)
  | .inr (.seek purpose) => if (M.symbolTracks s (M.purposeStack purpose)).isSome then
      (.inr (.seek purpose),s,.left)
      else match purpose with
      | .peek k q v => (.inr (.read k q v),s,.right)
      | .push k x q => (.inr (.ret q),M.trackSymbol (M.symbolBottom s)
          (Function.update (M.symbolTracks s) k (some x)),.right)
      | .pop k q => (.inr (.erase k q),s,.right)
  | .inr (.read k q v) => let v' := Function.update v k (M.symbolTracks s k)
      (.inr (.returnPeek k q v'),s,.stay)
  | .inr (.returnPeek k q v) => if M.symbolBottom s then M.finishPeek k q v s
      else (.inr (.returnPeek k q v),s,.right)
  | .inr (.erase k q) => if M.symbolBottom s then (.inr (.start q),s,.stay)
      else (.inr (.ret q),M.trackSymbol (M.symbolBottom s)
        (Function.update (M.symbolTracks s) k none),.right)
  | .inr (.ret q) => if M.symbolBottom s then (.inr (.start q),s,.stay)
      else (.inr (.ret q),s,.right)

 def sweep : TypedTape.Machine M.Control M.TrackSymbol := ⟨M.sweepTransition⟩

 def stackCell (_M : Machine) (s : List (Fin _M.alphabet)) (i : ℕ) : Option (Fin _M.alphabet) :=
  s.reverse[i]?

 def storageTracks (s : Fin M.count → List (Fin M.alphabet)) (z : ℤ) : M.Tops :=
  if z < -1 then fun k => M.stackCell (s k) (-z-2).toNat else fun _ => none

 def storage (s : Fin M.count → List (Fin M.alphabet)) (z : ℤ) : M.TapeSymbol :=
  M.trackSymbol (decide (z=-1)) (M.storageTracks s z)

@[simp] theorem storage_bottom (s : Fin M.count → List (Fin M.alphabet)) (z : ℤ) :
    M.symbolBottom (M.storage s z)=decide (z=-1) := by simp [storage]

@[simp] theorem storage_tracks (s : Fin M.count → List (Fin M.alphabet)) (z : ℤ) :
    M.symbolTracks (M.storage s z)=M.storageTracks s z := by simp [storage]

@[simp] theorem storage_origin (s : Fin M.count → List (Fin M.alphabet)) :
    M.storage s (-1)=M.trackSymbol true (fun _ => none) := by
  simp [storage,storageTracks]

@[simp] theorem storageTracks_origin (s : Fin M.count → List (Fin M.alphabet)) :
    M.storageTracks s (-1)=(fun _ => none) := by simp [storageTracks]

@[simp] theorem storageTracks_index (s : Fin M.count → List (Fin M.alphabet)) (i : ℕ) :
    M.storageTracks s (-(i:ℤ)-2)= fun k => M.stackCell (s k) i := by
  have hi : -(i:ℤ)-2< -1 := by omega
  have he : (-(-(i:ℤ)-2)-2).toNat=i := by omega
  simp only [storageTracks,ite_eq_left hi,he]

 def located (_M : Machine) (p : _M.TapeState) (z : ℤ) (tape : ℤ → _M.TapeSymbol) : _M.TapeConfig :=
  ⟨p,z,tape⟩

 def sweepEmbed (C : M.Config) : M.TapeConfig :=
  M.located (match C.state with | .inl b => .inl (if b then 1 else 2) | .inr q => .inr (.start q))
    (-1) (M.storage C.stack)

 def partialTops (s : Fin M.count → List (Fin M.alphabet)) (i : ℕ) : M.Tops :=
  fun k => if k.val < i then (s k).head? else none

 def topTuple (_M : Machine) (s : Fin _M.count → List (Fin _M.alphabet)) : _M.Tops :=
  fun k => (s k).head?

 def dispatchLocation (a : Command M.count M.alphabet M.states)
    (s : Fin M.count → List (Fin M.alphabet)) : M.TapeConfig := match a with
  | .next q => M.located (.inr (.start q)) (-1) (M.storage s)
  | .push k x q => M.located (.inr (.seek (.push k x q))) (-2) (M.storage s)
  | .pop k q => M.located (.inr (.seek (.pop k q))) (-2) (M.storage s)
  | .halt b => M.located (.inl (if b then 1 else 2)) (-1) (M.storage s)

end Machine
end WLTime.StackMachine

end OAI
end

section
-- module Solutions.OAIQW_WLTime.TapeCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLTime.StackMachine
namespace Machine
variable (M : Machine)

 def inputStacks (w : List Bool) := (M.initialConfig w).stack
 def rawTape (w : List Bool) := (M.sweep.initial w).tape
 def mixed (u v : List Bool) (z : ℤ) : M.TapeSymbol :=
  if 0 ≤ z then M.rawTape u z else M.storage (M.inputStacks v) z

end Machine
end WLTime.StackMachine

namespace WLTime.StackMachine
namespace Machine
variable (M : Machine)

noncomputable abbrev oneTape : OneTape := M.sweep.compile

end Machine
end WLTime.StackMachine

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Programs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK uA uS uT

namespace WLTime.TypedStack

inductive Command (K : Type uK) (A : Type uA) (S : Type uS) where
  | next (q : S)
  | push (k : K) (x : A) (q : S)
  | pop (k : K) (q : S)
  | halt (b : Bool)

structure Machine (K : Type uK) (A : Type uA) (S : Type uS) where
  inputStack : K
  inputLetter : Bool → A
  initial : S
  transition : S → (K → Option A) → Command K A S

structure Config (K : Type uK) (A : Type uA) (S : Type uS) where
  state : Bool ⊕ S
  stack : K → List A

namespace Machine
variable {K : Type uK} {A : Type uA} {S : Type uS} [DecidableEq K] (M : Machine K A S)

 def perform (_M : Machine K A S) (C : Config K A S) (a : Command K A S) : Config K A S := match a with
  | .next q => { C with state := .inr q }
  | .push k x q => ⟨.inr q,Function.update C.stack k (x::C.stack k)⟩
  | .pop k q => ⟨.inr q,Function.update C.stack k (C.stack k).tail⟩
  | .halt b => { C with state := .inl b }
 def step (C : Config K A S) : Config K A S := match C.state with
  | .inl _ => C
  | .inr q => M.perform C (M.transition q (fun k => (C.stack k).head?))
 def initialConfig (w : List Bool) : Config K A S :=
  ⟨.inr M.initial,fun k => if k=M.inputStack then w.map M.inputLetter else []⟩
 def run (w : List Bool) (t : ℕ) := M.step^[t] (M.initialConfig w)

variable [Fintype K] [Fintype A] [Fintype S]

noncomputable def registerEquiv : K ≃ Fin (Fintype.card K) :=
  (Equiv.swap M.inputStack ((Fintype.equivFin K).symm ⟨0,Fintype.card_pos_iff.mpr ⟨M.inputStack⟩⟩)).trans
    (Fintype.equivFin K)
omit [Fintype A] [Fintype S] in
@[simp] theorem register_input : (M.registerEquiv M.inputStack).val=0 := by
  simp [registerEquiv]

noncomputable def decodeSymbol (x : Fin (2+Fintype.card A)) : A :=
  match finSumFinEquiv.symm x with
  | .inl b => M.inputLetter (b.val=1)
  | .inr a => (Fintype.equivFin A).symm a

noncomputable def encodeSymbol (_M : Machine K A S) (x : A) : Fin (2+Fintype.card A) :=
  finSumFinEquiv (.inr (Fintype.equivFin A x))

omit [Fintype K] [Fintype S] [DecidableEq K] in
@[simp] theorem decode_encode (x : A) : M.decodeSymbol (M.encodeSymbol x)=x := by
  simp [decodeSymbol,encodeSymbol]

noncomputable def encodeCommand : Command K A S →
    StackMachine.Command (Fintype.card K) (2+Fintype.card A) (Fintype.card S)
  | .next q => .next (Fintype.equivFin S q)
  | .push k x q => .push (M.registerEquiv k) (M.encodeSymbol x) (Fintype.equivFin S q)
  | .pop k q => .pop (M.registerEquiv k) (Fintype.equivFin S q)
  | .halt b => .halt b

noncomputable abbrev compile : StackMachine.Machine where
  count := Fintype.card K
  alphabet := 2+Fintype.card A
  states := Fintype.card S
  count_pos := Fintype.card_pos_iff.mpr ⟨M.inputStack⟩
  alphabet_ge := by omega
  initial := Fintype.equivFin S M.initial
  transition q v := M.encodeCommand
    (M.transition ((Fintype.equivFin S).symm q) (fun k => (v (M.registerEquiv k)).map M.decodeSymbol))

noncomputable def project (C : M.compile.Config) : Config K A S where
  state := C.state.map id (Fintype.equivFin S).symm
  stack k := (C.stack (M.registerEquiv k)).map M.decodeSymbol

end Machine
end WLTime.TypedStack

namespace WLTime.TypedStack
namespace Command
variable {K : Type uK} {A : Type uA} {S : Type uS} {T : Type uT}
 def rename (f : S → T) : Command K A S → Command K A T
  | .next q => .next (f q)
  | .push k x q => .push k x (f q)
  | .pop k q => .pop k (f q)
  | .halt b => .halt b
 def redirect (f : S → T) (r : T) : Command K A S → Command K A T
  | .next q => .next (f q)
  | .push k x q => .push k x (f q)
  | .pop k q => .pop k (f q)
  | .halt _ => .next r
end Command

variable {K : Type uK} {A : Type uA} {S : Type uS} {T : Type uT} [DecidableEq K]
abbrev Stacks (K : Type uK) (A : Type uA) := K → List A
abbrev Tops (K : Type uK) (A : Type uA) := K → Option A
 def tops (s : Stacks K A) : Tops K A := fun k => (s k).head?

inductive Execution (tr : S → Tops K A → Command K A S) :
    S → Stacks K A → ℕ → Bool → Stacks K A → Prop
  | halt {q s b} (h : tr q (tops s)=.halt b) : Execution tr q s 1 b s
  | next {q s q' t b out} (h : tr q (tops s)=.next q')
      (tail : Execution tr q' s t b out) : Execution tr q s (t+1) b out
  | push {q s k x q' t b out} (h : tr q (tops s)=.push k x q')
      (tail : Execution tr q' (Function.update s k (x::s k)) t b out) :
      Execution tr q s (t+1) b out
  | pop {q s k q' t b out} (h : tr q (tops s)=.pop k q')
      (tail : Execution tr q' (Function.update s k (s k).tail) t b out) :
      Execution tr q s (t+1) b out

inductive Code (K : Type uK) (A : Type uA) where
  | skip
  | push (k : K) (x : A)
  | pushDyn (k : K) (letter : Tops K A → A)
  | pop (k : K)
  | seq (left right : Code K A)
  | branch (test : Tops K A → Bool) (yes no : Code K A)
  | loop (test : Tops K A → Bool) (body : Code K A)

namespace Code
 @[reducible] def State : Code K A → Type
  | .skip => Unit
  | .push _ _ => Fin 2
  | .pushDyn _ _ => Fin 2
  | .pop _ => Fin 2
  | .seq a b => a.State ⊕ b.State
  | .branch _ a b => Unit ⊕ (a.State ⊕ b.State)
  | .loop _ a => Unit ⊕ a.State

noncomputable instance stateFintype (c : Code K A) : Fintype c.State := by
  induction c with
  | skip => exact inferInstanceAs (Fintype Unit)
  | push k x => exact inferInstanceAs (Fintype (Fin 2))
  | pushDyn k f => exact inferInstanceAs (Fintype (Fin 2))
  | pop k => exact inferInstanceAs (Fintype (Fin 2))
  | seq a b ha hb => exact inferInstanceAs (Fintype (a.State ⊕ b.State))
  | branch p a b ha hb => exact inferInstanceAs (Fintype (Unit ⊕ (a.State ⊕ b.State)))
  | loop p a ha => exact inferInstanceAs (Fintype (Unit ⊕ a.State))

 def entry : (c : Code K A) → c.State
  | .skip => ()
  | .push _ _ => 0
  | .pushDyn _ _ => 0
  | .pop _ => 0
  | .seq a _ => .inl a.entry
  | .branch _ _ _ => .inl ()
  | .loop _ _ => .inl ()

 def transition : (c : Code K A) → c.State → Tops K A → Command K A c.State
  | .skip,_,_ => .halt false
  | .push k x,q,_ => if q=0 then .push k x 1 else .halt false
  | .pushDyn k f,q,v => if q=0 then .push k (f v) 1 else .halt false
  | .pop k,q,_ => if q=0 then .pop k 1 else .halt false
  | .seq a b,.inl q,v => Command.redirect Sum.inl (.inr b.entry) (a.transition q v)
  | .seq _ b,.inr q,v => Command.rename Sum.inr (b.transition q v)
  | .branch p a b,.inl _,v => .next (if p v then .inr (.inl a.entry) else .inr (.inr b.entry))
  | .branch _ a _,.inr (.inl q),v => Command.rename (Sum.inr ∘ Sum.inl) (a.transition q v)
  | .branch _ _ b,.inr (.inr q),v => Command.rename (Sum.inr ∘ Sum.inr) (b.transition q v)
  | .loop p a,.inl _,v => if p v then .next (.inr a.entry) else .halt false
  | .loop _ a,.inr q,v => Command.redirect Sum.inr (.inl ()) (a.transition q v)

inductive Exec : Code K A → Stacks K A → ℕ → Stacks K A → Prop
  | skip (s) : Exec .skip s 1 s
  | push (s k x) : Exec (.push k x) s 2 (Function.update s k (x::s k))
  | pushDyn (s k f) : Exec (.pushDyn k f) s 2 (Function.update s k (f (tops s)::s k))
  | pop (s k) : Exec (.pop k) s 2 (Function.update s k (s k).tail)
  | seq {a b s mid out t u} (first : Exec a s t mid) (second : Exec b mid u out) :
      Exec (.seq a b) s (t+u) out
  | branch_true {p a b s t out} (test : p (tops s)=true) (body : Exec a s t out) :
      Exec (.branch p a b) s (t+1) out
  | branch_false {p a b s t out} (test : p (tops s)=false) (body : Exec b s t out) :
      Exec (.branch p a b) s (t+1) out
  | loop_false {p a s} (test : p (tops s)=false) : Exec (.loop p a) s 1 s
  | loop_true {p a s mid out t u} (test : p (tops s)=true)
      (body : Exec a s t mid) (rest : Exec (.loop p a) mid u out) :
      Exec (.loop p a) s (t+u+1) out

end Code
end WLTime.TypedStack

namespace WLTime.TypedStack.Code
variable {K : Type uK} {A : Type uA} [DecidableEq K]

 def nonempty (k : K) (v : Tops K A) : Bool := (v k).isSome
 def clear (k : K) : Code K A := .loop (nonempty k) (.pop k)
 def transfer (a b : K) (zero : A) : Code K A :=
  .loop (nonempty a) (.seq (.pushDyn b (fun v => (v a).getD zero)) (.pop a))

 def distribute (a b c : K) (zero : A) : Code K A :=
  .loop (nonempty a) (.seq (.pushDyn b (fun v => (v a).getD zero))
    (.seq (.pushDyn c (fun v => (v a).getD zero)) (.pop a)))

end WLTime.TypedStack.Code

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Arithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK uA uL

namespace WLTime.TypedStack.Code
variable {K : Type uK} {A : Type uA} [DecidableEq K]

def copy (a b tmp : K) (zero : A) : Code K A :=
  .seq (transfer a tmp zero) (distribute tmp a b zero)

def moveList (a b tmp : K) (zero : A) : Code K A :=
  .seq (transfer a tmp zero) (transfer tmp b zero)

end WLTime.TypedStack.Code

namespace WLTime.UnaryPrograms
open TypedStack
variable {K : Type uK} [DecidableEq K]

def numeral (n : ℕ) : List Bool := List.replicate n true

def scan : List Bool → ℕ × List Bool
  | [] => (0,[])
  | false::xs => (0,xs)
  | true::xs => let p := scan xs; (p.1+1,p.2)

def isTrue (a : K) (v : Tops K Bool) : Bool := decide (v a=some true)
def readLoop (a b : K) : Code K Bool :=
  .loop (isTrue a) (.seq (.push b true) (.pop a))
def read (a b : K) : Code K Bool := .seq (readLoop a b) (.pop a)

def prefixTail : List Bool → List Bool
  | [] => []
  | false::xs => false::xs
  | true::xs => prefixTail xs

@[simp] theorem prefixTail_tail (xs : List Bool) : (prefixTail xs).tail=(scan xs).2 := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [prefixTail,scan,ih]

@[simp] theorem scan_numeral (n : ℕ) (xs : List Bool) : scan (numeral n++false::xs)=(n,xs) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (let p := scan (numeral n++false::xs); (p.1+1,p.2))=(n+1,xs)
    rw [ih]

end WLTime.UnaryPrograms

namespace WLTime.TypedStack.Code
variable {K : Type uK} {L : Type uL} {A : Type uA} [DecidableEq K] [DecidableEq L]

def relabel (f : K → L) : Code K A → Code L A
  | .skip => .skip
  | .push k x => .push (f k) x
  | .pushDyn k g => .pushDyn (f k) (fun v => g (v ∘ f))
  | .pop k => .pop (f k)
  | .seq a b => .seq (relabel f a) (relabel f b)
  | .branch p a b => .branch (fun v => p (v ∘ f)) (relabel f a) (relabel f b)
  | .loop p a => .loop (fun v => p (v ∘ f)) (relabel f a)

end WLTime.TypedStack.Code

namespace WLTime.UnaryPrograms
open TypedStack
variable {K : Type uK} [DecidableEq K]

def repeatN (base : K) (c : Code K Bool) : Code (Fin 2 ⊕ K) Bool :=
  .seq (Code.copy (.inr base) (.inl 0) (.inl 1) false)
    (.loop (Code.nonempty (.inl 0))
      (.seq (c.relabel Sum.inr) (.pop (.inl 0))))

def extra (n : ℕ) : Fin 2 → List Bool := fun i => if i=0 then numeral n else []

end WLTime.UnaryPrograms

namespace WLTime.TypedStack.Code
variable {K : Type uK} {L : Type uL} {A : Type uA} [DecidableEq K] [DecidableEq L]

noncomputable def liftStacks (f : K → L) (frame : Stacks L A) (s : Stacks K A) : Stacks L A := by
  classical
  exact fun l => if h : ∃ k,f k=l then s h.choose else frame l

end WLTime.TypedStack.Code

namespace WLTime.TypedStack

structure Program (K : Type uK) where
  scratch : ℕ
  code : Code (Fin scratch ⊕ K) Bool

namespace Program
variable {K : Type uK} [DecidableEq K]

def ambient (p : Program K) (s : Stacks K Bool) : Stacks (Fin p.scratch ⊕ K) Bool :=
  Sum.elim (fun _ => []) s

def Exec (p : Program K) (s : Stacks K Bool) (t : ℕ) (out : Stacks K Bool) : Prop :=
  p.code.Exec (p.ambient s) t (p.ambient out)

def embed {a b : ℕ} (j : Fin a → Fin b) : Fin a ⊕ K → Fin b ⊕ K := Sum.map j id

def ofCode (c : Code K Bool) : Program K := ⟨0,c.relabel Sum.inr⟩

def seq (p q : Program K) : Program K :=
  ⟨p.scratch+q.scratch,.seq
    (p.code.relabel (embed (Fin.castAdd q.scratch)))
    (q.code.relabel (embed (Fin.natAdd p.scratch)))⟩

def branch (test : Tops K Bool → Bool) (p q : Program K) : Program K :=
  ⟨p.scratch+q.scratch,.branch (fun v => test (v ∘ Sum.inr))
    (p.code.relabel (embed (Fin.castAdd q.scratch)))
    (q.code.relabel (embed (Fin.natAdd p.scratch)))⟩

def loop (test : Tops K Bool → Bool) (p : Program K) : Program K :=
  ⟨p.scratch,.loop (fun v => test (v ∘ Sum.inr)) p.code⟩

def skip : Program K := ofCode .skip
def push (a : K) (b : Bool) : Program K := ofCode (.push a b)
def pop (a : K) : Program K := ofCode (.pop a)
def clear (a : K) : Program K := ofCode (Code.clear a)
def read (a b : K) : Program K := ofCode (UnaryPrograms.read a b)
def copy (a b : K) : Program K :=
  ⟨1,Code.copy (.inr a) (.inr b) (.inl 0) false⟩

def merge (a b : ℕ) : Fin a ⊕ (Fin b ⊕ K) ≃ Fin (a+b) ⊕ K :=
  (Equiv.sumAssoc (Fin a) (Fin b) K).symm.trans
    (Equiv.sumCongr finSumFinEquiv (Equiv.refl K))

omit [DecidableEq K] in
@[simp] theorem merge_left (a b : ℕ) (i : Fin a) :
    merge (K:=K) a b (.inl i)=.inl (i.castAdd b) := rfl
omit [DecidableEq K] in
@[simp] theorem merge_middle (a b : ℕ) (i : Fin b) :
    merge (K:=K) a b (.inr (.inl i))=.inl (i.natAdd a) := rfl
omit [DecidableEq K] in
@[simp] theorem merge_right (a b : ℕ) (i : K) :
    merge (K:=K) a b (.inr (.inr i))=.inr i := rfl

def allocate {n : ℕ} (p : Program (Fin n ⊕ K)) : Program K :=
  ⟨p.scratch+n,p.code.relabel (merge p.scratch n)⟩

def repeatN (base : K) (p : Program K) : Program K :=
  ⟨2+p.scratch,(UnaryPrograms.repeatN (.inr base) p.code).relabel (merge 2 p.scratch)⟩

end Program
end WLTime.TypedStack

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Expressions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK uL

namespace WLTime.UnaryPrograms
open TypedStack
variable {K : Type uK} [DecidableEq K]

def skipFieldLoop (a : K) : Code K Bool := .loop (isTrue a) (.pop a)
def skipField (a : K) : Program K := Program.ofCode (.seq (skipFieldLoop a) (.pop a))

def tailField (xs : List Bool) := (scan xs).2

def skipEntry (a : K) : Program K :=
  Program.seq (skipField a) (Program.seq (skipField a) (skipField a))

def seek (a index : K) : Program K := Program.repeatN index (skipEntry a)

def prependRecord (a b : K) : Program K := Program.seq (Program.push b false) (Program.copy a b)

@[simp] theorem numeral_length (n : ℕ) : (numeral n).length=n := List.length_replicate

def mulAdd (a b c : K) : Program K := Program.repeatN a (Program.copy b c)

end WLTime.UnaryPrograms

namespace WLTime.TypedStack.Program
variable {K : Type uK} {L : Type uL} [DecidableEq K] [DecidableEq L]

def relabel (p : Program K) (j : K → L) : Program L :=
  ⟨p.scratch,p.code.relabel (Sum.map id j)⟩

def pushes (a : K) : List Bool → Program K
  | [] => skip
  | b::bs => seq (pushes a bs) (push a b)

def overwrite (a b : K) : Program K := seq (clear b) (copy a b)

def putNat (a : K) (n : ℕ) : Program K := seq (clear a) (pushes a (UnaryPrograms.numeral n))

def dropN (index dest : K) : Program K := repeatN index (pop dest)

def putBit (a b : K) : Program K := seq (clear b)
  (branch (fun v => v a==some true) (push b true) skip)

end WLTime.TypedStack.Program

namespace WLTime.NatCode
open TypedStack UnaryPrograms

inductive Binary where
  | add | mul | sub
  deriving DecidableEq

def Binary.eval : Binary → ℕ → ℕ → ℕ
  | .add => (·+·)
  | .mul => (·*·)
  | .sub => (·-·)

variable {L : Type uL} [DecidableEq L]

def core (op : Binary) (a b c : L) : Program L := Program.seq (Program.clear c)
  (match op with
  | .add => Program.seq (Program.copy a c) (Program.copy b c)
  | .mul => mulAdd a b c
  | .sub => Program.seq (Program.copy a c) (Program.dropN b c))

def binary (op : Binary) (a b c : L) : Program L :=
  Program.seq (core op a b c) (Program.seq (Program.clear a) (Program.clear b))

def bitAt (word index dest : L) : Program L := Program.allocate
  (Program.seq (Program.copy (.inr word) (.inl (0 : Fin 1)))
    (Program.seq (Program.dropN (.inr index) (.inl 0))
      (Program.seq (Program.putBit (.inl 0) (.inr dest)) (Program.clear (.inl 0)))))

end WLTime.NatCode

namespace WLTime.NatCode
open TypedStack UnaryPrograms

inductive Expr (K : Type uK) where
  | const (n : ℕ)
  | var (k : K)
  | binary (op : Binary) (left right : Expr K)
  | bit (index : Expr K)

namespace Expr
variable {K : Type uK} {L : Type uL}

def eval (σ : K → ℕ) (w : List Bool) : Expr K → ℕ
  | .const n => n
  | .var k => σ k
  | .binary op e f => op.eval (e.eval σ w) (f.eval σ w)
  | .bit e => if w.getD (e.eval σ w) false then 1 else 0

def Bounded (σ : K → ℕ) (w : List Bool) (B : ℕ) : Expr K → Prop
  | .const n => n≤B
  | .var k => σ k≤B
  | .binary op e f => e.Bounded σ w B ∧ f.Bounded σ w B ∧ op.eval (e.eval σ w) (f.eval σ w)≤B
  | .bit e => e.Bounded σ w B ∧ 1≤B

def charge : Expr K → ℕ
  | .const _ | .var _ => 20
  | .binary _ e f => e.charge+f.charge+100
  | .bit e => e.charge+120

def compile (e : Expr K) : {L : Type uL} → [DecidableEq L] → (K → L) → L → L → Program L :=
  match e with
  | .const n => fun _ρ _word dest => Program.putNat dest n
  | .var k => fun ρ _word dest => Program.overwrite (ρ k) dest
  | .binary op e f => fun ρ word dest => Program.allocate
      (Program.seq (e.compile (Sum.inr ∘ ρ) (.inr word) (.inl (0 : Fin 2)))
        (Program.seq (f.compile (Sum.inr ∘ ρ) (.inr word) (.inl 1))
          (NatCode.binary op (.inl 0) (.inl 1) (.inr dest))))
  | .bit e => fun ρ word dest => Program.allocate
      (Program.seq (e.compile (Sum.inr ∘ ρ) (.inr word) (.inl (0 : Fin 1)))
        (Program.seq (bitAt (.inr word) (.inl 0) (.inr dest)) (Program.clear (.inl 0))))

end Expr
end WLTime.NatCode

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Predicates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK uJ uT uL uP uE

namespace WLTime.NatCode
namespace Expr
variable {K : Type uK} {J : Type uJ}

def bind (f : K → Expr J) : Expr K → Expr J
  | .const n => .const n
  | .var k => f k
  | .binary op a b => .binary op (a.bind f) (b.bind f)
  | .bit a => .bit (a.bind f)

@[simp] theorem bind_eval (f : K → Expr J) (σ : J → ℕ) (w : List Bool) (e : Expr K) :
    (e.bind f).eval σ w=e.eval (fun k => (f k).eval σ w) w := by
  induction e with
  | const | var => rfl
  | binary op a b ha hb => simp only [bind,eval,ha,hb]
  | bit a ha => simp only [bind,eval,ha]

end Expr

inductive Predicate (K : Type uK) where
  | truth (b : Bool)
  | eq (a b : Expr K)
  | lt (a b : Expr K)
  | bit (a : Expr K)
  | conj (a b : Predicate K)
  | neg (a : Predicate K)

namespace Predicate
variable {K : Type uK}

def Holds (σ : K → ℕ) (w : List Bool) : Predicate K → Prop
  | .truth b => b=true
  | .eq a b => a.eval σ w=b.eval σ w
  | .lt a b => a.eval σ w<b.eval σ w
  | .bit a => w.getD (a.eval σ w) false=true
  | .conj a b => a.Holds σ w ∧ b.Holds σ w
  | .neg a => ¬a.Holds σ w

instance decidableHolds (σ : K → ℕ) (w : List Bool) : (p : Predicate K) → Decidable (p.Holds σ w)
  | .truth _ | .eq _ _ | .lt _ _ | .bit _ => by unfold Holds; infer_instance
  | .conj a b => @instDecidableAnd _ _ (decidableHolds σ w a) (decidableHolds σ w b)
  | .neg a => @instDecidableNot _ (decidableHolds σ w a)

def code : Predicate K → Expr K
  | .truth b => .const (if b then 1 else 0)
  | .eq a b => .binary .sub (.const 1) (.binary .add (.binary .sub a b) (.binary .sub b a))
  | .lt a b => .binary .sub (.const 1) (.binary .sub (.const 1) (.binary .sub b a))
  | .bit a => .bit a
  | .conj a b => .binary .mul a.code b.code
  | .neg a => .binary .sub (.const 1) a.code

def Bounded (σ : K → ℕ) (w : List Bool) (B : ℕ) : Predicate K → Prop
  | .truth _ => True
  | .eq a b | .lt a b => a.Bounded σ w B ∧ b.Bounded σ w B
  | .bit a => a.Bounded σ w B
  | .conj a b => a.Bounded σ w B ∧ b.Bounded σ w B
  | .neg a => a.Bounded σ w B

def disj (a b : Predicate K) := (a.neg.conj b.neg).neg
@[simp] theorem holds_disj (σ : K → ℕ) (w : List Bool) (a b : Predicate K) :
    (a.disj b).Holds σ w ↔ a.Holds σ w ∨ b.Holds σ w := by
  simp only [disj,Holds,not_and_or,not_not]

def all (l : List (Predicate K)) := l.foldr Predicate.conj (.truth true)
def any (l : List (Predicate K)) := (all (l.map Predicate.neg)).neg

@[simp] theorem holds_all (σ : K → ℕ) (w : List Bool) (l : List (Predicate K)) :
    (all l).Holds σ w ↔ ∀ p∈l,p.Holds σ w := by
  induction l with
  | nil => simp [all,Holds]
  | cons p l ih =>
    change (p.Holds σ w ∧ (all l).Holds σ w) ↔ _
    simp only [ih,List.mem_cons,forall_eq_or_imp]

@[simp] theorem holds_any (σ : K → ℕ) (w : List Bool) (l : List (Predicate K)) :
    (any l).Holds σ w ↔ ∃ p∈l,p.Holds σ w := by
  classical
  simp only [any,Holds,holds_all,List.mem_map,forall_exists_index,and_imp,
    forall_apply_eq_imp_iff₂,not_forall]
  simp only [not_not]
  simp only [exists_prop]

end Predicate
end WLTime.NatCode

namespace WLTime.Compression
open NatCode

namespace ReadoutName
variable {r m : ℕ} {T : Type uT} {L : Type uL}

def encode : ReadoutName r T L (Fin m) → NameTag r T L × ℕ × ℕ
  | .horizontal i t a b => (.horizontal i t,a.val,b.val)
  | .vertical i l a => (.vertical i l,a.val,0)

end ReadoutName

structure FormalName (T : Type uT) (J : Type uJ) where
  tag : T
  first : Expr J
  second : Expr J

namespace FormalName
variable {T : Type uT} {J : Type uJ}
def eval (σ : J → ℕ) (w : List Bool) (n : FormalName T J) : T × ℕ × ℕ :=
  (n.tag,n.first.eval σ w,n.second.eval σ w)
noncomputable def equal (n u : FormalName T J) : Predicate J := by
  classical
  exact (Predicate.truth (decide (n.tag=u.tag))).conj
    ((Predicate.eq n.first u.first).conj (.eq n.second u.second))

end FormalName

namespace ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} {J : Type uJ} (I : ConsistencyData (r+1) m P E)

abbrev BlockTag (K : ℕ) := Fin (r+1) × (TypeNode K P E ⊕ TypeLink K E)

def makeBlock (K : ℕ) : BlockTag (r:=r) (P:=P) (E:=E) K → Fin m → Fin m →
    RawBlock (r:=r) (m:=m) (P:=P) (E:=E) K
  | (i,.inl t),a,b => .site i t a b
  | (i,.inr l),a,b => .square i l a b

def fixedTags (K : ℕ) : BlockTag (r:=r) (P:=P) (E:=E) K → List (Tag (r:=r) (P:=P) (E:=E) K)
  | (i,.inl t) => [.horizontal i t]
  | (i,.inr l) => [.horizontal i (linkLeft K I.src l),.horizontal i (linkRight K I.dst l),
      .vertical i l,.vertical (finRotate (r+1) i) l]

noncomputable def footprintList (K : ℕ) : RawBlock (r:=r) (m:=m) (P:=P) (E:=E) K →
    List (RawName (r:=r) (m:=m) (P:=P) (E:=E) K)
  | .site i t a b => [.horizontal i t a b]
  | .square i l a b => [.horizontal i (linkLeft K I.src l) a b,
      .horizontal i (linkRight K I.dst l)
        (linkMatch K (fun e => I.coordinatePerm e i) l a)
        (linkMatch K (fun e => I.coordinatePerm e (finRotate (r+1) i)) l b),
      .vertical i l a,.vertical (finRotate (r+1) i) l b]

noncomputable def fixedForm (K : ℕ) : BlockTag (r:=r) (P:=P) (E:=E) K → I.TagValues K → F₂
  | (_,.inl _),_ => 0
  | (i,.inr l),v => I.leftForm K l (v (.horizontal i (linkLeft K I.src l))) +
      I.rightForm K l (v (.horizontal i (linkRight K I.dst l))) +
      v (.vertical i l) + v (.vertical (finRotate (r+1) i) l)

def fixedBias (K : ℕ) : BlockTag (r:=r) (P:=P) (E:=E) K → F₂
  | (_,.inl _) => 0
  | (i,.inr l) => seam i*I.linkBias K l

def FixedLegal (K : ℕ) (ε : F₂) (t : BlockTag (r:=r) (P:=P) (E:=E) K) (v : I.TagValues K) : Prop :=
  (∀s,s∉I.fixedTags K t → v s=0) ∧ I.fixedForm K t v=ε*I.fixedBias K t

end ConsistencyData
end WLTime.Compression

namespace WLTime.Compression
open NatCode
namespace ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} {J : Type uJ} (I : ConsistencyData (r+1) m P E)

variable (D : E → Fin (r+1) → Expr J → Predicate J)
variable (Q : E → Fin (r+1) → Expr J → Expr J)

def labelPredicate (K : ℕ) : TypeNode K P E → Fin (r+1) → Expr J → Predicate J
  | .inl _,_,_ => .truth true
  | .inr (e,_),i,a => D e i a

def blockPredicate (K : ℕ) : BlockTag (r:=r) (P:=P) (E:=E) K → Expr J → Expr J → Predicate J
  | (i,.inl t),a,b => (labelPredicate D K t i a).conj
      (labelPredicate D K t (finRotate (r+1) i) b)
  | (i,.inr l),a,b => (D l.1 i a).conj (D l.1 (finRotate (r+1) i) b)

noncomputable def validPredicate (K : ℕ) (ε : F₂) (t : BlockTag (r:=r) (P:=P) (E:=E) K)
    (v : I.TagValues K) (a b : Expr J) : Predicate J := by
  classical
  exact (blockPredicate D K t a b).conj (.truth (decide (I.FixedLegal K ε t v)))

def matchCode (K : ℕ) (l : TypeLink K E) (i : Fin (r+1)) (a : Expr J) : Expr J :=
  if l.2.val=4*K then Q l.1 i a else a

def formalFootprint (K : ℕ) : BlockTag (r:=r) (P:=P) (E:=E) K → Expr J → Expr J →
    List (FormalName (Tag (r:=r) (P:=P) (E:=E) K) J)
  | (i,.inl t),a,b => [⟨.horizontal i t,a,b⟩]
  | (i,.inr l),a,b => [⟨.horizontal i (linkLeft K I.src l),a,b⟩,
      ⟨.horizontal i (linkRight K I.dst l),matchCode Q K l i a,
        matchCode Q K l (finRotate (r+1) i) b⟩,
      ⟨.vertical i l,a,.const 0⟩,⟨.vertical (finRotate (r+1) i) l,b,.const 0⟩]

noncomputable def valueCode (K : ℕ) (v : I.TagValues K) (t : Tag (r:=r) (P:=P) (E:=E) K) : ℕ :=
  (Fintype.equivFin (I.TagValue K t) (v t)).val

noncomputable def overlapPredicate (K : ℕ)
    (l s : List (FormalName (Tag (r:=r) (P:=P) (E:=E) K) J)) : Predicate J :=
  Predicate.any (l.flatMap fun n => s.map fun u => n.equal u)

noncomputable def agreePredicate (K : ℕ) (v u : I.TagValues K)
    (l s : List (FormalName (Tag (r:=r) (P:=P) (E:=E) K) J)) : Predicate J := by
  classical
  exact Predicate.all (l.flatMap fun n => s.map fun z =>
    (n.equal z).neg.disj (.truth (decide (I.valueCode K v n.tag=I.valueCode K u z.tag))))

end ConsistencyData
end WLTime.Compression

namespace WLTime.Compression
open NatCode
namespace ReadoutName
variable {r m : ℕ} {T : Type uT} {L : Type uL}
@[simp] theorem encode_tag (n : ReadoutName r T L (Fin m)) : n.encode.1=n.tag := by cases n <;> rfl
end ReadoutName

namespace ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} {J : Type uJ} (I : ConsistencyData (r+1) m P E)

noncomputable def sameBlockPredicate (K : ℕ) (t u : BlockTag (r:=r) (P:=P) (E:=E) K)
    (a b c d : Expr J) : Predicate J := by
  classical
  exact (Predicate.truth (decide (t=u))).conj ((Predicate.eq a c).conj (.eq b d))

def RawAdjacent (K : ℕ) (v u : I.Descriptor K) : Prop :=
  v.1≠u.1 ∧ (∃n,n∈I.footprint K v.1 ∧ n∈I.footprint K u.1) ∧
    ∀n∈I.footprint K v.1,n∈I.footprint K u.1 → I.tagRead K v.2 n=I.tagRead K u.2 n

noncomputable def adjacencyPredicate (Q : E → Fin (r+1) → Expr J → Expr J) (K : ℕ)
    (t u : BlockTag (r:=r) (P:=P) (E:=E) K) (v z : I.TagValues K)
    (a b c d : Expr J) : Predicate J :=
  (sameBlockPredicate K t u a b c d).neg.conj
    ((overlapPredicate K (I.formalFootprint Q K t a b) (I.formalFootprint Q K u c d)).conj
      (I.agreePredicate K v z (I.formalFootprint Q K t a b) (I.formalFootprint Q K u c d)))

end ConsistencyData
end WLTime.Compression

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Digits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uJ

namespace WLTime.Digits

abbrev Word (d m : ℕ) := Fin d → Fin m
abbrev encode {d m : ℕ} : Word d m ≃ Fin (m^d) := finFunctionFinEquiv

def value {d m : ℕ} (a : Word d m) : ℕ := (encode a).val

@[simp] theorem value_zero {m : ℕ} (a : Word 0 m) : value a = 0 := by
  simp [value,encode]

theorem value_succ {d m : ℕ} (a : Word (d+1) m) :
    value a = (a 0).val + m * value (fun i : Fin d => a i.succ) := by
  simp only [value,encode,finFunctionFinEquiv_apply,Fin.sum_univ_succ,
    Fin.val_zero,pow_zero,Nat.mul_one,Fin.val_succ,pow_succ]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

def CarryDomain {d m : ℕ} (p : Fin (d+1)) (i : Fin d) : Finset (Fin m) :=
  Finset.univ.filter fun x => if i.val < p.val then x.val+1=m
    else if i.val=p.val then x.val + 1 < m else True

def Allowed {d m : ℕ} (p : Fin (d+1)) (a : Word d m) : Prop :=
  ∀ i, a i ∈ CarryDomain p i

theorem allowed_iff {d m : ℕ} (p : Fin (d+1)) (a : Word d m) :
    Allowed p a ↔ ∀ i, if i.val < p.val then (a i).val+1=m
      else if i.val=p.val then (a i).val + 1 < m else True := by
  simp only [Allowed,CarryDomain,Finset.mem_filter,Finset.mem_univ,true_and]

def inc (m : ℕ) : Equiv.Perm (Fin m) := finRotate m

def coordinate {d m : ℕ} (p : Fin (d+1)) (i : Fin d) : Equiv.Perm (Fin m) :=
  if i.val ≤ p.val then inc m else Equiv.refl _

def applyCarry {d m : ℕ} (p : Fin (d+1)) (a : Word d m) : Word d m :=
  fun i => coordinate p i (a i)

theorem inc_value {m : ℕ} (x : Fin m) :
    (inc m x).val = if x.val + 1 = m then 0 else x.val + 1 := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt x.pos)
  rw [inc,coe_finRotate]
  have he : x=Fin.last m ↔ x.val+1=m+1 := by
    simp only [Fin.ext_iff,Fin.val_last]
    omega
  simp only [he]

theorem allowed_zero {d m : ℕ} (a : Word (d+1) m) :
    Allowed (0 : Fin (d+2)) a ↔ (a 0).val + 1 < m := by
  simp [allowed_iff]

theorem allowed_succ {d m : ℕ} (p : Fin (d+1)) (a : Word (d+1) m) :
    Allowed p.succ a ↔ (a 0).val+1=m ∧ Allowed p (fun i => a i.succ) := by
  rw [allowed_iff,Fin.forall_fin_succ,allowed_iff]
  simp only [Fin.val_zero,Fin.val_succ,Nat.zero_lt_succ,ite_true,
    Nat.add_lt_add_iff_right,Nat.add_right_cancel_iff]

@[simp] theorem apply_zero_head {d m : ℕ} (a : Word (d+1) m) :
    applyCarry (0 : Fin (d+2)) a 0 = inc m (a 0) := by
  simp [applyCarry,coordinate]

@[simp] theorem apply_zero_tail {d m : ℕ} (a : Word (d+1) m) (i : Fin d) :
    applyCarry (0 : Fin (d+2)) a i.succ = a i.succ := by
  simp [applyCarry,coordinate]

@[simp] theorem apply_succ_head {d m : ℕ} (p : Fin (d+1)) (a : Word (d+1) m) :
    applyCarry p.succ a 0 = inc m (a 0) := by
  simp [applyCarry,coordinate]

@[simp] theorem apply_succ_tail {d m : ℕ} (p : Fin (d+1)) (a : Word (d+1) m) (i : Fin d) :
    applyCarry p.succ a i.succ = applyCarry p (fun i => a i.succ) i := by
  simp [applyCarry,coordinate]

theorem exists_allowed {d m : ℕ} (a : Word d m) : ∃ p : Fin (d+1), Allowed p a := by
  induction d with
  | zero => exact ⟨0,fun i => Fin.elim0 i⟩
  | succ d ih =>
    by_cases hm : (a 0).val+1=m
    · obtain ⟨p,hp⟩ := ih (fun i => a i.succ)
      exact ⟨p.succ,(allowed_succ p a).mpr ⟨hm,hp⟩⟩
    · exact ⟨0,(allowed_zero a).mpr (by have := (a 0).isLt; omega)⟩

theorem carry_value {d m : ℕ} (p : Fin (d+1)) (a : Word d m) (ha : Allowed p a) :
    value (applyCarry p a) = if p.val=d then 0 else value a+1 := by
  induction d with
  | zero => simp
  | succ d ih =>
    revert ha
    refine Fin.cases ?_ (fun p => ?_) p
    · intro ha
      have ha0 : (a 0).val+1< m := (allowed_zero a).mp ha
      simp only [Fin.val_zero,Ne.symm (Nat.succ_ne_zero d),ite_false]
      rw [value_succ,value_succ,apply_zero_head,inc_value]
      simp only [apply_zero_tail,ite_eq_right (Nat.ne_of_lt ha0)]
      omega
    · intro ha
      obtain ⟨ha0,hat⟩ := (allowed_succ p a).mp ha
      have ht := ih p (fun i => a i.succ) hat
      rw [value_succ,value_succ,apply_succ_head,inc_value,ite_eq_left ha0]
      simp only [apply_succ_tail,Fin.val_succ,Nat.add_right_cancel_iff]
      rw [ht]
      split_ifs with hp
      · simp
      · nlinarith

theorem wrap_value {d m : ℕ} (a : Word d m) (ha : Allowed (Fin.last d) a) :
    value a+1=m^d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hh : Fin.last (d+1) = (Fin.last d).succ := rfl
    rw [hh,allowed_succ] at ha
    obtain ⟨ha0,hat⟩ := ha
    have ht := ih (fun i => a i.succ) hat
    rw [value_succ,pow_succ]
    nlinarith

theorem carry_rotation {d m : ℕ} (p : Fin (d+1)) (a : Word d m) (ha : Allowed p a) :
    encode (applyCarry p a) = inc (m^d) (encode a) := by
  apply Fin.ext
  change value (applyCarry p a) = _
  rw [inc_value]
  change value (applyCarry p a) = if value a+1=m^d then 0 else value a+1
  rw [carry_value p a ha]
  by_cases hp : p.val=d
  · have he : p=Fin.last d := Fin.ext hp
    have hv := wrap_value a (he ▸ ha)
    simp only [hp,hv,ite_true]
  · have hv : value a+1 < m^d := by
      have hb := (encode (applyCarry p a)).isLt
      change value (applyCarry p a) < m^d at hb
      simpa only [carry_value p a ha,ite_eq_right hp] using hb
    simp only [ite_eq_right hp,ite_eq_right (Nat.ne_of_lt hv)]

theorem carry_relation {d m : ℕ} (a b : Word d m) :
    (∃ p : Fin (d+1), Allowed p a ∧ applyCarry p a=b) ↔
      encode b=inc (m^d) (encode a) := by
  constructor
  · rintro ⟨p,ha,rfl⟩
    exact carry_rotation p a ha
  · intro hab
    obtain ⟨p,ha⟩ := exists_allowed a
    refine ⟨p,ha,encode.injective ?_⟩
    exact (carry_rotation p a ha).trans hab.symm

theorem nonwrap_relation {d m : ℕ} (a b : Word d m) :
    (∃ p : Fin d, Allowed p.castSucc a ∧ applyCarry p.castSucc a=b) ↔
      value b=value a+1 := by
  constructor
  · rintro ⟨p,ha,rfl⟩
    rw [carry_value p.castSucc a ha]; simp only [Fin.val_castSucc,ite_eq_right (Nat.ne_of_lt p.isLt)]
  · intro hab
    obtain ⟨p,ha⟩ := exists_allowed a
    have hp : p.val<d := by
      have hv : value b< m^d := (encode b).isLt
      have hlt := p.isLt
      by_contra hn
      have he : p=Fin.last d := Fin.ext (by simp only [Fin.val_last]; omega)
      have hw := wrap_value a (he ▸ ha)
      omega
    let p' : Fin d := ⟨p.val,hp⟩
    have he : p'.castSucc=p := rfl
    refine ⟨p',he.symm ▸ ha,encode.injective ?_⟩
    apply Fin.ext
    change value (applyCarry p'.castSucc a)=value b
    rw [he,carry_value p a ha,ite_eq_right (Nat.ne_of_lt hp),hab]

theorem allowed_last_iff {d m : ℕ} (a : Word d m) :
    Allowed (Fin.last d) a ↔ ∀ i,(a i).val+1=m := by
  simp only [allowed_iff,Fin.val_last,Fin.isLt,ite_true]

theorem value_last_iff {d m : ℕ} (a : Word d m) :
    value a+1=m^d ↔ ∀ i,(a i).val+1=m := by
  constructor
  · intro h
    obtain ⟨p,hp⟩ := exists_allowed a
    have he : p.val=d := by
      by_contra hn
      have hb := (encode (applyCarry p a)).isLt
      change value (applyCarry p a)< m^d at hb
      rw [carry_value p a hp,ite_eq_right hn,h] at hb
      omega
    have he' : p=Fin.last d := Fin.ext he
    exact allowed_last_iff a |>.mp (he' ▸ hp)
  · intro h
    exact wrap_value a ((allowed_last_iff a).mpr h)

end WLTime.Digits

namespace WLTime.ProductBox
abbrev Address (r m : ℕ) := Fin r → Fin m

structure Box (r m : ℕ) where
  domain : Fin r → Finset (Fin m)
  coord : Fin r → Equiv.Perm (Fin m)

namespace Box
variable {r m : ℕ} (B : Box r m)

def Allowed (a : Address r m) : Prop := ∀ i, a i ∈ B.domain i

def apply (a : Address r m) : Address r m := fun i => B.coord i (a i)

def Rel (a b : Address r m) : Prop := B.Allowed a ∧ B.apply a=b

def reverse : Box r m where
  domain i := (B.domain i).image (B.coord i)
  coord i := (B.coord i).symm

@[simp] theorem reverse_apply_apply (a : Address r m) : B.reverse.apply (B.apply a)=a := by
  funext i
  exact (B.coord i).symm_apply_apply (a i)

@[simp] theorem apply_reverse_apply (a : Address r m) : B.apply (B.reverse.apply a)=a := by
  funext i
  exact (B.coord i).apply_symm_apply (a i)

theorem reverse_allowed (a : Address r m) : B.reverse.Allowed a ↔ B.Allowed (B.reverse.apply a) := by
  unfold Allowed reverse apply
  apply forall_congr'
  intro i
  constructor
  · intro h
    obtain ⟨b,hb,he⟩ := Finset.mem_image.mp h
    simpa only [← he,Equiv.symm_apply_apply] using hb
  · intro h
    exact Finset.mem_image.mpr ⟨(B.coord i).symm (a i),h,(B.coord i).apply_symm_apply (a i)⟩

theorem reverse_relation (a b : Address r m) : B.reverse.Rel a b ↔ B.Rel b a := by
  rw [Rel,reverse_allowed,Rel]
  constructor
  · rintro ⟨ha,hab⟩
    exact ⟨hab ▸ ha,by rw [← hab,B.apply_reverse_apply]⟩
  · rintro ⟨hb,hba⟩
    rw [← hba,B.reverse_apply_apply]
    exact ⟨hb,rfl⟩

def identity (r m : ℕ) : Box r m where
  domain _ := Finset.univ
  coord _ := Equiv.refl _

@[simp] theorem identity_rel (a b : Address r m) : (identity r m).Rel a b ↔ a=b := by
  change ((∀ i, a i ∈ (Finset.univ : Finset (Fin m))) ∧ a=b) ↔ a=b
  simp

def product {d q : ℕ} (B : Box d m) (C : Box q m) : Box (d+q) m where
  domain := Fin.addCases B.domain C.domain
  coord := Fin.addCases B.coord C.coord

@[simp] theorem product_allowed {d q : ℕ} (B : Box d m) (C : Box q m)
    (a : Address d m) (b : Address q m) :
    (B.product C).Allowed (Fin.append a b) ↔ B.Allowed a ∧ C.Allowed b := by
  simp [Allowed,product,Fin.forall_fin_add]

@[simp] theorem product_apply {d q : ℕ} (B : Box d m) (C : Box q m)
    (a : Address d m) (b : Address q m) :
    (B.product C).apply (Fin.append a b)=Fin.append (B.apply a) (C.apply b) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [apply,product]

def carry {d m : ℕ} (p : Fin (d+1)) : Box d m where
  domain := Digits.CarryDomain p
  coord := Digits.coordinate p

theorem carry_rel {d m : ℕ} (a b : Address d m) :
    (∃ p : Fin (d+1), (carry p).Rel a b) ↔
      Digits.encode b=Digits.inc (m^d) (Digits.encode a) :=
  Digits.carry_relation a b

theorem borrow_rel {d m : ℕ} (a b : Address d m) :
    (∃ p : Fin (d+1), (carry p).reverse.Rel a b) ↔
      Digits.encode b=(Digits.inc (m^d)).symm (Digits.encode a) := by
  simp_rw [reverse_relation]
  rw [carry_rel]
  constructor
  · intro h
    have he := congrArg (Digits.inc (m^d)).symm h
    simpa only [Equiv.symm_apply_apply] using he.symm
  · intro h
    have he := congrArg (Digits.inc (m^d)) h
    simpa only [Equiv.apply_symm_apply] using he.symm

end Box
end WLTime.ProductBox

namespace WLTime.ProductBox
abbrev time {d q m : ℕ} (a : Address (d+q) m) : Address d m := fun i => a (i.castAdd q)
abbrev space {d q m : ℕ} (a : Address (d+q) m) : Address q m := fun i => a (i.natAdd d)

@[simp] theorem append_time_space {d q m : ℕ} (a : Address (d+q) m) :
    Fin.append (time a) (space a)=a := Fin.append_castAdd_natAdd

@[simp] theorem time_append {d q m : ℕ} (a : Address d m) (b : Address q m) :
    time (Fin.append a b)=a := by funext i; exact Fin.append_left _ _ _
@[simp] theorem space_append {d q m : ℕ} (a : Address d m) (b : Address q m) :
    space (Fin.append a b)=b := by funext i; exact Fin.append_right _ _ _

def addressEquiv {d q m : ℕ} : Address (d+q) m ≃ Fin (m^d) × Fin (m^q) where
  toFun a := (Digits.encode (time a),Digits.encode (space a))
  invFun b := Fin.append (Digits.encode.symm b.1) (Digits.encode.symm b.2)
  left_inv a := by simp
  right_inv b := by simp

namespace Box
variable {d q m : ℕ}
theorem product_relation (B : Box d m) (C : Box q m) (a b : Address (d+q) m) :
    (B.product C).Rel a b ↔ B.Rel (time a) (time b) ∧ C.Rel (space a) (space b) := by
  rw [← append_time_space a,← append_time_space b]
  simp only [Rel,product_allowed,product_apply,time_append,space_append]
  have he {a a' : Address d m} {b b' : Address q m} :
      Fin.append a b=Fin.append a' b' ↔ a=a' ∧ b=b' := by
    constructor
    · intro h
      exact ⟨by simpa using congrArg time h,by simpa using congrArg space h⟩
    · rintro ⟨rfl,rfl⟩; rfl
  rw [he]
  tauto
end Box
end WLTime.ProductBox

namespace WLTime.NatCode
namespace Expr
variable {J : Type uJ}
def choose (p : Predicate J) (a b : Expr J) : Expr J :=
  .binary .add (.binary .mul p.code a) (.binary .mul (.binary .sub (.const 1) p.code) b)

def incCode (M a : Expr J) : Expr J :=
  choose (.eq (.binary .add a (.const 1)) M) (.const 0) (.binary .add a (.const 1))
def decCode (M a : Expr J) : Expr J :=
  choose (.eq a (.const 0)) (.binary .sub M (.const 1)) (.binary .sub a (.const 1))

end Expr
end WLTime.NatCode

namespace WLTime.ProductBox
open NatCode
namespace Formula
variable {d q m : ℕ} {J : Type uJ}

def carryDomain (p : Fin (d+1)) (i : Fin d) (M a : Expr J) : Predicate J :=
  if i.val<p.val then .eq (.binary .add a (.const 1)) M
  else if i.val=p.val then .lt (.binary .add a (.const 1)) M else .truth true

def carryCoord (p : Fin (d+1)) (i : Fin d) (M a : Expr J) : Expr J :=
  if i.val≤p.val then Expr.incCode M a else a

def borrowCoord (p : Fin (d+1)) (i : Fin d) (M a : Expr J) : Expr J :=
  if i.val≤p.val then Expr.decCode M a else a

def borrowDomain (p : Fin (d+1)) (i : Fin d) (M a : Expr J) : Predicate J :=
  carryDomain p i M (borrowCoord p i M a)

end Formula
end WLTime.ProductBox

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Tableau
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uP uE uS uT uG uH uF uAlphabet

namespace WLTime.CircuitEncoding

abbrev Address (r m : ℕ) := Fin r → Fin m

def ProductAllowed {r m : ℕ} (D : Fin r → Finset (Fin m)) (a : Address r m) : Prop :=
  ∀ i, a i ∈ D i

structure Schematic (r m : ℕ) (P : Type uP) (E : Type uE) (S : Type uS) (T : Type uT) where
  kind : P → Kind
  src : E → P
  dst : E → P
  port : (e : E) → Fin (kind (dst e)).dim
  domain : E → Fin r → Finset (Fin m)
  coord : (e : E) → (i : Fin r) → domain e i → Fin m
  coord_inj : ∀ e i, Function.Injective (coord e i)
  seedGate : S → P
  seedDomain : S → Fin r → Finset (Fin m)
  testGate : T → P
  testDomain : T → Fin r → Finset (Fin m)
  seed_scalar : ∀ s, kind (seedGate s) = .scalar
  test_scalar : ∀ t, kind (testGate t) = .scalar
  rank : P × Address r m → ℕ
  forward : ∀ e a (ha : ProductAllowed (domain e) a),
    rank (src e,a) < rank (dst e,fun i => coord e i ⟨a i,ha i⟩)
  test_terminal : ∀ e a, ProductAllowed (domain e) a →
    ∀ t, testGate t = src e → ¬ProductAllowed (testDomain t) a

namespace Schematic
variable {r m : ℕ} {P : Type uP} {E : Type uE} {S : Type uS} {T : Type uT} (C : Schematic r m P E S T)

abbrev Instance (_C : Schematic r m P E S T) := P × Address r m
abbrev Connection := Σ e : E, {a : Address r m // ProductAllowed (C.domain e) a}

def transmit (e : E) (a : Address r m) (h : ProductAllowed (C.domain e) a) : Address r m :=
  fun i => C.coord e i ⟨a i,h i⟩

open scoped Classical in
noncomputable def expand : Circuit C.Instance C.Connection where
  kind g := C.kind g.1
  src e := (C.src e.1,e.2.1)
  dst e := (C.dst e.1,C.transmit e.1 e.2.1 e.2.2)
  port e := C.port e.1
  rank := C.rank
  forward e := C.forward e.1 e.2.1 e.2.2
  seed g := decide (∃ s, C.seedGate s = g.1 ∧ ProductAllowed (C.seedDomain s) g.2)
  test g := decide (∃ t, C.testGate t = g.1 ∧ ProductAllowed (C.testDomain t) g.2)
  seed_scalar := by
    intro g hg
    obtain ⟨s,hs,_⟩ := of_decide_eq_true hg
    rw [← hs]
    exact C.seed_scalar s
  test_scalar := by
    intro g hg
    obtain ⟨t,ht,_⟩ := of_decide_eq_true hg
    rw [← ht]
    exact C.test_scalar t
  test_terminal := by
    intro e
    apply decide_eq_false
    rintro ⟨t,ht,ha⟩
    exact C.test_terminal e.1 e.2.1 e.2.2 t ht ha

inductive Node (P : Type uP) (E : Type uE) where
  | gate (p : P)
  | buffer (e : E)
  | dummy
  deriving DecidableEq, Fintype

inductive Edge (E : Type uE) (S : Type uS) (T : Type uT) where
  | first (e : E)
  | second (e : E)
  | third (e : E)
  | seed (s : S)
  | test (t : T)
  deriving DecidableEq, Fintype

def nodeDim : Node P E → ℕ
  | .gate p => (C.kind p).dim
  | .buffer _ => 2
  | .dummy => 1

def edgeSrc : Edge E S T → Node P E
  | .first e => .gate (C.src e)
  | .second e => .gate (C.src e)
  | .third e => .buffer e
  | .seed s => .gate (C.seedGate s)
  | .test t => .gate (C.testGate t)

def edgeDst : Edge E S T → Node P E
  | .first e => .buffer e
  | .second e => .buffer e
  | .third e => .gate (C.dst e)
  | .seed _ => .dummy
  | .test _ => .dummy

def edgeDomain : Edge E S T → Fin r → Finset (Fin m)
  | .first e => C.domain e
  | .second e => C.domain e
  | .third e => C.domain e
  | .seed s => C.seedDomain s
  | .test t => C.testDomain t

def edgeCoord : (f : Edge E S T) → (i : Fin r) → C.edgeDomain f i → Fin m
  | .first _, _ => Subtype.val
  | .second _, _ => Subtype.val
  | .third e, i => C.coord e i
  | .seed _, _ => Subtype.val
  | .test _, _ => Subtype.val

theorem edgeCoord_inj (f : Edge E S T) (i : Fin r) : Function.Injective (C.edgeCoord f i) := by
  cases f <;> first | exact Subtype.val_injective | exact C.coord_inj _ _

def sumForm (d : ℕ) : (Fin d → Bit) →ₗ[Bit] Bit where
  toFun x := ∑ i,x i
  map_add' x y := Finset.sum_add_distrib
  map_smul' a x := by simp only [Pi.smul_apply,smul_eq_mul,Finset.mul_sum,RingHom.id_apply]

def coordForm {d : ℕ} (i : Fin d) : (Fin d → Bit) →ₗ[Bit] Bit where
  toFun x := x i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def srcForm : (f : Edge E S T) → (Fin (C.nodeDim (C.edgeSrc f)) → Bit) →ₗ[Bit] Bit
  | .first _ => sumForm _
  | .second _ => sumForm _
  | .third _ => sumForm _
  | .seed _ => sumForm _
  | .test _ => sumForm _

def dstForm : (f : Edge E S T) → (Fin (C.nodeDim (C.edgeDst f)) → Bit) →ₗ[Bit] Bit
  | .first _ => coordForm (0 : Fin 2)
  | .second _ => coordForm (1 : Fin 2)
  | .third e => coordForm (C.port e)
  | .seed _ => 0
  | .test _ => 0

def dstBias : Edge E S T → Bit
  | .test _ => 1
  | _ => 0

def consistency : Compression.ConsistencyData r m (Node P E) (Edge E S T) where
  dim := C.nodeDim
  src := C.edgeSrc
  dst := C.edgeDst
  domain := C.edgeDomain
  coord := C.edgeCoord
  coord_inj := C.edgeCoord_inj
  linearSrc := C.srcForm
  linearDst := C.dstForm
  biasSrc := fun _ => 0
  biasDst := dstBias

@[simp] theorem same_transmit_first (e : E) (a : Address r m)
    (h : C.consistency.Allowed (.first e) a) :
    C.consistency.transmit (.first e) a h = a := rfl
@[simp] theorem same_transmit_second (e : E) (a : Address r m)
    (h : C.consistency.Allowed (.second e) a) :
    C.consistency.transmit (.second e) a h = a := rfl
@[simp] theorem same_transmit_third (e : E) (a : Address r m)
    (h : C.consistency.Allowed (.third e) a) :
    C.consistency.transmit (.third e) a h = C.transmit e a h := rfl
@[simp] theorem same_transmit_seed (s : S) (a : Address r m)
    (h : C.consistency.Allowed (.seed s) a) :
    C.consistency.transmit (.seed s) a h = a := rfl
@[simp] theorem same_transmit_test (t : T) (a : Address r m)
    (h : C.consistency.Allowed (.test t) a) :
    C.consistency.transmit (.test t) a h = a := rfl

theorem affineSrc_first (e : E) (a : Address r m) :
    C.consistency.affineSrc (.first e) = C.expand.output (C.src e,a) := by
  funext x
  exact add_zero _

theorem affineSrc_second (e : E) (a : Address r m) :
    C.consistency.affineSrc (.second e) = C.expand.output (C.src e,a) := by
  funext x
  exact add_zero _

theorem affineSrc_seed (e : S) (a : Address r m) :
    C.consistency.affineSrc (.seed e) = C.expand.output (C.seedGate e,a) := by
  funext x
  exact add_zero _

theorem affineSrc_test (e : T) (a : Address r m) :
    C.consistency.affineSrc (.test e) = C.expand.output (C.testGate e,a) := by
  funext x
  exact add_zero _

theorem affineSrc_third (e : E) :
    C.consistency.affineSrc (.third e) = (fun z : Fin 2 → Bit => z 0 + z 1) := by
  change (fun z : Fin 2 → Bit => (∑ i : Fin 2, (z i : Bit)) + 0) =
    (fun z : Fin 2 → Bit => (z 0 : Bit) + z 1)
  funext z
  rw [add_zero,Fin.sum_univ_two]

theorem affineDst_first (e : E) :
    C.consistency.affineDst (.first e) = (fun z : Fin 2 → Bit => z 0) := by
  funext z
  exact add_zero _

theorem affineDst_second (e : E) :
    C.consistency.affineDst (.second e) = (fun z : Fin 2 → Bit => z 1) := by
  funext z
  exact add_zero _

theorem affineDst_third (e : E) :
    C.consistency.affineDst (.third e) = (fun z : Fin (C.kind (C.dst e)).dim → Bit => z (C.port e)) := by
  funext z
  exact add_zero _

theorem affineDst_seed (e : S) :
    C.consistency.affineDst (.seed e) = (fun _ : Fin 1 → Bit => (0 : Bit)) := by
  funext z
  exact add_zero _

theorem affineDst_test (e : T) :
    C.consistency.affineDst (.test e) = (fun _ : Fin 1 → Bit => (1 : Bit)) := by
  funext z
  exact zero_add _

open Compression.ConsistencyData

open scoped Classical in

noncomputable def setsOfWitness (W : C.expand.Witness) :
    (p : Node P E) → Address r m → Set (Fin (C.nodeDim p) → Bit)
  | .gate p, a => W.gate (p,a)
  | .buffer e, a => if h : ProductAllowed (C.domain e) a then W.buffer ⟨e,⟨a,h⟩⟩ else Set.univ
  | .dummy, _ => Set.univ

noncomputable def witnessOfConsistent
    (Q : (p : Node P E) → Address r m → Set (Fin (C.nodeDim p) → Bit))
    (hQ : ∀ p a, (Q p a).Nonempty)
    (hE : ∀ f a (ha : C.consistency.Allowed f a),
      C.consistency.affineSrc f '' Q (C.edgeSrc f) a =
      C.consistency.affineDst f '' Q (C.edgeDst f) (C.consistency.transmit f a ha)) :
    C.expand.Witness where
  gate g := Q (.gate g.1) g.2
  buffer e := Q (.buffer e.1) e.2.1
  gate_nonempty g := hQ (.gate g.1) g.2
  buffer_nonempty e := hQ (.buffer e.1) e.2.1
  first e := by
    have h := hE (.first e.1) e.2.1 e.2.2
    rw [C.affineSrc_first e.1 e.2.1,C.affineDst_first e.1] at h
    exact h
  second e := by
    have h := hE (.second e.1) e.2.1 e.2.2
    rw [C.affineSrc_second e.1 e.2.1,C.affineDst_second e.1] at h
    exact h
  third e := by
    have h := hE (.third e.1) e.2.1 e.2.2
    rw [C.affineSrc_third e.1,C.affineDst_third e.1] at h
    exact h
  seeds := by
    classical
    rintro ⟨p,a⟩ hs
    obtain ⟨s,hs,ha⟩ := of_decide_eq_true hs
    change C.seedGate s=p at hs
    subst p
    have h := hE (.seed s) a ha
    rw [C.affineSrc_seed s a,C.affineDst_seed s] at h
    exact h.trans ((hQ .dummy a).image_const (0 : Bit))
  tests := by
    classical
    rintro ⟨p,a⟩ ht
    obtain ⟨t,ht,ha⟩ := of_decide_eq_true ht
    change C.testGate t=p at ht
    subst p
    have h := hE (.test t) a ha
    rw [C.affineSrc_test t a,C.affineDst_test t] at h
    exact h.trans ((hQ .dummy a).image_const (1 : Bit))

end Schematic
end WLTime.CircuitEncoding

namespace WLTime.CircuitEncoding.Circuit
variable {G : Type uG} {E : Type uE} {H : Type uH} {F : Type uF} (C : Circuit G E) (D : Circuit H F) (f : G ≃ H)

def EdgeCover : Prop := ∀ g s p,
  (∃ e,C.dst e=g ∧ C.src e=s ∧ (C.port e).val=p) ↔
  ∃ e,D.dst e=f g ∧ D.src e=f s ∧ (D.port e).val=p

end WLTime.CircuitEncoding.Circuit

namespace WLTime.CircuitEncoding.BoxTableau
open ProductBox
open Tableau

inductive Label (Alphabet : Type uAlphabet) (d q : ℕ) where
  | left (a b c : Alphabet) (time : Fin d) (space : Fin (q+1))
  | center (a b c : Alphabet) (time : Fin d)
  | bridge (a b c : Alphabet)
  | right (a b c : Alphabet) (time : Fin d) (space : Fin (q+1))
  | out (a b c : Alphabet)
  deriving DecidableEq

abbrev Tag (d q : ℕ) := (Fin d × Fin (q+1)) ⊕ Fin d ⊕ Unit ⊕ (Fin d × Fin (q+1)) ⊕ Unit

def labelEquiv (Alphabet : Type uAlphabet) (d q : ℕ) : Label Alphabet d q ≃ Alphabet × Alphabet × Alphabet × Tag d q where
  toFun
    | .left a b c t j => (a,b,c,.inl (t,j))
    | .center a b c t => (a,b,c,.inr (.inl t))
    | .bridge a b c => (a,b,c,.inr (.inr (.inl ())))
    | .right a b c t j => (a,b,c,.inr (.inr (.inr (.inl (t,j)))))
    | .out a b c => (a,b,c,.inr (.inr (.inr (.inr ()))))
  invFun
    | (a,b,c,.inl (t,j)) => .left a b c t j
    | (a,b,c,.inr (.inl t)) => .center a b c t
    | (a,b,c,.inr (.inr (.inl _))) => .bridge a b c
    | (a,b,c,.inr (.inr (.inr (.inl (t,j))))) => .right a b c t j
    | (a,b,c,.inr (.inr (.inr (.inr _)))) => .out a b c
  left_inv e := by cases e <;> rfl
  right_inv e := by
    rcases e with ⟨a,b,c,(⟨t,j⟩ | t | u | ⟨t,j⟩ | u)⟩
    · rfl
    · rfl
    · cases u; rfl
    · rfl
    · cases u; rfl

instance instFintypeLabel {Alphabet : Type uAlphabet} [Fintype Alphabet] (d q : ℕ) : Fintype (Label Alphabet d q) :=
  Fintype.ofEquiv _ (labelEquiv Alphabet d q).symm

variable {Alphabet : Type uAlphabet} {d q m : ℕ}
variable (F : Alphabet → Alphabet → Alphabet → Alphabet)

def src : Label Alphabet d q → Gate Alphabet
  | .left a _ _ _ _ => .scalar a
  | .center _ b _ _ => .scalar b
  | .bridge a b c => .first a b c
  | .right _ _ c _ _ => .scalar c
  | .out a b c => .second a b c

def dst : Label Alphabet d q → Gate Alphabet
  | .left a b c _ _ => .first a b c
  | .center a b c _ => .first a b c
  | .bridge a b c => .second a b c
  | .right a b c _ _ => .second a b c
  | .out a b c => .scalar (F a b c)

def port : (e : Label Alphabet d q) → Fin (dst F e).kind.dim
  | .left _ _ _ _ _ => (0 : Fin 2)
  | .center _ _ _ _ => (1 : Fin 2)
  | .bridge _ _ _ => (0 : Fin 2)
  | .right _ _ _ _ _ => (1 : Fin 2)
  | .out _ _ _ => (0 : Fin 1)

def box : Label Alphabet d q → ProductBox.Box (d+q) m
  | .left _ _ _ p s => (ProductBox.Box.carry p.castSucc).product (ProductBox.Box.carry s)
  | .center _ _ _ p => (ProductBox.Box.carry p.castSucc).product (ProductBox.Box.identity q m)
  | .bridge _ _ _ => ProductBox.Box.identity (d+q) m
  | .right _ _ _ p s => (ProductBox.Box.carry p.castSucc).product (ProductBox.Box.carry s).reverse
  | .out _ _ _ => ProductBox.Box.identity (d+q) m

def Numerical (e : Label Alphabet d q) (a b : ProductBox.Address (d+q) m) : Prop :=
  let t := Digits.value (ProductBox.time a)
  let t' := Digits.value (ProductBox.time b)
  let j := Digits.encode (ProductBox.space a)
  let j' := Digits.encode (ProductBox.space b)
  match e with
  | .left _ _ _ _ _ => t'=t+1 ∧ j'=Digits.inc (m^q) j
  | .center _ _ _ _ => t'=t+1 ∧ j'=j
  | .bridge _ _ _ => a=b
  | .right _ _ _ _ _ => t'=t+1 ∧ j'=(Digits.inc (m^q)).symm j
  | .out _ _ _ => a=b

theorem box_numerical (e : Label Alphabet d q) {a b : ProductBox.Address (d+q) m}
    (h : (box e).Rel a b) : Numerical e a b := by
  cases e with
  | left x y z p s =>
    obtain ⟨ht,hj⟩ := (ProductBox.Box.product_relation _ _ _ _).mp h
    exact ⟨(Digits.nonwrap_relation _ _).mp ⟨p,ht⟩,
      (ProductBox.Box.carry_rel _ _).mp ⟨s,hj⟩⟩
  | center x y z p =>
    obtain ⟨ht,hj⟩ := (ProductBox.Box.product_relation _ _ _ _).mp h
    exact ⟨(Digits.nonwrap_relation _ _).mp ⟨p,ht⟩,
      congrArg Digits.encode ((ProductBox.Box.identity_rel _ _).mp hj).symm⟩
  | bridge => exact (ProductBox.Box.identity_rel _ _).mp h
  | right x y z p s =>
    obtain ⟨ht,hj⟩ := (ProductBox.Box.product_relation _ _ _ _).mp h
    exact ⟨(Digits.nonwrap_relation _ _).mp ⟨p,ht⟩,
      (ProductBox.Box.borrow_rel _ _).mp ⟨s,hj⟩⟩
  | out => exact (ProductBox.Box.identity_rel _ _).mp h

def nodeMap (g : Gate Alphabet × ProductBox.Address (d+q) m) :
    Tableau.Node Alphabet (Fin (m^q)) (m^d) :=
  (g.1,Digits.encode (ProductBox.time g.2),Digits.encode (ProductBox.space g.2))

def nodeEquiv : (Gate Alphabet × ProductBox.Address (d+q) m) ≃
    Tableau.Node Alphabet (Fin (m^q)) (m^d) :=
  Equiv.prodCongr (Equiv.refl _) ProductBox.addressEquiv

@[simp] theorem nodeEquiv_apply (g : Gate Alphabet × ProductBox.Address (d+q) m) :
    nodeEquiv g=nodeMap g := rfl

theorem numerical_forward (e : Label Alphabet d q) {a b : ProductBox.Address (d+q) m}
    (h : Numerical e a b) :
    Tableau.rank (nodeMap (src e,a)) < Tableau.rank (nodeMap (dst F e,b)) := by
  cases e <;> simp only [Numerical] at h
  all_goals simp only [Tableau.rank,nodeMap,src,dst,Gate.phase,Digits.value] at *
  all_goals first | omega | subst b; omega

theorem box_forward (e : Label Alphabet d q) (a : ProductBox.Address (d+q) m)
    (ha : (box e).Allowed a) :
    Tableau.rank (nodeMap (src e,a)) <
      Tableau.rank (nodeMap (dst F e,(box e).apply a)) :=
  numerical_forward F e (box_numerical e ⟨ha,rfl⟩)

section Initialization
open scoped Classical
variable (input : Fin m → Alphabet) (blank : Alphabet)

noncomputable def initialDigit (a : ProductBox.Address (q+1) m) : Alphabet :=
  if ∀ i : Fin q,(a i.succ).val=0 then input (a 0) else blank

noncomputable def initialRing (j : Fin (m^(q+1))) : Alphabet :=
  initialDigit input blank (Digits.encode.symm j)

def seedGate : Alphabet ⊕ Fin q → Gate Alphabet
  | .inl f => .scalar f
  | .inr _ => .scalar blank

noncomputable def positionDomain : Alphabet ⊕ Fin q → Fin (q+1) → Finset (Fin m)
  | .inl f => Fin.cases (Finset.univ.filter fun x => input x=f)
      (fun _ => Finset.univ.filter fun x => x.val=0)
  | .inr i => fun j => Finset.univ.filter fun x => j=i.succ → x.val≠0

noncomputable def seedDomain (s : Alphabet ⊕ Fin q) : Fin (d+(q+1)) → Finset (Fin m) :=
  Fin.addCases (fun _ => Finset.univ.filter fun x => x.val=0) (positionDomain input s)

variable (accepting : Alphabet → Prop)

def testGate (f : {f : Alphabet // accepting f}) : Gate Alphabet := .scalar f.val

noncomputable def testDomain (_f : {f : Alphabet // accepting f}) :
    Fin (d+(q+1)) → Finset (Fin m) :=
  Fin.addCases (fun _ => Finset.univ.filter fun x => x.val+1=m) (fun _ => Finset.univ)

theorem test_allowed (f : {f : Alphabet // accepting f}) (a : ProductBox.Address (d+(q+1)) m) :
    ProductAllowed (testDomain accepting f) a ↔ Digits.value (ProductBox.time a)+1=m^d := by
  rw [Digits.value_last_iff]
  simp only [ProductAllowed,testDomain,Fin.forall_fin_add,Fin.addCases_left,
    Fin.addCases_right,Finset.mem_filter,Finset.mem_univ,true_and,and_true,forall_const]

theorem terminal (e : Label Alphabet d (q+1)) (a : ProductBox.Address (d+(q+1)) m)
    (ha : (box e).Allowed a) (f : {f : Alphabet // accepting f})
    (he : testGate accepting f=src e) : ¬ProductAllowed (testDomain accepting f) a := by
  intro ht
  have ht' := (test_allowed accepting f a).mp ht
  have hn := box_numerical e ⟨ha,rfl⟩
  have hl := (Digits.encode (ProductBox.time ((box e).apply a))).isLt
  cases e <;> simp only [testGate,src,Gate.scalar.injEq,reduceCtorEq] at he
  all_goals simp only [Numerical] at hn
  all_goals change Digits.value (ProductBox.time ((box _).apply a))< m^d at hl
  all_goals omega

noncomputable def schematic : Schematic (d+(q+1)) m (Gate Alphabet)
    (Label Alphabet d (q+1)) (Alphabet ⊕ Fin q) {f : Alphabet // accepting f} where
  kind := Gate.kind
  src := src
  dst := dst F
  port := port F
  domain e := (box e).domain
  coord e i x := (box e).coord i x.val
  coord_inj e i := (box e).coord i |>.injective.comp Subtype.val_injective
  seedGate := seedGate blank
  seedDomain := seedDomain input
  testGate := testGate accepting
  testDomain := testDomain accepting
  seed_scalar s := by cases s <;> rfl
  test_scalar _ := rfl
  rank g := Tableau.rank (nodeMap g)
  forward e a ha := box_forward F e a ha
  test_terminal := terminal accepting

end Initialization

end WLTime.CircuitEncoding.BoxTableau

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Simulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uJ uK uAlphabet

namespace WLTime.OneTape
variable (M : OneTape)
open CircuitEncoding

 def blankCell : M.Cell := (⟨0,by have := M.symbols_ge; omega⟩,none)

 def inputCell (w : List Bool) (i : Fin w.length) : M.Cell :=
  (M.toTM.symbol (w.getD i.val false),
    if i.val=0 then some ⟨0,by have := M.states_ge; omega⟩ else none)

end WLTime.OneTape

namespace WLTime.CircuitEncoding.BoxTableau
open NatCode ProductBox
namespace Formula
variable {Alphabet : Type uAlphabet} {J : Type uJ} {d q m : ℕ}

def labelDomain (e : Label Alphabet d q) (M a : Expr J) : Fin (d+q) → Predicate J :=
  match e with
  | .left _ _ _ t s => Fin.addCases (fun i => ProductBox.Formula.carryDomain t.castSucc i M a)
      (fun i => ProductBox.Formula.carryDomain s i M a)
  | .center _ _ _ t => Fin.addCases (fun i => ProductBox.Formula.carryDomain t.castSucc i M a)
      (fun _ => .truth true)
  | .bridge _ _ _ => fun _ => .truth true
  | .right _ _ _ t s => Fin.addCases (fun i => ProductBox.Formula.carryDomain t.castSucc i M a)
      (fun i => ProductBox.Formula.borrowDomain s i M a)
  | .out _ _ _ => fun _ => .truth true

def labelCoord (e : Label Alphabet d q) (M a : Expr J) : Fin (d+q) → Expr J :=
  match e with
  | .left _ _ _ t s => Fin.addCases (fun i => ProductBox.Formula.carryCoord t.castSucc i M a)
      (fun i => ProductBox.Formula.carryCoord s i M a)
  | .center _ _ _ t => Fin.addCases (fun i => ProductBox.Formula.carryCoord t.castSucc i M a) (fun _ => a)
  | .bridge _ _ _ => fun _ => a
  | .right _ _ _ t s => Fin.addCases (fun i => ProductBox.Formula.carryCoord t.castSucc i M a)
      (fun i => ProductBox.Formula.borrowCoord s i M a)
  | .out _ _ _ => fun _ => a

noncomputable def position (input : Alphabet → Expr J → Predicate J) (s : Alphabet ⊕ Fin q)
    (a : Expr J) : Fin (q+1) → Predicate J :=
  match s with
  | .inl f => Fin.cases (input f a) (fun _ => .eq a (.const 0))
  | .inr i => fun j => if j=i.succ then (Predicate.eq a (.const 0)).neg else .truth true

noncomputable def seed (input : Alphabet → Expr J → Predicate J) (s : Alphabet ⊕ Fin q)
    (a : Expr J) : Fin (d+(q+1)) → Predicate J :=
  Fin.addCases (fun _ => .eq a (.const 0)) (position input s a)

def test (M a : Expr J) : Fin (d+(q+1)) → Predicate J :=
  Fin.addCases (fun _ => .eq (.binary .add a (.const 1)) M) (fun _ => .truth true)

end Formula
end WLTime.CircuitEncoding.BoxTableau

namespace WLTime.OneTape
open NatCode
variable (M : OneTape) {J : Type uJ}
noncomputable def inputPredicate (f : M.Cell) (a : Expr J) : Predicate J := by
  classical
  exact (((Predicate.bit a).conj (.truth (decide (M.toTM.symbol true=f.1)))).disj
    ((Predicate.bit a).neg.conj (.truth (decide (M.toTM.symbol false=f.1))))).conj
      (((Predicate.eq a (.const 0)).conj (.truth (decide (some (⟨0,by have := M.states_ge; omega⟩ : Fin M.states)=f.2)))).disj
        ((Predicate.eq a (.const 0)).neg.conj (.truth (decide ((none : Option (Fin M.states))=f.2)))))

end WLTime.OneTape

namespace WLTime.NatCode
variable {J : Type uJ}
namespace Predicate

@[simp] theorem bounded_disj (p q : Predicate J) (σ : J → ℕ) (w : List Bool) (B : ℕ) :
    (p.disj q).Bounded σ w B ↔ p.Bounded σ w B ∧ q.Bounded σ w B := Iff.rfl

@[simp] theorem bounded_all (l : List (Predicate J)) (σ : J → ℕ) (w : List Bool) (B : ℕ) :
    (all l).Bounded σ w B ↔ ∀p∈l,p.Bounded σ w B := by
  induction l with
  | nil => simp only [all,List.foldr_nil,Bounded,List.not_mem_nil,false_implies,implies_true]
  | cons p l ih =>
    change p.Bounded σ w B ∧ (all l).Bounded σ w B ↔ _
    simp only [ih,List.mem_cons,forall_eq_or_imp]

@[simp] theorem bounded_any (l : List (Predicate J)) (σ : J → ℕ) (w : List Bool) (B : ℕ) :
    (any l).Bounded σ w B ↔ ∀p∈l,p.Bounded σ w B := by
  simp only [any,Bounded,bounded_all,List.mem_map,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂]
end Predicate
end WLTime.NatCode

end OAI
end

section
-- module Solutions.OAIQW_WLTime.GraphFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uJ uT uP uE uA uB uA' uB' uV uW uU

namespace WLTime.Compression
open NatCode
namespace FormalName
variable {T : Type uT} {J : Type uJ}
def Bounded (σ : J → ℕ) (w : List Bool) (B : ℕ) (n : FormalName T J) : Prop :=
  n.first.Bounded σ w B ∧ n.second.Bounded σ w B
end FormalName
end WLTime.Compression

namespace WLTime.OneTape.Symbolic
open CircuitEncoding NatCode Compression
variable (M : OneTape) (d q : ℕ)

abbrev Node := Schematic.Node (Tableau.Gate M.Cell) (BoxTableau.Label M.Cell d (q+1))
abbrev Edge := Schematic.Edge (BoxTableau.Label M.Cell d (q+1)) (M.Cell ⊕ Fin q)
  {f : M.Cell // M.letterAccepting f}

noncomputable def schema (w : List Bool) : Schematic (d+q+1) w.length (Tableau.Gate M.Cell)
    (BoxTableau.Label M.Cell d (q+1)) (M.Cell ⊕ Fin q) {f : M.Cell // M.letterAccepting f} :=
  BoxTableau.schematic (d:=d) (q:=q) M.localRule (M.inputCell w) M.blankCell M.letterAccepting

noncomputable def instanceData (w : List Bool) : ConsistencyData (d+q+1) w.length (Node M d q) (Edge M d q) :=
  (schema M d q w).consistency

variable {J : Type uJ}
noncomputable def domain (N : Expr J) : Edge M d q → Fin (d+q+1) → Expr J → Predicate J
  | .first e,i,a => BoxTableau.Formula.labelDomain e N a i
  | .second e,i,a => BoxTableau.Formula.labelDomain e N a i
  | .third e,i,a => BoxTableau.Formula.labelDomain e N a i
  | .seed s,i,a => BoxTableau.Formula.seed (d:=d) (q:=q) M.inputPredicate s a i
  | .test _,i,a => BoxTableau.Formula.test (d:=d) (q:=q) N a i

def coord (N : Expr J) : Edge M d q → Fin (d+q+1) → Expr J → Expr J
  | .third e,i,a => BoxTableau.Formula.labelCoord e N a i
  | _,_,a => a

abbrev BlockTag (K : ℕ) := ConsistencyData.BlockTag (r:=d+q) (P:=Node M d q) (E:=Edge M d q) K
abbrev Values (K : ℕ) := (instanceData M d q []).TagValues K

noncomputable def validity (N : Expr J) (K : ℕ) (ε : F₂) (t : BlockTag M d q K)
    (v : Values M d q K) (a b : Expr J) : Predicate J :=
  (instanceData M d q []).validPredicate (domain M d q N) K ε t v a b

noncomputable def adjacent (N : Expr J) (K : ℕ) (t u : BlockTag M d q K)
    (v z : Values M d q K) (a b c e : Expr J) : Predicate J :=
  (instanceData M d q []).adjacencyPredicate (coord M d q N) K t u v z a b c e

end WLTime.OneTape.Symbolic

namespace WLTime.Compression.ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} (I : ConsistencyData (r+1) m P E)

abbrev Rect (K : ℕ) := BlockTag (r:=r) (P:=P) (E:=E) K × I.TagValues K × Fin m × Fin m

noncomputable def rectEquiv (K : ℕ) : I.Rect K ≃ I.Descriptor K where
  toFun x := (makeBlock K x.1 x.2.2.1 x.2.2.2,x.2.1)
  invFun x := match x.1 with
    | .site i t a b => ((i,.inl t),x.2,a,b)
    | .square i l a b => ((i,.inr l),x.2,a,b)
  left_inv x := by rcases x with ⟨⟨i,t|l⟩,v,a,b⟩ <;> rfl
  right_inv x := by rcases x with ⟨b,v⟩; cases b <;> rfl

def RectValid (K : ℕ) (ε : F₂) (v : I.Rect K) : Prop :=
  I.DescriptorValid K ε (I.rectEquiv K v)

noncomputable def rectVertexEquiv (K : ℕ) (hK : 0<K) (hr : 1≤r) (ε : F₂) :
    {v : I.Rect K // I.RectValid K ε v} ≃ I.Vertex K ε :=
  (Equiv.subtypeEquiv (I.rectEquiv K) (fun _ => Iff.rfl)).trans (I.descriptorEquiv K hK hr ε)

variable [Fintype P] [Fintype E]
open scoped Classical

noncomputable def mixedCode (K : ℕ) (t : BlockTag (r:=r) (P:=P) (E:=E) K) (a b : Fin m) : ℕ :=
  (b.val+m*(a.val+m*(Fintype.equivFin _ t).val))+1

noncomputable def rawCode (K : ℕ) : RawBlock (r:=r) (m:=m) (P:=P) (E:=E) K → ℕ
  | .site i t a b => mixedCode (P:=P) (E:=E) K (i,.inl t) a b
  | .square i e a b => mixedCode (P:=P) (E:=E) K (i,.inr e) a b

noncomputable def rectCoefficient (K : ℕ) :=
  Fintype.card (BlockTag (r:=r) (P:=P) (E:=E) K)*Fintype.card (I.TagValues K)

noncomputable def spacedCount (K : ℕ) (v : I.Block K) : ℕ :=
  rawCode K v.val*(I.rectCoefficient K*m^2+1)

noncomputable def slotLimit (K : ℕ) : ℕ := (I.rectCoefficient K*m^2+1)^2+1

noncomputable def slots (K : ℕ) (hK : 0<K) (hr : 1≤r) (ε : F₂) (q : ℕ) :
    (I.Rect K × Fin (I.slotLimit K)) ⊕ Fin q → Option (Marking.Slot (I.Vertex K ε) (fun v => I.spacedCount K v.1)) :=
  Marking.decodeSlots (I.rectVertexEquiv K hK hr ε) (I.slotLimit K) q

noncomputable def rectangularGraph (K : ℕ) (hK : 0<K) (hr : 1≤r) (ε : F₂) (q : ℕ) :=
  Marking.rawGraph (I.valuationGraph K ε) (I.slots K hK hr ε q)
end WLTime.Compression.ConsistencyData

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Writer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uD uV uJ uK uL uT

namespace WLTime.Marking
variable {D : Type uD} {V : Type uV} {p : D → Prop} {count : V → ℕ}

def rectangleAdj (R : D → D → Prop) (c : D → ℕ) (d e : D) (i j : ℕ) : Prop :=
  p d ∧ p e ∧ i ≤ c d ∧ j ≤ c e ∧
    ((i=0 ∧ j=0 ∧ R d e) ∨ (i=0 ∧ j≠0 ∧ d=e) ∨ (i≠0 ∧ j=0 ∧ d=e))

end WLTime.Marking

namespace WLTime.NatCode
namespace Expr
variable {J : Type uJ}
def add (a b : Expr J) : Expr J := .binary .add a b
def mul (a b : Expr J) : Expr J := .binary .mul a b
@[simp] theorem add_eval (a b : Expr J) (σ : J → ℕ) (w : List Bool) :
    (a.add b).eval σ w=a.eval σ w+b.eval σ w := rfl
@[simp] theorem mul_eval (a b : Expr J) (σ : J → ℕ) (w : List Bool) :
    (a.mul b).eval σ w=a.eval σ w*b.eval σ w := rfl
end Expr
namespace Predicate
variable {J : Type uJ}
def le (a b : Expr J) : Predicate J := (Predicate.lt b a).neg
@[simp] theorem le_holds (a b : Expr J) (σ : J → ℕ) (w : List Bool) :
    (le a b).Holds σ w ↔ a.eval σ w≤b.eval σ w := by
  exact Nat.not_lt

def rectangular (p q R same : Predicate J) (a b i j : Expr J) : Predicate J :=
  p.conj (q.conj ((le i a).conj ((le j b).conj
    (((Predicate.eq i (Expr.const 0)).conj ((Predicate.eq j (Expr.const 0)).conj R)).disj
      (((Predicate.eq i (Expr.const 0)).conj ((Predicate.eq j (Expr.const 0)).neg.conj same)).disj
        ((Predicate.eq i (Expr.const 0)).neg.conj ((Predicate.eq j (Expr.const 0)).conj same)))))))
end Predicate
end WLTime.NatCode

namespace WLTime.OneTape.Symbolic
open CircuitEncoding NatCode Compression
variable (M : OneTape) (d q K : ℕ)
open scoped Classical
noncomputable def coefficient : ℕ := (instanceData M d q []).rectCoefficient K

variable {J : Type uJ}
noncomputable def countExpr (N : Expr J) (t : BlockTag M d q K) (a b : Expr J) : Expr J :=
  ((b.add (N.mul (a.add (N.mul (Expr.const (Fintype.equivFin _ t).val))))).add (Expr.const 1)).mul
    (((Expr.const (coefficient M d q K)).mul (N.mul N)).add (Expr.const 1))

noncomputable def sameRect (t u : BlockTag M d q K) (v z : Values M d q K)
    (a b c e : Expr J) : Predicate J :=
  (Predicate.truth (decide (t=u ∧ v=z))).conj ((Predicate.eq a c).conj (Predicate.eq b e))

noncomputable def slotPredicate (N : Expr J) (ε : F₂) (t u : BlockTag M d q K)
    (v z : Values M d q K) (a b i c e j : Expr J) : Predicate J :=
  Predicate.rectangular (validity M d q N K ε t v a b) (validity M d q N K ε u z c e)
    (adjacent M d q N K t u v z a b c e) (sameRect M d q K t u v z a b c e)
    (countExpr M d q K N t a b) (countExpr M d q K N u c e) i j

end WLTime.OneTape.Symbolic

namespace WLTime.NatCode
open TypedStack UnaryPrograms
universe u

inductive Writer : Type u → Type (u+1) where
  | emit {K : Type u} (p : Predicate K) : Writer K
  | seq {K : Type u} (a b : Writer K) : Writer K
  | loop {K : Type u} (n : Expr K) (body : Writer (Option K)) : Writer K

namespace Writer
variable {K : Type u}

def eval {K : Type u} : Writer K → (K → ℕ) → List Bool → List Bool
  | .emit p,σ,w => [decide (p.Holds σ w)]
  | .seq a b,σ,w => a.eval σ w++b.eval σ w
  | .loop n body,σ,w => (List.range (n.eval σ w)).flatMap (fun i => body.eval (Option.elim' i σ) w)

def depth {K : Type u} : Writer K → ℕ
  | .emit _ => 0
  | .seq a b => max a.depth b.depth
  | .loop _ body => body.depth+1

def charge {K : Type u} : Writer K → ℕ
  | .emit p => 4*p.code.charge+20
  | .seq a b => a.charge+b.charge
  | .loop n body => n.charge+body.charge+100

def Safe {K : Type u} : Writer K → (K → ℕ) → List Bool → ℕ → Prop
  | .emit p,σ,w,B => p.Bounded σ w B
  | .seq a b,σ,w,B => a.Safe σ w B ∧ b.Safe σ w B
  | .loop n body,σ,w,B => n.Bounded σ w B ∧ ∀i<n.eval σ w,body.Safe (Option.elim' i σ) w B

def compile {K : Type u} : Writer K → {L : Type uL} → [DecidableEq L] → (K → L) → L → L → Program L
  | .emit p,_,_,ρ,word,out => Program.allocate
    (Program.seq (p.code.compile (Sum.inr ∘ ρ) (.inr word) (.inl (0 : Fin 1)))
      (Program.seq (Program.ofCode (.pushDyn (.inr out) (fun z => z (.inl 0)==some true)))
        (Program.clear (.inl 0))))
  | .seq a b,_,_,ρ,word,out => Program.seq (a.compile ρ word out) (b.compile ρ word out)
  | .loop n body,_,_,ρ,word,out => Program.allocate
    (Program.seq (n.compile (Sum.inr ∘ ρ) (.inr word) (.inl (1 : Fin 2)))
      (Program.seq (Program.repeatN (.inl 1)
        (Program.seq (body.compile (Option.elim' (.inl 0) (Sum.inr ∘ ρ)) (.inr word) (.inr out))
          (Program.push (.inl 0) true)))
        (Program.seq (Program.clear (.inl 0)) (Program.clear (.inl 1)))))

end Writer
end WLTime.NatCode

namespace WLTime.NatCode
namespace Expr
variable {K : Type uK} {J : Type uJ}
def rename (f : K → J) (e : Expr K) : Expr J := e.bind (Expr.var ∘ f)
@[simp] theorem rename_eval (f : K → J) (e : Expr K) (σ : J → ℕ) (w : List Bool) :
    (e.rename f).eval σ w=e.eval (σ ∘ f) w := by simp only [rename,bind_eval,eval,Function.comp_def]

end Expr
namespace Writer
variable {K : Type uK}
def empty : Writer K := .loop (.const 0) (.emit (.truth false))
@[simp] theorem empty_eval (σ : K → ℕ) (w : List Bool) : (empty : Writer K).eval σ w=[] := rfl
@[simp] theorem empty_depth : (empty : Writer K).depth=1 := rfl
def each {T : Type uT} (l : List T) (f : T → Writer K) : Writer K := l.foldr (fun t p => .seq (f t) p) empty
@[simp] theorem each_eval {T : Type uT} (l : List T) (f : T → Writer K) (σ : K → ℕ) (w : List Bool) :
    (each l f).eval σ w=l.flatMap (fun t => (f t).eval σ w) := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    change (f t).eval σ w++(each l f).eval σ w=_
    rw [ih,List.flatMap_cons]

def grid (N L : Expr K) (body : Writer (Option (Option (Option K)))) : Writer K :=
  .loop N (.loop (N.rename some) (.loop (L.rename (some ∘ some)) body))
@[simp] theorem grid_depth (N L : Expr K) (body : Writer (Option (Option (Option K)))) :
    (grid N L body).depth=body.depth+3 := by simp only [grid,depth]
end Writer
end WLTime.NatCode

end OAI
end

section
-- module Solutions.OAIQW_WLTime.MatrixWriter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV uW uT uS uJ uR uJ'

namespace WLTime.Enumeration
variable {V : Type uV} {W : Type uW}
structure Listing (V : Type uV) where
  items : List V
  nodup : items.Nodup
  complete : ∀v,v∈items

noncomputable def Listing.equiv (l : Listing V) : Fin l.items.length ≃ V :=
  Equiv.ofBijective l.items.get ⟨List.nodup_iff_injective_get.mp l.nodup,
    fun v => List.mem_iff_get.mp (l.complete v)⟩
@[simp] theorem Listing.equiv_apply (l : Listing V) (i : Fin l.items.length) : l.equiv i=l.items.get i := rfl

noncomputable def ofFintype (V : Type uV) [Fintype V] : Listing V := by
  classical
  exact ⟨Finset.univ.toList,Finset.nodup_toList _,fun v => by simp⟩

def fin (n : ℕ) : Listing (Fin n) := ⟨List.finRange n,List.nodup_finRange n,List.mem_finRange⟩

def Listing.prod (l : Listing V) (k : Listing W) : Listing (V × W) where
  items := l.items.flatMap (fun v => k.items.map (fun w => (v,w)))
  nodup := by
    apply List.nodup_flatMap.mpr
    refine ⟨fun v _ => (List.nodup_map_iff (fun x y h => (Prod.mk.inj h).2)).mpr k.nodup,?_⟩
    apply l.nodup.imp
    intro x y hxy
    apply List.disjoint_left.mpr
    intro a ha hb
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp ha
    obtain ⟨v,_,he⟩ := List.mem_map.mp hb
    exact hxy (Prod.mk.inj he).1.symm
  complete := by
    rintro ⟨v,w⟩
    exact List.mem_flatMap.mpr ⟨v,l.complete v,List.mem_map.mpr ⟨w,k.complete w,rfl⟩⟩

def Listing.sum (l : Listing V) (k : Listing W) : Listing (V ⊕ W) where
  items := l.items.map Sum.inl ++ k.items.map Sum.inr
  nodup := by
    apply List.nodup_append.mpr
    refine ⟨(List.nodup_map_iff Sum.inl_injective).mpr l.nodup,
      (List.nodup_map_iff Sum.inr_injective).mpr k.nodup,?_⟩
    intro a ha b hb
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp ha
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hb
    exact Sum.inl_ne_inr
  complete := by
    intro v; cases v with
    | inl v => exact List.mem_append_left _ (List.mem_map.mpr ⟨v,l.complete v,rfl⟩)
    | inr w => exact List.mem_append_right _ (List.mem_map.mpr ⟨w,k.complete w,rfl⟩)

def Listing.option (l : Listing V) : Listing (Option V) where
  items := none::l.items.map some
  nodup := by
    rw [List.nodup_cons]
    exact ⟨by simp,(List.nodup_map_iff (Option.some_injective V)).mpr l.nodup⟩
  complete := by
    intro v; cases v with
    | none => exact List.mem_cons_self
    | some v => exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨v,l.complete v,rfl⟩)

end WLTime.Enumeration

namespace WLTime.Enumeration
open NatCode
variable {T : Type uT} {S : Type uS} {J : Type uJ}
abbrev Vertex (T : Type uT) (S : Type uS) (m L p : ℕ) := Option ((((T × S × Fin m × Fin m) × Fin L)) ⊕ Fin p)

def rectangle (t : Listing T) (s : Listing S) (m L p : ℕ) : Listing (Vertex T S m L p) :=
  ((t.prod (s.prod ((fin m).prod (fin m)))).prod (fin L) |>.sum (fin p)).option

def writer (t : Listing T) (s : Listing S) (N L P : Expr J)
    (hub : Writer J) (slot : T → S → Writer (Option (Option (Option J))))
    (pad : Writer (Option J)) : Writer J :=
  .seq hub (.seq (Writer.each t.items (fun t => Writer.each s.items (fun s => Writer.grid N L (slot t s))))
    (.loop P pad))

end WLTime.Enumeration

namespace WLTime.Enumeration
variable {V : Type uV}
open scoped Classical
noncomputable def Listing.matrix (l : Listing V) (G : SimpleGraph V) : Graph l.items.length :=
  Graph.ofSimple G l.equiv.symm

end WLTime.Enumeration

namespace WLTime.OneTape.Symbolic
open CircuitEncoding NatCode Compression Enumeration
variable (M : OneTape) (d q K : ℕ)
open scoped Classical

noncomputable instance valuesFintype : Fintype (Values M d q K) := by
  classical
  letI : Fintype (ConsistencyData.Tag (r:=d+q) (P:=Node M d q) (E:=Edge M d q) K) := inferInstance
  letI : ∀ t : ConsistencyData.Tag (r:=d+q) (P:=Node M d q) (E:=Edge M d q) K,
      Fintype ((instanceData M d q []).TagValue K t) := fun t => by
    cases t <;> dsimp [ConsistencyData.TagValue] <;> infer_instance
  change Fintype ((t : ConsistencyData.Tag (r:=d+q) (P:=Node M d q) (E:=Edge M d q) K) →
    (instanceData M d q []).TagValue K t)
  infer_instance

abbrev RawVertex (w : List Bool) (pad : ℕ) :=
  Enumeration.Vertex (BlockTag M d q K) (Values M d q K) w.length
    ((instanceData M d q w).slotLimit K) pad

noncomputable def listing (w : List Bool) (pad : ℕ) : Listing (RawVertex M d q K w pad) :=
  Enumeration.rectangle (ofFintype (BlockTag M d q K)) (ofFintype (Values M d q K))
    w.length ((instanceData M d q w).slotLimit K) pad

inductive Location (J : Type uJ) where
  | hub | hole
  | slot (tag : BlockTag M d q K) (value : Values M d q K) (a b i : Expr J)

namespace Location
variable {M d q K} {J : Type uJ} {J' : Type uJ'}
def rename (f : J → J') : Location M d q K J → Location M d q K J'
  | .hub => .hub
  | .hole => .hole
  | .slot t v a b i => .slot t v (a.rename f) (b.rename f) (i.rename f)
end Location

variable {J : Type uJ}
inductive Represents (σ : J → ℕ) (w : List Bool) (pad : ℕ) :
    Location M d q K J → RawVertex M d q K w pad → Prop
  | hub : Represents σ w pad .hub none
  | hole (i : Fin pad) : Represents σ w pad .hole (some (.inr i))
  | slot (t : BlockTag M d q K) (v : Values M d q K) (a b i : Expr J)
      (x y : Fin w.length) (s : Fin ((instanceData M d q w).slotLimit K))
      (ha : a.eval σ w=x.val) (hb : b.eval σ w=y.val) (hi : i.eval σ w=s.val) :
      Represents σ w pad (.slot t v a b i) (some (.inl ((t,v,x,y),s)))

noncomputable def adjacency (N : Expr J) (ε : F₂) :
    Location M d q K J → Location M d q K J → Predicate J
  | .hub,.hub => .truth false
  | .hub,_ => .truth true
  | _,.hub => .truth true
  | .slot t v a b i,.slot u z c e j => slotPredicate M d q K N ε t u v z a b i c e j
  | _,_ => .truth false

abbrev up3 {J : Type uJ} : J → Option (Option (Option J)) := some ∘ some ∘ some

def slotLocation (t : BlockTag M d q K) (v : Values M d q K) : Location M d q K (Option (Option (Option J))) :=
  .slot t v (.var (some (some none))) (.var (some none)) (.var none)

noncomputable def columns (N L P : Expr J) (ε : F₂) (row : Location M d q K J) : Writer J :=
  Enumeration.writer (ofFintype (BlockTag M d q K)) (ofFintype (Values M d q K)) N L P
    (.emit (adjacency M d q K N ε row .hub))
    (fun t v => .emit (adjacency M d q K (N.rename up3) ε (row.rename up3) (slotLocation M d q K t v)))
    (.emit (adjacency M d q K (N.rename some) ε (row.rename some) .hole))

noncomputable def matrixWriter (N L P : Expr J) (ε : F₂) : Writer J :=
  Enumeration.writer (ofFintype (BlockTag M d q K)) (ofFintype (Values M d q K)) N L P
    (columns M d q K N L P ε .hub)
    (fun t v => columns M d q K (N.rename up3) (L.rename up3) (P.rename up3) ε (slotLocation M d q K t v))
    (columns M d q K (N.rename some) (L.rename some) (P.rename some) ε .hole)

end WLTime.OneTape.Symbolic

namespace WLTime.OneTape.Symbolic
open CircuitEncoding NatCode Compression Enumeration
variable (M : OneTape) (d q K : ℕ) {J : Type uJ}
open scoped Classical

namespace Location
variable {M d q K}
def Bounded (σ : J → ℕ) (w : List Bool) (B : ℕ) : Location M d q K J → Prop
  | .slot _ _ a b i => a.Bounded σ w B ∧ b.Bounded σ w B ∧ i.Bounded σ w B ∧
      a.eval σ w<w.length ∧ b.eval σ w<w.length
  | _ => True
end Location

end WLTime.OneTape.Symbolic

end OAI
end

section
-- module Solutions.OAIQW_WLTime.MatrixBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uJ uK uL uA

namespace WLTime.OneTape.Symbolic
open CircuitEncoding NatCode Compression Enumeration
variable (M : OneTape) (d q : ℕ)
open scoped Classical

noncomputable def baseOrder (m : ℕ) : ℕ :=
  let C := coefficient M d q (d+q+2)
  1+C*m^2*((C*m^2+1)^2+1)

noncomputable def pairGraph (hr : 2≤d+q) (w : List Bool) (pad : ℕ) (ε : F₂) :
    Graph (listing M d q (d+q+2) w pad).items.length :=
  (listing M d q (d+q+2) w pad).matrix
    ((instanceData M d q w).rectangularGraph (d+q+2) (by omega) (by omega) ε pad)

variable {J : Type uJ}
noncomputable def pairWriter (N L P : Expr J) : Writer J :=
  .seq (matrixWriter M d q (d+q+2) N L P 0) (matrixWriter M d q (d+q+2) N L P 1)

end WLTime.OneTape.Symbolic

namespace WLTime.TypedStack.Code
variable {K : Type uK} {L : Type uL} {A : Type uA}
def controlSize : Code K A → ℕ
  | .skip => 1
  | .push _ _ | .pushDyn _ _ | .pop _ => 2
  | .seq p q => p.controlSize+q.controlSize
  | .branch _ p q => 1+p.controlSize+q.controlSize
  | .loop _ p => 1+p.controlSize
 @[simp] theorem relabel_controlSize (p : Code K A) (f : K → L) : (p.relabel f).controlSize=p.controlSize := by
  induction p <;> simp_all [relabel,controlSize]
end WLTime.TypedStack.Code

namespace WLTime.TypedStack.Program
variable {K : Type uK} [DecidableEq K]

def seqShared (p q : Program K) : Program K :=
  ⟨max p.scratch q.scratch,.seq
    (p.code.relabel (embed (Fin.castLE (Nat.le_max_left _ _))))
    (q.code.relabel (embed (Fin.castLE (Nat.le_max_right _ _))))⟩
 omit [DecidableEq K] in
 @[simp] theorem seqShared_size (p q : Program K) :
    (seqShared p q).code.controlSize=p.code.controlSize+q.code.controlSize := by
  simp only [seqShared,Code.controlSize,Code.relabel_controlSize]
 omit [DecidableEq K] in
 @[simp] theorem pushes_scratch (a : K) (bs : List Bool) : (pushes a bs).scratch=0 := by
  induction bs <;> simp_all [pushes,skip,push,seq,ofCode]
 omit [DecidableEq K] in
 @[simp] theorem pushes_size (a : K) (bs : List Bool) : (pushes a bs).code.controlSize=2*bs.length+1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [pushes,seq,Code.controlSize,Code.relabel_controlSize,push,ofCode,ih,List.length_cons]; omega

 def doubleUnary (a : K) : Program K :=
  allocate (seqShared (copy (Sum.inr a) (Sum.inl (0 : Fin 1)))
    (ofCode (Code.transfer (Sum.inl (0 : Fin 1)) (Sum.inr a) false)))
 omit [DecidableEq K] in
 @[simp] theorem doubleUnary_scratch (a : K) : (doubleUnary a).scratch=2 := rfl

 def loadDigits (a : K) : List ℕ → Program K
  | [] => skip
  | b::bs => seqShared (loadDigits a bs)
      (seqShared (doubleUnary a) (pushes a (UnaryPrograms.numeral b)))
 def loadNat (a : K) (n : ℕ) : Program K := loadDigits a (Nat.digits 2 n)
end WLTime.TypedStack.Program

namespace WLTime.TypedStack.Code
variable {K : Type uK} [DecidableEq K]
def countLoop (a b : K) : Code K Bool := .loop (nonempty a) (.seq (.pop a) (.push b true))
end WLTime.TypedStack.Code
namespace WLTime.TypedStack.Program
variable {K : Type uK} [DecidableEq K]
def countLength (a b : K) : Program K := allocate
  (seq (copy (.inr a) (.inl (0 : Fin 1))) (ofCode (Code.countLoop (.inl (0 : Fin 1)) (.inr b))))
end WLTime.TypedStack.Program

namespace WLTime.NatCode.Expr
variable {K : Type uK}
def degree : Expr K → ℕ
  | .const _ | .var _ => 1
  | .binary _ a b => a.degree+b.degree+1
  | .bit a => a.degree+1

def AtomsBounded (σ : K → ℕ) (Q : ℕ) : Expr K → Prop
  | .const n => n≤Q
  | .var k => σ k≤Q
  | .binary _ a b => a.AtomsBounded σ Q ∧ b.AtomsBounded σ Q
  | .bit a => a.AtomsBounded σ Q

end WLTime.NatCode.Expr

end OAI
end

section
-- module Solutions.OAIQW_WLTime.TapePair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK uA uB uL uS uT

namespace WLTime.OneTape.Symbolic
open NatCode TypedStack UnaryPrograms
open scoped Classical
variable (M : OneTape) (d q : ℕ)
namespace FullWriter
inductive Reg where
  | word | len | order | output
  deriving DecidableEq
instance instFintypeReg : Fintype Reg := ⟨{.word,.len,.order,.output},by intro r; cases r <;> simp⟩

def args (m n : ℕ) : Bool → ℕ := fun b => if b then n else m
def N : Expr Bool := .var false
noncomputable def R : Expr Bool := .binary .mul (.const (coefficient M d q (d+q+2))) (.binary .mul N N)
noncomputable def E : Expr Bool := .binary .add (R M d q) (.const 1)
noncomputable def L : Expr Bool := .binary .add (.binary .mul (E M d q) (E M d q)) (.const 1)
noncomputable def B : Expr Bool := .binary .add (.const 1) (.binary .mul (R M d q) (L M d q))
noncomputable def P : Expr Bool := .binary .sub (.var true) (B M d q)
noncomputable def body : Writer Bool := pairWriter M d q N (L M d q) (P M d q)
def rho : Bool → Reg := fun b => if b then .order else .len
noncomputable def program (n : ℕ) : Program Reg :=
  .seqShared (.countLength .word .len)
    (.seqShared (.loadNat .order n)
      (.seqShared (.pushes .output (encodeNat n).reverse)
        ((body M d q).compile rho .word .output)))

noncomputable def budget (n m : ℕ) : ℕ :=
  17*m+3+24*((Nat.digits 2 n).length+1)*(n+1)+(2*(encodeNat n).length+1)+
    (body M d q).charge*(6*(coefficient M d q (d+q+2)+n+m+2)^27+1)^8

end FullWriter
end WLTime.OneTape.Symbolic

namespace WLTime.TypedStack.Code
variable {K : Type uK} {A : Type uA} {B : Type uB} [DecidableEq K]
def mapLetters (f : A → B) (g : B → A) : Code K A → Code K B
  | .skip => .skip
  | .push k x => .push k (f x)
  | .pushDyn k h => .pushDyn k (fun v => f (h (fun k => (v k).map g)))
  | .pop k => .pop k
  | .seq p q => .seq (p.mapLetters f g) (q.mapLetters f g)
  | .branch test p q => .branch (fun v => test (fun k => (v k).map g)) (p.mapLetters f g) (q.mapLetters f g)
  | .loop test p => .loop (fun v => test (fun k => (v k).map g)) (p.mapLetters f g)
 def listMap (f : A → B) (s : Stacks K A) : Stacks K B := fun k => (s k).map f
 omit [DecidableEq K] in
 @[simp] theorem mapLetters_size (p : Code K A) (f : A → B) (g : B → A) :
    (p.mapLetters f g).controlSize=p.controlSize := by induction p <;> simp_all [mapLetters,controlSize]
end WLTime.TypedStack.Code

namespace WLTime.TypedStack.Command
variable {K : Type uK} {L : Type uL} {A : Type uA} {S : Type uS} {T : Type uT}
def transport (f : K → L) (g : S → T) (answer : Bool → Bool) : Command K A S → Command L A T
  | .next q => .next (g q)
  | .push k x q => .push (f k) x (g q)
  | .pop k q => .pop (f k) (g q)
  | .halt b => .halt (answer b)
end WLTime.TypedStack.Command

namespace WLTime.TapePair
variable {A : Type uA}
structure Tape (A : Type uA) where
  left : List A
  right : List A
  deriving DecidableEq

 def contents (blank : A) (s : Tape A) (z : ℤ) : A :=
  if z<0 then s.left.getD (-z-1).toNat blank else s.right.getD z.toNat blank

 def moveWrite (blank x : A) (d : Move) (s : Tape A) : Tape A := match d with
  | .stay => ⟨s.left,x::s.right.tail⟩
  | .right => ⟨x::s.left,s.right.tail⟩
  | .left => ⟨s.left.tail,s.left.headD blank::x::s.right.tail⟩

@[simp] theorem contents_zero (blank : A) (s : Tape A) : contents blank s 0=s.right.headD blank := by
  simp only [contents,show ¬(0:ℤ)<0 by omega,ite_false,Int.toNat_zero]
  cases s.right <;> rfl

end WLTime.TapePair

namespace WLTime.TMStack
open TypedStack
variable {K : Type uK} {A : Type uA} [DecidableEq K]

def store (s : K → TapePair.Tape A) : Stacks (K × Bool) A :=
  fun k => if k.2 then (s k.1).right else (s k.1).left

def single (blank : A) (k : K) (x : A) : Move → Code (K × Bool) A
  | .stay => .seq (.pop (k,true)) (.push (k,true) x)
  | .right => .seq (.pop (k,true)) (.push (k,false) x)
  | .left => .seq (.seq (.seq (.pop (k,true)) (.push (k,true) x))
      (.pushDyn (k,true) (fun v => (v (k,false)).getD blank))) (.pop (k,false))

def tapeCost : Move → ℕ
  | .left => 8
  | _ => 4

def body (blank : A) (w : K → A) (d : K → Move) : List K → Code (K × Bool) A
  | [] => .skip
  | k::ks => .seq (single blank k (w k) (d k)) (body blank w d ks)

def bodyCost (d : K → Move) (ks : List K) := (ks.map (tapeCost ∘ d)).sum+1

end WLTime.TMStack

namespace WLTime.TMStack
open TypedStack
variable (M : TM)

def blank : Fin M.symbols := ⟨0,by have := M.symbols_ge; omega⟩
instance moveFintype : Fintype Move := ⟨{.left,.stay,.right},by intro d; cases d <;> simp⟩

abbrev Payload := Fin M.states × (Fin M.tapes → Fin M.symbols) × (Fin M.tapes → Move)
def stepCode (p : Payload M) : Code (Fin M.tapes × Bool) (Fin M.symbols) :=
  body (blank M) p.2.1 p.2.2 (List.finRange M.tapes)
abbrev State := Fin M.states ⊕ (p : Payload M) × (stepCode M p).State
noncomputable instance instFintypeState : Fintype (State M) := inferInstanceAs
  (Fintype (Fin M.states ⊕ (p : Payload M) × (stepCode M p).State))

def transition : State M → Tops (Fin M.tapes × Bool) (Fin M.symbols) →
    Command (Fin M.tapes × Bool) (Fin M.symbols) (State M)
  | .inl q,v => if q.val=1 then .halt true else if q.val=2 then .halt false else
      let p := M.transition q (fun a => (v (a,true)).getD (blank M))
      .next (.inr ⟨p,(stepCode M p).entry⟩)
  | .inr ⟨p,q⟩,v => Command.redirect (fun r => .inr ⟨p,r⟩) (.inl p.1)
      ((stepCode M p).transition q v)

def machine : Machine (Fin M.tapes × Bool) (Fin M.symbols) (State M) where
  inputStack := (⟨0,M.tapes_pos⟩,true)
  inputLetter := M.symbol
  initial := .inl ⟨0,by have := M.states_ge; omega⟩
  transition := transition M

def Relative (C : M.Config) (s : Fin M.tapes → TapePair.Tape (Fin M.symbols)) : Prop :=
  ∀ a z, TapePair.contents (blank M) (s a) z = C.tape a (C.head a+z)

def nextTapes (p : Payload M) (s : Fin M.tapes → TapePair.Tape (Fin M.symbols)) :=
  fun a => TapePair.moveWrite (blank M) (p.2.1 a) (p.2.2 a) (s a)

end WLTime.TMStack

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Consumer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK uA uB

namespace WLTime.TMStack
open TypedStack
variable (M : TM)

def initialTapes (w : List Bool) : Fin M.tapes → TapePair.Tape (Fin M.symbols) :=
  fun a => ⟨[],if a.val=0 then w.map M.symbol else []⟩

end WLTime.TMStack

namespace WLTime.TMConsumer
open TypedStack
variable {K : Type uK} [DecidableEq K] (M : TM)
def decode (x : Fin M.symbols) : Bool := decide (x.val=2)
def boolInput (k : K) (w : List Bool) : Stacks K Bool := fun j => if j=k then w else []
abbrev Reg (M : TM) (K : Type uK) := K ⊕ (Fin M.tapes × Bool)
def tmInput : Fin M.tapes × Bool := (⟨0,M.tapes_pos⟩,true)
def preludeCode (c : Code K Bool) (output : K) : Code (Reg M K) (Fin M.symbols) :=
  .seq ((c.mapLetters M.symbol (decode M)).relabel Sum.inl)
    (Code.transfer (.inl output) (.inr (tmInput M)) (TMStack.blank M))
abbrev State (c : Code K Bool) (output : K) := (preludeCode M c output).State ⊕ TMStack.State M
noncomputable instance instFintypeState (c : Code K Bool) (output : K) : Fintype (State M c output) := inferInstanceAs
  (Fintype ((preludeCode M c output).State ⊕ TMStack.State M))
def transition (c : Code K Bool) (output : K) (answer : Bool → Bool) : State M c output →
    Tops (Reg M K) (Fin M.symbols) → Command (Reg M K) (Fin M.symbols) (State M c output)
  | .inl q,v => Command.redirect Sum.inl (.inr (TMStack.machine M).initial) ((preludeCode M c output).transition q v)
  | .inr q,v => Command.transport Sum.inr Sum.inr answer (TMStack.transition M q (v ∘ Sum.inr))
def machine (c : Code K Bool) (input output : K) (answer : Bool → Bool) :
    Machine (Reg M K) (Fin M.symbols) (State M c output) where
  inputStack := .inl input
  inputLetter := M.symbol
  initial := .inl (preludeCode M c output).entry
  transition := transition M c output answer

variable [Fintype K]
noncomputable def oneTape (c : Code K Bool) (input output : K) (answer : Bool → Bool) : OneTape :=
  (machine M c input output answer).compile.oneTape
end WLTime.TMConsumer

namespace WLTime.StackMachine.Machine
variable (K a q : ℕ)
abbrev ControlCode := Fin 14 × Option (Fin K) × Option (Fin a) × Option (Fin q) × (Fin K → Option (Fin a))
def controlCode : SweepControl K a q → ControlCode K a q
  | .mark => (0,none,none,none,fun _ => none)
  | .seekEnd => (1,none,none,none,fun _ => none)
  | .take => (2,none,none,none,fun _ => none)
  | .bring x => (3,none,some x,none,fun _ => none)
  | .append x => (4,none,some x,none,fun _ => none)
  | .back => (5,none,none,none,fun _ => none)
  | .start z => (6,none,none,some z,fun _ => none)
  | .seek (.peek k z v) => (7,some k,none,some z,v)
  | .seek (.push k x z) => (8,some k,some x,some z,fun _ => none)
  | .seek (.pop k z) => (9,some k,none,some z,fun _ => none)
  | .read k z v => (10,some k,none,some z,v)
  | .returnPeek k z v => (11,some k,none,some z,v)
  | .erase k z => (12,some k,none,some z,fun _ => none)
  | .ret z => (13,none,none,some z,fun _ => none)
def decodeControl (c : ControlCode K a q) : Option (SweepControl K a q) :=
  let (tag,k,x,z,v) := c
  match tag.val with
  | 0 => some .mark
  | 1 => some .seekEnd
  | 2 => some .take
  | 3 => x.map .bring
  | 4 => x.map .append
  | 5 => some .back
  | 6 => z.map .start
  | 7 => do let k←k; let z←z; pure (.seek (.peek k z v))
  | 8 => do let k←k; let x←x; let z←z; pure (.seek (.push k x z))
  | 9 => do let k←k; let z←z; pure (.seek (.pop k z))
  | 10 => do let k←k; let z←z; pure (.read k z v)
  | 11 => do let k←k; let z←z; pure (.returnPeek k z v)
  | 12 => do let k←k; let z←z; pure (.erase k z)
  | _ => z.map .ret
end WLTime.StackMachine.Machine

namespace WLTime.OneTape.Symbolic.FullWriter
open NatCode TypedStack UnaryPrograms
open scoped Classical
variable (U : OneTape) (d q : ℕ)
@[simp] theorem card_reg : Fintype.card Reg=4 := by
  decide
@[simp] theorem encodeNat_length (n : ℕ) : (encodeNat n).length=2*(Nat.digits 2 n).length+1 := by
  simp only [encodeNat,List.length_append,List.length_replicate,List.length_cons,List.length_nil,List.length_map]
  omega

noncomputable def scratchBound : ℕ := (Program.countLength Reg.word Reg.len).scratch+2+
  ((body U d q).compile rho Reg.word Reg.output).scratch
noncomputable def syntaxBound : ℕ :=
  (Program.countLength Reg.word Reg.len).code.controlSize+
  (Program.doubleUnary Reg.order).code.controlSize+10+
  ((body U d q).compile rho Reg.word Reg.output).code.controlSize

noncomputable def consumer (A : TM) (n : ℕ) : OneTape :=
  TMConsumer.oneTape A (program U d q n).code (.inr Reg.word) (.inr Reg.output) not

noncomputable def consumerFactor (A : TM) : ℕ := 8*(scratchBound U d q+4+2*A.tapes+1)

end WLTime.OneTape.Symbolic.FullWriter

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Universal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLTime.OneTape.Symbolic.FullWriter
open TypedStack
open scoped Classical
variable (U : OneTape) (d q : ℕ) (A : TM)
noncomputable def tapesBound : ℕ := scratchBound U d q+4+2*A.tapes
noncomputable def alphabetBound : ℕ := 3+2*(A.symbols+3)^(tapesBound U d q A)
noncomputable def statesBound : ℕ := 3+14*(tapesBound U d q A+1)*(A.symbols+3)*
  (syntaxBound U d q+6+Fintype.card (TMStack.State A))*(A.symbols+3)^(tapesBound U d q A)

end WLTime.OneTape.Symbolic.FullWriter

namespace WLTime.Diagonal

 def unary (n : ℕ) : List Bool := List.replicate n true ++ [false]

 def moveCode : Move → ℕ
  | .left => 0 | .stay => 1 | .right => 2

abbrev Entry := ℕ × ℕ × ℕ
structure Raw where
  states : ℕ
  symbols : ℕ
  table : List Entry
  deriving DecidableEq

 def Raw.Valid (R : Raw) : Prop :=
  3 ≤ R.states ∧ 3 ≤ R.symbols ∧ R.table.length=R.states*R.symbols ∧
    ∀ e ∈ R.table, e.1<R.states ∧ e.2.1<R.symbols ∧ e.2.2<3

instance instDecidableValid (R : Raw) : Decidable R.Valid := by unfold Raw.Valid; infer_instance

 def raw (M : OneTape) : Raw where
  states := M.states
  symbols := M.symbols
  table := List.ofFn fun i : Fin (M.states*M.symbols) =>
    let p := finProdFinEquiv.symm i
    let a := M.transition p.1 p.2
    (a.1.val,a.2.1.val,moveCode a.2.2)

 def entryBits (e : Entry) : List Bool := unary e.1++unary e.2.1++unary e.2.2
 def tableBits (es : List Entry) : List Bool := (es.map entryBits).flatten
 def Raw.bits (R : Raw) : List Bool := unary R.states++unary R.symbols++tableBits R.table

 def description (M : OneTape) : List Bool := (raw M).bits

 def designation (M : OneTape) : List Bool := unary (description M).length++description M

end WLTime.Diagonal

namespace WLTime.Universal
open UnaryPrograms

def fields : List ℕ → List Bool := List.flatMap (fun n => numeral n++[false])

@[simp] theorem fields_nil : fields []=[] := rfl
@[simp] theorem fields_cons (n : ℕ) (ns : List ℕ) :
    fields (n::ns)=numeral n++false::fields ns := by
  simp only [fields,List.flatMap_cons,List.cons_append,List.nil_append,List.append_assoc]

@[simp] theorem scan_fields_cons (n : ℕ) (ns : List ℕ) :
    scan (fields (n::ns))=(n,fields ns) := by rw [fields_cons,scan_numeral]

def tile (n : ℕ) : List Bool := numeral n++[false]

@[simp] theorem fields_head (ns : List ℕ) : (scan (fields ns)).1=ns.headD 0 := by
  cases ns <;> simp [scan]
@[simp] theorem fields_tail (ns : List ℕ) : (scan (fields ns)).2=fields ns.tail := by
  cases ns <;> simp [scan]

end WLTime.Universal

namespace WLTime.Universal
open TypedStack UnaryPrograms

inductive Reg
  | tab | alpha | state | left | right | base | halt | search | index | cur | write | dir | input | temp
  deriving DecidableEq

open Reg

instance instFintypeReg : Fintype Reg := ⟨{tab,alpha,state,left,right,base,halt,search,index,cur,write,dir,input,temp},
  by intro r; cases r <;> simp⟩

def lookup : Program Reg :=
  Program.seq (Program.copy tab search) <|
  Program.seq (mulAdd state alpha index) <|
  Program.seq (Program.copy cur index) <|
  Program.seq (seek search index) <|
  Program.seq (Program.clear state) <|
  Program.seq (Program.read search state) <|
  Program.seq (Program.read search write) <|
  Program.seq (Program.read search dir) <|
  Program.seq (Program.clear search) (Program.clear index)

end WLTime.Universal

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Interpreter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK uC

namespace WLTime.Universal
open TypedStack UnaryPrograms Reg

def motionLeft : Program Reg :=
  Program.seq (prependRecord write right) <|
  Program.seq (Program.read left cur) <|
  Program.seq (prependRecord cur right) (Program.clear cur)

def motion : Program Reg :=
  Program.branch (UnaryPrograms.isTrue dir)
    (Program.seq (Program.pop dir) (Program.branch (UnaryPrograms.isTrue dir)
      (prependRecord write left) (prependRecord write right))) motionLeft

def shiftTape (x : ℕ) (d : Move) (L R : List ℕ) : List ℕ × List ℕ := match d with
  | .left => (L.tail,L.headD 0::x::R)
  | .stay => (L,x::R)
  | .right => (x::L,R)

def movedDir : Move → ℕ
  | .right => 1 | _ => 0

end WLTime.Universal

namespace WLTime.Universal
open TypedStack UnaryPrograms Reg

def haltFlag (q : ℕ) : List Bool := if q=1 then [false] else if q=2 then [true] else []

def flagTest : Program Reg :=
  Program.branch (UnaryPrograms.isTrue temp)
    (Program.seq (Program.pop temp) (Program.branch (UnaryPrograms.isTrue temp)
      (Program.seq (Program.pop temp) (Program.branch (UnaryPrograms.isTrue temp) Program.skip (Program.push halt true)))
      (Program.push halt false))) Program.skip

def flagState : Program Reg :=
  Program.seq (Program.copy state temp) (Program.seq flagTest (Program.clear temp))

end WLTime.Universal

namespace WLTime.Universal
open TypedStack UnaryPrograms Reg

def zeroSymbol (M : OneTape) : Fin M.symbols := ⟨0,by have := M.symbols_ge; omega⟩

def store (M : OneTape) (q : Fin M.states) (T : TapePair.Tape (Fin M.symbols)) (m : ℕ) :
    Stacks Reg Bool
  | .tab => Diagonal.tableBits (Diagonal.raw M).table
  | .alpha => numeral M.symbols
  | .state => numeral q.val
  | .left => fields (T.left.map Fin.val)
  | .right => fields (T.right.map Fin.val)
  | .base => numeral m
  | .halt => haltFlag q.val
  | _ => []

@[simp] theorem map_head_val {n : ℕ} (xs : List (Fin n)) (z : Fin n) (hz : z.val=0) :
    (xs.map Fin.val).headD 0=(xs.headD z).val := by cases xs <;> simp [hz]

@[simp] theorem map_head_zero (M : OneTape) (xs : List (Fin M.symbols)) :
    (xs.map Fin.val).headD 0=(xs.headD (zeroSymbol M)).val :=
  map_head_val xs (zeroSymbol M) rfl

@[simp] theorem table_lookup (M : OneTape) (q : Fin M.states) (x : Fin M.symbols)
    (hi : q.val*M.symbols+x.val<(Diagonal.raw M).table.length) :
    (Diagonal.raw M).table[q.val*M.symbols+x.val]=
      ((M.transition q x).1.val,(M.transition q x).2.1.val,Diagonal.moveCode (M.transition q x).2.2) := by
  have hv : (finProdFinEquiv (q,x)).val=q.val*M.symbols+x.val := by
    change x.val+M.symbols*q.val=q.val*M.symbols+x.val
    ring
  have he : (⟨q.val*M.symbols+x.val,by simpa [Diagonal.raw] using hi⟩ : Fin (M.states*M.symbols))=
      finProdFinEquiv (q,x) := Fin.ext hv.symm
  simp only [Diagonal.raw,List.getElem_ofFn,he,Equiv.symm_apply_apply]

def activeStep : Program Reg :=
  Program.seq (Program.read right cur) <|
  Program.seq lookup <|
  Program.seq (Program.clear cur) <|
  Program.seq motion <|
  Program.seq (Program.clear write) <|
  Program.seq (Program.clear dir) flagState

def step : Program Reg := Program.branch (fun v => (v halt).isNone) activeStep Program.skip

def stepBound (M : OneTape) : ℕ :=
  (M.states*M.symbols+1)*(30*(Diagonal.tableBits (Diagonal.raw M).table).length+
    60*M.states+60*M.symbols+100)+50*M.states+100*M.symbols+100

def nextState (M : OneTape) (q : Fin M.states) (T : TapePair.Tape (Fin M.symbols)) :=
  if q.val=1 ∨ q.val=2 then q else (M.transition q (T.right.headD (zeroSymbol M))).1

def nextTape (M : OneTape) (q : Fin M.states) (T : TapePair.Tape (Fin M.symbols)) :=
  if q.val=1 ∨ q.val=2 then T else
    TapePair.moveWrite (zeroSymbol M) (M.transition q (T.right.headD (zeroSymbol M))).2.1
      (M.transition q (T.right.headD (zeroSymbol M))).2.2 T

end WLTime.Universal

namespace WLTime.Universal
open TypedStack UnaryPrograms Reg

abbrev Config (M : OneTape) := Fin M.states × TapePair.Tape (Fin M.symbols)

def next (M : OneTape) (c : Config M) : Config M := (nextState M c.1 c.2,nextTape M c.1 c.2)

def encode (M : OneTape) (m : ℕ) (c : Config M) : Stacks Reg Bool := store M c.1 c.2 m

def steps : ℕ → Program Reg
  | 0 => step
  | s+1 => Program.repeatN base (steps s)

end WLTime.Universal

end OAI
end

section
-- module Solutions.OAIQW_WLTime.BoundedRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK

namespace WLTime.TypedStack.Program
variable {K : Type uK} [DecidableEq K]

def reverseInto (a b : K) : Program K := ofCode (Code.transfer a b false)

def shift (a b : K) : Program K :=
  ofCode (.seq (.pushDyn b (fun v => (v a).getD false)) (.pop a))

end WLTime.TypedStack.Program

namespace WLTime.Universal
open TypedStack UnaryPrograms Reg

def shiftPair (p : List Bool × List Bool) := (p.1.tail,p.1.headD false::p.2)

def takeDescription : Program Reg :=
  Program.seq (Program.repeatN index (Program.shift search temp)) (Program.reverseInto temp tab)

end WLTime.Universal

namespace WLTime.Universal
open TypedStack UnaryPrograms Reg

def bitValue : Bool → ℕ | false => 1 | true => 2

@[simp] theorem fields_append (xs ys : List ℕ) : fields (xs++ys)=fields xs++fields ys :=
  List.flatMap_append

def tapeBody : Program Reg :=
  Program.seq (Program.push right false) <|
  Program.seq (Program.push right true) <|
  Program.seq (Program.branch (UnaryPrograms.isTrue temp) (Program.push right true) Program.skip) <|
  Program.seq (Program.pop temp) (Program.push base true)

def tapeLoop : Program Reg := Program.loop (Code.nonempty temp) tapeBody

def inputPrep : Program Reg :=
  Program.seq (Program.copy input search) <|
  Program.seq (Program.reverseInto input temp) tapeLoop

def inputStore (w : List Bool) : Stacks Reg Bool := fun r => if r=input then w else []

def prepared (w : List Bool) : Stacks Reg Bool
  | .search => w
  | .base => numeral w.length
  | .right => fields (w.map bitValue)
  | _ => []

end WLTime.Universal

namespace WLTime.Universal
open TypedStack UnaryPrograms Reg

def initialConfig (M : OneTape) (w : List Bool) : Config M :=
  (⟨0,by have := M.states_ge; omega⟩,⟨[],w.map M.toTM.symbol⟩)

@[simp] theorem symbol_val (M : OneTape) (b : Bool) : (M.toTM.symbol b).val=bitValue b := by
  cases b <;> rfl

@[simp] theorem map_symbols_val (M : OneTape) (w : List Bool) :
    (w.map M.toTM.symbol).map Fin.val=w.map bitValue := by
  simp only [List.map_map,Function.comp_def,symbol_val]

def parseProgram : Program Reg :=
  Program.seq (Program.read search index) <|
  Program.seq takeDescription <|
  Program.seq (Program.clear search) <|
  Program.seq (Program.clear index) <|
  Program.seq (skipField tab) (Program.read tab alpha)

def initProgram : Program Reg := Program.seq inputPrep parseProgram

end WLTime.Universal

namespace WLTime.Universal
open OneTape

def Relative (M : OneTape) (C : M.Config ℤ) (c : Config M) : Prop :=
  c.1=C.state ∧ ∀ z,TapePair.contents (zeroSymbol M) c.2 z=C.tape (C.head+z)

end WLTime.Universal

namespace WLTime.TypedStack.Program
variable {K : Type uK} [DecidableEq K]

def inputStacks (k : K) (w : List Bool) : Stacks K Bool := fun j => if j=k then w else []

abbrev FinalState (p : Program K) := p.code.State ⊕ Unit

def finalTransition (p : Program K) (answer : Tops K Bool → Bool) :
    FinalState p → Tops (Fin p.scratch ⊕ K) Bool → Command (Fin p.scratch ⊕ K) Bool (FinalState p)
  | .inl q,v => Command.redirect Sum.inl (.inr ()) (p.code.transition q v)
  | .inr _,v => .halt (answer (v ∘ Sum.inr))

def machine (p : Program K) (k : K) (answer : Tops K Bool → Bool) :
    Machine (Fin p.scratch ⊕ K) Bool (FinalState p) where
  inputStack := .inr k
  inputLetter := id
  initial := .inl p.code.entry
  transition := finalTransition p answer

end WLTime.TypedStack.Program

namespace WLTime.Universal
open TypedStack Reg

def boundedProgram (s : ℕ) : Program Reg := Program.seq initProgram (steps s)
def answer (v : Tops Reg Bool) : Bool := v halt != some false

noncomputable def machine (s : ℕ) : OneTape := ((boundedProgram s).machine input answer).compile.oneTape

@[simp] theorem haltFlag_answer (q : ℕ) : ((haltFlag q).head? != some false)=decide (q≠1) := by
  by_cases h1 : q=1
  · simp [haltFlag,h1]
  · by_cases h2 : q=2 <;> simp [haltFlag,h1,h2]

def timeBound (s : ℕ) (M : OneTape) (m : ℕ) : ℕ :=
  8*((boundedProgram s).scratch+Fintype.card Reg+1)*
    (65*m+3*M.states+5*M.symbols+21+(stepBound M+18*s)*m^s)^2

end WLTime.Universal

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Diagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLTime.Diagonal
@[simp] theorem unary_length (n : ℕ) : (unary n).length=n+1 := by simp [unary]
@[simp] theorem entryBits_length (e : Entry) : (entryBits e).length=e.1+e.2.1+e.2.2+3 := by
  simp [entryBits]; omega
end WLTime.Diagonal

namespace WLTime.Numeric
noncomputable def base (C m : ℕ) := 1+C*m^2*((C*m^2+1)^2+1)
noncomputable def chooseOrder (C n : ℕ) := Nat.findGreatest (fun m => base C m≤n) n
end WLTime.Numeric
namespace WLTime
open OneTape.Symbolic OneTape.Symbolic.FullWriter
open scoped Classical
 def conventionShift : Convention → ℕ | .joint => 1 | .separate => 2
end WLTime

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Transducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK uA uT

namespace WLTime.TypedStack.Code
variable {K : Type uK} {A : Type uA} {T : Type uT} [DecidableEq K] [DecidableEq T]
def casesList (select : Tops K A → T) (body : T → Code K A) : List T → Code K A
  | [] => .skip
  | x::xs => .branch (fun v => decide (select v=x)) (body x) (casesList select body xs)
noncomputable def casesAll [Fintype T] (select : Tops K A → T) (body : T → Code K A) : Code K A :=
  casesList select body Finset.univ.toList
end WLTime.TypedStack.Code

namespace WLTime
instance instFintypeMove : Fintype Move := ⟨{.left,.stay,.right},by intro d; cases d <;> simp⟩
end WLTime

namespace WLTime.TMTransducer
open TypedStack
variable (M : TM)
abbrev Letter := Fin M.symbols ⊕ Fin M.states ⊕ Move
abbrev Reg := Fin 2 ⊕ (Fin M.tapes × Bool)
def stateReg : Reg M := .inl 0
def historyReg : Reg M := .inl 1
def symbolDecode : Letter M → Fin M.symbols
  | .inl x => x
  | _ => TMStack.blank M
def stateDecode : Option (Letter M) → Fin M.states
  | some (.inr (.inl q)) => q
  | _ => ⟨0,by have := M.states_ge; omega⟩
def store (q : Fin M.states) (s : Fin M.tapes → TapePair.Tape (Fin M.symbols)) (ds : List Move) : Stacks (Reg M) (Letter M) :=
  Sum.elim (fun i => if i.val=0 then [.inr (.inl q)] else ds.map (fun d => .inr (.inr d)))
    (Code.listMap Sum.inl (TMStack.store s))
abbrev Key := Fin M.states × (Fin M.tapes → Fin M.symbols)
def select (v : Tops (Reg M) (Letter M)) : Key M :=
  (stateDecode M (v (stateReg M)),fun a => ((v (.inr (a,true))).map (symbolDecode M)).getD (TMStack.blank M))
def live (v : Tops (Reg M) (Letter M)) : Bool := decide
  (¬((select M v).1.val=1 ∨ (select M v).1.val=2))
def stepBody (p : TMStack.Payload M) : Code (Reg M) (Letter M) :=
  .seq (((TMStack.stepCode M p).mapLetters Sum.inl (symbolDecode M)).relabel Sum.inr)
    (.seq (.pop (stateReg M)) (.seq (.push (stateReg M) (.inr (.inl p.1)))
      (.push (historyReg M) (.inr (.inr (p.2.2 ⟨0,M.tapes_pos⟩))))))
noncomputable def step : Code (Reg M) (Letter M) :=
  .casesAll (select M) (fun x => stepBody M (M.transition x.1 x.2))
noncomputable def runCode : Code (Reg M) (Letter M) := .loop (live M) (step M)

noncomputable def stepFactor : ℕ := 8*M.tapes+Fintype.card (Key M)+8
end WLTime.TMTransducer

namespace WLTime.Move
 def inverse : Move → Move | .left => .right | .stay => .stay | .right => .left
 @[simp] theorem inverse_displacement (d : Move) : d.inverse.displacement= -d.displacement := by cases d <;> rfl
end WLTime.Move
namespace WLTime.TapePair
variable {A : Type uA}
def move (blank : A) (d : Move) (s : Tape A) : Tape A := moveWrite blank (s.right.headD blank) d s
end WLTime.TapePair
namespace WLTime.TMTransducer
open TypedStack
variable (M : TM)
def zeroTape : Fin M.tapes := ⟨0,M.tapes_pos⟩
def historyDecode : Option (Letter M) → Move
  | some (.inr (.inr d)) => d
  | _ => .stay
def rewindKey (v : Tops (Reg M) (Letter M)) : Move × Fin M.symbols :=
  (historyDecode M (v (historyReg M)),((v (.inr (zeroTape M,true))).map (symbolDecode M)).getD (TMStack.blank M))
def rewindBody (d : Move) (x : Fin M.symbols) : Code (Reg M) (Letter M) :=
  .seq (((TMStack.single (TMStack.blank M) (zeroTape M) x d.inverse).mapLetters Sum.inl (symbolDecode M)).relabel Sum.inr)
    (.pop (historyReg M))
noncomputable def rewindStep : Code (Reg M) (Letter M) :=
  .casesAll (rewindKey M) (fun x => rewindBody M x.1 x.2)
noncomputable def rewindCode : Code (Reg M) (Letter M) :=
  .loop (fun v => (v (historyReg M)).isSome) (rewindStep M)
def moveOrigin (s : Fin M.tapes → TapePair.Tape (Fin M.symbols)) (d : Move) :=
  Function.update s (zeroTape M) (TapePair.move (TMStack.blank M) d.inverse (s (zeroTape M)))
def rewindTapes (s : Fin M.tapes → TapePair.Tape (Fin M.symbols)) : List Move → Fin M.tapes → TapePair.Tape (Fin M.symbols)
  | [] => s
  | d::ds => rewindTapes (moveOrigin M s d) ds

noncomputable def rewindFactor : ℕ := 12+Fintype.card (Move × Fin M.symbols)
end WLTime.TMTransducer

namespace WLTime.TypedStack.Code
variable {K : Type uK} {A : Type uA} [DecidableEq K]
def takeN (a b : K) (f : A → A) (zero : A) : ℕ → Code K A
  | 0 => .skip
  | n+1 => .seq (.seq (.pushDyn b (fun v => f ((v a).getD zero))) (.pop a)) (takeN a b f zero n)
def readN (zero : A) (xs : List A) (n : ℕ) : List A := List.ofFn (fun i : Fin n => xs.getD i.val zero)
 omit [DecidableEq K] in
 theorem takeN_size (a b : K) (f : A → A) (zero : A) (n : ℕ) :
    (takeN a b f zero n).controlSize=4*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [takeN,controlSize,ih]; omega
end WLTime.TypedStack.Code

namespace WLTime.TypedStack.Code
variable {K : Type uK} {A : Type uA} [DecidableEq K] [Fintype K]
def mass (s : Stacks K A) : ℕ := ∑ k, (s k).length

def clearList : List K → Code K A
  | [] => .skip
  | k::ks => .seq (.clear k) (clearList ks)
def cleared (ks : List K) (s : Stacks K A) : Stacks K A := fun k => if k ∈ ks then [] else s k
end WLTime.TypedStack.Code

end OAI
end

section
-- module Solutions.OAIQW_WLTime.SparseSearch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK uA

namespace WLTime.BitWords
 def value (xs : List Bool) : ℕ := Nat.ofDigits 2 (xs.map Bool.toNat)
 @[simp] theorem value_nil : value []=0 := rfl
 @[simp] theorem value_cons (b : Bool) (xs : List Bool) : value (b::xs)=b.toNat+2*value xs := rfl
 def inc : List Bool → List Bool
  | [] => []
  | false::xs => true::xs
  | true::xs => false::inc xs
 @[simp] theorem length_inc (xs : List Bool) : (inc xs).length=xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [inc,ih]
end WLTime.BitWords

namespace WLTime.BitWords
 def carry : List Bool → ℕ
  | true::xs => carry xs+1
  | _ => 0
 def rest : List Bool → List Bool
  | true::xs => rest xs
  | xs => xs
 def raise : List Bool → List Bool
  | [] => []
  | _::xs => true::xs
end WLTime.BitWords
namespace WLTime.TypedStack.Code
open BitWords
variable {K : Type uK} [DecidableEq K]
def carryCode (a b : K) : Code K Bool :=
  .loop (fun v => v a==some true) (.seq (.pop a) (.push b false))
def raiseCode (a : K) : Code K Bool :=
  .branch (nonempty a) (.seq (.pop a) (.push a true)) .skip
def increment (a b : K) : Code K Bool :=
  .seq (carryCode a b) (.seq (raiseCode a) (.transfer b a false))
end WLTime.TypedStack.Code

namespace WLTime.SparseMatch
open TypedStack
abbrev Reg := Fin 4
def state (a b f h : List Bool) : Stacks Reg Bool := ![a,b,f,h]
def body : Code Reg Bool :=
  .seq (.pushDyn 2 (fun v => (v 2).getD false && ((v 0).getD false == (v 1).getD false)))
    (.seq (.pushDyn 3 (fun v => (v 0).getD false)) (.seq (.pop 0) (.pop 1)))
def program : ℕ → Code Reg Bool
  | 0 => .skip
  | n+1 => .seq body (program n)
 theorem program_size (n : ℕ) : (program n).controlSize=8*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [program,body,Code.controlSize,ih]; omega
end WLTime.SparseMatch
namespace WLTime.SparseTake
open TypedStack
abbrev Reg := Fin 3
def state (a b c : List Bool) : Stacks Reg Bool := ![a,b,c]
def body : Code Reg Bool :=
  .seq (.pushDyn 1 (fun v => (v 0).getD false))
    (.seq (.pushDyn 2 (fun v => (v 0).getD false)) (.pop 0))
def program : ℕ → Code Reg Bool
  | 0 => .skip
  | n+1 => .seq body (program n)
 theorem program_size (n : ℕ) : (program n).controlSize=6*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [program,body,Code.controlSize,ih]; omega
end WLTime.SparseTake

namespace WLTime.SparseLookup
open TypedStack
abbrev Reg := Fin 8
def state (log query out hist copy flags candidate tmp : List Bool) : Stacks Reg Bool :=
  ![log,query,out,hist,copy,flags,candidate,tmp]
def matchMap : Fin 4 → Reg := ![0,4,5,3]
def takeMap : Fin 3 → Reg := ![0,3,6]
def first (w : ℕ) : Code Reg Bool :=
  .seq (.copy 1 4 7 false) (.seq (.push 5 true)
    (.seq ((SparseMatch.program w).relabel matchMap) ((SparseTake.program w).relabel takeMap)))
def finish : Code Reg Bool :=
  .seq (.branch (fun v => (v 5).getD false) (.transfer 6 2 false) (.clear 6)) (.clear 5)
def one (w : ℕ) : Code Reg Bool := .seq (first w) finish
end WLTime.SparseLookup
namespace WLTime.TypedStack.Code
variable {K : Type uK} {A : Type uA} [DecidableEq K]
def pushList (k : K) : List A → Code K A
  | [] => .skip
  | x::xs => .seq (pushList k xs) (.push k x)
 omit [DecidableEq K] in
 theorem pushList_size (k : K) (xs : List A) : (pushList k xs).controlSize=2*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [pushList,controlSize,List.length_cons,ih]; omega
end WLTime.TypedStack.Code
namespace WLTime.SparseLookup
open TypedStack
abbrev Entry := List Bool × List Bool
def flatten (l : List Entry) : List Bool := l.flatMap (fun e => e.1++e.2)
def WellFormed (w : ℕ) (l : List Entry) : Prop := ∀e∈l,e.1.length=w ∧ e.2.length=w
def consumed (q : List Bool) : List Entry → List Entry
  | [] => []
  | e::l => if e.1=q then [e] else e::consumed q l
def remaining (q : List Bool) : List Entry → List Entry
  | [] => []
  | e::l => if e.1=q then l else remaining q l
def found (q : List Bool) : List Entry → List Bool
  | [] => []
  | e::l => if e.1=q then e.2 else found q l
def keepGoing (v : Tops Reg Bool) : Bool := (Code.nonempty 0 v) && !(Code.nonempty 2 v)
def search (w : ℕ) : Code Reg Bool := .loop keepGoing (one w)
end WLTime.SparseLookup

end OAI
end

section
-- module Solutions.OAIQW_WLTime.SparseStore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uB

namespace WLTime.SparseLookup
open TypedStack
def answer (w : ℕ) (q : List Bool) (l : List Entry) : List Bool :=
  if found q l=[] then List.replicate w false else found q l
def supplyZero (w : ℕ) : Code Reg Bool :=
  .branch (Code.nonempty 2) .skip (.pushList 2 (List.replicate w false))
def program (w : ℕ) : Code Reg Bool :=
  .seq (search w) (.seq (.transfer 3 0 false) (supplyZero w))
 theorem program_size (w : ℕ) : (program w).controlSize ≤ 30*w+100 := by
  simp only [program,search,one,first,finish,supplyZero,Code.controlSize,Code.relabel_controlSize,
    SparseMatch.program_size,SparseTake.program_size,Code.copy,Code.transfer,Code.distribute,Code.clear,
    Code.pushList_size,List.length_replicate]
  omega
end WLTime.SparseLookup

namespace WLTime.WordMemory
open TypedStack
abbrev Log (w : ℕ) := List (Word w × Word w)
def read {w : ℕ} (q : Word w) : Log w → Word w
  | [] => ⟨0,by positivity⟩
  | e::l => if e.1=q then e.2 else read q l
def entries {w : ℕ} (l : Log w) : List SparseLookup.Entry :=
  l.map (fun e => (wordBits e.1,wordBits e.2))
end WLTime.WordMemory
namespace WLTime.SparseStore
open TypedStack
abbrev Reg := Fin 4
def state (log key value tmp : List Bool) : Stacks Reg Bool := ![log,key,value,tmp]
def program : Code Reg Bool := .seq (.copy 2 0 3 false) (.copy 1 0 3 false)
end WLTime.SparseStore

namespace WLTime.WordMemory
open TypedStack
def chunk (w : ℕ) (input : List Bool) (a : ℕ) : List Bool :=
  Code.readN false (input.drop (w*a)) w
end WLTime.WordMemory
namespace WLTime.WordMemory
def address (w a : ℕ) : Word w := ⟨a%(2^w),Nat.mod_lt _ (by positivity)⟩
def initialLog (w : ℕ) (input : List Bool) : ℕ → Log w
  | 0 => []
  | a+1 => (address w a,RAM.packedWord w input (address w a))::initialLog w input a
end WLTime.WordMemory

namespace WLTime.RAMInput
open TypedStack WordMemory
abbrev Reg := Fin 6
def state (input log addr value temp scratch : List Bool) : Stacks Reg Bool :=
  ![input,log,addr,value,temp,scratch]
def storeMap : SparseStore.Reg → Reg := ![1,2,3,5]
noncomputable def body (w : ℕ) : Code Reg Bool :=
  .seq (.takeN 0 4 id false w) (.seq (.transfer 4 3 false)
    (.seq (SparseStore.program.relabel storeMap) (.seq (.clear 3) (.increment 2 5))))
def running (v : Tops Reg Bool) : Bool := Code.nonempty 0 v
noncomputable def loopCode (w : ℕ) : Code Reg Bool := .loop running (body w)
noncomputable def program (w : ℕ) : Code Reg Bool :=
  .seq (.pushList 2 (List.replicate w false)) (.seq (loopCode w) (.clear 2))

def packedState (w : ℕ) (input : List Bool) (a : ℕ) : Stacks Reg Bool :=
  state (input.drop (w*a)) (SparseLookup.flatten (entries (initialLog w input a)))
    (wordBits (address w a)) [] [] []
 theorem body_size (w : ℕ) : (body w).controlSize ≤ 4*w+100 := by
  simp [body,Code.controlSize,Code.takeN_size,Code.relabel_controlSize,SparseStore.program,
    Code.copy,Code.transfer,Code.distribute,Code.clear,Code.increment,Code.carryCode,Code.raiseCode]
 theorem program_size (w : ℕ) : (program w).controlSize ≤ 6*w+110 := by
  have hb := body_size w
  simp only [program,loopCode,Code.controlSize,Code.pushList_size,List.length_replicate,Code.clear]
  omega
end WLTime.RAMInput

namespace WLTime.TMPort
open TypedStack
variable (M : TM)
abbrev Letter := Bool ⊕ TMTransducer.Letter M
abbrev Reg := Fin 3 ⊕ TMTransducer.Reg M
def port : Reg M := .inl 0
def temp : Reg M := .inl 1
def result : Reg M := .inl 2
def tapeIn : Reg M := .inr (.inr (TMTransducer.zeroTape M,true))
def inputSymbol : Letter M → Letter M
  | .inl b => .inr (.inl (M.symbol b))
  | _ => .inr (.inl (TMStack.blank M))
def outputSymbol : Letter M → Letter M
  | .inr (.inl a) => .inl (decide (a.val=2))
  | _ => .inl false
def unletter : Letter M → TMTransducer.Letter M
  | .inr a => a
  | _ => .inl (TMStack.blank M)
def inputState (xs : List Bool) : Stacks (Reg M) (Letter M) :=
  fun k => if k=port M then xs.map Sum.inl else []
def innerState (q : Fin M.states) (s : Fin M.tapes → TapePair.Tape (Fin M.symbols)) (ds : List Move) : Stacks (Reg M) (Letter M) :=
  Sum.elim (fun _ => []) (Code.listMap Sum.inr (TMTransducer.store M q s ds))
def load (n : ℕ) : Code (Reg M) (Letter M) :=
  .seq (.takeN (port M) (temp M) (inputSymbol M) (.inl false) n)
    (.seq (.transfer (temp M) (tapeIn M) (.inl false))
      (.push (.inr (TMTransducer.stateReg M)) (.inr (.inr (.inl ⟨0,by have := M.states_ge; omega⟩)))))
noncomputable def runCode : Code (Reg M) (Letter M) :=
  ((TMTransducer.runCode M).mapLetters Sum.inr (unletter M)).relabel Sum.inr
noncomputable def rewindCode : Code (Reg M) (Letter M) :=
  ((TMTransducer.rewindCode M).mapLetters Sum.inr (unletter M)).relabel Sum.inr
def extract (n : ℕ) : Code (Reg M) (Letter M) :=
  .seq (.takeN (tapeIn M) (result M) (outputSymbol M) (.inr (.inl (TMStack.blank M))) n)
    (.transfer (result M) (port M) (.inl false))
end WLTime.TMPort

end OAI
end

section
-- module Solutions.OAIQW_WLTime.RAMMemory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA

namespace WLTime.TMPort
open TypedStack
open scoped Classical
variable (M : TM)
noncomputable def privateRegs : List (Reg M) := (Finset.univ : Finset (TMTransducer.Reg M)).toList.map Sum.inr
noncomputable def program (n o : ℕ) : Code (Reg M) (Letter M) :=
  .seq (load M n) (.seq (runCode M) (.seq (rewindCode M) (.seq (extract M o) (.clearList (privateRegs M)))))
noncomputable def factor : ℕ := 50+4*(TMTransducer.stepFactor M+TMTransducer.rewindFactor M)+Fintype.card (TMTransducer.Reg M)
 theorem size_load (n : ℕ) : (load M n).controlSize=4*n+8 := by
  simp only [load,Code.controlSize,Code.takeN_size,Code.transfer]
 theorem size_extract (n : ℕ) : (extract M n).controlSize=4*n+6 := by
  simp only [extract,Code.controlSize,Code.takeN_size,Code.transfer]
noncomputable def sizeFactor : ℕ := 14+(runCode M).controlSize+(rewindCode M).controlSize+(Code.clearList (privateRegs M) : Code (Reg M) (Letter M)).controlSize
 theorem program_size (n o : ℕ) : (program M n o).controlSize ≤ sizeFactor M*(n+o+1) := by
  simp only [program,Code.controlSize,size_load,size_extract,sizeFactor]
  nlinarith
end WLTime.TMPort

namespace WLTime.RAMSlices
open TypedStack
abbrev Reg := Fin 4
def state (file value pre tmp : List Bool) : Stacks Reg Bool := ![file,value,pre,tmp]
def read (offset len : ℕ) : Code Reg Bool :=
  .seq (.copy 0 2 3 false) (.seq (.takeN 2 3 id false offset) (.seq (.clear 3)
    (.seq (.takeN 2 3 id false len) (.seq (.clear 2) (.transfer 3 1 false)))))
def write (offset len : ℕ) : Code Reg Bool :=
  .seq (.takeN 0 2 id false offset) (.seq (.takeN 0 3 id false len) (.seq (.clear 3)
    (.seq (.moveList 1 0 3 false) (.transfer 2 0 false))))
 theorem read_size (offset len : ℕ) : (read offset len).controlSize ≤ 4*(offset+len)+40 := by
  simp [read,Code.controlSize,Code.takeN_size,Code.copy,Code.transfer,Code.distribute,Code.clear]
  omega
 theorem write_size (offset len : ℕ) : (write offset len).controlSize ≤ 4*(offset+len)+30 := by
  simp [write,Code.controlSize,Code.takeN_size,Code.moveList,Code.transfer,Code.clear]
  omega
end WLTime.RAMSlices

namespace WLTime.RegisterFile
 theorem flatten_length {A : Type uA} (w : ℕ) (xs : List (List A)) (hx : ∀ x ∈ xs,x.length=w) :
    xs.flatten.length=w*xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hh := hx x (by simp)
    have ht := ih (fun a ha => hx a (by simp [ha]))
    simp only [List.flatten_cons,List.length_append,List.length_cons,hh,ht]
    ring
 theorem length {R w : ℕ} (a : Fin R → Word w) : (registerBits a).length=R*w := by
  unfold registerBits
  rw [flatten_length w _ (by intro xs hx; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx; simp [wordBits])]
  simp [Nat.mul_comm]
end WLTime.RegisterFile

namespace WLTime.RAMMemory
open TypedStack WordMemory
abbrev Reg := Fin 12
def state (file log key value : List Bool) : Stacks Reg Bool :=
  ![file,log,key,value,[],[],[],[],[],[],[],[]]
def keyMap : RAMSlices.Reg → Reg := ![0,2,4,5]
def valueMap : RAMSlices.Reg → Reg := ![0,3,4,5]
def lookupMap : SparseLookup.Reg → Reg := ![1,2,3,6,7,8,9,10]
def storeMap : SparseStore.Reg → Reg := ![1,2,3,5]
noncomputable def readKey (w i : ℕ) : Code Reg Bool := (RAMSlices.read (w*i) w).relabel keyMap
noncomputable def readValue (w i : ℕ) : Code Reg Bool := (RAMSlices.read (w*i) w).relabel valueMap
noncomputable def writeValue (w i : ℕ) : Code Reg Bool := (RAMSlices.write (w*i) w).relabel valueMap
noncomputable def lookup (w : ℕ) : Code Reg Bool := (SparseLookup.program w).relabel lookupMap
noncomputable def store : Code Reg Bool := SparseStore.program.relabel storeMap
noncomputable def load (w dest addr : ℕ) : Code Reg Bool :=
  .seq (readKey w addr) (.seq (lookup w) (.seq (writeValue w dest) (.clear 2)))
noncomputable def save (w addr src : ℕ) : Code Reg Bool :=
  .seq (readKey w addr) (.seq (readValue w src) (.seq store (.seq (.clear 2) (.clear 3))))
 def cost (R w L : ℕ) := 500*(R+1)*(w+1)*(L+1)
 theorem load_size (R w : ℕ) (dest addr : Fin R) : (load w dest.val addr.val).controlSize ≤ cost R w 0 := by
  have h₁ := RAMSlices.read_size (w*addr.val) w
  have h₂ := RAMSlices.write_size (w*dest.val) w
  have h₃ := SparseLookup.program_size w
  have ha : w*addr.val ≤ w*R := Nat.mul_le_mul_left _ (Nat.le_of_lt addr.isLt)
  have hd : w*dest.val ≤ w*R := Nat.mul_le_mul_left _ (Nat.le_of_lt dest.isLt)
  simp only [load,readKey,writeValue,lookup,Code.controlSize,Code.relabel_controlSize,Code.clear]
  unfold cost
  nlinarith
 theorem save_size (R w : ℕ) (addr src : Fin R) : (save w addr.val src.val).controlSize ≤ cost R w 0 := by
  have h₁ := RAMSlices.read_size (w*addr.val) w
  have h₂ := RAMSlices.read_size (w*src.val) w
  have ha : w*addr.val ≤ w*R := Nat.mul_le_mul_left _ (Nat.le_of_lt addr.isLt)
  have hd : w*src.val ≤ w*R := Nat.mul_le_mul_left _ (Nat.le_of_lt src.isLt)
  simp only [save,readKey,readValue,store,Code.controlSize,Code.relabel_controlSize,Code.clear,
    SparseStore.program,Code.copy,Code.transfer,Code.distribute]
  unfold cost
  nlinarith
end WLTime.RAMMemory

end OAI
end

section
-- module Solutions.OAIQW_WLTime.RAMInstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLTime.ZeroTest
open TypedStack
abbrev Reg := Fin 2
def state (input flags : List Bool) : Stacks Reg Bool := ![input,flags]
def marks : List Bool → Bool → List Bool → List Bool
  | [],b,hist => b::hist
  | x::xs,b,hist => marks xs (b||x) (b::hist)
def body : Code Reg Bool := .seq (.pushDyn 1 (fun v => (v 1).getD false || (v 0).getD false)) (.pop 0)
def loopCode : Code Reg Bool := .loop (Code.nonempty 0) body
def finish : Code Reg Bool := .branch (fun v : Tops Reg Bool => (v 1).getD false)
  (.seq (.clear 1) (.push 1 true)) (.seq (.clear 1) (.push 1 false))
def program : Code Reg Bool := .seq (.push 1 false) (.seq loopCode finish)
 theorem program_size : program.controlSize=18 := by rfl
end WLTime.ZeroTest

namespace WLTime.RAMInstruction
 def operations {R P : ℕ} : RAMInstruction R P → List (WordOperation R)
  | .halt _ | .jump _ => []
  | .compute op next => op::operations next
  | .load _ _ next | .store _ _ next => operations next
  | .branchZero _ yes no => operations yes++operations no
 def depth {R P : ℕ} : RAMInstruction R P → ℕ
  | .halt _ | .jump _ => 1
  | .compute _ next | .load _ _ next | .store _ _ next => depth next+1
  | .branchZero _ yes no => max (depth yes) (depth no)+1
end WLTime.RAMInstruction
namespace WLTime.SparseRAM
open WordMemory
structure Config (R P w : ℕ) where
  pc : Fin P
  registers : Fin R → Word w
  log : Log w
  answer : Option Bool

def execute {R P w : ℕ} : RAMInstruction R P → Config R P w → Config R P w
  | .halt b,C => {C with answer := some b}
  | .jump pc,C => {C with pc := pc}
  | .compute op next,C => execute next {C with registers := op.apply w C.registers}
  | .load dest addr next,C => execute next {C with registers := Function.update C.registers dest (read (C.registers addr) C.log)}
  | .store addr src next,C => execute next {C with log := (C.registers addr,C.registers src)::C.log}
  | .branchZero reg yes no,C => if (C.registers reg).val=0 then execute yes C else execute no C
 def forget (A : RAM) (n : ℕ) (C : Config A.registers A.locations (A.width.bits n)) : A.Config n where
  pc := C.pc
  registers := C.registers
  memory := fun q => read q C.log
  answer := C.answer
 def step (A : RAM) (w : ℕ) (C : Config A.registers A.locations w) : Config A.registers A.locations w :=
  match C.answer with
  | some _ => C
  | none => execute (A.program C.pc) C
end WLTime.SparseRAM

namespace WLTime.RAMAlphabet
open TypedStack
open scoped Classical
noncomputable section
variable (A : RAM)
def operations : List (WordOperation A.registers) :=
  (List.ofFn A.program).flatMap RAMInstruction.operations
abbrev Index := Fin (operations A).length
def operation (i : Index A) : WordOperation A.registers := (operations A).get i
abbrev Reg := Fin 14 ⊕ ((i : Index A) × TMPort.Reg (operation A i).implementation)
abbrev Letter := Bool ⊕ (Fin A.locations ⊕ ((i : Index A) × TMTransducer.Letter (operation A i).implementation))
def decode : Letter A → Bool
  | .inl b => b
  | .inr _ => false
def memMap (i : RAMMemory.Reg) : Reg A := .inl ⟨i.val,by omega⟩
def liftMem (s : Stacks RAMMemory.Reg Bool) (pc : Fin A.locations) (answer : Option Bool) : Stacks (Reg A) (Letter A)
  | .inl i => if h : i.val<12 then (s ⟨i.val,h⟩).map Sum.inl
      else if i=12 then [.inr (.inl pc)] else answer.toList.map Sum.inl
  | .inr _ => []
def state {w : ℕ} (C : SparseRAM.Config A.registers A.locations w) : Stacks (Reg A) (Letter A) :=
  liftMem A (RAMMemory.state (registerBits C.registers) (SparseLookup.flatten (WordMemory.entries C.log)) [] []) C.pc C.answer
 def opReg (i : Index A) (r : TMPort.Reg (operation A i).implementation) : Reg A :=
  if r=TMPort.port (operation A i).implementation then .inl 0 else .inr ⟨i,r⟩
 def opLetter (i : Index A) : TMPort.Letter (operation A i).implementation → Letter A
  | .inl b => .inl b
  | .inr c => .inr (.inr ⟨i,c⟩)
 def opDecode (i : Index A) : Letter A → TMPort.Letter (operation A i).implementation :=
  Function.invFun (opLetter A i)
 def opCode (i : Index A) (n o : ℕ) : Code (Reg A) (Letter A) :=
  (((TMPort.program (operation A i).implementation n o).mapLetters (opLetter A i) (opDecode A i)).relabel (opReg A i))
 def fileState (file log : List Bool) (pc : Fin A.locations) (answer : Option Bool) : Stacks (Reg A) (Letter A) :=
  liftMem A (RAMMemory.state file log [] []) pc answer
 theorem opCode_size (i : Index A) (n o : ℕ) :
    (opCode A i n o).controlSize ≤ TMPort.sizeFactor (operation A i).implementation*(n+o+1) := by
  simpa [opCode] using TMPort.program_size (operation A i).implementation n o
 theorem mem_program (pc : Fin A.locations) : ∀op ∈ (A.program pc).operations, op ∈ operations A := by
  intro op hop
  apply List.mem_flatMap.mpr
  exact ⟨A.program pc,List.mem_ofFn.mpr ⟨pc,rfl⟩,hop⟩
 def locate (op : WordOperation A.registers) (h : op ∈ operations A) : Index A :=
  ⟨(operations A).idxOf op,List.idxOf_lt_length_iff.mpr h⟩
 theorem locate_eq (op : WordOperation A.registers) (h : op ∈ operations A) : operation A (locate A op h)=op := by
  exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr h)
end
end WLTime.RAMAlphabet

namespace WLTime.RAMTests
open TypedStack
open scoped Classical
abbrev Reg := RAMMemory.Reg
def flags (file log : List Bool) (b : Bool) : Stacks Reg Bool :=
  Function.update (RAMMemory.state file log [] []) 11 [b]
def testMap : ZeroTest.Reg → Reg := ![2,11]
noncomputable def testCode (w i : ℕ) : Code Reg Bool :=
  .seq (RAMMemory.readKey w i) (ZeroTest.program.relabel testMap)
 theorem code_size (R w : ℕ) (i : Fin R) : (testCode w i.val).controlSize ≤ 10*(R+1)*(w+1)+100 := by
  have he := RAMSlices.read_size (w*i.val) w
  have hi := Nat.mul_le_mul_left w (Nat.le_of_lt i.isLt)
  simp only [testCode,RAMMemory.readKey,Code.controlSize,Code.relabel_controlSize,ZeroTest.program_size]
  nlinarith
end WLTime.RAMTests
namespace WLTime.RAMAlphabet
open TypedStack
open scoped Classical
noncomputable section
variable (A : RAM)
 def memCode (c : Code RAMMemory.Reg Bool) : Code (Reg A) (Letter A) :=
  (c.mapLetters Sum.inl (decode A)).relabel (memMap A)
 theorem memCode_size (c : Code RAMMemory.Reg Bool) : (memCode A c).controlSize=c.controlSize := by simp [memCode]
 def compute (w : ℕ) (op : WordOperation A.registers) (h : op ∈ operations A) : Code (Reg A) (Letter A) :=
  .seq (.pushList (.inl 0) ((encodeNat w).map Sum.inl))
    (opCode A (locate A op h) ((encodeNat w).length+A.registers*w) (A.registers*w))
 theorem compute_size (w : ℕ) (op : WordOperation A.registers) (h : op ∈ operations A) :
    (compute A w op h).controlSize ≤ 2*(encodeNat w).length+2+
      TMPort.sizeFactor op.implementation*((encodeNat w).length+2*(A.registers*w)+1) := by
  have he := opCode_size A (locate A op h) ((encodeNat w).length+A.registers*w) (A.registers*w)
  rw [locate_eq] at he
  simp only [compute,Code.controlSize,Code.pushList_size,List.length_map]
  nlinarith only [he]
end
end WLTime.RAMAlphabet

namespace WLTime.RAMAlphabet
open TypedStack
open scoped Classical
noncomputable section
variable (A : RAM)
 def opCost (w : ℕ) (op : WordOperation A.registers) : ℕ :=
  2*(encodeNat w).length+1+TMPort.factor op.implementation*
      ((encodeNat w).length+2*(A.registers*w)+op.constant*(w+1)^op.exponent+1)
 def unitCost (w : ℕ) : ℕ := 1000*(A.registers+1)*(w+1)+∑i : Index A,opCost A w (operation A i)
 def haltCode (b : Bool) : Code (Reg A) (Letter A) := .seq (.clear (.inl 13)) (.push (.inl 13) (.inl b))
 def jumpCode (pc : Fin A.locations) : Code (Reg A) (Letter A) := .seq (.clear (.inl 12)) (.push (.inl 12) (.inr (.inl pc)))
end
end WLTime.RAMAlphabet

end OAI
end

section
-- module Solutions.OAIQW_WLTime.RAMSimulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK uX uT

namespace WLTime.RAMAlphabet
open TypedStack
open scoped Classical
noncomputable section
variable (A : RAM)
def instruction (w : ℕ) : (I : RAMInstruction A.registers A.locations) →
    (∀op ∈ I.operations,op ∈ operations A) → Code (Reg A) (Letter A)
  | .halt b,_ => haltCode A b
  | .jump pc,_ => jumpCode A pc
  | .compute op next,h => .seq (compute A w op (h op (by simp [RAMInstruction.operations])))
      (instruction w next (fun q hq => h q (by simp [RAMInstruction.operations,hq])))
  | .load dest addr next,h => .seq (memCode A (RAMMemory.load w dest.val addr.val))
      (instruction w next h)
  | .store addr src next,h => .seq (memCode A (RAMMemory.save w addr.val src.val))
      (instruction w next h)
  | .branchZero reg yes no,h =>
      .seq (memCode A (RAMTests.testCode w reg.val))
        (.branch (fun v => ((v (.inl 11)).map (decode A)).getD false)
          (.seq (.pop (.inl 11)) (instruction w no (fun q hq => h q (by simp [RAMInstruction.operations,hq]))))
          (.seq (.pop (.inl 11)) (instruction w yes (fun q hq => h q (by simp [RAMInstruction.operations,hq])))))
end
end WLTime.RAMAlphabet

namespace WLTime.RAMAlphabet
open TypedStack
open scoped Classical
noncomputable section
variable (A : RAM)
 theorem encode_length_bound (w : ℕ) : (encodeNat w).length ≤ 2*w+1 := by
  have hd : (Nat.digits 2 w).length≤w := (Nat.digits_length_le_iff (by decide) w).mpr w.lt_two_pow_self
  simp only [encodeNat,List.length_append,List.length_replicate,List.length_cons,List.length_nil,List.length_map]
  omega
 def exponent : ℕ := 1+Finset.univ.sup (fun i : Index A => (operation A i).exponent)
 def opConstant (op : WordOperation A.registers) : ℕ :=
  7+TMPort.factor op.implementation*(2*A.registers+op.constant+4)
 def constant : ℕ := 1000*(A.registers+1)+∑i : Index A,opConstant A (operation A i)
 def opSizeConstant (op : WordOperation A.registers) : ℕ := 10+TMPort.sizeFactor op.implementation*(2*A.registers+4)
 theorem compute_linear (w : ℕ) (op : WordOperation A.registers) (h : op ∈ operations A) :
    (compute A w op h).controlSize ≤ opSizeConstant A op*(w+1) := by
  have he := compute_size A w op h
  have hl := encode_length_bound w
  have hh := Nat.mul_le_mul_left (TMPort.sizeFactor op.implementation)
    (show (encodeNat w).length+2*(A.registers*w)+1≤(2*A.registers+4)*(w+1) by nlinarith only [hl])
  dsimp only [opSizeConstant]
  nlinarith only [he,hl,hh]
 theorem instruction_linear (I : RAMInstruction A.registers A.locations) :
    ∃S,∀w h,(instruction A w I h).controlSize≤S*(w+1) := by
  induction I with
  | halt b =>
    refine ⟨10,?_⟩
    intro w h
    simp only [instruction,haltCode,Code.controlSize,Code.clear]
    omega
  | jump pc =>
    refine ⟨10,?_⟩
    intro w h
    simp only [instruction,jumpCode,Code.controlSize,Code.clear]
    omega
  | compute op next ih =>
    obtain ⟨S,hS⟩ := ih
    refine ⟨opSizeConstant A op+S+1,?_⟩
    intro w h
    have hn : ∀q∈next.operations,q∈operations A := fun q hq => h q (by simp [RAMInstruction.operations,hq])
    have ho := compute_linear A w op (h op (by simp [RAMInstruction.operations]))
    have hs := hS w hn
    simp only [instruction,Code.controlSize]
    nlinarith only [ho,hs]
  | load dest addr next ih =>
    obtain ⟨S,hS⟩ := ih
    refine ⟨500*(A.registers+1)+S+1,?_⟩
    intro w h
    have hm := RAMMemory.load_size A.registers w dest addr
    have hs := hS w h
    simp only [instruction,Code.controlSize,memCode_size]
    simp only [RAMMemory.cost,Nat.zero_add,Nat.mul_one] at hm
    nlinarith only [hm,hs]
  | store addr src next ih =>
    obtain ⟨S,hS⟩ := ih
    refine ⟨500*(A.registers+1)+S+1,?_⟩
    intro w h
    have hm := RAMMemory.save_size A.registers w addr src
    have hs := hS w h
    simp only [instruction,Code.controlSize,memCode_size]
    simp only [RAMMemory.cost,Nat.zero_add,Nat.mul_one] at hm
    nlinarith only [hm,hs]
  | branchZero reg yes no ih ih' =>
    obtain ⟨S,hS⟩ := ih
    obtain ⟨T,hT⟩ := ih'
    refine ⟨110*(A.registers+1)+S+T+10,?_⟩
    intro w h
    have hy : ∀q∈yes.operations,q∈operations A := fun q hq => h q (by simp [RAMInstruction.operations,hq])
    have hn : ∀q∈no.operations,q∈operations A := fun q hq => h q (by simp [RAMInstruction.operations,hq])
    have hs := hS w hy
    have ht := hT w hn
    have hm := RAMTests.code_size A.registers w reg
    simp only [instruction,Code.controlSize,memCode_size]
    nlinarith only [hs,ht,hm]
end
end WLTime.RAMAlphabet

namespace WLTime.TypedStack.Code
variable {K : Type uK} {X : Type uX} {T : Type uT} [DecidableEq K] [DecidableEq T]
 omit [DecidableEq K] in
 theorem casesList_size (select : Tops K X → T) (body : T → Code K X) (xs : List T) :
    (casesList select body xs).controlSize=1+xs.length+(xs.map (fun x => (body x).controlSize)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [casesList,controlSize,ih,List.length_cons,List.map_cons,List.sum_cons]; omega
 omit [DecidableEq K] in
 theorem casesAll_size [Fintype T] (select : Tops K X → T) (body : T → Code K X) :
    (casesAll select body).controlSize=1+Fintype.card T+∑x : T,(body x).controlSize := by
  rw [casesAll,casesList_size,Finset.length_toList,Finset.card_univ]
  congr 1
  exact Finset.sum_map_toList _ _
end WLTime.TypedStack.Code
namespace WLTime.RAMAlphabet
open TypedStack
open scoped Classical
noncomputable section
variable (A : RAM)
def depth : ℕ := Finset.univ.sup (fun pc : Fin A.locations => (A.program pc).depth)
def selectPC (v : Tops (Reg A) (Letter A)) : Fin A.locations :=
  match v (.inl 12) with
  | some (.inr (.inl pc)) => pc
  | _ => ⟨0,A.locations_pos⟩
def dispatch (w : ℕ) : Code (Reg A) (Letter A) :=
  Code.casesAll (selectPC A) (fun pc : Fin A.locations => instruction A w (A.program pc) (mem_program A pc))
def stepBound (w L : ℕ) : ℕ := unitCost A w*depth A*(L+depth A+1)+A.locations
 def running (v : Tops (Reg A) (Letter A)) : Bool := !(v (.inl 13)).isSome
 def loopCode (w : ℕ) : Code (Reg A) (Letter A) := .loop (running A) (dispatch A w)
 theorem dispatch_linear : ∃S,∀w,(dispatch A w).controlSize≤S*(w+1) := by
  choose S hS using fun pc : Fin A.locations => instruction_linear A (A.program pc)
  refine ⟨1+A.locations+∑pc,S pc,?_⟩
  intro w
  have hs : (∑pc : Fin A.locations,(instruction A w (A.program pc) (mem_program A pc)).controlSize)≤(∑pc,S pc)*(w+1) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun pc _ => hS pc w (mem_program A pc))
  rw [dispatch,Code.casesAll_size,Fintype.card_fin]
  nlinarith only [hs]
end
end WLTime.RAMAlphabet

namespace WLTime.RAMAlphabet
open TypedStack
open scoped Classical
noncomputable section
variable (A : RAM)
def inputMap (i : RAMInput.Reg) : RAMMemory.Reg := ⟨i.val,by omega⟩
def loader (w : ℕ) : Code RAMMemory.Reg Bool := (RAMInput.program w).relabel inputMap
 def inputState (xs : List Bool) : Stacks (Reg A) (Letter A) := fun r => if r=.inl 0 then xs.map Sum.inl else []
 def initial (w : ℕ) (xs : List Bool) (n : ℕ) : SparseRAM.Config A.registers A.locations w where
  pc := ⟨0,A.locations_pos⟩
  registers := fun _ => ⟨0,by positivity⟩
  log := WordMemory.initialLog w xs n
  answer := none
 def initCode (w : ℕ) : Code (Reg A) (Letter A) :=
  .seq (.push (.inl 12) (.inr (.inl ⟨0,A.locations_pos⟩)))
    (.seq (memCode A (loader w)) (.pushList (.inl 0) ((List.replicate (A.registers*w) false).map Sum.inl)))
 def initBound (w len : ℕ) : ℕ := 100*(A.registers+1)*(w+1)*(len+1)
 def program (w : ℕ) : Code (Reg A) (Letter A) := .seq (initCode A w) (loopCode A w)
 def budget (w len time : ℕ) : ℕ := initBound A w len+(stepBound A w (len+time*depth A)+1)*time+1
 theorem init_linear (w : ℕ) : (initCode A w).controlSize≤500*(A.registers+1)*(w+1) := by
  have he := RAMInput.program_size w
  simp only [initCode,Code.controlSize,memCode_size,loader,Code.relabel_controlSize,Code.pushList_size,List.length_map,List.length_replicate]
  nlinarith only [he]
 theorem program_linear : ∃S,∀w,(program A w).controlSize≤S*(w+1) := by
  obtain ⟨S,hS⟩ := dispatch_linear A
  refine ⟨500*(A.registers+1)+S+1,?_⟩
  intro w
  have hi := init_linear A w
  have hd := hS w
  simp only [program,loopCode,Code.controlSize]
  nlinarith only [hi,hd]
end
end WLTime.RAMAlphabet

end OAI
end

section
-- module Solutions.OAIQW_WLTime.RAMBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK uX

namespace WLTime.TypedStack.Code
variable {K : Type uK} {X : Type uX} [DecidableEq K]
abbrev HaltState (c : Code K X) := c.State ⊕ Unit
def haltTransition (c : Code K X) (answer : Tops K X → Bool) :
    HaltState c → Tops K X → Command K X (HaltState c)
  | .inl q,v => Command.redirect Sum.inl (.inr ()) (c.transition q v)
  | .inr _,v => .halt (answer v)
def haltMachine (c : Code K X) (input : K) (letter : Bool → X) (answer : Tops K X → Bool) :
    Machine K X (HaltState c) where
  inputStack := input
  inputLetter := letter
  initial := .inl c.entry
  transition := haltTransition c answer
variable [Fintype K] [Fintype X]
noncomputable def haltOneTape (c : Code K X) (input : K) (letter : Bool → X) (answer : Tops K X → Bool) : OneTape :=
  (haltMachine c input letter answer).compile.oneTape
end WLTime.TypedStack.Code

namespace WLTime.RAMAlphabet
open scoped Classical
noncomputable section
variable (A : RAM)
def budgetConstant : ℕ := 100*(A.registers+1)+constant A*depth A*(depth A+1)+A.locations+2
end
end WLTime.RAMAlphabet

namespace WLTime.RAMConsumer
open TypedStack
noncomputable section
variable {K : Type uK} [DecidableEq K] (A : RAM)
abbrev Reg (K : Type uK) := K ⊕ RAMAlphabet.Reg A
abbrev Letter := RAMAlphabet.Letter A
local instance instDecidableEqReg : DecidableEq (RAMAlphabet.Reg A) := Classical.decEq _
local instance instDecidableEqLetter_re4fab7_1 : DecidableEq (Letter A) := Classical.decEq _
def preludeCode (c : Code K Bool) (output : K) : Code (Reg A K) (Letter A) :=
  .seq ((c.mapLetters Sum.inl (RAMAlphabet.decode A)).relabel Sum.inl)
    (.transfer (.inl output) (.inr (.inl 0)) (.inl false))
def code (c : Code K Bool) (output : K) (w : ℕ) : Code (Reg A K) (Letter A) :=
  .seq (preludeCode A c output) ((RAMAlphabet.program A w).relabel Sum.inr)
def answer (v : Tops (Reg A K) (Letter A)) : Bool :=
  !((v (.inr (.inl 13))).map (RAMAlphabet.decode A)).getD false
variable [Fintype K]
def oneTape (c : Code K Bool) (input output : K) (n : ℕ) : OneTape :=
  (code A c output (A.width.bits n)).haltOneTape (.inl input) Sum.inl (answer A)
end
end WLTime.RAMConsumer

namespace WLTime.OneTape.Symbolic.RAMWriter
open TypedStack
open scoped Classical
noncomputable section
variable (U : OneTape) (d q : ℕ) (A : RAM)
def consumer (n : ℕ) : OneTape :=
  RAMConsumer.oneTape A (FullWriter.program U d q n).code (.inr FullWriter.Reg.word) (.inr FullWriter.Reg.output) n
def consumerFactor : ℕ := 8*(FullWriter.scratchBound U d q+4+Fintype.card (RAMAlphabet.Reg A)+1)
 def tapesBound : ℕ := FullWriter.scratchBound U d q+4+Fintype.card (RAMAlphabet.Reg A)
 def alphabetBound : ℕ := 3+2*(3+Fintype.card (RAMAlphabet.Letter A))^tapesBound U d q A
 def ramSize : ℕ := Classical.choose (RAMAlphabet.program_linear A)
 def statesBound : ℕ := 3+14*(tapesBound U d q A+1)*(3+Fintype.card (RAMAlphabet.Letter A))*
    (FullWriter.syntaxBound U d q+ramSize A+7)*(3+Fintype.card (RAMAlphabet.Letter A))^tapesBound U d q A
end
end WLTime.OneTape.Symbolic.RAMWriter

namespace WLTime.OneTape.Symbolic.RAMWriter
open scoped Classical
noncomputable section
variable (A : RAM)
def widthFactor : ℕ := 10*(A.width.bound+1)
end
end WLTime.OneTape.Symbolic.RAMWriter

end OAI
end


