-- Prove2me | Definitions.Def_OAIQWWLI000
-- name    : OAIQWWLI000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-23T21:18:53.109981+00:00
-- url     : https://prove2.me/theorems/1706f20f-f14c-48ac-81bd-d2c08ea6e1fa
-- title:
--   OpenAI Weisfeiler–Leman identification split: definitions bundle OAIQWWLI000
-- statement:
--   A definitions bundle of the split of OpenAI's proof that deciding whether Weisfeiler–Leman refinement of a given dimension identifies a graph is EXPTIME-complete (`OAI.WLIdentification.main`, the paper's Theorem 1.1). It holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Computability/WLIdentification` (OpenAI, *The complexity of identifying a graph by Weisfeiler–Leman refinement*, OpenAI Math Release, September 25, 2026, result family 133, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies.
--
--   This bundle holds the graph constructions: degree data and leaf attachments (`degreeNeighbors`, `withLeaves`, `taggedGraph`), the polynomially presented finite types (`Bit`, `fin`, `prod`, `sum`, `option`, `subtype`, `sigma`), the affine blocks and their legal local solutions (`AffineBlocks`, `Legal`, `Solves`), the base graph and its pieces (`baseGraph`, `Piece`, `pieceGraph`), and the bijection systems behind the pebble-game characterization (`BijectionSystem`).
--
--   The definitions of the published statement (`Graph`, `WLdim`, `dimensionLanguage`, `InEXPTIME`, `PolytimeManyOne`, `EXPTIMEComplete` and the rest) are not repeated: the bundle imports them from the published bundle `Def_WLIdentification`. It imports no other bundle of this split.
--
--   Modules: `AcceptingMates`, `AddressArithmetic`, `AffineIncidence`, `AffinePresentation`, `AffineTranslations`, `BijectionGames`, `BinaryAddresses`, `BoundedWords`, `BufferedCircuits`, `CarryPresentation`, `CellularCircuits`, `CellularPresentation`, `CircuitCodes`, `CircuitForms`, `CircuitPresentation`, `ConstraintSchemas`, `CycleSums`, `DimensionDecider`, `ExponentialComputation`, `ExpressionBounds`, `ExpressionCompiler`, `FiniteEncoding`, `FinitePresentation`, `GlobalSolvability`, `GraphEnumeration`, `LeafPresentation`, `LinearExtensions`, `LocalImages`, `LocalPresentation`, `MachineCells`, `MachineReduction`, `MateReconstruction`, `NumericKernel`, `NumericRefinement`, `PolynomialArithmetic`, `PolynomialWords`, `PresentationArithmetic`, `PrivateLeaves`, `ProductPresentation`, `Refinement`, `RejectingMates`, `RingPresentation`, `RowOffsets`, `ScalarExtension`, `SeedBits`, `StableColors`, `StackMachines`, `TypedArithmetic`, `TypedCases`, `WordArithmetic`, `WordExpressions`.
--
--   The theorems of the development that the definitions do not need are proved in the single solution of this split, which imports the bundle `OAIQWWLI002` (and through it the other two) and proves `OAI.WLIdentification.main`. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, The complexity of identifying a graph by Weisfeiler–Leman refinement, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 133; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-complexity-of-identifying-a-graph-by-Weisfeiler-Leman-refinement-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability/WLIdentification at commit adc7f12

import Mathlib
import Definitions.Def_WLIdentification

section
-- module Solutions.OAIQW_WLIdentification.Compat
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
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.Refinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

/-- Equality of finite color histograms admits a color-preserving bijection. -/
theorem exists_colorEquiv {α β γ : Type} [Fintype α] [Fintype β]
    (f : α → γ) (g : β → γ)
    (h : Finset.univ.val.map f = Finset.univ.val.map g) :
    ∃ e : α ≃ β, ∀ a, f a = g (e a) := by
  classical
  have hc (c : γ) : Fintype.card {a // f a = c} = Fintype.card {b // g b = c} := by
    have hh := congrArg (Multiset.count c) h
    simpa only [Multiset.count_map, Fintype.card_subtype, ← Finset.filter_val,
      Finset.card_def, eq_comm] using hh
  let E (c : γ) : {a // f a = c} ≃ {b // g b = c} :=
    Classical.choice (Fintype.card_eq.mp (hc c))
  let e : α ≃ β := (Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight E).trans (Equiv.sigmaFiberEquiv g))
  refine ⟨e, ?_⟩
  intro a
  exact (E (f a) ⟨a, rfl⟩).property.symm

/-- A round witness is a bijection on the entire tuple table. -/
theorem tupleRound_bijection {G H : Graph} {k s : ℕ}
    (h : tupleHistogram G k s = tupleHistogram H k s) :
    ∃ e : (Fin k → Fin G.order) ≃ (Fin k → Fin H.order),
      ∀ v, tupleColor G k s v = tupleColor H k s (e v) :=
  exists_colorEquiv _ _ h

def degree (G : Graph) (v : Fin G.order) : ℕ :=
  (Finset.univ.filter (fun w => G.edge v w = true)).card

/-- Degree is already recoverable from a joint-update round, with two distinct slots. -/
def degreeOfColor {k : ℕ} (i j : Fin k) (c : TupleColor k 1) : ℕ :=
  (c.2.map (fun vector => (vector j).2 i j)).count true

@[simp]
theorem degreeOfColor_tuple {G : Graph} {k : ℕ} (i j : Fin k) (hij : i ≠ j)
    (v : Fin k → Fin G.order) :
    degreeOfColor i j (tupleColor G k 1 v) = degree G (v i) := by
  classical
  unfold degreeOfColor
  dsimp only [tupleColor, TupleColor]
  rw [Multiset.map_map]
  simp only [Function.comp_def, Function.update_of_ne hij, Function.update_self]
  rw [Multiset.count_map]
  change (Multiset.filter (fun z => true = G.edge (v i) z) Finset.univ.val).card = _
  rw [show Multiset.filter (fun z => true = G.edge (v i) z) Finset.univ.val =
      Multiset.filter (fun z => G.edge (v i) z = true) Finset.univ.val from
    Multiset.filter_congr (fun _ _ => eq_comm)]
  rfl

/-- Equal one-round tuple colors preserve adjacency, equality and the degrees of its slots. -/
theorem round_one_local {G H : Graph} {k : ℕ} (hk : 2 ≤ k)
    {v : Fin k → Fin G.order} {w : Fin k → Fin H.order}
    (h : tupleColor G k 1 v = tupleColor H k 1 w) :
    (∀ i j, v i = v j ↔ w i = w j) ∧
    (∀ i j, G.edge (v i) (v j) = H.edge (w i) (w j)) ∧
    (∀ i, degree G (v i) = degree H (w i)) := by
  have h0 : tupleColor G k 0 v = tupleColor H k 0 w := congrArg Prod.fst h
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    have he := congrFun (congrFun (congrArg Prod.fst h0) i) j
    exact decide_eq_decide.mp he
  · intro i j
    exact congrFun (congrFun (congrArg Prod.snd h0) i) j
  · intro i
    have hj : ∃ j : Fin k, i ≠ j := by
      let a : Fin k := ⟨0, by omega⟩
      let b : Fin k := ⟨1, by omega⟩
      by_cases hia : i = a
      · refine ⟨b, ?_⟩
        subst i
        intro he
        have := congrArg Fin.val he
        simp [a, b] at this
      · exact ⟨a, hia⟩
    obtain ⟨j, hij⟩ := hj
    have he := congrArg (degreeOfColor i j) h
    simpa only [degreeOfColor_tuple i j hij] using he

def degreeNeighbors (G : Graph) (v : Fin G.order) (d : ℕ) : ℕ :=
  (Finset.univ.filter (fun w => G.edge v w = true ∧ degree G w = d)).card

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.PrivateLeaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

noncomputable def graphOfSimple {V : Type} [Fintype V] (G : SimpleGraph V) : Graph := by
  classical
  exact {
    order := Fintype.card V
    edge := fun i j => decide (G.Adj ((Fintype.equivFin V).symm i) ((Fintype.equivFin V).symm j))
    symmetric := fun i j => by simp only [G.adj_comm]
    loopless := fun i => by simp }

@[simp]
theorem graphOfSimple_edge {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (v w : V) :
    (graphOfSimple G).edge (Fintype.equivFin V v) (Fintype.equivFin V w) =
      decide (G.Adj v w) := by
  classical
  simp [graphOfSimple]

@[simp]
theorem graphOfSimple_degree {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) :
    degree (graphOfSimple G) (Fintype.equivFin V v) = G.degree v := by
  classical
  unfold degree SimpleGraph.degree
  apply Finset.card_equiv (Fintype.equivFin V).symm
  intro j
  simp only [graphOfSimple]
  simp
  intro _
  exact Finset.mem_univ _

abbrev LeafVertex {V : Type} (ell : V → ℕ) := V ⊕ (Σ v, Fin (ell v))

def withLeaves {V : Type} (G : SimpleGraph V) (ell : V → ℕ) : SimpleGraph (LeafVertex ell) where
  Adj x y := match x, y with
    | .inl v, .inl w => G.Adj v w
    | .inl v, .inr w => v = w.1
    | .inr v, .inl w => v.1 = w
    | .inr _, .inr _ => False
  symm := ⟨by
    intro x y
    cases x <;> cases y <;> first | exact G.adj_symm | exact Eq.symm | exact id⟩
  loopless := ⟨by
    intro x
    cases x <;> simp⟩

noncomputable instance withLeaves_decidable {V : Type} (G : SimpleGraph V) (ell : V → ℕ) :
    DecidableRel (withLeaves G ell).Adj := Classical.decRel _

def baseNeighborEquiv {V : Type} (G : SimpleGraph V) (ell : V → ℕ) (v : V) :
    (withLeaves G ell).neighborSet (.inl v) ≃ G.neighborSet v ⊕ Fin (ell v) where
  toFun x := by
    obtain ⟨x, hx⟩ := x
    cases x with
    | inl w => exact .inl ⟨w, hx⟩
    | inr w =>
      obtain ⟨w, j⟩ := w
      have h : v = w := hx
      subst w
      exact .inr j
  invFun x := match x with
    | .inl w => ⟨.inl w.val, w.property⟩
    | .inr j => ⟨.inr ⟨v, j⟩, rfl⟩
  left_inv x := by
    obtain ⟨x, hx⟩ := x
    cases x with
    | inl w => rfl
    | inr w =>
      obtain ⟨w, j⟩ := w
      have h : v = w := hx
      subst w
      rfl
  right_inv x := by cases x <;> rfl

@[simp]
theorem withLeaves_base_degree {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (ell : V → ℕ) (v : V) :
    (withLeaves G ell).degree (.inl v) = G.degree v + ell v := by
  classical
  rw [← SimpleGraph.card_neighborSet_eq_degree,
    Fintype.card_congr (baseNeighborEquiv G ell v), Fintype.card_sum,
    Fintype.card_fin, SimpleGraph.card_neighborSet_eq_degree]

@[simp]
theorem withLeaves_leaf_degree {V : Type} [Fintype V] (G : SimpleGraph V)
    (ell : V → ℕ) (v : V) (j : Fin (ell v)) :
    (withLeaves G ell).degree (.inr ⟨v, j⟩) = 1 := by
  classical
  apply SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr
  refine ⟨.inl v, rfl, ?_⟩
  intro y hy
  cases y with
  | inl w => exact congrArg Sum.inl (Eq.symm hy)
  | inr _ => exact False.elim hy

def tagSize {V : Type} [Fintype V] (color : V → ℕ) (v : V) : ℕ :=
  color v * (Fintype.card V + 1)

noncomputable def taggedGraph {V : Type} [Fintype V] (G : SimpleGraph V) (color : V → ℕ) : Graph :=
  graphOfSimple (withLeaves G (tagSize color))

/-- The color is recovered literally by the indicated disjoint degree intervals. -/
theorem tag_degree_color {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (color : V → ℕ) (v : V) :
    (withLeaves G (tagSize color)).degree (.inl v) / (Fintype.card V + 1) = color v := by
  rw [withLeaves_base_degree, tagSize, Nat.add_mul_div_right _ _ (by omega)]
  have hlt := G.degree_lt_card_verts v
  rw [Nat.div_eq_of_lt (by omega : G.degree v < Fintype.card V + 1)]
  omega

theorem tag_base_degree_gt_one {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (color : V → ℕ) (hcolor : ∀ v, 0 < color v) (v : V) :
    1 < (withLeaves G (tagSize color)).degree (.inl v) := by
  rw [withLeaves_base_degree, tagSize]
  have hN := Fintype.card_pos_iff.mpr ⟨v⟩
  have hj := hcolor v
  nlinarith

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.AffineIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

abbrev Bit := ZMod 2

/- Fixed-depth natural codes. Unlike arbitrary finite enumerations these are
literal arithmetic presentations, so tag sizes can be generated uniformly. -/
namespace NaturalCode
variable {A B : Type}

def fin (n : ℕ) : Fin n ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
def bool : Bool ↪ ℕ := ⟨fun b => if b then 1 else 0, by decide⟩
def unit : Unit ↪ ℕ := ⟨fun _ => 0, fun _ _ _ => rfl⟩
def prod (a : A ↪ ℕ) (b : B ↪ ℕ) : A × B ↪ ℕ :=
  (a.prodMap b).trans Nat.pairEquiv.toEmbedding

def sum (a : A ↪ ℕ) (b : B ↪ ℕ) : A ⊕ B ↪ ℕ where
  toFun
    | .inl x => 2 * a x
    | .inr y => 2 * b y + 1
  inj' := by
    intro x y h
    cases x <;> cases y
    · exact congrArg Sum.inl (a.injective (by dsimp at h; omega))
    · dsimp at h; omega
    · dsimp at h; omega
    · exact congrArg Sum.inr (b.injective (by dsimp at h; omega))

def option (a : A ↪ ℕ) : Option A ↪ ℕ where
  toFun
    | none => 0
    | some x => a x + 1
  inj' := by
    intro x y h
    cases x <;> cases y
    · rfl
    · dsimp at h; omega
    · dsimp at h; omega
    · exact congrArg some (a.injective (by dsimp at h; omega))

def subtype (a : A ↪ ℕ) (p : A → Prop) : {x // p x} ↪ ℕ :=
  (Function.Embedding.subtype _).trans a

def sigma {B : A → Type} (a : A ↪ ℕ) (b : ∀ x, B x ↪ ℕ) : (Σ x, B x) ↪ ℕ where
  toFun x := Nat.pair (a x.1) (b x.1 x.2)
  inj' := by
    rintro ⟨x,u⟩ ⟨y,v⟩ h
    obtain ⟨hx,hv⟩ := Nat.pair_eq_pair.mp h
    have he := a.injective hx
    dsimp only at he hv
    subst y
    have hu := (b x).injective hv
    subst v
    rfl

noncomputable def fixed (A : Type) [Fintype A] : A ↪ ℕ :=
  (Fintype.equivFin A).toEmbedding.trans (fin _)

end NaturalCode

structure AffineBlocks (C B : Type) [Fintype C] [DecidableEq C] where
  colorIndex : (C ⊕ B) ↪ ℕ
  coordinates : B → Finset C
  form : (b : B) → ((c : coordinates b) → Bit) →ₗ[Bit] Bit
  constrained : B → Bool
  nonzero : ∀ b, constrained b = true → form b ≠ 0

namespace AffineBlocks

variable {C B : Type} [Fintype C] [DecidableEq C]

abbrev Local (D : AffineBlocks C B) (b : B) := (c : D.coordinates b) → Bit

def Legal (D : AffineBlocks C B) (beta : B → Bit) (b : B) (v : D.Local b) : Prop :=
  D.constrained b = true → D.form b v = beta b

noncomputable instance legalDecidable (D : AffineBlocks C B) (beta : B → Bit) (b : B) :
    DecidablePred (D.Legal beta b) := Classical.decPred _

def restrict (D : AffineBlocks C B) (b : B) (x : C → Bit) : D.Local b := fun c => x c.val

def Solves (D : AffineBlocks C B) (beta : B → Bit) (x : C → Bit) : Prop :=
  ∀ b, D.Legal beta b (D.restrict b x)

theorem local_nonempty (D : AffineBlocks C B) (beta : B → Bit) (b : B) :
    ∃ v, D.Legal beta b v := by
  by_cases hc : D.constrained b = true
  · obtain ⟨v, hv⟩ := LinearMap.surjective_of_ne_zero (D.nonzero b hc) (beta b)
    exact ⟨v, fun _ => hv⟩
  · exact ⟨0, fun h => False.elim (hc h)⟩

theorem legal_zero (D : AffineBlocks C B) (b : B) : D.Legal 0 b 0 := by
  intro _
  exact map_zero _

/-- Only local nonemptiness is used here; no simultaneous solution is presumed. -/
def legalTranslate (D : AffineBlocks C B) {beta gamma : B → Bit} (b : B)
    (offset : D.Local b) (ho : ∀ _ : D.constrained b = true,
      D.form b offset = gamma b - beta b) :
    {v // D.Legal beta b v} ≃ {v // D.Legal gamma b v} where
  toFun v := ⟨v.val + offset, by
    intro h
    rw [map_add, v.property h, ho h]
    abel⟩
  invFun v := ⟨v.val - offset, by
    intro h
    rw [map_sub, v.property h, ho h]
    abel⟩
  left_inv v := by ext c; simp
  right_inv v := by ext c; simp

theorem legal_card (D : AffineBlocks C B) (beta gamma : B → Bit) (b : B) :
    Fintype.card {v // D.Legal beta b v} = Fintype.card {v // D.Legal gamma b v} := by
  classical
  obtain ⟨o, ho⟩ := D.local_nonempty (gamma - beta) b
  exact Fintype.card_congr (D.legalTranslate b o ho)

abbrev Vertex (D : AffineBlocks C B) (beta : B → Bit) :=
  (C × Bit) ⊕ (Σ b, {v // D.Legal beta b v})

def colorName (D : AffineBlocks C B) {beta : B → Bit} : D.Vertex beta → C ⊕ B
  | .inl p => .inl p.1
  | .inr v => .inr v.1

def baseGraph (D : AffineBlocks C B) (beta : B → Bit) : SimpleGraph (D.Vertex beta) where
  Adj u v := match u, v with
    | .inl p, .inr w => ∃ h : p.1 ∈ D.coordinates w.1, w.2.val ⟨p.1, h⟩ = p.2
    | .inr w, .inl p => ∃ h : p.1 ∈ D.coordinates w.1, w.2.val ⟨p.1, h⟩ = p.2
    | _, _ => False
  symm := ⟨by intro u v; cases u <;> cases v <;> exact id⟩
  loopless := ⟨by intro u; cases u <;> exact not_false⟩

noncomputable instance baseGraph_decidable (D : AffineBlocks C B) (beta : B → Bit) :
    DecidableRel (D.baseGraph beta).Adj := Classical.decRel _

/-- Translation uses the same named coordinate offset in every incident block. -/
def translationIso (D : AffineBlocks C B) (beta : B → Bit)
    (offset : C → Bit) (ho : D.Solves beta offset) : D.baseGraph 0 ≃g D.baseGraph beta where
  toEquiv := Equiv.sumCongr
    (Equiv.prodCongrRight (fun c => Equiv.addRight (offset c)))
    (Equiv.sigmaCongrRight (fun b => D.legalTranslate b (D.restrict b offset)
      (by intro h; simpa using ho b h)))
  map_rel_iff' := by
    intro x y
    cases x with
    | inl p =>
      cases y with
      | inl q => rfl
      | inr v =>
        change (∃ h : p.1 ∈ D.coordinates v.1,
          v.2.val ⟨p.1, h⟩ + offset p.1 = p.2 + offset p.1) ↔ _
        simp only [add_left_inj]
        rfl
    | inr v =>
      cases y with
      | inl p =>
        change (∃ h : p.1 ∈ D.coordinates v.1,
          v.2.val ⟨p.1, h⟩ + offset p.1 = p.2 + offset p.1) ↔ _
        simp only [add_left_inj]
        rfl
      | inr w => rfl

@[simp]
theorem translationIso_color (D : AffineBlocks C B) (beta : B → Bit)
    (offset : C → Bit) (ho : D.Solves beta offset) (v : D.Vertex 0) :
    D.colorName (D.translationIso beta offset ho v) = D.colorName v := by
  cases v <;> rfl

theorem exists_bit_of_color (D : AffineBlocks C B) {beta : B → Bit}
    (v : D.Vertex beta) (c : C) (h : D.colorName v = .inl c) :
    ∃ a, v = .inl (c, a) := by
  cases v with
  | inl p =>
    have hp : p.1 = c := Sum.inl.inj h
    exact ⟨p.2, by cases p; simp_all⟩
  | inr w => simp [colorName] at h

theorem exists_valuation_of_color (D : AffineBlocks C B) {beta : B → Bit}
    (v : D.Vertex beta) (b : B) (h : D.colorName v = .inr b) :
    ∃ w : {w // D.Legal beta b w}, v = .inr ⟨b, w⟩ := by
  cases v with
  | inl p => simp [colorName] at h
  | inr w =>
    obtain ⟨b', w⟩ := w
    have hb : b' = b := Sum.inr.inj h
    subst b'
    exact ⟨w, rfl⟩

variable [Fintype B]

noncomputable def colorNat (D : AffineBlocks C B) {beta : B → Bit} (v : D.Vertex beta) : ℕ :=
  D.colorIndex (D.colorName v) + 1

omit [Fintype B] in
theorem colorNat_pos (D : AffineBlocks C B) {beta : B → Bit} (v : D.Vertex beta) :
    0 < D.colorNat v := Nat.zero_lt_succ _

omit [Fintype B] in
theorem colorNat_eq_iff (D : AffineBlocks C B) {beta gamma : B → Bit}
    (v : D.Vertex beta) (w : D.Vertex gamma) :
    D.colorNat v = D.colorNat w ↔ D.colorName v = D.colorName w := by
  simp only [colorNat, Nat.add_right_cancel_iff]
  constructor
  · intro h
    exact D.colorIndex.injective h
  · exact congrArg D.colorIndex

theorem vertex_card (D : AffineBlocks C B) (beta gamma : B → Bit) :
    Fintype.card (D.Vertex beta) = Fintype.card (D.Vertex gamma) := by
  simp only [Vertex, Fintype.card_sum, Fintype.card_sigma]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  exact D.legal_card beta gamma b

noncomputable def graph (D : AffineBlocks C B) (beta : B → Bit) : Graph :=
  taggedGraph (D.baseGraph beta) D.colorNat

omit [Fintype B]

/-- A complete bounded incidence piece consists of its valuation class and both
vertices of every bit pair used by this block. -/
abbrev Piece (D : AffineBlocks C B) (beta : B → Bit) (b : B) :=
  (D.coordinates b × Bit) ⊕ {v // D.Legal beta b v}

def pieceEmbed (D : AffineBlocks C B) {beta : B → Bit} (b : B) :
    D.Piece beta b ↪ D.Vertex beta where
  toFun x := match x with
    | .inl p => .inl (p.1.val, p.2)
    | .inr v => .inr ⟨b, v⟩
  inj' := by
    intro x y h
    cases x <;> cases y
    · simp only [Sum.inl.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      apply congrArg Sum.inl
      exact Prod.ext (Subtype.ext h1) h2
    · cases h
    · cases h
    · simp only [Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
      exact congrArg Sum.inr h

def pieceGraph (D : AffineBlocks C B) (beta : B → Bit) (b : B) :
    SimpleGraph (D.Piece beta b) := (D.baseGraph beta).comap (D.pieceEmbed b)

/-- Adjacencies are allowed only between a valuation class and a named bit
coordinate used by that block. This records no right-hand-side information. -/
def Allowed (D : AffineBlocks C B) {beta : B → Bit} (x y : D.Vertex beta) : Prop :=
  match x, y with
  | .inl c, .inr v => c.1 ∈ D.coordinates v.1
  | .inr v, .inl c => c.1 ∈ D.coordinates v.1
  | _, _ => False

end AffineBlocks

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.MateReconstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

def simpleOfGraph (G : Graph) : SimpleGraph (Fin G.order) where
  Adj v w := G.edge v w = true
  symm := ⟨by intro v w; rw [G.symmetric v w]; exact id⟩
  loopless := ⟨by intro v; rw [G.loopless v]; decide⟩

instance simpleOfGraph_decidable (G : Graph) : DecidableRel (simpleOfGraph G).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ = true))

@[simp]
theorem simpleOfGraph_degree (G : Graph) (v : Fin G.order) :
    (simpleOfGraph G).degree v = degree G v := by
  unfold SimpleGraph.degree degree
  congr 1
  ext w
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

def simpleDegreeNeighbors {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) (d : ℕ) : ℕ :=
  (Finset.univ.filter (fun w => G.Adj v w ∧ G.degree w = d)).card

@[simp]
theorem graphOfSimple_degree_at {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (i : Fin (Fintype.card V)) :
    degree (graphOfSimple G) i = G.degree ((Fintype.equivFin V).symm i) := by
  have hh := graphOfSimple_degree G ((Fintype.equivFin V).symm i)
  simpa only [Equiv.apply_symm_apply] using hh

@[simp]
theorem graphOfSimple_degreeNeighbors {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) (d : ℕ) :
    degreeNeighbors (graphOfSimple G) (Fintype.equivFin V v) d = simpleDegreeNeighbors G v d := by
  classical
  unfold degreeNeighbors simpleDegreeNeighbors
  apply Finset.card_equiv (Fintype.equivFin V).symm
  intro j
  have hdegree := graphOfSimple_degree_at G j
  simp only [graphOfSimple] at hdegree ⊢
  simp [hdegree]
  intro _ _
  exact Finset.mem_univ _

namespace AffineBlocks

variable {C B : Type} [Fintype C] [DecidableEq C]

def AllowedName (D : AffineBlocks C B) (x y : C ⊕ B) : Prop :=
  match x, y with
  | .inl c, .inr b => c ∈ D.coordinates b
  | .inr b, .inl c => c ∈ D.coordinates b
  | _, _ => False

end AffineBlocks

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.CycleSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace CycleRows

open scoped BigOperators

theorem rotate_val {n : ℕ} (i : Fin n) :
    (finRotate n i).val = if i.val + 1 < n then i.val + 1 else 0 := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    by_cases hi : i.val < n
    · have hh : i = ⟨i.val, i.isLt⟩ := rfl
      rw [hh, finRotate_of_lt hi]
      simp only [ite_eq_left (by omega : i.val + 1 < n + 1)]
    · have hi' : i = Fin.last n := by
        apply Fin.ext
        change i.val = n
        have := i.isLt
        omega
      rw [hi', finRotate_last]
      simp

theorem rotate_ne_self {n : ℕ} (hn : 2 ≤ n) (i : Fin n) : finRotate n i ≠ i := by
  intro h
  have hw := rotate_val i
  rw [h] at hw
  split_ifs at hw <;> omega

theorem rotate_twice_ne_self {n : ℕ} (hn : 3 ≤ n) (i : Fin n) :
    finRotate n (finRotate n i) ≠ i := by
  intro h
  have hw := rotate_val i
  have hw' := rotate_val (finRotate n i)
  rw [h] at hw'
  split_ifs at hw hw' <;> omega

end CycleRows

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.BijectionGames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

/-- A finite-slot bijective extension system. The extra slot is genuine:
a k-tuple is extended before any one of its slots is discarded. -/
structure BijectionSystem (G H : Graph) (K : ℕ) where
  relates : (m : ℕ) → (Fin m → Fin G.order) → (Fin m → Fin H.order) → Prop
  empty : ∀ v w, relates 0 v w
  restrict : ∀ {m n} {v w}, relates m v w → ∀ f : Fin n → Fin m,
    relates n (v ∘ f) (w ∘ f)
  atomic : ∀ {m v w}, relates m v w →
    (∀ i j, v i = v j ↔ w i = w j) ∧
    (∀ i j, G.edge (v i) (v j) = H.edge (w i) (w j))
  extend : ∀ {m}, m < K → ∀ {v w}, relates m v w →
    ∃ e : Fin G.order ≃ Fin H.order, ∀ z,
      relates (m + 1) (Fin.snoc v z) (Fin.snoc w (e z))

namespace BijectionSystem

def tupleSnocEquiv (V : Type) (m : ℕ) : ((Fin m → V) × V) ≃ (Fin (m + 1) → V) where
  toFun p := Fin.snoc p.1 p.2
  invFun v := (Fin.init v, v (Fin.last m))
  left_inv _ := by simp
  right_inv _ := Fin.snoc_init_self _

end BijectionSystem

/-- Finite descending choice, used only for actual finite vertex/tuple bijections. -/
theorem finite_descending_choice {A : Type} [Fintype A]
    (P : ℕ → A → Prop) (hm : ∀ n a, P (n + 1) a → P n a)
    (he : ∀ n, ∃ a, P n a) : ∃ a, ∀ n, P n a := by
  classical
  by_contra h
  have hn : ∀ a : A, ∃ n, ¬ P n a := by simpa only [not_exists, not_forall] using h
  choose n hn using hn
  let N : ℕ := ∑ a : A, n a
  obtain ⟨a, ha⟩ := he N
  have hle : n a ≤ N := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
  have hdown : ∀ j l, j ≤ l → P l a → P j a := by
    intro j l hj
    induction l, hj using Nat.le_induction with
    | base => exact id
    | succ l _ ih => exact fun hp => ih (hm l a hp)
  exact hn a (hdown (n a) N hle ha)

def StableTuple {G H : Graph} (k : ℕ) (v : Fin k → Fin G.order) (w : Fin k → Fin H.order) : Prop :=
  ∀ round, tupleColor G k round v = tupleColor H k round w

theorem stableTuple_exists {G H : Graph} {k : ℕ} (hk : k ≠ 1)
    (h : Equivalent k G H) (v : Fin k → Fin G.order) :
    ∃ w : Fin k → Fin H.order, StableTuple k v w := by
  rw [Equivalent, ite_eq_right hk] at h
  apply finite_descending_choice (fun r w => tupleColor G k r v = tupleColor H k r w)
  · intro r w hh
    exact congrArg Prod.fst hh
  · intro r
    obtain ⟨E, hE⟩ := tupleRound_bijection (h r)
    exact ⟨E v, hE v⟩

/-- Stable joint colors supply one permanent finite vertex bijection for all
replacement coordinates and all refinement rounds, not a separate round choice. -/
theorem stableTuple_extension {G H : Graph} {k : ℕ}
    {v : Fin k → Fin G.order} {w : Fin k → Fin H.order} (h : StableTuple k v w) :
    ∃ e : Fin G.order ≃ Fin H.order, ∀ z i,
      StableTuple k (Function.update v i z) (Function.update w i (e z)) := by
  classical
  let P (r : ℕ) (e : Fin G.order ≃ Fin H.order) : Prop := ∀ z i,
    tupleColor G k r (Function.update v i z) = tupleColor H k r (Function.update w i (e z))
  have hmono (r : ℕ) (e : Fin G.order ≃ Fin H.order) (he : P (r + 1) e) : P r e := by
    intro z i
    exact congrArg Prod.fst (he z i)
  have hn (r : ℕ) : ∃ e, P r e := by
    have hh := congrArg Prod.snd (h (r + 1))
    change Finset.univ.val.map (fun z => fun i => tupleColor G k r (Function.update v i z)) =
      Finset.univ.val.map (fun z => fun i => tupleColor H k r (Function.update w i z)) at hh
    obtain ⟨e, he⟩ := exists_colorEquiv _ _ hh
    exact ⟨e, fun z i => congrFun (he z) i⟩
  obtain ⟨e, he⟩ := finite_descending_choice P hmono hn
  exact ⟨e, fun z i r => he r z i⟩

/-- Such an extension fixes all currently paired vertices and preserves adjacency
to every current slot, as can be tested in a different replacement coordinate. -/
theorem stableTuple_extension_local {G H : Graph} {k : ℕ} (hk : 2 ≤ k)
    {v : Fin k → Fin G.order} {w : Fin k → Fin H.order} (h : StableTuple k v w) :
    ∃ e : Fin G.order ≃ Fin H.order,
      (∀ z i, StableTuple k (Function.update v i z) (Function.update w i (e z))) ∧
      (∀ i, e (v i) = w i) ∧
      (∀ z i, G.edge (v i) z = H.edge (w i) (e z)) ∧
      (∀ z, degree G z = degree H (e z)) := by
  obtain ⟨e, he⟩ := stableTuple_extension h
  have hdif (i : Fin k) : ∃ j : Fin k, i ≠ j := by
    let a : Fin k := ⟨0, by omega⟩
    let b : Fin k := ⟨1, by omega⟩
    by_cases hia : i = a
    · refine ⟨b, ?_⟩
      subst i
      intro hh
      have := congrArg Fin.val hh
      simp [a, b] at this
    · exact ⟨a, hia⟩
  refine ⟨e, he, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨j, hij⟩ := hdif i
    have hh := (round_one_local hk (he (v i) j 1)).1 i j
    have hh' : w i = e (v i) := by
      simpa only [Function.update_of_ne hij, Function.update_self] using hh.mp (by simp only [Function.update_of_ne hij, Function.update_self])
    exact hh'.symm
  · intro z i
    obtain ⟨j, hij⟩ := hdif i
    have hh := (round_one_local hk (he z j 1)).2.1 i j
    simpa only [Function.update_of_ne hij, Function.update_self] using hh
  · intro z
    let i : Fin k := ⟨0, by omega⟩
    simpa only [Function.update_self] using (round_one_local hk (he z i 1)).2.2 i

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.AffineTranslations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace AffineBlocks

variable {C B : Type} [Fintype C] [DecidableEq C] [DecidableEq B]

structure OffsetFamily (D : AffineBlocks C B) (beta : B → Bit) (K : ℕ) where
  admissible : Finset B → (C → Bit) → Prop
  empty : ∃ x, admissible ∅ x
  legal : ∀ {U x}, admissible U x → ∀ b ∈ U, D.Legal beta b (D.restrict b x)
  restrict : ∀ {U V x}, V ⊆ U → admissible U x → admissible V x
  extend : ∀ {U x}, U.card < K → admissible U x → ∀ b,
    ∃ y, admissible (insert b U) y ∧ ∀ b' ∈ U, ∀ c ∈ D.coordinates b', y c = x c

/-- Purely local interfaces for the actual affine vertex translations. The
`piecewise` field is a bijection on vertices, not an asserted game strategy. -/
structure OwnedTranslations (D : AffineBlocks C B) (beta : B → Bit)
    {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W) where
  owner : V → B
  images : (C → Bit) → V → W → Prop
  atomic : ∀ {x v v' w w'}, images x v w → images x v' w' →
    (v = v' ↔ w = w') ∧ (G.Adj v v' ↔ H.Adj w w')
  locality : ∀ {x y v w}, images x v w →
    (∀ c ∈ D.coordinates (owner v), y c = x c) → images y v w
  piecewise : ∀ f : B → C → Bit,
    (∀ b, D.Legal beta b (D.restrict b (f b))) →
    ∃ e : V ≃ W, ∀ v, images (f (owner v)) v (e v)

namespace OwnedTranslations

variable {D : AffineBlocks C B} {beta : B → Bit}
    {V W : Type} [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}

/-- Combining independently selected owner bijections gives one announced
vertex bijection before the next vertex is selected. -/
noncomputable def bijectionSystem (T : OwnedTranslations D beta G H)
    {K : ℕ} (F : OffsetFamily D beta K) :
    BijectionSystem (graphOfSimple G) (graphOfSimple H) K := by
  classical
  let ev := Fintype.equivFin V
  let ew := Fintype.equivFin W
  let support {m : ℕ} (v : Fin m → Fin (Fintype.card V)) : Finset B :=
    Finset.univ.image (fun i => T.owner (ev.symm (v i)))
  have hmem {m : ℕ} (v : Fin m → Fin (Fintype.card V)) (i : Fin m) :
      T.owner (ev.symm (v i)) ∈ support v := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  refine {
    relates := fun m v w => ∃ x, F.admissible (support v) x ∧
      ∀ i : Fin m, T.images x (ev.symm (v i)) (ew.symm (w i))
    empty := ?_
    restrict := ?_
    atomic := ?_
    extend := ?_ }
  · intro v w
    obtain ⟨x, hx⟩ := F.empty
    refine ⟨x, ?_, fun i => Fin.elim0 i⟩
    simpa only [support, Finset.univ_eq_empty, Finset.image_empty] using hx
  · intro m n v w hh f
    obtain ⟨x, hx, hi⟩ := hh
    refine ⟨x, F.restrict ?_ hx, fun i => hi (f i)⟩
    intro b hb
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb
    exact hmem v (f i)
  · intro m v w hh
    obtain ⟨x, _, hi⟩ := hh
    constructor
    · intro i j
      exact (ev.symm.injective.eq_iff).symm.trans
        (((T.atomic (hi i) (hi j)).1).trans ew.symm.injective.eq_iff)
    · intro i j
      change decide (G.Adj (ev.symm (v i)) (ev.symm (v j))) =
        decide (H.Adj (ew.symm (w i)) (ew.symm (w j)))
      exact decide_eq_decide.mpr ((T.atomic (hi i) (hi j)).2)
  · intro m hm v w hh
    obtain ⟨x, hx, hi⟩ := hh
    have hcard : (support v).card < K := lt_of_le_of_lt
      (by simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin m)))
        (f := fun i => T.owner (ev.symm (v i))))) hm
    have hext := F.extend hcard hx
    choose y hy hagree using hext
    have hlegal (b : B) : D.Legal beta b (D.restrict b (y b)) :=
      F.legal (hy b) b (Finset.mem_insert_self _ _)
    obtain ⟨e, he⟩ := T.piecewise y hlegal
    let E := ev.symm.trans (e.trans ew)
    refine ⟨E, ?_⟩
    intro z
    let b := T.owner (ev.symm z)
    refine ⟨y b, ?_, ?_⟩
    · apply F.restrict _ (hy b)
      intro b' hb'
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb'
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Fin.snoc_last] using Finset.mem_insert_self b (support v)
      · simpa only [Fin.snoc_castSucc] using Finset.mem_insert_of_mem (hmem v j)
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.snoc_last]
        change T.images (y b) (ev.symm z) (ew.symm (ew (e (ev.symm z))))
        simpa only [Equiv.symm_apply_apply] using he (ev.symm z)
      · simpa only [Fin.snoc_castSucc] using
          T.locality (hi j) (hagree b (T.owner (ev.symm (v j))) (hmem v j))

end OwnedTranslations
end AffineBlocks

namespace AffineBlocks

variable {C B : Type} [Fintype C] [DecidableEq C]

abbrev BareVertex (D : AffineBlocks C B) := (C × Bit) ⊕ (Σ b, D.Local b)

def erase (D : AffineBlocks C B) {beta : B → Bit} : D.Vertex beta → D.BareVertex
  | .inl p => .inl p
  | .inr v => .inr ⟨v.1, v.2.val⟩

theorem erase_injective (D : AffineBlocks C B) (beta : B → Bit) :
    Function.Injective (D.erase (beta := beta)) := by
  intro v w h
  cases v with
  | inl p => cases w with
    | inl q => exact congrArg Sum.inl (Sum.inl.inj h)
    | inr w => cases h
  | inr v => cases w with
    | inl q => cases h
    | inr w =>
      obtain ⟨b, v⟩ := v
      obtain ⟨c, w⟩ := w
      have hbc : b = c := congrArg Sigma.fst (Sum.inr.inj h)
      subst c
      have hvw : v.val = w.val := by simpa only [erase, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] using h
      exact congrArg (fun a => Sum.inr (Sigma.mk b a)) (Subtype.ext hvw)

def bareTranslation (D : AffineBlocks C B) (x : C → Bit) : D.BareVertex ≃ D.BareVertex :=
  Equiv.sumCongr
    (Equiv.prodCongrRight (fun c => Equiv.addRight (x c)))
    (Equiv.sigmaCongrRight (fun b => Equiv.addRight (D.restrict b x)))

def BaseImages (D : AffineBlocks C B) {beta : B → Bit}
    (x : C → Bit) (v : D.Vertex 0) (w : D.Vertex beta) : Prop :=
  D.erase w = D.bareTranslation x (D.erase v)

def BareAdj (D : AffineBlocks C B) : D.BareVertex → D.BareVertex → Prop
  | .inl p, .inr v => ∃ h : p.1 ∈ D.coordinates v.1, v.2 ⟨p.1, h⟩ = p.2
  | .inr v, .inl p => ∃ h : p.1 ∈ D.coordinates v.1, v.2 ⟨p.1, h⟩ = p.2
  | _, _ => False

theorem bareAdj_erase (D : AffineBlocks C B) {beta : B → Bit} (v w : D.Vertex beta) :
    D.BareAdj (D.erase v) (D.erase w) ↔ (D.baseGraph beta).Adj v w := by
  cases v <;> cases w <;> rfl

theorem bareAdj_translation (D : AffineBlocks C B) (x : C → Bit) (v w : D.BareVertex) :
    D.BareAdj (D.bareTranslation x v) (D.bareTranslation x w) ↔ D.BareAdj v w := by
  cases v with
  | inl p => cases w with
    | inl q => rfl
    | inr w =>
      change (∃ h : p.1 ∈ D.coordinates w.1,
        w.2 ⟨p.1, h⟩ + x p.1 = p.2 + x p.1) ↔ _
      simp only [add_left_inj]
      rfl
  | inr v => cases w with
    | inl p =>
      change (∃ h : p.1 ∈ D.coordinates v.1,
        v.2 ⟨p.1, h⟩ + x p.1 = p.2 + x p.1) ↔ _
      simp only [add_left_inj]
      rfl
    | inr w => rfl

theorem baseImages_atomic (D : AffineBlocks C B) {beta : B → Bit}
    {x : C → Bit} {v v' : D.Vertex 0} {w w' : D.Vertex beta}
    (h : D.BaseImages x v w) (h' : D.BaseImages x v' w') :
    (v = v' ↔ w = w') ∧ ((D.baseGraph 0).Adj v v' ↔ (D.baseGraph beta).Adj w w') := by
  constructor
  · rw [← (D.erase_injective 0).eq_iff, ← (D.bareTranslation x).injective.eq_iff,
      ← h, ← h', (D.erase_injective beta).eq_iff]
  · rw [← D.bareAdj_erase v v', ← D.bareAdj_erase w w', h, h', D.bareAdj_translation]

def vertexOwner (D : AffineBlocks C B) (owner : C → B) {beta : B → Bit} : D.Vertex beta → B
  | .inl p => owner p.1
  | .inr v => v.1

theorem baseImages_locality (D : AffineBlocks C B) (owner : C → B)
    (ho : ∀ c, c ∈ D.coordinates (owner c)) {beta : B → Bit}
    {x y : C → Bit} {v : D.Vertex 0} {w : D.Vertex beta}
    (h : D.BaseImages x v w)
    (ha : ∀ c ∈ D.coordinates (D.vertexOwner owner v), y c = x c) : D.BaseImages y v w := by
  unfold BaseImages at h ⊢
  rw [h]
  cases v with
  | inl p =>
    change Sum.inl (p.1, p.2 + x p.1) = Sum.inl (p.1, p.2 + y p.1)
    rw [ha p.1 (ho p.1)]
  | inr v =>
    change (Sum.inr ⟨v.1, v.2.val + D.restrict v.1 x⟩ : D.BareVertex) =
      Sum.inr ⟨v.1, v.2.val + D.restrict v.1 y⟩
    have he : D.restrict v.1 x = D.restrict v.1 y := by
      funext c
      exact (ha c.val c.property).symm
    rw [he]

def piecewiseTranslation (D : AffineBlocks C B) (owner : C → B) (beta : B → Bit)
    (f : B → C → Bit) (hf : ∀ b, D.Legal beta b (D.restrict b (f b))) :
    D.Vertex 0 ≃ D.Vertex beta :=
  Equiv.sumCongr
    (Equiv.prodCongrRight (fun c => Equiv.addRight (f (owner c) c)))
    (Equiv.sigmaCongrRight (fun b => D.legalTranslate b (D.restrict b (f b))
      (by intro h; simpa using hf b h)))

theorem piecewiseTranslation_images (D : AffineBlocks C B) (owner : C → B) (beta : B → Bit)
    (f : B → C → Bit) (hf : ∀ b, D.Legal beta b (D.restrict b (f b))) (v : D.Vertex 0) :
    D.BaseImages (f (D.vertexOwner owner v)) v (D.piecewiseTranslation owner beta f hf v) := by
  cases v <;> rfl

theorem baseImages_color (D : AffineBlocks C B) {beta : B → Bit}
    {x : C → Bit} {v : D.Vertex 0} {w : D.Vertex beta} (h : D.BaseImages x v w) :
    D.colorName w = D.colorName v := by
  let col : D.BareVertex → C ⊕ B := Sum.elim (fun p => .inl p.1) (fun v => .inr v.1)
  have he (u : D.BareVertex) : col (D.bareTranslation x u) = col u := by cases u <;> rfl
  have hv : col (D.erase v) = D.colorName v := by cases v <;> rfl
  have hw : col (D.erase w) = D.colorName w := by cases w <;> rfl
  rw [← hw, h, he, hv]

variable [DecidableEq B]

/-- The finite affine construction realizes the local interfaces with no
assumed graph isomorphism or winning strategy. -/
def baseTranslations (D : AffineBlocks C B) (owner : C → B)
    (ho : ∀ c, c ∈ D.coordinates (owner c)) (beta : B → Bit) :
    OwnedTranslations D beta (D.baseGraph 0) (D.baseGraph beta) where
  owner := D.vertexOwner owner
  images := D.BaseImages
  atomic := D.baseImages_atomic
  locality := D.baseImages_locality owner ho
  piecewise f hf := ⟨D.piecewiseTranslation owner beta f hf,
    D.piecewiseTranslation_images owner beta f hf⟩

end AffineBlocks

/-- Parent and private index give an injective description of leaf-coded vertices. -/
def leafParent {V : Type} {ell : V → ℕ} : LeafVertex ell → V
  | .inl v => v
  | .inr v => v.1

def leafIndex {V : Type} {ell : V → ℕ} : LeafVertex ell → Option ℕ
  | .inl _ => none
  | .inr v => some v.2.val

theorem leaf_eq_iff {V : Type} {ell : V → ℕ} (v w : LeafVertex ell) :
    v = w ↔ leafParent v = leafParent w ∧ leafIndex v = leafIndex w := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨hp, hi⟩
    cases v with
    | inl v => cases w with
      | inl w => exact congrArg Sum.inl hp
      | inr w => cases hi
    | inr v => cases w with
      | inl w => cases hi
      | inr w =>
        obtain ⟨v, i⟩ := v
        obtain ⟨w, j⟩ := w
        change v = w at hp
        subst w
        have hij : i = j := Fin.ext (Option.some.inj hi)
        subst j
        rfl

theorem withLeaves_adj_iff {V : Type} (G : SimpleGraph V) (ell : V → ℕ)
    (v w : LeafVertex ell) : (withLeaves G ell).Adj v w ↔
      if leafIndex v = none then
        if leafIndex w = none then G.Adj (leafParent v) (leafParent w)
        else leafParent v = leafParent w
      else if leafIndex w = none then leafParent v = leafParent w else False := by
  cases v <;> cases w <;> simp only [leafIndex, leafParent, withLeaves,
    ite_true, Option.some_ne_none, ite_false]

namespace AffineBlocks.OwnedTranslations

variable {C B V W : Type} [Fintype C] [DecidableEq C] [DecidableEq B]
    {D : AffineBlocks C B} {beta : B → Bit} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Private leaves extend local translations exactly, retaining each private
index; this is used before the owner pieces are combined into a game bijection. -/
def withLeaves (T : OwnedTranslations D beta G H) (ell : V → ℕ) (ell' : W → ℕ)
    (hl : ∀ {x v w}, T.images x v w → ell v = ell' w) :
    OwnedTranslations D beta (WLIdentification.withLeaves G ell)
      (WLIdentification.withLeaves H ell') where
  owner v := T.owner (leafParent v)
  images x v w := T.images x (leafParent v) (leafParent w) ∧ leafIndex v = leafIndex w
  atomic := by
    intro x v v' w w' h h'
    obtain ⟨he, ha⟩ := T.atomic h.1 h'.1
    constructor
    · rw [leaf_eq_iff, leaf_eq_iff, he, h.2, h'.2]
    · rw [withLeaves_adj_iff, withLeaves_adj_iff, ← h.2, ← h'.2]
      split <;> split
      · exact ha
      · exact he
      · exact he
      · rfl
  locality := by
    intro x y v w h hh
    exact ⟨T.locality h.1 hh, h.2⟩
  piecewise := by
    intro f hf
    obtain ⟨e, he⟩ := T.piecewise f hf
    let E : LeafVertex ell ≃ LeafVertex ell' :=
      Equiv.sumCongr e (Equiv.sigmaCongr e (fun v => finCongr (hl (he v))))
    refine ⟨E, ?_⟩
    intro v
    cases v with
    | inl v => exact ⟨he v, rfl⟩
    | inr v => exact ⟨he v.1, rfl⟩

end AffineBlocks.OwnedTranslations

namespace AffineBlocks
variable {C B : Type} [Fintype C] [DecidableEq C] [Fintype B] [DecidableEq B]

/-- Complete interface from exact-projection coordinate families to the actual
uncolored graphs, with every private leaf and its owner included. -/
noncomputable def taggedTranslations (D : AffineBlocks C B) (owner : C → B)
    (ho : ∀ c, c ∈ D.coordinates (owner c)) (beta : B → Bit) :
    OwnedTranslations D beta
      (withLeaves (D.baseGraph 0) (tagSize D.colorNat))
      (withLeaves (D.baseGraph beta) (tagSize D.colorNat)) :=
  (D.baseTranslations owner ho beta).withLeaves _ _ (by
    intro x v w h
    have hc : D.colorNat w = D.colorNat v :=
      (D.colorNat_eq_iff w v).mpr (D.baseImages_color h)
    dsimp only [tagSize]
    rw [hc, D.vertex_card 0 beta])

end AffineBlocks

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.RowOffsets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace CycleRows

/-- The row-sum restriction is retained explicitly; pointwise globally consistent
address values alone are not used as a substitute for actual readout offsets. -/
def RowSum {r : ℕ} (A : Fin r → Type) (V : Type) [AddCommMonoid V]
    (h : ((i : Fin r) → A i) → V) : Prop :=
  ∃ f : (i : Fin r) → A i → A (finRotate r i) → V,
    ∀ a, h a = ∑ i, f i (a i) (a (finRotate r i))

end CycleRows

structure RingLayout (r : ℕ) (T L : Type) where
  typeIndex : T ↪ ℕ
  linkIndex : L ↪ ℕ
  dimension : T → ℕ
  dimension_bound : ∀ t, dimension t = 1 ∨ dimension t = 2
  labels : T → Fin r → Finset Bool
  labels_nonempty : ∀ t i, (labels t i).Nonempty
  first : L → T
  second : L → T
  endpoints_ne : ∀ e, first e ≠ second e
  internal_endpoint : ∀ e, dimension (first e) = 1 ∨ dimension (second e) = 1
  matchLabels : L → Fin r → Finset Bool
  matchLabels_nonempty : ∀ e i, (matchLabels e i).Nonempty
  firstLabel : (e : L) → (i : Fin r) → {a // a ∈ matchLabels e i} → {a // a ∈ labels (first e) i}
  secondLabel : (e : L) → (i : Fin r) → {a // a ∈ matchLabels e i} → {a // a ∈ labels (second e) i}
  firstLabel_injective : ∀ e i, Function.Injective (firstLabel e i)
  secondLabel_injective : ∀ e i, Function.Injective (secondLabel e i)
  firstForm : (e : L) → (Fin (dimension (first e)) → Bit) →ₗ[Bit] Bit
  secondForm : (e : L) → (Fin (dimension (second e)) → Bit) →ₗ[Bit] Bit

namespace RingLayout
variable {r : ℕ} {T L : Type} (R : RingLayout r T L)

abbrev Label (t : T) (i : Fin r) := {a // a ∈ R.labels t i}
abbrev Match (e : L) (i : Fin r) := {a // a ∈ R.matchLabels e i}
abbrev HName := Σ t : T, Σ i : Fin r, R.Label t i × R.Label t (finRotate r i)
abbrev VName := Σ e : L, Σ i : Fin r, R.Match e i
abbrev Square := Σ e : L, Σ i : Fin r, R.Match e i × R.Match e (finRotate r i)
abbrev Coordinate := (Σ h : R.HName, Fin (R.dimension h.1)) ⊕ R.VName
abbrev Block := R.HName ⊕ R.Square

def leftH (b : R.Square) : R.HName :=
  ⟨R.first b.1, b.2.1, R.firstLabel b.1 b.2.1 b.2.2.1,
    R.firstLabel b.1 (finRotate r b.2.1) b.2.2.2⟩

def rightH (b : R.Square) : R.HName :=
  ⟨R.second b.1, b.2.1, R.secondLabel b.1 b.2.1 b.2.2.1,
    R.secondLabel b.1 (finRotate r b.2.1) b.2.2.2⟩

def topV (b : R.Square) : R.VName := ⟨b.1, b.2.1, b.2.2.1⟩
def bottomV (b : R.Square) : R.VName := ⟨b.1, finRotate r b.2.1, b.2.2.2⟩

theorem vertical_ne (hr : 2 ≤ r) (b : R.Square) : R.topV b ≠ R.bottomV b := by
  intro h
  have hi : b.2.1 = finRotate r b.2.1 := congrArg (fun v : R.VName => v.2.1) h
  exact CycleRows.rotate_ne_self hr _ hi.symm

noncomputable instance coordinateDecidableEq : DecidableEq R.Coordinate := Classical.decEq _
noncomputable instance blockDecidableEq : DecidableEq R.Block := Classical.decEq _

noncomputable def hCoords (h : R.HName) : Finset R.Coordinate := by
  classical
  exact Finset.univ.image (fun j => Sum.inl ⟨h, j⟩)

noncomputable def coordinates : R.Block → Finset R.Coordinate
  | .inl h => R.hCoords h
  | .inr b => R.hCoords (R.leftH b) ∪ R.hCoords (R.rightH b) ∪
      {Sum.inr (R.topV b), Sum.inr (R.bottomV b)}

theorem hCoord_mem (h : R.HName) (j : Fin (R.dimension h.1)) :
    Sum.inl ⟨h, j⟩ ∈ R.hCoords h := by
  classical
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

theorem left_mem (b : R.Square) (j : Fin (R.dimension (R.first b.1))) :
    Sum.inl ⟨R.leftH b, j⟩ ∈ R.coordinates (.inr b) := by
  classical
  exact Finset.mem_union_left _ (Finset.mem_union_left _ (R.hCoord_mem (R.leftH b) j))

theorem right_mem (b : R.Square) (j : Fin (R.dimension (R.second b.1))) :
    Sum.inl ⟨R.rightH b, j⟩ ∈ R.coordinates (.inr b) := by
  classical
  exact Finset.mem_union_left _ (Finset.mem_union_right _ (R.hCoord_mem (R.rightH b) j))

theorem top_mem (b : R.Square) : Sum.inr (R.topV b) ∈ R.coordinates (.inr b) := by
  classical
  exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)

theorem bottom_mem (b : R.Square) : Sum.inr (R.bottomV b) ∈ R.coordinates (.inr b) := by
  classical
  exact Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

def localProj (b : R.Block) (c : R.Coordinate) (hc : c ∈ R.coordinates b) :
    ((a : R.coordinates b) → Bit) →ₗ[Bit] Bit := LinearMap.proj ⟨c, hc⟩

noncomputable def squareForm (b : R.Square) :
    ((c : R.coordinates (.inr b)) → Bit) →ₗ[Bit] Bit :=
  (R.firstForm b.1).comp (LinearMap.pi (fun j => R.localProj _ _ (R.left_mem b j))) +
  (R.secondForm b.1).comp (LinearMap.pi (fun j => R.localProj _ _ (R.right_mem b j))) +
  R.localProj _ _ (R.top_mem b) + R.localProj _ _ (R.bottom_mem b)

theorem squareForm_apply (b : R.Square) (x : (c : R.coordinates (.inr b)) → Bit) :
    R.squareForm b x =
      R.firstForm b.1 (fun j => x ⟨_, R.left_mem b j⟩) +
      R.secondForm b.1 (fun j => x ⟨_, R.right_mem b j⟩) +
      x ⟨_, R.top_mem b⟩ + x ⟨_, R.bottom_mem b⟩ := rfl

theorem squareForm_nonzero (hr : 2 ≤ r) (b : R.Square) : R.squareForm b ≠ 0 := by
  classical
  let c : R.coordinates (.inr b) := ⟨.inr (R.topV b), R.top_mem b⟩
  let x : (a : R.coordinates (.inr b)) → Bit := Pi.single c 1
  have hl : (fun j => x ⟨_, R.left_mem b j⟩) = 0 := by
    funext j
    apply Pi.single_eq_of_ne
    intro hh
    have := congrArg Subtype.val hh
    cases this
  have hu : (fun j => x ⟨_, R.right_mem b j⟩) = 0 := by
    funext j
    apply Pi.single_eq_of_ne
    intro hh
    have := congrArg Subtype.val hh
    cases this
  have hb : x ⟨_, R.bottom_mem b⟩ = 0 := by
    apply Pi.single_eq_of_ne
    intro hh
    exact R.vertical_ne hr b (Sum.inr.inj (congrArg Subtype.val hh)).symm
  have hx : R.squareForm b x = 1 := by
    rw [R.squareForm_apply, hl, hu, map_zero, map_zero, hb]
    change 0 + 0 + (Pi.single c (1 : Bit) : (a : R.coordinates (.inr b)) → Bit) c + 0 = 1
    simp
  intro h
  rw [h, LinearMap.zero_apply] at hx
  exact zero_ne_one hx

variable [Fintype T] [Fintype L]

def hIndex : R.HName ↪ ℕ :=
  NaturalCode.sigma R.typeIndex (fun _ => NaturalCode.sigma (NaturalCode.fin r) (fun _ =>
    NaturalCode.prod (NaturalCode.subtype NaturalCode.bool _) (NaturalCode.subtype NaturalCode.bool _)))

def vIndex : R.VName ↪ ℕ :=
  NaturalCode.sigma R.linkIndex (fun _ => NaturalCode.sigma (NaturalCode.fin r) (fun _ =>
    NaturalCode.subtype NaturalCode.bool _))

def squareIndex : R.Square ↪ ℕ :=
  NaturalCode.sigma R.linkIndex (fun _ => NaturalCode.sigma (NaturalCode.fin r) (fun _ =>
    NaturalCode.prod (NaturalCode.subtype NaturalCode.bool _) (NaturalCode.subtype NaturalCode.bool _)))

def colorIndex : (R.Coordinate ⊕ R.Block) ↪ ℕ :=
  NaturalCode.sum
    (NaturalCode.sum (NaturalCode.sigma R.hIndex (fun _ => NaturalCode.fin _)) R.vIndex)
    (NaturalCode.sum R.hIndex R.squareIndex)

noncomputable def affine (hr : 2 ≤ r) : AffineBlocks R.Coordinate R.Block where
  colorIndex := R.colorIndex
  coordinates := R.coordinates
  form b := match b with
    | .inl _ => 0
    | .inr q => R.squareForm q
  constrained b := match b with
    | .inl _ => false
    | .inr _ => true
  nonzero b hb := by
    cases b with
    | inl h => cases hb
    | inr b => exact R.squareForm_nonzero hr b

end RingLayout

namespace RingLayout
variable {r : ℕ} {T L : Type} [Fintype T] [Fintype L] (R : RingLayout r T L)

abbrev Horizontal := (h : R.HName) → Fin (R.dimension h.1) → Bit
abbrev Vertical := R.VName → Bit

def horizontal (z : R.Coordinate → Bit) : R.Horizontal := fun h j => z (.inl ⟨h, j⟩)
def vertical (z : R.Coordinate → Bit) : R.Vertical := fun v => z (.inr v)
def pack (x : R.Horizontal) (y : R.Vertical) : R.Coordinate → Bit
  | .inl h => x h.1 h.2
  | .inr v => y v

abbrev Address (t : T) := (i : Fin r) → R.Label t i
abbrev MatchAddress (e : L) := (i : Fin r) → R.Match e i

def leftAddress (e : L) (a : R.MatchAddress e) : R.Address (R.first e) :=
  fun i => R.firstLabel e i (a i)
def rightAddress (e : L) (a : R.MatchAddress e) : R.Address (R.second e) :=
  fun i => R.secondLabel e i (a i)

def linkShift (beta : R.Block → Bit) (e : L) (a : R.MatchAddress e) : Bit :=
  ∑ i, beta (.inr ⟨e, i, a i, a (finRotate r i)⟩)

end RingLayout

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.ConstraintSchemas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

structure ComparisonSchemas (r : ℕ) (P E : Type) where
  pointIndex : P ↪ ℕ
  edgeIndex : E ↪ ℕ
  dimension : P → ℕ
  dimension_bound : ∀ p, dimension p = 1 ∨ dimension p = 2
  source : E → P
  target : E → P
  domain : E → Fin r → Finset Bool
  domain_nonempty : ∀ e i, (domain e i).Nonempty
  mapping : (e : E) → (i : Fin r) → {a // a ∈ domain e i} → Bool
  mapping_injective : ∀ e i, Function.Injective (mapping e i)
  left : (e : E) → (Fin (dimension (source e)) → Bit) →ₗ[Bit] Bit
  right : (e : E) → (Fin (dimension (target e)) → Bit) →ₗ[Bit] Bit

namespace ComparisonSchemas
variable {r : ℕ} {P E : Type} (S : ComparisonSchemas r P E)

abbrev InternalType (_S : ComparisonSchemas r P E) (n : ℕ) := P ⊕ (E × Fin (n + 1))
abbrev Link (_S : ComparisonSchemas r P E) (n : ℕ) := E ⊕ ((E × Fin n) ⊕ E)

def first (n : ℕ) : S.Link n → S.InternalType n
  | .inl e => .inl (S.source e)
  | .inr (.inl (e, i)) => .inr (e, i.castSucc)
  | .inr (.inr e) => .inr (e, Fin.last n)

def second (n : ℕ) : S.Link n → S.InternalType n
  | .inl e => .inr (e, 0)
  | .inr (.inl (e, i)) => .inr (e, i.succ)
  | .inr (.inr e) => .inl (S.target e)

def wire (n : ℕ) : S.Link n → E
  | .inl e => e
  | .inr (.inl (e, _)) => e
  | .inr (.inr e) => e

def layoutDimension (n : ℕ) : S.InternalType n → ℕ
  | .inl p => S.dimension p
  | .inr _ => 1

def layoutLabels (n : ℕ) : S.InternalType n → Fin r → Finset Bool
  | .inl _, _ => Finset.univ
  | .inr (e, _), i => S.domain e i

def firstLabel (n : ℕ) (l : S.Link n) (i : Fin r) :
    {a // a ∈ S.domain (S.wire n l) i} → {a // a ∈ S.layoutLabels n (S.first n l) i} := by
  cases l with
  | inl e => exact fun a => ⟨a.val, Finset.mem_univ _⟩
  | inr l => cases l with
    | inl p => exact id
    | inr e => exact id

def secondLabel (n : ℕ) (l : S.Link n) (i : Fin r) :
    {a // a ∈ S.domain (S.wire n l) i} → {a // a ∈ S.layoutLabels n (S.second n l) i} := by
  cases l with
  | inl e => exact id
  | inr l => cases l with
    | inl p => exact id
    | inr e => exact fun a => ⟨S.mapping e i a, Finset.mem_univ _⟩

def firstForm (n : ℕ) (l : S.Link n) :
    (Fin (S.layoutDimension n (S.first n l)) → Bit) →ₗ[Bit] Bit := by
  cases l with
  | inl e => exact S.left e
  | inr l => cases l with
    | inl p => exact (LinearMap.proj (0 : Fin 1))
    | inr e => exact (LinearMap.proj (0 : Fin 1))

def secondForm (n : ℕ) (l : S.Link n) :
    (Fin (S.layoutDimension n (S.second n l)) → Bit) →ₗ[Bit] Bit := by
  cases l with
  | inl e => exact (LinearMap.proj (0 : Fin 1))
  | inr l => cases l with
    | inl p => exact (LinearMap.proj (0 : Fin 1))
    | inr e => exact S.right e

def layout (n : ℕ) : RingLayout r (S.InternalType n) (S.Link n) where
  typeIndex := NaturalCode.sum S.pointIndex (NaturalCode.prod S.edgeIndex (NaturalCode.fin _))
  linkIndex := NaturalCode.sum S.edgeIndex (NaturalCode.sum (NaturalCode.prod S.edgeIndex (NaturalCode.fin _)) S.edgeIndex)
  dimension := S.layoutDimension n
  dimension_bound t := by cases t with
    | inl p => exact S.dimension_bound p
    | inr p => exact Or.inl rfl
  labels := S.layoutLabels n
  labels_nonempty t i := by cases t with
    | inl p => exact ⟨false, Finset.mem_univ _⟩
    | inr p => exact S.domain_nonempty p.1 i
  first := S.first n
  second := S.second n
  endpoints_ne l := by
    cases l with
    | inl e => intro h; cases h
    | inr l => cases l with
      | inl p =>
        intro h
        have hi := congrArg (fun t : S.InternalType n =>
          match t with | .inl _ => 0 | .inr p => p.2.val) h
        change p.2.val = p.2.val + 1 at hi
        omega
      | inr e => intro h; cases h
  internal_endpoint l := by
    cases l with
    | inl e => exact Or.inr rfl
    | inr l => cases l <;> exact Or.inl rfl
  matchLabels l i := S.domain (S.wire n l) i
  matchLabels_nonempty l i := S.domain_nonempty (S.wire n l) i
  firstLabel := S.firstLabel n
  secondLabel := S.secondLabel n
  firstLabel_injective l i := by
    cases l with
    | inl e =>
      intro a b h
      apply Subtype.ext
      exact congrArg (fun x : {a // a ∈ S.layoutLabels n (S.first n (.inl e)) i} => x.val) h
    | inr l => cases l <;> exact Function.injective_id
  secondLabel_injective l i := by
    cases l with
    | inl e => exact Function.injective_id
    | inr l => cases l with
      | inl p => exact Function.injective_id
      | inr e => exact fun a b h => S.mapping_injective e i (congrArg Subtype.val h)
  firstForm := S.firstForm n
  secondForm := S.secondForm n

end ComparisonSchemas

namespace WireAlgebra

def prefixSum {n : ℕ} (c : Fin n → Bit) (j : Fin (n + 1)) : Bit :=
  ∑ i : Fin n, if i.val < j.val then c i else 0

@[simp]
theorem prefix_zero {n : ℕ} (c : Fin n → Bit) : prefixSum c 0 = 0 := by
  simp [prefixSum]

@[simp]
theorem prefix_last {n : ℕ} (c : Fin n → Bit) : prefixSum c (Fin.last n) = ∑ i, c i := by
  simp [prefixSum]

theorem prefix_succ {n : ℕ} (c : Fin n → Bit) (j : Fin n) :
    prefixSum c j.succ = prefixSum c j.castSucc + c j := by
  have hi (i : Fin n) : (if i.val < j.val + 1 then c i else 0) =
      (if i.val < j.val then c i else 0) + (if i = j then c i else 0) := by
    by_cases h : i.val < j.val
    · have hne : i ≠ j := fun hh => by subst i; omega
      simp [h, hne, show i.val < j.val + 1 by omega]
    · by_cases he : i = j
      · subst i; simp
      · have hn : ¬i.val < j.val + 1 := by
          intro hh
          exact he (Fin.ext (by omega))
        simp [h, he, hn]
  simp only [prefixSum, Fin.val_succ, Fin.val_castSucc, hi, Finset.sum_add_distrib]
  simp

end WireAlgebra

namespace ComparisonSchemas
variable {r : ℕ} {P E : Type} (S : ComparisonSchemas r P E)

abbrev Address (_S : ComparisonSchemas r P E) :=
  Fin r → {a : Bool // a ∈ (Finset.univ : Finset Bool)}
abbrev DomainAddress (e : E) := (i : Fin r) → {a // a ∈ S.domain e i}

def sourceAddress (e : E) (a : S.DomainAddress e) : S.Address :=
  fun i => ⟨(a i).val, Finset.mem_univ _⟩
def targetAddress (e : E) (a : S.DomainAddress e) : S.Address :=
  fun i => ⟨S.mapping e i (a i), Finset.mem_univ _⟩

def firstShift (n : ℕ) (beta : (S.layout n).Block → Bit) (e : E)
    (a : S.DomainAddress e) : Bit := (S.layout n).linkShift beta (.inl e) a

def middleShift (n : ℕ) (beta : (S.layout n).Block → Bit) (e : E) (j : Fin n)
    (a : S.DomainAddress e) : Bit := (S.layout n).linkShift beta (.inr (.inl (e, j))) a

def lastShift (n : ℕ) (beta : (S.layout n).Block → Bit) (e : E)
    (a : S.DomainAddress e) : Bit := (S.layout n).linkShift beta (.inr (.inr e)) a

def wireShift (n : ℕ) (beta : (S.layout n).Block → Bit) (e : E)
    (a : S.DomainAddress e) : Bit :=
  S.firstShift n beta e a + (∑ j, S.middleShift n beta e j a) + S.lastShift n beta e a

end ComparisonSchemas

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.StableColors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

/-- Stable joint colors, transported to actual finite vertex types. -/
def SimpleStable {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) {k : ℕ}
    (v : Fin k → V) (w : Fin k → W) : Prop :=
  StableTuple (G := graphOfSimple G) (H := graphOfSimple H) k
    (fun i => Fintype.equivFin V (v i)) (fun i => Fintype.equivFin W (w i))

namespace SimpleStable
variable {V W : Type} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]
    {k : ℕ} {v : Fin k → V} {w : Fin k → W}

theorem local_info (hk : 2 ≤ k) (h : SimpleStable G H v w) :
    (∀ i j, v i = v j ↔ w i = w j) ∧
    (∀ i j, G.Adj (v i) (v j) ↔ H.Adj (w i) (w j)) ∧
    (∀ i, G.degree (v i) = H.degree (w i)) := by
  obtain ⟨he, ha, hd⟩ := round_one_local hk (h 1)
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    constructor
    · intro hh
      exact (Fintype.equivFin W).injective ((he i j).mp (congrArg (Fintype.equivFin V) hh))
    · intro hh
      exact (Fintype.equivFin V).injective ((he i j).mpr (congrArg (Fintype.equivFin W) hh))
  · intro i j
    simpa only [graphOfSimple_edge, decide_eq_decide] using ha i j
  · intro i
    simpa only [graphOfSimple_degree] using hd i

theorem extension (hk : 2 ≤ k) (h : SimpleStable G H v w) :
    ∃ e : V ≃ W,
      (∀ z i, SimpleStable G H (Function.update v i z) (Function.update w i (e z))) ∧
      (∀ i, e (v i) = w i) ∧
      (∀ z i, G.Adj (v i) z ↔ H.Adj (w i) (e z)) ∧
      (∀ z, G.degree z = H.degree (e z)) := by
  classical
  obtain ⟨f, hf, hfix, ha, hd⟩ := stableTuple_extension_local hk h
  change Fin (Fintype.card V) ≃ Fin (Fintype.card W) at f
  let e := (Fintype.equivFin V).trans (f.trans (Fintype.equivFin W).symm)
  have he (z : V) : Fintype.equivFin W (e z) = f (Fintype.equivFin V z) := by
    exact (Fintype.equivFin W).apply_symm_apply (f (Fintype.equivFin V z))
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · intro z i
    have h1 : (fun j => Fintype.equivFin V (Function.update v i z j)) =
        Function.update (fun j => Fintype.equivFin V (v j)) i (Fintype.equivFin V z) := by
      funext j; by_cases hj : j = i <;> simp [hj]
    have h2 : (fun j => Fintype.equivFin W (Function.update w i (e z) j)) =
        Function.update (fun j => Fintype.equivFin W (w j)) i (f (Fintype.equivFin V z)) := by
      funext j; by_cases hj : j = i <;> simp [hj, he]
    dsimp only [SimpleStable]
    rw [h1, h2]
    exact hf _ _
  · intro i
    apply (Fintype.equivFin W).injective
    exact (he (v i)).trans (hfix i)
  · intro z i
    have hh := (ha (Fintype.equivFin V z) i).trans
      (congrArg ((graphOfSimple H).edge (Fintype.equivFin W (w i))) (he z).symm)
    simpa only [graphOfSimple_edge, decide_eq_decide] using hh
  · intro z
    have hh := (hd (Fintype.equivFin V z)).trans
      (congrArg (degree (graphOfSimple H)) (he z).symm)
    simpa only [graphOfSimple_degree] using hh

end SimpleStable

/-- Testing degree intervals converts stable uncolored tuples back into their
named base classes, without assuming color information as a new WL hypothesis. -/
def TagStable {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (color : V → ℕ) (color' : W → ℕ)
    {k : ℕ} (v : Fin k → V) (w : Fin k → W) : Prop :=
  SimpleStable (withLeaves G (tagSize color)) (withLeaves H (tagSize color'))
    (fun i => .inl (v i)) (fun i => .inl (w i))

namespace TagStable
variable {V W : Type} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]
    {color : V → ℕ} {color' : W → ℕ} {k : ℕ} {v : Fin k → V} {w : Fin k → W}

theorem colors (hk : 2 ≤ k) (hN : Fintype.card V = Fintype.card W)
    (h : TagStable G H color color' v w) (i : Fin k) : color (v i) = color' (w i) := by
  have hd := (SimpleStable.local_info hk h).2.2 i
  have hh := congrArg (fun n => n / (Fintype.card V + 1)) hd
  rw [tag_degree_color, hN, tag_degree_color] at hh
  exact hh

omit [DecidableRel H.Adj] in
theorem exists_of_equivalent (hk : 2 ≤ k) (hc : ∀ v, 0 < color v)
    (h : Equivalent k (taggedGraph G color) (taggedGraph H color')) (v : Fin k → V) :
    ∃ w : Fin k → W, TagStable G H color color' v w := by
  classical
  obtain ⟨f, hf⟩ := stableTuple_exists (by omega : k ≠ 1) h
    (fun i => Fintype.equivFin (LeafVertex (tagSize color)) (.inl (v i)))
  let w' (i : Fin k) := (Fintype.equivFin (LeafVertex (tagSize color'))).symm (f i)
  have hw : SimpleStable (withLeaves G (tagSize color)) (withLeaves H (tagSize color'))
      (fun i => .inl (v i)) w' := by
    dsimp only [SimpleStable, w']
    convert hf using 1
    apply Iff.of_eq
    congr 1
    funext i
    exact (Fintype.equivFin (LeafVertex (tagSize color'))).apply_symm_apply (f i)
  have hd := (SimpleStable.local_info hk hw).2.2
  have hb (i : Fin k) : ∃ x : W, w' i = .inl x := by
    cases hwi : w' i with
    | inl x => exact ⟨x, rfl⟩
    | inr p =>
      have hh := hd i
      rw [hwi, withLeaves_leaf_degree] at hh
      have := tag_base_degree_gt_one G color hc (v i)
      omega
  choose w hw' using hb
  refine ⟨w, ?_⟩
  have hh : w' = fun i => .inl (w i) := funext hw'
  rw [hh] at hw
  exact hw

theorem extension (hk : 2 ≤ k) (hc : ∀ v, 0 < color v)
    (hN : Fintype.card V = Fintype.card W) (h : TagStable G H color color' v w) :
    ∃ e : V → W,
      (∀ z i, TagStable G H color color' (Function.update v i z) (Function.update w i (e z))) ∧
      (∀ z, color z = color' (e z)) ∧
      (∀ z i, G.Adj (v i) z ↔ H.Adj (w i) (e z)) := by
  classical
  obtain ⟨f, hf, _, ha, hd⟩ := SimpleStable.extension hk h
  have hb (z : V) : ∃ x : W, f (.inl z) = .inl x := by
    cases hz : f (.inl z) with
    | inl x => exact ⟨x, rfl⟩
    | inr p =>
      have hh := hd (.inl z)
      rw [hz, withLeaves_leaf_degree] at hh
      have := tag_base_degree_gt_one G color hc z
      omega
  choose e he using hb
  refine ⟨e, ?_, ?_, ?_⟩
  · intro z i
    have hh := hf (.inl z) i
    rw [he] at hh
    have h1 : Function.update (fun j => Sum.inl (v j) : Fin k → LeafVertex (tagSize color)) i (.inl z) =
        fun j => .inl (Function.update v i z j) := by
      funext j; by_cases hj : j = i <;> simp [hj]
    have h2 : Function.update (fun j => Sum.inl (w j) : Fin k → LeafVertex (tagSize color')) i (.inl (e z)) =
        fun j => .inl (Function.update w i (e z) j) := by
      funext j; by_cases hj : j = i <;> simp [hj]
    rw [h1, h2] at hh
    exact hh
  · intro z
    have hh := hd (.inl z)
    rw [he] at hh
    have hh' := congrArg (fun n => n / (Fintype.card V + 1)) hh
    rw [tag_degree_color, hN, tag_degree_color] at hh'
    exact hh'
  · intro z i
    have hh := ha (.inl z) i
    rw [he] at hh
    exact hh

end TagStable

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.LinearExtensions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace AffineBlocks
variable {C B : Type} [Fintype C] [DecidableEq C] [Fintype B] (D : AffineBlocks C B)

abbrev Response (beta : B → Bit) := Σ b, {v // D.Legal beta b v}

def zeroVertex (b : B) : D.Vertex 0 := .inr ⟨b, 0, D.legal_zero b⟩

def BlockWinning {k : ℕ} {beta : B → Bit} (p : Fin k → D.Response beta) : Prop :=
  TagStable (D.baseGraph 0) (D.baseGraph beta) D.colorNat D.colorNat
    (fun i => D.zeroVertex (p i).1) (fun i => .inr (p i))

/-- Stable block responses agree on every shared bit. The probe retains all
current responses and asks one zero bit through the stable extension bijection. -/
theorem blockWinning_consistent {k : ℕ} (hk : 2 ≤ k) {beta : B → Bit}
    {p : Fin k → D.Response beta} (hp : D.BlockWinning p) (i j : Fin k)
    (c : C) (hi : c ∈ D.coordinates (p i).1) (hj : c ∈ D.coordinates (p j).1) :
    (p i).2.val ⟨c, hi⟩ = (p j).2.val ⟨c, hj⟩ := by
  obtain ⟨e, _, hc, ha⟩ := TagStable.extension hk D.colorNat_pos (D.vertex_card 0 beta) hp
  have he := (D.colorNat_eq_iff (.inl (c, 0)) (e (.inl (c, 0)))).mp (hc (.inl (c, 0)))
  obtain ⟨a, heq⟩ := D.exists_bit_of_color (e (.inl (c, 0))) c he.symm
  have h1 := (ha (.inl (c, 0)) i).mp (by exact ⟨hi, rfl⟩)
  have h2 := (ha (.inl (c, 0)) j).mp (by exact ⟨hj, rfl⟩)
  rw [heq] at h1 h2
  obtain ⟨_, h1⟩ := h1
  obtain ⟨_, h2⟩ := h2
  exact h1.trans h2.symm

theorem blockWinning_exists {k : ℕ} (hk : 2 ≤ k) {beta : B → Bit}
    (h : Equivalent k (D.graph 0) (D.graph beta)) (b : Fin k → B) :
    ∃ p : Fin k → D.Response beta, D.BlockWinning p ∧ ∀ i, (p i).1 = b i := by
  classical
  obtain ⟨w, hw⟩ := TagStable.exists_of_equivalent hk D.colorNat_pos h (fun i => D.zeroVertex (b i))
  have hc (i : Fin k) : D.colorName (w i) = .inr (b i) := by
    exact ((D.colorNat_eq_iff _ _).mp (TagStable.colors hk (D.vertex_card 0 beta) hw i)).symm
  choose q hq using fun i => D.exists_valuation_of_color (w i) (b i) (hc i)
  refine ⟨fun i => ⟨b i, q i⟩, ?_, fun _ => rfl⟩
  have hh : w = fun i => .inr ⟨b i, q i⟩ := funext hq
  rw [hh] at hw
  exact hw

/-- One response extends simultaneously in every replacement slot, and agrees
with all old responses, even the one to be discarded. This is the literal
place-before-discard property needed for ring transfers. -/
theorem blockWinning_extend {k : ℕ} (hk : 2 ≤ k) {beta : B → Bit}
    {p : Fin k → D.Response beta} (hp : D.BlockWinning p) (b : B) :
    ∃ q : {v // D.Legal beta b v},
      (∀ i, D.BlockWinning (Function.update p i ⟨b, q⟩)) ∧
      (∀ i c (hi : c ∈ D.coordinates (p i).1) (hb : c ∈ D.coordinates b),
        (p i).2.val ⟨c, hi⟩ = q.val ⟨c, hb⟩) := by
  classical
  obtain ⟨e, he, hc, _⟩ := TagStable.extension hk D.colorNat_pos (D.vertex_card 0 beta) hp
  have hn := ((D.colorNat_eq_iff _ _).mp (hc (D.zeroVertex b))).symm
  obtain ⟨q, hq⟩ := D.exists_valuation_of_color (e (D.zeroVertex b)) b hn
  have hh (i : Fin k) : D.BlockWinning (Function.update p i ⟨b, q⟩) := by
    have ht := he (D.zeroVertex b) i
    rw [hq] at ht
    have h1 : Function.update (fun j => D.zeroVertex (p j).1) i (D.zeroVertex b) =
        fun j => D.zeroVertex (Function.update p i ⟨b, q⟩ j).1 := by
      funext j; by_cases hji : j = i <;> simp [hji]
    have h2 : Function.update (fun j => Sum.inr (p j) : Fin k → D.Vertex beta) i (.inr ⟨b, q⟩) =
        fun j => .inr (Function.update p i ⟨b, q⟩ j) := by
      funext j; by_cases hji : j = i <;> simp [hji]
    rw [h1, h2] at ht
    exact ht
  refine ⟨q, hh, ?_⟩
  intro i c hi hb
  have hj : ∃ j : Fin k, i ≠ j := by
    let a : Fin k := ⟨0, by omega⟩
    let b : Fin k := ⟨1, by omega⟩
    by_cases hia : i = a
    · refine ⟨b, ?_⟩
      intro h
      have := congrArg Fin.val (hia.symm.trans h)
      simp [a, b] at this
    · exact ⟨a, hia⟩
  obtain ⟨j, hij⟩ := hj
  have hcons := D.blockWinning_consistent hk (hh j) i j
  rw [Function.update_of_ne hij, Function.update_self] at hcons
  exact hcons c hi hb

end AffineBlocks

namespace AffineBlocks
variable {C B : Type} [Fintype C] [DecidableEq C] [Fintype B] (D : AffineBlocks C B)

noncomputable def responseValue {beta : B → Bit} (p : D.Response beta) (c : C) : Bit :=
  if h : c ∈ D.coordinates p.1 then p.2.val ⟨c, h⟩ else 0

omit [Fintype B] in
theorem responseValue_of_mem {beta : B → Bit} (p : D.Response beta) (c : C)
    (hc : c ∈ D.coordinates p.1) : D.responseValue p c = p.2.val ⟨c, hc⟩ := by
  simp only [responseValue, dite_eq_left hc]

def Agree {beta : B → Bit} (p q : D.Response beta) : Prop :=
  ∀ c, c ∈ D.coordinates p.1 → c ∈ D.coordinates q.1 →
    D.responseValue p c = D.responseValue q c

omit [Fintype B] in
theorem agree_symm {beta : B → Bit} {p q : D.Response beta} (h : D.Agree p q) : D.Agree q p :=
  fun c hq hp => (h c hp hq).symm

theorem blockWinning_agree {beta : B → Bit} {k : ℕ} (hk : 2 ≤ k)
    {p : Fin k → D.Response beta} (hp : D.BlockWinning p) (i j : Fin k) : D.Agree (p i) (p j) := by
  intro c hi hj
  rw [D.responseValue_of_mem _ _ hi, D.responseValue_of_mem _ _ hj]
  exact D.blockWinning_consistent hk hp i j c hi hj

/-- Sequentially transfer every slot to its prescribed next block. For every
row the shared-coordinate values of its old block are retained. -/
theorem blockWinning_transfer {beta : B → Bit} {k : ℕ} (hk : 2 ≤ k)
    {p : Fin k → D.Response beta} (hp : D.BlockWinning p) (b : Fin k → B) :
    ∃ q : Fin k → D.Response beta, D.BlockWinning q ∧
      (∀ i, (q i).1 = b i) ∧ (∀ i, D.Agree (p i) (q i)) := by
  classical
  have h (U : Finset (Fin k)) : ∃ q : Fin k → D.Response beta, D.BlockWinning q ∧
      (∀ i ∈ U, (q i).1 = b i ∧ D.Agree (p i) (q i)) ∧
      (∀ i ∉ U, q i = p i) := by
    induction U using Finset.induction_on with
    | empty => exact ⟨p, hp, by simp, fun _ _ => rfl⟩
    | @insert i U hi ih =>
      obtain ⟨q, hq, hdone, hold⟩ := ih
      obtain ⟨v, hv, ha⟩ := D.blockWinning_extend hk hq (b i)
      refine ⟨Function.update q i ⟨b i, v⟩, hv i, ?_, ?_⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with hji | hj
        · subst j
          refine ⟨by simp, ?_⟩
          simp only [Function.update_self]
          intro c hc hc'
          have hh := ha i
          rw [hold i hi] at hh
          rw [D.responseValue_of_mem _ _ hc, D.responseValue_of_mem _ _ hc']
          exact hh c hc hc'
        · have hji : j ≠ i := fun h => hi (h ▸ hj)
          simpa only [Function.update_of_ne hji] using hdone j hj
      · intro j hj
        have hji : j ≠ i := fun h => hj (h ▸ Finset.mem_insert_self _ _)
        rw [Function.update_of_ne hji]
        exact hold j (fun h => hj (Finset.mem_insert_of_mem h))
  obtain ⟨q, hq, hd, _⟩ := h Finset.univ
  exact ⟨q, hq, fun i => (hd i (Finset.mem_univ _)).1,
    fun i => (hd i (Finset.mem_univ _)).2⟩

end AffineBlocks

namespace AffineBlocks
variable {C B : Type} [Fintype C] [DecidableEq C] [Fintype B] (D : AffineBlocks C B)

omit [Fintype B] in
theorem response_legal {beta : B → Bit} (p : D.Response beta) :
    D.Legal beta p.1 (D.restrict p.1 (D.responseValue p)) := by
  have hh : D.restrict p.1 (D.responseValue p) = p.2.val := by
    funext c
    exact D.responseValue_of_mem p c.val c.property
  rw [hh]
  exact p.2.property

end AffineBlocks

namespace RingLayout
variable {r : ℕ} {T L : Type} [Fintype T] [Fintype L] (R : RingLayout r T L)

abbrev siteRing (t : T) (a : R.Address t) (i : Fin r) : R.HName :=
  ⟨t, i, a i, a (finRotate r i)⟩
abbrev squareRing (e : L) (a : R.MatchAddress e) (i : Fin r) : R.Square :=
  ⟨e, i, a i, a (finRotate r i)⟩

noncomputable def responseRingSum (hr : 2 ≤ r) {beta : R.Block → Bit}
    (p : Fin r → (R.affine hr).Response beta) (t : T) (a : R.Address t) :
    Fin (R.dimension t) → Bit :=
  ∑ i, R.horizontal ((R.affine hr).responseValue (p i)) (R.siteRing t a i)

theorem horizontal_agree (hr : 2 ≤ r) {beta : R.Block → Bit}
    {p q : (R.affine hr).Response beta} (ha : (R.affine hr).Agree p q)
    (h : R.HName)
    (hp : ∀ j, Sum.inl ⟨h, j⟩ ∈ R.coordinates p.1)
    (hq : ∀ j, Sum.inl ⟨h, j⟩ ∈ R.coordinates q.1) :
    R.horizontal ((R.affine hr).responseValue p) h =
      R.horizontal ((R.affine hr).responseValue q) h := by
  funext j
  exact ha _ (hp j) (hq j)

/-- The actual responses of a square ring obey its summed equation. Verticals
cancel because adjacent stable marked squares agree on their shared bit. -/
theorem square_ring_sum (hr : 2 ≤ r) {beta : R.Block → Bit}
    {q : Fin r → (R.affine hr).Response beta} (hq : (R.affine hr).BlockWinning q)
    (e : L) (a : R.MatchAddress e)
    (hn : ∀ i, (q i).1 = .inr (R.squareRing e a i)) :
    R.firstForm e (∑ i, R.horizontal ((R.affine hr).responseValue (q i)) (R.leftH (R.squareRing e a i))) +
      R.secondForm e (∑ i, R.horizontal ((R.affine hr).responseValue (q i)) (R.rightH (R.squareRing e a i))) =
      R.linkShift beta e a := by
  classical
  let z (i : Fin r) := (R.affine hr).responseValue (q i)
  have hsq (i : Fin r) :
      R.firstForm e (R.horizontal (z i) (R.leftH (R.squareRing e a i))) +
      R.secondForm e (R.horizontal (z i) (R.rightH (R.squareRing e a i))) +
      R.vertical (z i) (R.topV (R.squareRing e a i)) +
      R.vertical (z i) (R.bottomV (R.squareRing e a i)) = beta (.inr (R.squareRing e a i)) := by
    have hh := (R.affine hr).response_legal (q i)
    rw [hn i] at hh
    exact hh rfl
  have hv (i : Fin r) : R.vertical (z i) (R.bottomV (R.squareRing e a i)) =
      R.vertical (z (finRotate r i)) (R.topV (R.squareRing e a (finRotate r i))) := by
    apply (R.affine hr).blockWinning_agree hr hq i (finRotate r i)
    · rw [hn i]
      exact R.bottom_mem _
    · rw [hn (finRotate r i)]
      exact R.top_mem _
  have hs := congrArg (fun f : Fin r → Bit => ∑ i, f i) (funext hsq)
  simp only [Finset.sum_add_distrib] at hs
  have hb : (∑ i, R.vertical (z i) (R.bottomV (R.squareRing e a i))) =
      ∑ i, R.vertical (z i) (R.topV (R.squareRing e a i)) := by
    simp_rw [hv]
    exact Equiv.sum_comp (finRotate r) (fun i : Fin r => R.vertical (z i) (R.topV (R.squareRing e a i)))
  rw [hb] at hs
  dsimp only [horizontal, leftH, rightH, squareRing] at hs ⊢
  rw [map_sum, map_sum]
  simpa only [z, add_assoc, CharTwo.add_self_eq_zero, add_zero, linkShift] using hs

/-- Site-ring images are defined by all stable responses, not by a selected
memoryless strategy or by a simultaneous choice of endpoint vectors. -/
def ImageSet (hr : 2 ≤ r) (beta : R.Block → Bit) (t : T) (a : R.Address t) :
    Set (Fin (R.dimension t) → Bit) :=
  {x | ∃ p : Fin r → (R.affine hr).Response beta,
    (R.affine hr).BlockWinning p ∧
    (∀ i, (p i).1 = .inl (R.siteRing t a i)) ∧ R.responseRingSum hr p t a = x}

theorem imageSet_nonempty (hr : 2 ≤ r) {beta : R.Block → Bit}
    (h : Equivalent r ((R.affine hr).graph 0) ((R.affine hr).graph beta)) (t : T) (a : R.Address t) :
    (R.ImageSet hr beta t a).Nonempty := by
  obtain ⟨p, hp, hn⟩ := (R.affine hr).blockWinning_exists hr h (fun i => .inl (R.siteRing t a i))
  exact ⟨_, p, hp, hn, rfl⟩

end RingLayout

namespace RingLayout
variable {r : ℕ} {T L : Type} [Fintype T] [Fintype L] (R : RingLayout r T L)

theorem transfer_left_sums (hr : 2 ≤ r) {beta : R.Block → Bit}
    {p q : Fin r → (R.affine hr).Response beta} (e : L) (a : R.MatchAddress e)
    (hp : ∀ i, (p i).1 = .inl (R.siteRing (R.first e) (R.leftAddress e a) i))
    (hq : ∀ i, (q i).1 = .inr (R.squareRing e a i))
    (ha : ∀ i, (R.affine hr).Agree (p i) (q i)) :
    R.responseRingSum hr p (R.first e) (R.leftAddress e a) =
      ∑ i, R.horizontal ((R.affine hr).responseValue (q i)) (R.leftH (R.squareRing e a i)) := by
  apply Finset.sum_congr rfl
  intro i _
  apply R.horizontal_agree hr (ha i)
  · intro j
    rw [hp i]
    exact R.hCoord_mem _ j
  · intro j
    rw [hq i]
    exact R.left_mem (R.squareRing e a i) j

theorem transfer_right_sums (hr : 2 ≤ r) {beta : R.Block → Bit}
    {p q : Fin r → (R.affine hr).Response beta} (e : L) (a : R.MatchAddress e)
    (hp : ∀ i, (p i).1 = .inl (R.siteRing (R.second e) (R.rightAddress e a) i))
    (hq : ∀ i, (q i).1 = .inr (R.squareRing e a i))
    (ha : ∀ i, (R.affine hr).Agree (p i) (q i)) :
    R.responseRingSum hr p (R.second e) (R.rightAddress e a) =
      ∑ i, R.horizontal ((R.affine hr).responseValue (q i)) (R.rightH (R.squareRing e a i)) := by
  apply Finset.sum_congr rfl
  intro i _
  apply R.horizontal_agree hr (ha i)
  · intro j
    rw [hp i]
    exact R.hCoord_mem _ j
  · intro j
    rw [hq i]
    exact R.right_mem (R.squareRing e a i) j

theorem imageSet_left_support (hr : 2 ≤ r) {beta : R.Block → Bit}
    (e : L) (a : R.MatchAddress e) {x : Fin (R.dimension (R.first e)) → Bit}
    (hx : x ∈ R.ImageSet hr beta (R.first e) (R.leftAddress e a)) :
    ∃ y ∈ R.ImageSet hr beta (R.second e) (R.rightAddress e a),
      R.firstForm e x + R.secondForm e y = R.linkShift beta e a := by
  classical
  obtain ⟨p, hp, hpn, hpx⟩ := hx
  obtain ⟨q, hq, hqn, hqa⟩ := (R.affine hr).blockWinning_transfer hr hp
    (fun i => .inr (R.squareRing e a i))
  obtain ⟨s, hs, hsn, hsa⟩ := (R.affine hr).blockWinning_transfer hr hq
    (fun i => .inl (R.siteRing (R.second e) (R.rightAddress e a) i))
  refine ⟨_, ⟨s, hs, hsn, rfl⟩, ?_⟩
  rw [← hpx, R.transfer_left_sums hr e a hpn hqn hqa,
    R.transfer_right_sums hr e a hsn hqn (fun i => (R.affine hr).agree_symm (hsa i))]
  exact R.square_ring_sum hr hq e a hqn

theorem imageSet_right_support (hr : 2 ≤ r) {beta : R.Block → Bit}
    (e : L) (a : R.MatchAddress e) {y : Fin (R.dimension (R.second e)) → Bit}
    (hy : y ∈ R.ImageSet hr beta (R.second e) (R.rightAddress e a)) :
    ∃ x ∈ R.ImageSet hr beta (R.first e) (R.leftAddress e a),
      R.firstForm e x + R.secondForm e y = R.linkShift beta e a := by
  classical
  obtain ⟨p, hp, hpn, hpy⟩ := hy
  obtain ⟨q, hq, hqn, hqa⟩ := (R.affine hr).blockWinning_transfer hr hp
    (fun i => .inr (R.squareRing e a i))
  obtain ⟨s, hs, hsn, hsa⟩ := (R.affine hr).blockWinning_transfer hr hq
    (fun i => .inl (R.siteRing (R.first e) (R.leftAddress e a) i))
  refine ⟨_, ⟨s, hs, hsn, rfl⟩, ?_⟩
  rw [← hpy, R.transfer_right_sums hr e a hpn hqn hqa,
    R.transfer_left_sums hr e a hsn hqn (fun i => (R.affine hr).agree_symm (hsa i))]
  exact R.square_ring_sum hr hq e a hqn

end RingLayout

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.LocalImages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

/-- Characteristic-two rearrangement, stated without an arithmetic oracle. -/
theorem bit_eq_add_of_add_eq {x y z : Bit} (h : x + y = z) : x = z + y := by
  calc
    x = x + (y + y) := by rw [CharTwo.add_self_eq_zero, add_zero]
    _ = z + y := by rw [← add_assoc, h]

namespace RingLayout
variable {r : ℕ} {T L : Type} [Fintype T] [Fintype L] (R : RingLayout r T L)

/-- Image consistency for every link. Only scalar image sets are equated;
no common vector choice is silently imposed on distinct comparisons. -/
theorem imageSet_link (hr : 2 ≤ r) (beta : R.Block → Bit) (e : L) (a : R.MatchAddress e) :
    (R.firstForm e) '' R.ImageSet hr beta (R.first e) (R.leftAddress e a) =
      (fun y => R.linkShift beta e a + R.secondForm e y) ''
        R.ImageSet hr beta (R.second e) (R.rightAddress e a) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy, he⟩ := R.imageSet_left_support hr e a hx
    exact ⟨y, hy, (bit_eq_add_of_add_eq he).symm⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx, he⟩ := R.imageSet_right_support hr e a hy
    exact ⟨x, hx, bit_eq_add_of_add_eq he⟩

end RingLayout

namespace WireAlgebra

def shiftSet (c : Bit) (X : Set Bit) : Set Bit := (fun x => c + x) '' X

@[simp]
theorem shiftSet_zero (X : Set Bit) : shiftSet 0 X = X := by
  simp [shiftSet]

@[simp]
theorem shiftSet_shiftSet (c d : Bit) (X : Set Bit) :
    shiftSet c (shiftSet d X) = shiftSet (c + d) X := by
  simp only [shiftSet, Set.image_image, add_assoc]

/-- Private internal scalar image sets telescope by translations. This does not
cancel Minkowski sums or select a common endpoint vector across comparisons. -/
theorem chain_sets {n : ℕ} (left right : Set Bit) (q : Fin (n + 1) → Set Bit)
    (first last : Bit) (middle : Fin n → Bit)
    (hfirst : left = shiftSet first (q 0))
    (hmiddle : ∀ i, q i.castSucc = shiftSet (middle i) (q i.succ))
    (hlast : q (Fin.last n) = shiftSet last right) :
    left = shiftSet (first + (∑ i, middle i) + last) right := by
  have hj (j : Fin (n + 1)) : left = shiftSet (first + prefixSum middle j) (q j) := by
    induction j using Fin.induction with
    | zero => simpa only [prefix_zero, add_zero] using hfirst
    | succ i ih =>
      rw [hmiddle i, shiftSet_shiftSet] at ih
      simpa only [prefix_succ, add_assoc] using ih
  have hh := hj (Fin.last n)
  rw [hlast, shiftSet_shiftSet, prefix_last] at hh
  exact hh

end WireAlgebra

namespace ComparisonSchemas
variable {r : ℕ} {P E : Type} [Fintype P] [Fintype E] (S : ComparisonSchemas r P E)

noncomputable def responseImages (hr : 2 ≤ r) (n : ℕ) (beta : (S.layout n).Block → Bit)
    (p : P) (a : S.Address) : Set (Fin (S.dimension p) → Bit) :=
  (S.layout n).ImageSet hr beta (.inl p) a

theorem image_consistency (hr : 32 ≤ r) (n : ℕ) (beta : (S.layout n).Block → Bit)
    (h : Equivalent r (((S.layout n).affine (by omega)).graph 0)
      (((S.layout n).affine (by omega)).graph beta)) :
    (∀ p a, (S.responseImages (by omega) n beta p a).Nonempty) ∧
    ∀ e (a : S.DomainAddress e),
      (S.left e) '' S.responseImages (by omega) n beta (S.source e) (S.sourceAddress e a) =
        (fun y => S.wireShift n beta e a + S.right e y) ''
          S.responseImages (by omega) n beta (S.target e) (S.targetAddress e a) := by
  have hr2 : 2 ≤ r := by omega
  constructor
  · intro p a
    exact (S.layout n).imageSet_nonempty hr2 h (.inl p) a
  · intro e a
    let q (j : Fin (n + 1)) : Set Bit :=
      (fun v : Fin 1 → Bit => v 0) '' (S.layout n).ImageSet hr2 beta (.inr (e, j)) a
    have hf : (S.left e) '' S.responseImages hr2 n beta (S.source e) (S.sourceAddress e a) =
        WireAlgebra.shiftSet (S.firstShift n beta e a) (q 0) := by
      have hh := (S.layout n).imageSet_link hr2 beta (.inl e) a
      change (S.left e) '' S.responseImages hr2 n beta (S.source e) (S.sourceAddress e a) =
        (fun v : Fin 1 → Bit => S.firstShift n beta e a + v 0) ''
          (S.layout n).ImageSet hr2 beta (.inr (e, 0)) a at hh
      exact hh.trans (Set.image_image _ _ _).symm
    have hm (j : Fin n) : q j.castSucc = WireAlgebra.shiftSet (S.middleShift n beta e j a) (q j.succ) := by
      have hh := (S.layout n).imageSet_link hr2 beta (.inr (.inl (e, j))) a
      change q j.castSucc =
        (fun v : Fin 1 → Bit => S.middleShift n beta e j a + v 0) ''
          (S.layout n).ImageSet hr2 beta (.inr (e, j.succ)) a at hh
      exact hh.trans (Set.image_image _ _ _).symm
    have hl : q (Fin.last n) = WireAlgebra.shiftSet (S.lastShift n beta e a)
        ((S.right e) '' S.responseImages hr2 n beta (S.target e) (S.targetAddress e a)) := by
      have hh := (S.layout n).imageSet_link hr2 beta (.inr (.inr e)) a
      change q (Fin.last n) =
        (fun v => S.lastShift n beta e a + S.right e v) ''
          S.responseImages hr2 n beta (S.target e) (S.targetAddress e a) at hh
      simpa only [WireAlgebra.shiftSet, Set.image_image] using hh
    simpa only [WireAlgebra.shiftSet, Set.image_image, Function.comp_def, wireShift] using
      WireAlgebra.chain_sets _ _ q _ _ _ hf hm hl

end ComparisonSchemas

namespace Marker
variable {V : Type} {G : SimpleGraph V}

def walkSum (m : V → V → Bit) {u v : V} : G.Walk u v → Bit
  | .nil => 0
  | .cons (u := u) (v := v) _ p => m u v + walkSum m p

@[simp] theorem walkSum_nil (m : V → V → Bit) (u : V) :
    walkSum m (.nil : G.Walk u u) = 0 := rfl

@[simp] theorem walkSum_cons (m : V → V → Bit) {u v w : V} (h : G.Adj u v)
    (p : G.Walk v w) : walkSum m (.cons h p) = m u v + walkSum m p := rfl

@[simp] theorem walkSum_append (m : V → V → Bit) {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) :
    walkSum m (p.append q) = walkSum m p + walkSum m q := by
  induction p with
  | nil => simp
  | cons h p ih => simp only [SimpleGraph.Walk.cons_append, walkSum_cons, ih, add_assoc]

@[simp] theorem walkSum_reverse (m : V → V → Bit)
    (hm : ∀ u v, G.Adj u v → m u v = m v u) {u v : V} (p : G.Walk u v) :
    walkSum m p.reverse = walkSum m p := by
  induction p with
  | nil => rfl
  | @cons u v w h p ih =>
    rw [SimpleGraph.Walk.reverse_cons, walkSum_append, walkSum_cons, walkSum_nil, ih,
      ← hm u v h, add_zero, add_comm, walkSum_cons]

theorem walkSum_cast_left (m : V → V → Bit) {u u' v : V}
    (h : u = u') (p : G.Walk u v) : walkSum m (h ▸ p) = walkSum m p := by
  subst u'
  rfl

/-- A nonwrapping marker is an exact coboundary. No finiteness or connectedness
assumption is needed; roots are chosen separately in actual graph components. -/
theorem exact_of_closed_zero (m : V → V → Bit)
    (hm : ∀ u v, G.Adj u v → m u v = m v u)
    (hc : ∀ u (p : G.Walk u u), walkSum m p = 0) :
    ∃ s : V → Bit, ∀ u v, G.Adj u v → m u v = s u + s v := by
  classical
  let root (v : V) : V := (G.connectedComponentMk v).out
  have hr (v : V) : G.Reachable (root v) v := @Quotient.mk_out V G.reachableSetoid v
  let path (v : V) : G.Walk (root v) v := (hr v).some
  refine ⟨fun v => walkSum m (path v), ?_⟩
  intro u v huv
  have he : root u = root v := congrArg (fun c : G.ConnectedComponent => c.out) (SimpleGraph.ConnectedComponent.sound huv.reachable)
  let q : G.Walk (root u) v := he.symm ▸ path v
  have hq : walkSum m q = walkSum m (path v) := by exact walkSum_cast_left m he.symm (path v)
  have hz := hc (root u) ((path u).append (huv.toWalk.append q.reverse))
  simp only [walkSum_append, walkSum_cons, walkSum_nil, add_zero,
    walkSum_reverse m hm, hq] at hz
  calc
    m u v = m u v + (walkSum m (path u) + (m u v + walkSum m (path v))) := by rw [hz, add_zero]
    _ = (m u v + m u v) + (walkSum m (path u) + walkSum m (path v)) := by abel
    _ = _ := by rw [CharTwo.add_self_eq_zero, zero_add]

/-- Conversely, a potential cancels around every closed walk. -/
theorem walkSum_of_exact (s : V → Bit) (m : V → V → Bit)
    (hm : ∀ u v, G.Adj u v → m u v = s u + s v)
    {u v : V} (p : G.Walk u v) : walkSum m p = s u + s v := by
  induction p with
  | nil => rw [walkSum_nil, CharTwo.add_self_eq_zero]
  | @cons u v w h p ih =>
    rw [walkSum_cons, hm u v h, ih]
    calc
      _ = (s v + s v) + (s u + s w) := by abel
      _ = _ := by rw [CharTwo.add_self_eq_zero, zero_add]

@[simp] theorem walkSum_add (m n : V → V → Bit) {u v : V} (p : G.Walk u v) :
    walkSum (fun u v => m u v + n u v) p = walkSum m p + walkSum n p := by
  induction p with
  | nil => simp
  | cons h p ih => simp only [walkSum_cons, ih]; abel

@[simp] theorem walkSum_smul (a : Bit) (m : V → V → Bit) {u v : V} (p : G.Walk u v) :
    walkSum (fun u v => a * m u v) p = a * walkSum m p := by
  induction p with
  | nil => simp
  | cons h p ih => simp only [walkSum_cons, ih, mul_add]

def cut {r : ℕ} (j i : Fin r) : Bit := if j.val < i.val then 1 else 0

def delta {r : ℕ} (i : Fin r) : Bit := if i.val + 1 = r then 1 else 0

/-- Moving the marked row to any other cut changes the marker by a boundary
potential, including for singleton coordinate domains. -/
theorem cut_toggle {r : ℕ} (j i : Fin r) :
    cut j i + cut j (finRotate r i) = delta i + (if i = j then 1 else 0) := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ n =>
    dsimp only [cut, delta]
    rw [coe_finRotate]
    by_cases hl : i = Fin.last n
    · subst i
      by_cases hj : j = Fin.last n
      · subst j; simp [CharTwo.add_self_eq_zero]
      · have hj' : j.val < n := Fin.val_lt_last hj
        simp [hj', Ne.symm hj]
    · have hi : i.val + 1 ≠ n + 1 := by
        intro hh
        apply hl
        apply Fin.ext
        exact Nat.add_right_cancel hh
      rw [ite_eq_right hl, ite_eq_right hi]
      by_cases he : i = j
      · subst j; simp
      · have he' : i.val ≠ j.val := fun hh => he (Fin.ext hh)
        by_cases hlt : j.val < i.val
        · simp [he, hlt, show j.val < i.val + 1 by omega, CharTwo.add_self_eq_zero]
        · have hgt : ¬j.val < i.val + 1 := by omega
          simp [he, hlt, hgt]

/-- If one row is absent, the ring marker is a boundary potential. This is
valid on an arbitrary corner subgraph and uses no assumption on label factors. -/
theorem closed_zero_of_missing_row {r : ℕ} (row : V → Fin r) (j : Fin r)
    (m : V → V → Bit)
    (he : ∀ u v, G.Adj u v →
      (row u = row v ∧ m u v = 0) ∨
      ∃ i : Fin r, i ≠ j ∧ m u v = delta i ∧
        ((row u = i ∧ row v = finRotate r i) ∨
         (row v = i ∧ row u = finRotate r i))) :
    ∀ u (p : G.Walk u u), walkSum m p = 0 := by
  have hm : ∀ u v, G.Adj u v → m u v = cut j (row u) + cut j (row v) := by
    intro u v huv
    rcases he u v huv with ⟨hr, hm⟩ | ⟨i, hij, hm, hh⟩
    · rw [hm, hr, CharTwo.add_self_eq_zero]
    · have hi := cut_toggle j i
      rw [ite_eq_right hij, add_zero] at hi
      rcases hh with ⟨hu, hv⟩ | ⟨hv, hu⟩
      · rw [hu, hv, hm, hi]
      · rw [hu, hv, hm, add_comm, hi]
  intro u p
  rw [walkSum_of_exact (fun v => cut j (row v)) m hm p, CharTwo.add_self_eq_zero]

/-- The potential adjustment in the exact-projection argument, at a horizontal
readout. Vector coordinates are adjusted together, not independently chosen. -/
theorem horizontal_adjust {W : Type} [AddCommGroup W] [Module Bit W]
    (M N old new : W) (s t d : Bit) (hd : s + t = d) :
    (M + s • (new + old)) + (N + t • (new + old)) + d • new = M + N + d • old := by
  calc
    _ = M + N + ((s + t) • (new + old) + d • new) := by rw [add_smul]; abel
    _ = M + N + (d • (new + new) + d • old) := by rw [hd, smul_add, smul_add]; abel
    _ = _ := by
      have hz : new + new = 0 := by
        have hh : ((1 : Bit) + 1) • new = (0 : Bit) • new := by congr 1
        simpa only [add_smul, one_smul, zero_smul] using hh
      rw [hz, smul_zero, zero_add]

/-- Vertical readouts survive the same adjustment because the difference of
the two affine component shifts solves the homogeneous link equation. -/
theorem vertical_adjust {W X : Type} [AddCommGroup W] [AddCommGroup X]
    [Module Bit W] [Module Bit X] (L : W →ₗ[Bit] Bit) (R : X →ₗ[Bit] Bit)
    (M : W) (N : X) (g : W) (h : X) (s t : Bit)
    (hst : s = t) (he : L g + R h = 0) :
    L (M + s • g) + R (N + t • h) = L M + R N := by
  subst t
  rw [map_add, map_add, map_smul, map_smul]
  calc
    _ = L M + R N + s * (L g + R h) := by simp only [smul_eq_mul]; ring
    _ = _ := by rw [he, mul_zero, add_zero]

end Marker

namespace RingLayout
variable {r : ℕ} {T L : Type} (R : RingLayout r T L)

abbrev Corner := Σ t : T, Σ i : Fin r, R.Label t i
abbrev Name := R.HName ⊕ R.VName

noncomputable instance nameDecidableEq : DecidableEq R.Name := Classical.decEq _

def nameFirst : R.Name → R.Corner
  | .inl h => ⟨h.1, h.2.1, h.2.2.1⟩
  | .inr v => ⟨R.first v.1, v.2.1, R.firstLabel v.1 v.2.1 v.2.2⟩

def nameSecond : R.Name → R.Corner
  | .inl h => ⟨h.1, finRotate r h.2.1, h.2.2.2⟩
  | .inr v => ⟨R.second v.1, v.2.1, R.secondLabel v.1 v.2.1 v.2.2⟩

theorem name_endpoints_ne (hr : 2 ≤ r) (n : R.Name) : R.nameFirst n ≠ R.nameSecond n := by
  intro h
  cases n with
  | inl n =>
    exact CycleRows.rotate_ne_self hr n.2.1
      (congrArg (fun c : R.Corner => c.2.1) h).symm
  | inr n => exact R.endpoints_ne n.1 (congrArg Sigma.fst h)

noncomputable def blockNames : R.Block → Finset R.Name
  | .inl h => {Sum.inl h}
  | .inr b => {Sum.inl (R.leftH b), Sum.inl (R.rightH b), Sum.inr (R.topV b), Sum.inr (R.bottomV b)}

noncomputable def names (U : Finset R.Block) : Finset R.Name := by
  classical
  exact U.biUnion R.blockNames

def blockRow : R.Block → Fin r
  | .inl h => h.2.1
  | .inr b => b.2.1

/-- Shared names give a single edge. Vector bit coordinates are not counted as
separate horizontal edges in the corner graph. -/
noncomputable def cornerGraph (hr : 2 ≤ r) (U : Finset R.Block) : SimpleGraph R.Corner where
  Adj u v := ∃ n ∈ R.names U,
    (R.nameFirst n = u ∧ R.nameSecond n = v) ∨ (R.nameFirst n = v ∧ R.nameSecond n = u)
  symm := ⟨by
    intro u v
    rintro ⟨n, hn, h⟩
    exact ⟨n, hn, h.symm⟩⟩
  loopless := ⟨by
    intro u
    rintro ⟨n, _, h⟩
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact R.name_endpoints_ne hr n (h1.trans h2.symm)⟩

def cornerMarker (u v : R.Corner) : Bit :=
  if u.2.1 = v.2.1 then 0 else
    if v.2.1 = finRotate r u.2.1 then Marker.delta u.2.1 else Marker.delta v.2.1

theorem cornerMarker_horizontal (hr : 3 ≤ r) (h : R.HName) :
    R.cornerMarker (R.nameFirst (.inl h)) (R.nameSecond (.inl h)) = Marker.delta h.2.1 ∧
    R.cornerMarker (R.nameSecond (.inl h)) (R.nameFirst (.inl h)) = Marker.delta h.2.1 := by
  have h1 := CycleRows.rotate_ne_self (show 2 ≤ r by omega) h.2.1
  have h2 := CycleRows.rotate_twice_ne_self hr h.2.1
  dsimp only [cornerMarker, nameFirst, nameSecond]
  constructor
  · rw [ite_eq_right (Ne.symm h1), ite_eq_left rfl]
  · rw [ite_eq_right h1, ite_eq_right (Ne.symm h2)]

theorem cornerMarker_vertical (v : R.VName) :
    R.cornerMarker (R.nameFirst (.inr v)) (R.nameSecond (.inr v)) = 0 ∧
    R.cornerMarker (R.nameSecond (.inr v)) (R.nameFirst (.inr v)) = 0 := by
  simp [cornerMarker, nameFirst, nameSecond]

theorem horizontal_row_mem {U : Finset R.Block} {h : R.HName}
    (hh : Sum.inl h ∈ R.names U) : h.2.1 ∈ U.image R.blockRow := by
  classical
  obtain ⟨b, hb, hm⟩ := Finset.mem_biUnion.mp hh
  refine Finset.mem_image.mpr ⟨b, hb, ?_⟩
  cases b with
  | inl b =>
    have he : h = b := Sum.inl.inj (Finset.mem_singleton.mp hm)
    subst h
    rfl
  | inr b =>
    simp only [blockNames, Finset.mem_insert, Finset.mem_singleton, Sum.inl.injEq,
      Sum.inl_ne_inr, or_false] at hm
    rcases hm with rfl | rfl <;> rfl

/-- Every horizontal edge in the support comes from a block in its own row;
vertical edges preserve the boundary index and have marker zero. -/
theorem cornerGraph_row_edge (hr : 3 ≤ r) {U : Finset R.Block} {u v : R.Corner}
    (h : (R.cornerGraph (by omega) U).Adj u v) :
    (u.2.1 = v.2.1 ∧ R.cornerMarker u v = 0) ∨
    ∃ i ∈ U.image R.blockRow, R.cornerMarker u v = Marker.delta i ∧
      ((u.2.1 = i ∧ v.2.1 = finRotate r i) ∨
       (v.2.1 = i ∧ u.2.1 = finRotate r i)) := by
  classical
  obtain ⟨n, hn, h⟩ := h
  cases n with
  | inl n =>
    refine Or.inr ⟨n.2.1, R.horizontal_row_mem hn, ?_⟩
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨(R.cornerMarker_horizontal hr n).1, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨(R.cornerMarker_horizontal hr n).2, Or.inr ⟨rfl, rfl⟩⟩
  | inr n =>
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, (R.cornerMarker_vertical n).1⟩
    · exact Or.inl ⟨rfl, (R.cornerMarker_vertical n).2⟩

def Wrapping (hr : 2 ≤ r) (U : Finset R.Block) : Prop :=
  ∃ (u : R.Corner) (p : (R.cornerGraph hr U).Walk u u), Marker.walkSum R.cornerMarker p = 1

/-- A closed walk of odd marker forces every row to be represented. -/
theorem wrapping_rows (hr : 3 ≤ r) {U : Finset R.Block}
    (h : R.Wrapping (by omega) U) (j : Fin r) : j ∈ U.image R.blockRow := by
  classical
  by_contra hj
  have hz := Marker.closed_zero_of_missing_row (G := R.cornerGraph (by omega) U)
    (fun c : R.Corner => c.2.1) j R.cornerMarker ?_
  · obtain ⟨u, p, hp⟩ := h
    have := hz u p
    rw [hp] at this
    exact one_ne_zero this
  · intro u v huv
    rcases R.cornerGraph_row_edge hr huv with hh | ⟨i, hi, hm, hh⟩
    · exact Or.inl hh
    · exact Or.inr ⟨i, fun he => hj (he ▸ hi), hm, hh⟩

/-- A wrapping family has at least one block per row. The count is blocks, not
readout names and not vertices; a square still supplies only one row. -/
theorem wrapping_card (hr : 3 ≤ r) {U : Finset R.Block}
    (h : R.Wrapping (by omega) U) : r ≤ U.card := by
  classical
  have hs : (Finset.univ : Finset (Fin r)) ⊆ U.image R.blockRow :=
    fun j _ => R.wrapping_rows hr h j
  have hc := Finset.card_le_card hs
  simpa only [Finset.card_univ, Fintype.card_fin] using hc.trans (Finset.card_image_le)

end RingLayout

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.ScalarExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace RingLayout
variable {r : ℕ} {T L : Type} (R : RingLayout r T L)

theorem wrapping_row_inj (hr : 3 ≤ r) {U : Finset R.Block}
    (h : R.Wrapping (by omega) U) (hu : U.card ≤ r) : Set.InjOn R.blockRow U := by
  classical
  apply Finset.card_image_iff.mp
  have he : U.image R.blockRow = Finset.univ := Finset.eq_univ_of_forall (R.wrapping_rows hr h)
  rw [he, Finset.card_univ, Fintype.card_fin]
  exact Nat.le_antisymm (R.wrapping_card hr h) hu

def blockRepresentative : R.Block → R.Corner
  | .inl h => R.nameFirst (.inl h)
  | .inr b => R.nameFirst (.inl (R.leftH b))

theorem name_present {U : Finset R.Block} {b : R.Block} (hb : b ∈ U)
    {n : R.Name} (hn : n ∈ R.blockNames b) : n ∈ R.names U := by
  classical
  exact Finset.mem_biUnion.mpr ⟨b, hb, hn⟩

theorem name_reachable (hr : 2 ≤ r) {U : Finset R.Block} {n : R.Name}
    (hn : n ∈ R.names U) :
    (R.cornerGraph hr U).Reachable (R.nameFirst n) (R.nameSecond n) :=
  SimpleGraph.Adj.reachable ⟨n, hn, Or.inl ⟨rfl, rfl⟩⟩

/-- Every name of a block belongs to the block's unique corner component. -/
theorem block_reachable (hr : 2 ≤ r) {U : Finset R.Block} {b : R.Block} (hb : b ∈ U)
    {n : R.Name} (hn : n ∈ R.blockNames b) :
    (R.cornerGraph hr U).Reachable (R.blockRepresentative b) (R.nameFirst n) ∧
    (R.cornerGraph hr U).Reachable (R.blockRepresentative b) (R.nameSecond n) := by
  classical
  cases b with
  | inl b =>
    have he : n = Sum.inl b := Finset.mem_singleton.mp hn
    subst n
    exact ⟨SimpleGraph.Reachable.refl _, R.name_reachable hr (R.name_present hb hn)⟩
  | inr b =>
    have hl := R.name_reachable hr (R.name_present hb
      (show Sum.inl (R.leftH b) ∈ R.blockNames (.inr b) by simp [blockNames]))
    have hr' := R.name_reachable hr (R.name_present hb
      (show Sum.inl (R.rightH b) ∈ R.blockNames (.inr b) by simp [blockNames]))
    have ht := R.name_reachable hr (R.name_present hb
      (show Sum.inr (R.topV b) ∈ R.blockNames (.inr b) by simp [blockNames]))
    have hb' := R.name_reachable hr (R.name_present hb
      (show Sum.inr (R.bottomV b) ∈ R.blockNames (.inr b) by simp [blockNames]))
    simp only [blockNames, Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl | rfl
    · exact ⟨SimpleGraph.Reachable.refl _, hl⟩
    · exact ⟨ht, ht.trans hr'⟩
    · exact ⟨SimpleGraph.Reachable.refl _, ht⟩
    · exact ⟨hl, hl.trans hb'⟩

noncomputable def componentBlocks (hr : 2 ≤ r) (U : Finset R.Block) (u : R.Corner) : Finset R.Block := by
  classical
  exact U.filter (fun b => (R.cornerGraph hr U).Reachable u (R.blockRepresentative b))

theorem componentBlocks_subset (hr : 2 ≤ r) (U : Finset R.Block) (u : R.Corner) :
    R.componentBlocks hr U u ⊆ U := by
  classical
  exact Finset.filter_subset _ _

theorem component_edge (hr : 2 ≤ r) {U : Finset R.Block} {root u v : R.Corner}
    (hu : (R.cornerGraph hr U).Reachable root u) (h : (R.cornerGraph hr U).Adj u v) :
    (R.cornerGraph hr (R.componentBlocks hr U root)).Adj u v := by
  classical
  obtain ⟨n, hn, h⟩ := h
  obtain ⟨b, hb, hbn⟩ := Finset.mem_biUnion.mp hn
  have hb' : b ∈ R.componentBlocks hr U root := by
    apply Finset.mem_filter.mpr
    refine ⟨hb, ?_⟩
    obtain ⟨hfirst, hsecond⟩ := R.block_reachable hr hb hbn
    rcases h with ⟨hf, _⟩ | ⟨_, hs⟩
    · exact hu.trans (hf ▸ hfirst).symm
    · exact hu.trans (hs ▸ hsecond).symm
  exact ⟨n, R.name_present hb' hbn, h⟩

theorem component_walk (hr : 2 ≤ r) {U : Finset R.Block} (root : R.Corner)
    {u v : R.Corner} (p : (R.cornerGraph hr U).Walk u v) :
    (R.cornerGraph hr U).Reachable root u →
    ∃ q : (R.cornerGraph hr (R.componentBlocks hr U root)).Walk u v,
      Marker.walkSum R.cornerMarker q = Marker.walkSum R.cornerMarker p := by
  induction p with
  | nil => exact fun _ => ⟨.nil, rfl⟩
  | cons h p ih =>
    intro hu
    obtain ⟨q, hq⟩ := ih (hu.trans h.reachable)
    exact ⟨.cons (R.component_edge hr hu h) q, congrArg (fun x => R.cornerMarker _ _ + x) hq⟩

/-- A wrapping collection of at most r blocks is entirely in the component of
its odd closed walk. This also rules out two independent old wrapping choices. -/
theorem wrapping_component (hr : 3 ≤ r) {U : Finset R.Block} (hu : U.card ≤ r)
    {u : R.Corner} (p : (R.cornerGraph (by omega) U).Walk u u)
    (hp : Marker.walkSum R.cornerMarker p = 1) :
    R.componentBlocks (by omega) U u = U := by
  obtain ⟨q, hq⟩ := R.component_walk (by omega) u p (SimpleGraph.Reachable.refl _)
  have hw : R.Wrapping (by omega) (R.componentBlocks (by omega) U u) := ⟨u, q, hq.trans hp⟩
  exact Finset.eq_of_subset_of_card_le (R.componentBlocks_subset _ U u)
    (hu.trans (R.wrapping_card hr hw))

end RingLayout

namespace Marker

/-- Label separation at a boundary cuts every winding walk. The parity
incidence argument is expressed as a coboundary. -/
theorem closed_zero_of_mismatched_labels {r : ℕ} (hr : 2 ≤ r)
    {V : Type} {G : SimpleGraph V} (row : V → Fin r) (label : V → Bool)
    (start finish : Fin r → Bool) (j : Fin r) (hj : finish j ≠ start (finRotate r j))
    (m : V → V → Bit)
    (he : ∀ u v, G.Adj u v →
      (row u = row v ∧ label u = label v ∧ m u v = 0) ∨
      ∃ i, m u v = delta i ∧
        ((row u = i ∧ row v = finRotate r i ∧ label u = start i ∧ label v = finish i) ∨
         (row v = i ∧ row u = finRotate r i ∧ label v = start i ∧ label u = finish i))) :
    ∀ u (p : G.Walk u u), walkSum m p = 0 := by
  let mark (i : Fin r) (a : Bool) : Bit := if i = finRotate r j ∧ a = finish j then 1 else 0
  have hmark (i : Fin r) : mark i (start i) + mark (finRotate r i) (finish i) =
      if i = j then 1 else 0 := by
    by_cases hi : i = j
    · subst i
      have hne := CycleRows.rotate_ne_self hr j
      dsimp only [mark]
      rw [ite_eq_right (fun h => hne h.1.symm), ite_eq_left ⟨rfl, rfl⟩, ite_eq_left rfl, zero_add]
    · by_cases hi' : i = finRotate r j
      · subst i
        have hne := CycleRows.rotate_ne_self hr (finRotate r j)
        dsimp only [mark]
        rw [ite_eq_right (fun h => hj h.2.symm), ite_eq_right (fun h => hne h.1), ite_eq_right hi, add_zero]
      · have hrot : finRotate r i ≠ finRotate r j := fun h => hi ((finRotate r).injective h)
        dsimp only [mark]
        rw [ite_eq_right (fun h => hi' h.1), ite_eq_right (fun h => hrot h.1), ite_eq_right hi, add_zero]
  let pot (v : V) : Bit := cut j (row v) + mark (row v) (label v)
  have hm : ∀ u v, G.Adj u v → m u v = pot u + pot v := by
    intro u v huv
    rcases he u v huv with ⟨hrow, hlab, hz⟩ | ⟨i, hval, hh⟩
    · dsimp only [pot]
      rw [hrow, hlab, CharTwo.add_self_eq_zero, hz]
    · have hcalc : delta i =
          (cut j i + mark i (start i)) + (cut j (finRotate r i) + mark (finRotate r i) (finish i)) := by
        calc
          _ = (cut j i + cut j (finRotate r i)) +
              (mark i (start i) + mark (finRotate r i) (finish i)) := by
            rw [cut_toggle, hmark, add_assoc, CharTwo.add_self_eq_zero, add_zero]
          _ = _ := by abel
      dsimp only [pot]
      rcases hh with ⟨hu, hv, hlu, hlv⟩ | ⟨hv, hu, hlv, hlu⟩
      · rw [hu, hv, hlu, hlv, hval, hcalc]
      · rw [hu, hv, hlu, hlv, hval, add_comm]
        exact hcalc
  intro u p
  rw [walkSum_of_exact pot m hm p, CharTwo.add_self_eq_zero]

end Marker

namespace RingLayout
variable {r : ℕ} {T L : Type} (R : RingLayout r T L)

/-- An alignment is only required to respect actual vertical readout names.
No assertion is made that ambient labels inhabit every product factor. -/
def Aligned (U : Finset R.Block) (a : R.Corner → Bool) : Prop :=
  ∀ v : R.VName, Sum.inr v ∈ R.names U → a (R.nameFirst (.inr v)) = a (R.nameSecond (.inr v))

def blockStart (a : R.Corner → Bool) : R.Block → Bool
  | .inl h => a (R.nameFirst (.inl h))
  | .inr b => a (R.nameFirst (.inl (R.leftH b)))

def blockFinish (a : R.Corner → Bool) : R.Block → Bool
  | .inl h => a (R.nameSecond (.inl h))
  | .inr b => a (R.nameSecond (.inl (R.leftH b)))

theorem horizontal_labels {U : Finset R.Block} {a : R.Corner → Bool} (ha : R.Aligned U a)
    {h : R.HName} (hh : Sum.inl h ∈ R.names U) :
    ∃ b ∈ U, R.blockRow b = h.2.1 ∧
      a (R.nameFirst (.inl h)) = R.blockStart a b ∧
      a (R.nameSecond (.inl h)) = R.blockFinish a b := by
  classical
  obtain ⟨b, hb, hm⟩ := Finset.mem_biUnion.mp hh
  refine ⟨b, hb, ?_⟩
  cases b with
  | inl b =>
    have he : h = b := Sum.inl.inj (Finset.mem_singleton.mp hm)
    subst h
    exact ⟨rfl, rfl, rfl⟩
  | inr b =>
    have ht := ha (R.topV b) (R.name_present hb (by simp [blockNames]))
    have hb' := ha (R.bottomV b) (R.name_present hb (by simp [blockNames]))
    simp only [blockNames, Finset.mem_insert, Finset.mem_singleton, Sum.inl.injEq,
      Sum.inl_ne_inr, or_false] at hm
    rcases hm with rfl | rfl
    · exact ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, ht.symm, hb'.symm⟩

def IsWrappingAddress (U : Finset R.Block) (a : R.Corner → Bool) (address : Fin r → Bool) : Prop :=
  ∀ b ∈ U, R.blockStart a b = address (R.blockRow b) ∧
    R.blockFinish a b = address (finRotate r (R.blockRow b))

/-- Exactly r wrapping blocks prescribe one genuine aligned address. -/
theorem wrapping_address (hr : 3 ≤ r) {U : Finset R.Block}
    (h : R.Wrapping (by omega) U) (hu : U.card ≤ r)
    {a : R.Corner → Bool} (ha : R.Aligned U a) :
    ∃! address : Fin r → Bool, R.IsWrappingAddress U a address := by
  classical
  have hex (i : Fin r) : ∃ b ∈ U, R.blockRow b = i := Finset.mem_image.mp (R.wrapping_rows hr h i)
  choose blocks hb hrow using hex
  have huniq {b : R.Block} (hb' : b ∈ U) : blocks (R.blockRow b) = b :=
    R.wrapping_row_inj hr h hu (hb _) hb' (hrow _)
  let start (i : Fin r) := R.blockStart a (blocks i)
  let finish (i : Fin r) := R.blockFinish a (blocks i)
  have hmatch (j : Fin r) : finish j = start (finRotate r j) := by
    by_contra hj
    have hz := Marker.closed_zero_of_mismatched_labels (show 2 ≤ r by omega)
      (G := R.cornerGraph (by omega) U) (fun c : R.Corner => c.2.1) a start finish j hj
      R.cornerMarker ?_
    · obtain ⟨u, p, hp⟩ := h
      have := hz u p
      rw [hp] at this
      exact one_ne_zero this
    · intro u v huv
      obtain ⟨n, hn, hh⟩ := huv
      cases n with
      | inl n =>
        obtain ⟨b, hb', hr', hl, ht⟩ := R.horizontal_labels ha hn
        have hs : a (R.nameFirst (.inl n)) = start n.2.1 := by
          rw [hl, ← hr']; dsimp only [start]; rw [huniq hb']
        have hf : a (R.nameSecond (.inl n)) = finish n.2.1 := by
          rw [ht, ← hr']; dsimp only [finish]; rw [huniq hb']
        refine Or.inr ⟨n.2.1, ?_⟩
        rcases hh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨(R.cornerMarker_horizontal hr n).1, Or.inl ⟨rfl, rfl, hs, hf⟩⟩
        · exact ⟨(R.cornerMarker_horizontal hr n).2, Or.inr ⟨rfl, rfl, hs, hf⟩⟩
      | inr n =>
        have he := ha n hn
        rcases hh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨rfl, he, (R.cornerMarker_vertical n).1⟩
        · exact Or.inl ⟨rfl, he.symm, (R.cornerMarker_vertical n).2⟩
  refine ⟨start, ?_, ?_⟩
  · intro b hb'
    constructor
    · dsimp only [start]; rw [huniq hb']
    · rw [← hmatch]
      dsimp only [finish]; rw [huniq hb']
  · intro other ho
    funext i
    have hi := (ho (blocks i) (hb i)).1
    rw [hrow i] at hi
    exact hi.symm

end RingLayout

namespace RingLayout
variable {r : ℕ} {T L : Type} (R : RingLayout r T L)

theorem names_mono {V U : Finset R.Block} (h : V ⊆ U) : R.names V ⊆ R.names U := by
  classical
  intro n hn
  obtain ⟨b, hb, hn⟩ := Finset.mem_biUnion.mp hn
  exact R.name_present (h hb) hn

theorem aligned_mono {V U : Finset R.Block} (h : V ⊆ U) {a : R.Corner → Bool}
    (ha : R.Aligned U a) : R.Aligned V a :=
  fun v hv => ha v (R.names_mono h hv)

theorem wrapping_blocks_reachable (hr : 3 ≤ r) {U : Finset R.Block}
    (hu : U.card ≤ r) (hw : R.Wrapping (by omega) U) {b c : R.Block} (hb : b ∈ U) (hc : c ∈ U) :
    (R.cornerGraph (by omega) U).Reachable (R.blockRepresentative b) (R.blockRepresentative c) := by
  classical
  obtain ⟨u, p, hp⟩ := hw
  have he := R.wrapping_component hr hu p hp
  have hb' : b ∈ R.componentBlocks (by omega) U u := by rw [he]; exact hb
  have hc' : c ∈ R.componentBlocks (by omega) U u := by rw [he]; exact hc
  exact (Finset.mem_filter.mp hb').2.symm.trans (Finset.mem_filter.mp hc').2

/-- Two r-element subcollections of r+1 blocks differ by at most one block. -/
theorem small_sdiff {U V W : Finset R.Block} (hV : V ⊆ U) (hW : W ⊆ U)
    (hu : U.card ≤ r + 1) (hw : r ≤ W.card) : (V \ W).card ≤ 1 := by
  classical
  have hs : V \ W ⊆ U \ W := by
    intro b hb
    exact Finset.mem_sdiff.mpr ⟨hV (Finset.mem_sdiff.mp hb).1, (Finset.mem_sdiff.mp hb).2⟩
  have hc := Finset.card_sdiff_add_card_inter U W
  rw [Finset.inter_eq_right.mpr hW] at hc
  have hd := Finset.card_le_card hs
  omega

/-- The common rows of two wrapping r-subcollections touch every boundary.
This is exactly where r≥3 is used for address compatibility. -/
theorem shared_incident (hr : 3 ≤ r) {U V W : Finset R.Block}
    (hV : V ⊆ U) (hW : W ⊆ U) (hu : U.card ≤ r + 1)
    (hv : R.Wrapping (by omega) V) (hw : R.Wrapping (by omega) W) (i : Fin r) :
    ∃ b ∈ V ∩ W, R.blockRow b = i ∨ finRotate r (R.blockRow b) = i := by
  classical
  obtain ⟨b, hb, hbi⟩ := Finset.mem_image.mp (R.wrapping_rows hr hv i)
  obtain ⟨c, hc, hci⟩ := Finset.mem_image.mp (R.wrapping_rows hr hv ((finRotate r).symm i))
  by_cases hbW : b ∈ W
  · exact ⟨b, Finset.mem_inter.mpr ⟨hb, hbW⟩, Or.inl hbi⟩
  by_cases hcW : c ∈ W
  · refine ⟨c, Finset.mem_inter.mpr ⟨hc, hcW⟩, Or.inr ?_⟩
    rw [hci, Equiv.apply_symm_apply]
  have hd := R.small_sdiff hV hW hu (R.wrapping_card hr hw)
  have he := Finset.card_le_one.mp hd b (Finset.mem_sdiff.mpr ⟨hb, hbW⟩)
    c (Finset.mem_sdiff.mpr ⟨hc, hcW⟩)
  have hi : finRotate r i = i := calc
    _ = finRotate r (R.blockRow b) := congrArg (finRotate r) hbi.symm
    _ = finRotate r (R.blockRow c) := congrArg (fun b => finRotate r (R.blockRow b)) he
    _ = i := by rw [hci, Equiv.apply_symm_apply]
  exact (CycleRows.rotate_ne_self (by omega) i hi).elim

/-- All wrapping r-subcollections of r+1 blocks have the same address in a
single ambient alignment; no address is imposed by an arbitrary r+1-cycle. -/
theorem wrapping_addresses_agree (hr : 3 ≤ r) {U V W : Finset R.Block}
    (hV : V ⊆ U) (hW : W ⊆ U) (hu : U.card ≤ r + 1)
    (hv : R.Wrapping (by omega) V) (hw : R.Wrapping (by omega) W)
    {a : R.Corner → Bool} {v w : Fin r → Bool}
    (hvaddr : R.IsWrappingAddress V a v) (hwaddr : R.IsWrappingAddress W a w) : v = w := by
  funext i
  obtain ⟨b, hb, hi⟩ := R.shared_incident hr hV hW hu hv hw i
  obtain ⟨hbV, hbW⟩ := Finset.mem_inter.mp hb
  rcases hi with hi | hi
  · rw [← hi, ← (hvaddr b hbV).1, ← (hwaddr b hbW).1]
  · rw [← hi, ← (hvaddr b hbV).2, ← (hwaddr b hbW).2]

end RingLayout

namespace RingLayout
variable {r : ℕ} {T L : Type} (R : RingLayout r T L)

noncomputable def usedLinks (U : Finset R.Block) : Finset L := by
  classical
  exact U.biUnion (fun b => match b with | .inl _ => ∅ | .inr q => {q.1})

theorem mem_usedLinks {U : Finset R.Block} {l : L} : l ∈ R.usedLinks U ↔
    ∃ q : R.Square, Sum.inr q ∈ U ∧ q.1 = l := by
  classical
  constructor
  · intro h
    obtain ⟨b, hb, hm⟩ := Finset.mem_biUnion.mp h
    cases b with
    | inl b => exact (Finset.notMem_empty _ hm).elim
    | inr b => exact ⟨b, hb, (Finset.mem_singleton.mp hm).symm⟩
  · rintro ⟨q, hq, rfl⟩
    exact Finset.mem_biUnion.mpr ⟨.inr q, hq, Finset.mem_singleton_self _⟩

theorem usedLinks_card (U : Finset R.Block) : (R.usedLinks U).card ≤ U.card := by
  classical
  calc
    _ ≤ ∑ b ∈ U, (match b with | .inl _ => (∅ : Finset L) | .inr q => {q.1}).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _b ∈ U, 1 := by
      apply Finset.sum_le_sum
      intro b _
      cases b <;> simp
    _ = _ := by simp

end RingLayout

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.GlobalSolvability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace ComparisonSchemas
variable {r : ℕ} {P E : Type} (S : ComparisonSchemas r P E)

/-- Cut an unused middle link on each private wire. End links need never be
removed: the private interior alone is longer than any small support. -/
def Avoids (n : ℕ) (U : Finset (S.layout n).Block) (cut : E → Fin n) : Prop :=
  ∀ e, Sum.inr (Sum.inl (e, cut e)) ∉ (S.layout n).usedLinks U

theorem exists_cuts (n : ℕ) (U : Finset (S.layout n).Block) (hu : U.card < n) :
    ∃ cut : E → Fin n, S.Avoids n U cut := by
  classical
  have hex (e : E) : ∃ i : Fin n, Sum.inr (Sum.inl (e, i)) ∉ (S.layout n).usedLinks U := by
    by_contra h
    have hall : ∀ i : Fin n, Sum.inr (Sum.inl (e, i)) ∈ (S.layout n).usedLinks U := by
      simpa only [not_exists, not_not] using h
    have hs : Finset.univ.image (fun i : Fin n => (Sum.inr (Sum.inl (e, i)) : S.Link n)) ⊆
        (S.layout n).usedLinks U := by
      intro l hl
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hl
      exact hall i
    have hinj : Function.Injective (fun i : Fin n => (Sum.inr (Sum.inl (e, i)) : S.Link n)) := by
      intro i j hij
      exact (Prod.mk.inj (Sum.inl.inj (Sum.inr.inj hij))).2
    have hc := Finset.card_le_card hs
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at hc
    have hb := (S.layout n).usedLinks_card U
    omega
  choose cut hc using hex
  exact ⟨cut, hc⟩

def root (n : ℕ) (cut : E → Fin n) : S.InternalType n → P
  | .inl p => p
  | .inr (e, i) => if i.val ≤ (cut e).val then S.source e else S.target e

def onLeft (_S : ComparisonSchemas r P E) (n : ℕ) (cut : E → Fin n) (e : E) (i : Fin (n + 1)) : Prop :=
  i.val ≤ (cut e).val

instance instDecidableOnLeft (n : ℕ) (cut : E → Fin n) (e : E) (i : Fin (n + 1)) :
    Decidable (S.onLeft n cut e i) := inferInstanceAs (Decidable (i.val ≤ (cut e).val))

theorem cut_middle {n : ℕ} {cut : E → Fin n} {e : E} {i : Fin n} (hi : i ≠ cut e) :
    S.onLeft n cut e i.castSucc ↔ S.onLeft n cut e i.succ := by
  have hne : i.val ≠ (cut e).val := fun h => hi (Fin.ext h)
  dsimp only [onLeft, Fin.val_castSucc, Fin.val_succ]
  omega

/-- Every injective partial binary coordinate map extends to a permutation.
This lemma preserves singleton domains rather than silently enlarging them. -/
theorem binary_extension (A : Finset Bool) (hA : A.Nonempty)
    (f : {a // a ∈ A} → Bool) (hf : Function.Injective f) :
    ∃ p : Equiv.Perm Bool, ∀ a, p a.val = f a := by
  classical
  obtain ⟨x, hx⟩ := hA
  let a0 : {a // a ∈ A} := ⟨x, hx⟩
  let flip : Equiv.Perm Bool := ⟨Bool.not, Bool.not, Bool.not_not, Bool.not_not⟩
  by_cases he : f a0 = x
  · refine ⟨Equiv.refl Bool, ?_⟩
    intro a
    change a.val = f a
    by_cases ha : a = a0
    · subst a; exact he.symm
    · have hav : a.val ≠ x := fun h => ha (Subtype.ext h)
      have hfa : f a ≠ f a0 := fun h => ha (hf h)
      rw [he] at hfa
      cases hval : a.val <;> cases hfx : f a <;> cases x <;> simp_all
  · refine ⟨flip, ?_⟩
    intro a
    change (!a.val) = f a
    by_cases ha : a = a0
    · subst a
      dsimp only [a0]
      cases hfx : f ⟨x, hx⟩ <;> cases x <;> simp_all [a0]
    · have hav : a.val ≠ x := fun h => ha (Subtype.ext h)
      have hfa : f a ≠ f a0 := fun h => ha (hf h)
      cases hval : a.val <;> cases hfx : f a <;> cases hf0 : f a0 <;> cases x <;> simp_all

noncomputable def permutation (e : E) (i : Fin r) : Equiv.Perm Bool :=
  (binary_extension (S.domain e i) (S.domain_nonempty e i)
    (S.mapping e i) (S.mapping_injective e i)).choose

theorem permutation_apply (e : E) (i : Fin r) (a : {a // a ∈ S.domain e i}) :
    S.permutation e i a.val = S.mapping e i a :=
  (binary_extension (S.domain e i) (S.domain_nonempty e i)
    (S.mapping e i) (S.mapping_injective e i)).choose_spec a

noncomputable def align (n : ℕ) (cut : E → Fin n) : (S.layout n).Corner → Bool
  | ⟨.inl _, _, a⟩ => a.val
  | ⟨.inr (e, j), i, a⟩ => if S.onLeft n cut e j then a.val else S.permutation e i a.val

theorem align_link {n : ℕ} {U : Finset (S.layout n).Block} {cut : E → Fin n}
    (hc : S.Avoids n U cut) {l : S.Link n} (hl : l ∈ (S.layout n).usedLinks U)
    (i : Fin r) (a : (S.layout n).Match l i) :
    S.align n cut ((S.layout n).nameFirst (.inr ⟨l, i, a⟩)) =
    S.align n cut ((S.layout n).nameSecond (.inr ⟨l, i, a⟩)) := by
  cases l with
  | inl e =>
    change a.val = (if 0 ≤ (cut e).val then a.val else S.permutation e i a.val)
    rw [ite_eq_left (Nat.zero_le _)]
  | inr l => cases l with
    | inl ei =>
      obtain ⟨e, j⟩ := ei
      have hj : j ≠ cut e := fun he => hc e (he ▸ hl)
      change (if S.onLeft n cut e j.castSucc then a.val else S.permutation e i a.val) =
        (if S.onLeft n cut e j.succ then a.val else S.permutation e i a.val)
      simp only [S.cut_middle hj]
    | inr e =>
      change (if n ≤ (cut e).val then a.val else S.permutation e i a.val) = S.mapping e i a
      rw [ite_eq_right (Nat.not_le.mpr (cut e).isLt)]
      exact S.permutation_apply e i a

end ComparisonSchemas

namespace RingLayout
variable {r : ℕ} {T L : Type} (R : RingLayout r T L)

theorem vertical_usedLink {U : Finset R.Block} {v : R.VName}
    (hv : Sum.inr v ∈ R.names U) : v.1 ∈ R.usedLinks U := by
  classical
  obtain ⟨b, hb, hn⟩ := Finset.mem_biUnion.mp hv
  cases b with
  | inl b => simp [blockNames] at hn
  | inr b =>
    simp only [blockNames, Finset.mem_insert, Finset.mem_singleton, Sum.inr_ne_inl,
      Sum.inr.injEq, false_or] at hn
    rcases hn with rfl | rfl <;> exact R.mem_usedLinks.mpr ⟨b, hb, rfl⟩

abbrev Shift := (t : T) → Fin (R.dimension t) → Bit
abbrev Potential := (c : R.Corner) → Fin (R.dimension c.1) → Bit

def potentialHorizontal (h : R.Shift) (M : R.Potential) : R.Horizontal :=
  fun x => M ⟨x.1, x.2.1, x.2.2.1⟩ + M ⟨x.1, finRotate r x.2.1, x.2.2.2⟩ + Marker.delta x.2.1 • h x.1

def potentialVertical (M : R.Potential) : R.Vertical :=
  fun x => R.firstForm x.1 (M (R.nameFirst (.inr x))) +
    R.secondForm x.1 (M (R.nameSecond (.inr x)))

def translation (h : R.Shift) (M : R.Potential) : R.Coordinate → Bit :=
  R.pack (R.potentialHorizontal h M) (R.potentialVertical M)

/-- The potential terms cancel on every square, leaving only its row marker
multiplied by the affine link-shift equation. -/
theorem translation_square (h : R.Shift) (M : R.Potential) (b : R.Square) :
    R.firstForm b.1 (R.horizontal (R.translation h M) (R.leftH b)) +
      R.secondForm b.1 (R.horizontal (R.translation h M) (R.rightH b)) +
      R.vertical (R.translation h M) (R.topV b) +
      R.vertical (R.translation h M) (R.bottomV b) =
    Marker.delta b.2.1 * (R.firstForm b.1 (h (R.first b.1)) +
      R.secondForm b.1 (h (R.second b.1))) := by
  have hh : R.horizontal (R.translation h M) = R.potentialHorizontal h M := rfl
  have hv : R.vertical (R.translation h M) = R.potentialVertical M := rfl
  rw [hh, hv]
  dsimp only [potentialHorizontal, potentialVertical, leftH, rightH, topV,
    bottomV, nameFirst, nameSecond]
  simp only [map_add, map_smul, smul_eq_mul]
  ring_nf
  simp only [show (2 : Bit) = 0 by decide, mul_zero, zero_add, add_zero]

end RingLayout

namespace ComparisonSchemas
variable {r : ℕ} {P E : Type} (S : ComparisonSchemas r P E)

theorem align_aligned {n : ℕ} {U : Finset (S.layout n).Block} {cut : E → Fin n}
    (hc : S.Avoids n U cut) : (S.layout n).Aligned U (S.align n cut) := by
  intro v hv
  exact S.align_link hc ((S.layout n).vertical_usedLink hv) v.2.1 v.2.2

abbrev RealShift := (p : P) → Fin (S.dimension p) → Bit

def linkConstant (n : ℕ) (b : E → Bit) : S.Link n → Bit
  | .inl _ => 0
  | .inr (.inl _) => 0
  | .inr (.inr e) => b e

def specialTwist (n : ℕ) (b : E → Bit) : (S.layout n).Block → Bit
  | .inl _ => 0
  | .inr q => Marker.delta q.2.1 * S.linkConstant n b q.1

/-- Completing the cut layout to rooted stars gives a uniform affine shift.
The real vectors may be arbitrary; internal values are constant on each arm. -/
def starShift (n : ℕ) (cut : E → Fin n) (b : E → Bit) (q : S.RealShift) : (S.layout n).Shift
  | .inl p => q p
  | .inr (e, i) => fun _ => if S.onLeft n cut e i then S.left e (q (S.source e))
      else b e + S.right e (q (S.target e))

theorem starShift_link {n : ℕ} {U : Finset (S.layout n).Block} {cut : E → Fin n}
    (hc : S.Avoids n U cut) (b : E → Bit) (q : S.RealShift)
    {l : S.Link n} (hl : l ∈ (S.layout n).usedLinks U) :
    (S.layout n).firstForm l (S.starShift n cut b q ((S.layout n).first l)) +
      (S.layout n).secondForm l (S.starShift n cut b q ((S.layout n).second l)) =
      S.linkConstant n b l := by
  cases l with
  | inl e =>
    change S.left e (q (S.source e)) +
      (if 0 ≤ (cut e).val then S.left e (q (S.source e)) else b e + S.right e (q (S.target e))) = 0
    rw [ite_eq_left (Nat.zero_le _), CharTwo.add_self_eq_zero]
  | inr l => cases l with
    | inl ei =>
      obtain ⟨e, i⟩ := ei
      have hi : i ≠ cut e := fun he => hc e (he ▸ hl)
      change (if S.onLeft n cut e i.castSucc then S.left e (q (S.source e)) else b e + S.right e (q (S.target e))) +
        (if S.onLeft n cut e i.succ then S.left e (q (S.source e)) else b e + S.right e (q (S.target e))) = 0
      simp only [S.cut_middle hi, CharTwo.add_self_eq_zero]
    | inr e =>
      change (if n ≤ (cut e).val then S.left e (q (S.source e)) else b e + S.right e (q (S.target e))) +
        S.right e (q (S.target e)) = b e
      rw [ite_eq_right (Nat.not_le.mpr (cut e).isLt), add_assoc, CharTwo.add_self_eq_zero, add_zero]

variable [Fintype P] [Fintype E]

theorem translation_legal {n : ℕ} {U : Finset (S.layout n).Block} {cut : E → Fin n}
    (hc : S.Avoids n U cut) (hr : 2 ≤ r) (b : E → Bit) (q : S.RealShift)
    (M : (S.layout n).Potential) {a : (S.layout n).Block} (ha : a ∈ U) :
    ((S.layout n).affine hr).Legal (S.specialTwist n b) a
      (((S.layout n).affine hr).restrict a ((S.layout n).translation (S.starShift n cut b q) M)) := by
  cases a with
  | inl a => intro hh; cases hh
  | inr a =>
    intro _
    change (S.layout n).squareForm a (fun c => (S.layout n).translation (S.starShift n cut b q) M c.val) = _
    rw [RingLayout.squareForm_apply]
    change (S.layout n).firstForm a.1
      ((S.layout n).horizontal ((S.layout n).translation (S.starShift n cut b q) M) ((S.layout n).leftH a)) +
      (S.layout n).secondForm a.1
      ((S.layout n).horizontal ((S.layout n).translation (S.starShift n cut b q) M) ((S.layout n).rightH a)) +
      (S.layout n).vertical ((S.layout n).translation (S.starShift n cut b q) M) ((S.layout n).topV a) +
      (S.layout n).vertical ((S.layout n).translation (S.starShift n cut b q) M) ((S.layout n).bottomV a) = _
    rw [RingLayout.translation_square, S.starShift_link hc b q ((S.layout n).mem_usedLinks.mpr ⟨a, ha, rfl⟩)]
    rfl

end ComparisonSchemas

namespace RingLayout
variable {r : ℕ} {T L : Type} (R : RingLayout r T L)

def coordinateName : R.Coordinate → R.Name
  | .inl h => .inl h.1
  | .inr v => .inr v

theorem coordinate_name_mem {b : R.Block} {c : R.Coordinate}
    (hc : c ∈ R.coordinates b) : R.coordinateName c ∈ R.blockNames b := by
  classical
  cases b with
  | inl h =>
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_singleton_self _
  | inr b =>
    simp only [coordinates, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with (hh | hh) | hh | hh
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hh
      simp [coordinateName, blockNames]
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hh
      simp [coordinateName, blockNames]
    · subst c
      simp [coordinateName, blockNames]
    · subst c
      simp [coordinateName, blockNames]

theorem cornerMarker_symm (hr : 3 ≤ r) {U : Finset R.Block} {u v : R.Corner}
    (h : (R.cornerGraph (by omega) U).Adj u v) : R.cornerMarker u v = R.cornerMarker v u := by
  obtain ⟨n, _, h⟩ := h
  cases n with
  | inl n =>
    obtain ⟨h1, h2⟩ := R.cornerMarker_horizontal hr n
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1.trans h2.symm
    · exact h2.trans h1.symm
  | inr n =>
    obtain ⟨h1, h2⟩ := R.cornerMarker_vertical n
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1.trans h2.symm
    · exact h2.trans h1.symm

theorem nonwrapping_exact (hr : 3 ≤ r) {U : Finset R.Block}
    (hw : ¬R.Wrapping (by omega) U) :
    ∃ s : R.Corner → Bit, ∀ n ∈ R.names U,
      R.cornerMarker (R.nameFirst n) (R.nameSecond n) = s (R.nameFirst n) + s (R.nameSecond n) := by
  have hc : ∀ u (p : (R.cornerGraph (by omega) U).Walk u u), Marker.walkSum R.cornerMarker p = 0 := by
    intro u p
    have hb : ∀ x : Bit, x = 0 ∨ x = 1 := by intro x; fin_cases x <;> (first | exact Or.inl rfl | exact Or.inr rfl)
    rcases hb (Marker.walkSum R.cornerMarker p) with h | h
    · exact h
    · exact (hw ⟨u, p, h⟩).elim
  obtain ⟨s, hs⟩ := Marker.exact_of_closed_zero R.cornerMarker
    (fun _ _ h => R.cornerMarker_symm hr h) hc
  exact ⟨s, fun n hn => hs _ _ ⟨n, hn, Or.inl ⟨rfl, rfl⟩⟩⟩

/-- On a nonwrapping support any two shifts with the same affine link equations
induce the same offset family after a potential adjustment. -/
theorem adjust_potential (hr : 3 ≤ r) {U : Finset R.Block}
    (hw : ¬R.Wrapping (by omega) U) (old new : R.Shift) (M : R.Potential)
    (he : ∀ l ∈ R.usedLinks U,
      R.firstForm l (old (R.first l)) + R.secondForm l (old (R.second l)) =
      R.firstForm l (new (R.first l)) + R.secondForm l (new (R.second l))) :
    ∃ N : R.Potential, ∀ b ∈ U, ∀ c ∈ R.coordinates b,
      R.translation new N c = R.translation old M c := by
  classical
  obtain ⟨s, hs⟩ := R.nonwrapping_exact hr hw
  let N : R.Potential := fun c => M c + s c • (new c.1 + old c.1)
  have hh {h : R.HName} (hh : Sum.inl h ∈ R.names U) :
      R.potentialHorizontal new N h = R.potentialHorizontal old M h := by
    have hm := (R.cornerMarker_horizontal hr h).1.symm.trans (hs (.inl h) hh)
    exact Marker.horizontal_adjust (M (R.nameFirst (.inl h))) (M (R.nameSecond (.inl h)))
      (old h.1) (new h.1) (s (R.nameFirst (.inl h))) (s (R.nameSecond (.inl h)))
      (Marker.delta h.2.1) hm.symm
  have hv {v : R.VName} (hv : Sum.inr v ∈ R.names U) :
      R.potentialVertical N v = R.potentialVertical M v := by
    have hm := (R.cornerMarker_vertical v).1.symm.trans (hs (.inr v) hv)
    have hst : s (R.nameFirst (.inr v)) = s (R.nameSecond (.inr v)) := by
      calc
        _ = s (R.nameFirst (.inr v)) + (s (R.nameFirst (.inr v)) + s (R.nameSecond (.inr v))) := by rw [← hm, add_zero]
        _ = _ := by rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    have hl := he v.1 (R.vertical_usedLink hv)
    have he' : R.firstForm v.1 (new (R.first v.1) + old (R.first v.1)) +
        R.secondForm v.1 (new (R.second v.1) + old (R.second v.1)) = 0 := by
      rw [map_add, map_add]
      calc
        _ = (R.firstForm v.1 (new (R.first v.1)) + R.secondForm v.1 (new (R.second v.1))) +
            (R.firstForm v.1 (old (R.first v.1)) + R.secondForm v.1 (old (R.second v.1))) := by abel
        _ = 0 := by rw [hl, CharTwo.add_self_eq_zero]
    exact Marker.vertical_adjust (R.firstForm v.1) (R.secondForm v.1)
      (M (R.nameFirst (.inr v))) (M (R.nameSecond (.inr v)))
      (new (R.first v.1) + old (R.first v.1)) (new (R.second v.1) + old (R.second v.1))
      (s (R.nameFirst (.inr v))) (s (R.nameSecond (.inr v))) hst he'
  refine ⟨N, ?_⟩
  intro b hb c hc
  have hn := R.name_present hb (R.coordinate_name_mem hc)
  cases c with
  | inl h => exact congrFun (hh hn) h.2
  | inr v => exact hv hn

end RingLayout

namespace ComparisonSchemas
variable {r : ℕ} {P E : Type} (S : ComparisonSchemas r P E)

def GoodAddress (n : ℕ) (hr : 2 ≤ r) (U : Finset (S.layout n).Block)
    (cut : E → Fin n) (a : Fin r → Bool) : Prop :=
  ∀ V ⊆ U, V.card ≤ r → (S.layout n).Wrapping hr V →
    (S.layout n).IsWrappingAddress V (S.align n cut) a

theorem goodAddress_exists (n : ℕ) (hr : 3 ≤ r) {U : Finset (S.layout n).Block}
    (hu : U.card ≤ r + 1) {cut : E → Fin n} (hc : S.Avoids n U cut) :
    ∃ a, S.GoodAddress n (by omega) U cut a := by
  classical
  by_cases hw : ∃ V ⊆ U, V.card ≤ r ∧ (S.layout n).Wrapping (by omega) V
  · obtain ⟨V, hV, hv, hwV⟩ := hw
    obtain ⟨a, ha, _⟩ := (S.layout n).wrapping_address hr hwV hv
      ((S.layout n).aligned_mono hV (S.align_aligned hc))
    refine ⟨a, ?_⟩
    intro W hW hw' hww
    obtain ⟨a', ha', _⟩ := (S.layout n).wrapping_address hr hww hw'
      ((S.layout n).aligned_mono hW (S.align_aligned hc))
    have he := (S.layout n).wrapping_addresses_agree hr hV hW hu hwV hww ha ha'
    exact he ▸ ha'
  · exact ⟨fun _ => false, fun V hV hv hwV => (hw ⟨V, hV, hv, hwV⟩).elim⟩

theorem avoids_mono {n : ℕ} {V U : Finset (S.layout n).Block} (h : V ⊆ U)
    {cut : E → Fin n} (hc : S.Avoids n U cut) : S.Avoids n V cut := by
  intro e he
  obtain ⟨b, hb, hb'⟩ := (S.layout n).mem_usedLinks.mp he
  exact hc e ((S.layout n).mem_usedLinks.mpr ⟨b, h hb, hb'⟩)

theorem goodAddress_mono {n : ℕ} {hr : 2 ≤ r} {V U : Finset (S.layout n).Block}
    (h : V ⊆ U) {cut : E → Fin n} {a : Fin r → Bool}
    (ha : S.GoodAddress n hr U cut a) : S.GoodAddress n hr V cut a :=
  fun W hW => ha W (hW.trans h)

end ComparisonSchemas

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.AcceptingMates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace SimpleGraph

theorem reachable_propagate {V : Type} {G : SimpleGraph V} {a b : V} {P : V → Prop}
    (hab : G.Reachable a b) (ha : P a)
    (step : ∀ {u v}, G.Reachable a u → G.Adj u v → P u → P v) : P b := by
  obtain ⟨p⟩ := hab
  have aux : ∀ {u v} (p : G.Walk u v), G.Reachable a u → P u → P v := by
    intro u v p
    induction p with
    | nil => exact fun _ h => h
    | cons h p ih =>
      intro hu hp
      exact ih (hu.trans h.reachable) (step hu h hp)
  exact aux p (.refl a) ha

end SimpleGraph

namespace ComparisonSchemas
variable {r : ℕ} {P E : Type} (S : ComparisonSchemas r P E)

theorem shift_link_forward {n : ℕ} (h h' : (S.layout n).Shift) (l : S.Link n)
    (he : (S.layout n).firstForm l (h ((S.layout n).first l)) +
        (S.layout n).secondForm l (h ((S.layout n).second l)) =
      (S.layout n).firstForm l (h' ((S.layout n).first l)) +
        (S.layout n).secondForm l (h' ((S.layout n).second l)))
    (hreal : ∀ p, (S.layout n).second l = Sum.inl p → h (.inl p) = h' (.inl p))
    (hh : h ((S.layout n).first l) = h' ((S.layout n).first l)) :
    h ((S.layout n).second l) = h' ((S.layout n).second l) := by
  rw [hh] at he
  have hv := add_left_cancel he
  cases l with
  | inl e =>
    funext j
    have hj : j = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
    subst j
    exact hv
  | inr l => cases l with
    | inl ei =>
      funext j
      have hj : j = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
      subst j
      exact hv
    | inr e => exact hreal (S.target e) rfl

theorem shift_link_backward {n : ℕ} (h h' : (S.layout n).Shift) (l : S.Link n)
    (he : (S.layout n).firstForm l (h ((S.layout n).first l)) +
        (S.layout n).secondForm l (h ((S.layout n).second l)) =
      (S.layout n).firstForm l (h' ((S.layout n).first l)) +
        (S.layout n).secondForm l (h' ((S.layout n).second l)))
    (hreal : ∀ p, (S.layout n).first l = Sum.inl p → h (.inl p) = h' (.inl p))
    (hh : h ((S.layout n).second l) = h' ((S.layout n).second l)) :
    h ((S.layout n).first l) = h' ((S.layout n).first l) := by
  rw [hh] at he
  have hv := add_right_cancel he
  cases l with
  | inl e => exact hreal (S.source e) rfl
  | inr l => cases l with
    | inl ei =>
      funext j
      have hj : j = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
      subst j
      exact hv
    | inr e =>
      funext j
      have hj : j = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
      subst j
      exact hv

theorem shift_agreement_reachable {n : ℕ} {U : Finset (S.layout n).Block}
    (hr : 2 ≤ r) (old new : (S.layout n).Shift) {a c : (S.layout n).Corner}
    (he : ∀ l ∈ (S.layout n).usedLinks U,
      (S.layout n).firstForm l (old ((S.layout n).first l)) +
        (S.layout n).secondForm l (old ((S.layout n).second l)) =
      (S.layout n).firstForm l (new ((S.layout n).first l)) +
        (S.layout n).secondForm l (new ((S.layout n).second l)))
    (hreal : ∀ d, ((S.layout n).cornerGraph hr U).Reachable a d →
      ∀ p, d.1 = Sum.inl p → old (.inl p) = new (.inl p))
    (ha : old a.1 = new a.1)
    (hc : ((S.layout n).cornerGraph hr U).Reachable a c) : old c.1 = new c.1 := by
  apply SimpleGraph.reachable_propagate hc ha
  intro u v hu huv hh
  have hv := hu.trans huv.reachable
  obtain ⟨x, hx, hd⟩ := huv
  cases x with
  | inl x => rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact hh
  | inr x =>
    have hl := he x.1 ((S.layout n).vertical_usedLink hx)
    rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact S.shift_link_forward old new x.1 hl (hreal _ hv) hh
    · exact S.shift_link_backward old new x.1 hl (hreal _ hv) hh

def SameAlignment (n : ℕ) (cut cut' : E → Fin n) (t : S.InternalType n) : Prop :=
  ∀ i (a : (S.layout n).Label t i),
    S.align n cut ⟨t, i, a⟩ = S.align n cut' ⟨t, i, a⟩

theorem alignment_link_forward {n : ℕ} {U : Finset (S.layout n).Block}
    {cut cut' : E → Fin n} (hc : S.Avoids n U cut) (hc' : S.Avoids n U cut')
    {l : S.Link n} (hl : l ∈ (S.layout n).usedLinks U)
    (hh : S.SameAlignment n cut cut' ((S.layout n).first l)) :
    S.SameAlignment n cut cut' ((S.layout n).second l) := by
  have step (i : Fin r) (a : (S.layout n).Match l i) :=
    (S.align_link hc hl i a).symm.trans ((hh i _).trans (S.align_link hc' hl i a))
  cases l with
  | inl e => exact step
  | inr l => cases l with
    | inl ei => exact step
    | inr e => exact fun _ _ => rfl

theorem alignment_link_backward {n : ℕ} {U : Finset (S.layout n).Block}
    {cut cut' : E → Fin n} (hc : S.Avoids n U cut) (hc' : S.Avoids n U cut')
    {l : S.Link n} (hl : l ∈ (S.layout n).usedLinks U)
    (hh : S.SameAlignment n cut cut' ((S.layout n).second l)) :
    S.SameAlignment n cut cut' ((S.layout n).first l) := by
  have step (i : Fin r) (a : (S.layout n).Match l i) :=
    (S.align_link hc hl i a).trans ((hh i _).trans (S.align_link hc' hl i a).symm)
  cases l with
  | inl e => exact fun _ _ => rfl
  | inr l => cases l with
    | inl ei => exact step
    | inr e => exact step

theorem alignment_agreement_reachable {n : ℕ} {U : Finset (S.layout n).Block}
    {cut cut' : E → Fin n} (hc : S.Avoids n U cut) (hc' : S.Avoids n U cut')
    (hr : 2 ≤ r) {a c : (S.layout n).Corner}
    (ha : S.SameAlignment n cut cut' a.1)
    (h : ((S.layout n).cornerGraph hr U).Reachable a c) :
    S.SameAlignment n cut cut' c.1 := by
  apply SimpleGraph.reachable_propagate h ha
  intro u v _ huv hh
  obtain ⟨x, hx, hd⟩ := huv
  cases x with
  | inl x => rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact hh
  | inr x =>
    have hl := (S.layout n).vertical_usedLink hx
    rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact S.alignment_link_forward hc hc' hl hh
    · exact S.alignment_link_backward hc hc' hl hh

end ComparisonSchemas

namespace ComparisonSchemas
variable {r : ℕ} {P E : Type} (S : ComparisonSchemas r P E)

def arm (n : ℕ) (cut : E → Fin n) : S.InternalType n → Option (E × Bool)
  | .inl _ => none
  | .inr (e, j) => some (e, decide (S.onLeft n cut e j))

def NoRealFrom (n : ℕ) (hr : 2 ≤ r) (U : Finset (S.layout n).Block)
    (a : (S.layout n).Corner) : Prop :=
  ∀ c, ((S.layout n).cornerGraph hr U).Reachable a c → ∀ p, c.1 ≠ Sum.inl p

theorem arm_link {n : ℕ} {U : Finset (S.layout n).Block} {cut : E → Fin n}
    (hc : S.Avoids n U cut) {l : S.Link n} (hl : l ∈ (S.layout n).usedLinks U)
    (hf : ∀ p, (S.layout n).first l ≠ Sum.inl p)
    (hs : ∀ p, (S.layout n).second l ≠ Sum.inl p) :
    S.arm n cut ((S.layout n).first l) = S.arm n cut ((S.layout n).second l) := by
  cases l with
  | inl e => exact (hf (S.source e) rfl).elim
  | inr l => cases l with
    | inl ei =>
      obtain ⟨e, j⟩ := ei
      have hj : j ≠ cut e := fun h => hc e (h ▸ hl)
      change some (e, decide (S.onLeft n cut e j.castSucc)) =
        some (e, decide (S.onLeft n cut e j.succ))
      simp only [S.cut_middle hj]
    | inr e => exact (hs (S.target e) rfl).elim

theorem arm_reachable {n : ℕ} {U : Finset (S.layout n).Block} {cut : E → Fin n}
    (hc : S.Avoids n U cut) (hr : 2 ≤ r) {a c : (S.layout n).Corner}
    (hn : S.NoRealFrom n hr U a)
    (hh : ((S.layout n).cornerGraph hr U).Reachable a c) :
    S.arm n cut c.1 = S.arm n cut a.1 := by
  apply SimpleGraph.reachable_propagate (P := fun d => S.arm n cut d.1 = S.arm n cut a.1) hh rfl
  intro u v hu huv ih
  have hv := hu.trans huv.reachable
  obtain ⟨x, hx, hd⟩ := huv
  cases x with
  | inl x => rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ih
  | inr x =>
    rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (S.arm_link hc ((S.layout n).vertical_usedLink hx) (hn _ hu) (hn _ hv)).symm.trans ih
    · exact (S.arm_link hc ((S.layout n).vertical_usedLink hx) (hn _ hv) (hn _ hu)).trans ih

theorem arm_label {n : ℕ} {cut : E → Fin n} {c : (S.layout n).Corner}
    {e : E} {side : Bool} (h : S.arm n cut c.1 = some (e, side)) :
    c.2.2.val ∈ S.domain e c.2.1 ∧
      S.align n cut c = if side then c.2.2.val else S.permutation e c.2.1 c.2.2.val := by
  obtain ⟨t, i, a⟩ := c
  cases t with
  | inl p => cases h
  | inr ej =>
    obtain ⟨f, j⟩ := ej
    have he := (Prod.mk.inj (Option.some.inj h)).1
    have hs := (Prod.mk.inj (Option.some.inj h)).2
    subst f
    refine ⟨a.property, ?_⟩
    change (if S.onLeft n cut e j then a.val else S.permutation e i a.val) = _
    rw [← hs]
    simp only [decide_eq_true_eq]

end ComparisonSchemas

namespace RingLayout
variable {r : ℕ} {T L : Type} (R : RingLayout r T L)

theorem blockStart_eq (a : R.Corner → Bool) (b : R.Block) :
    R.blockStart a b = a (R.blockRepresentative b) := by cases b <;> rfl

theorem representative_row (b : R.Block) : (R.blockRepresentative b).2.1 = R.blockRow b := by
  cases b <;> rfl

theorem wrapping_names_reachable (hr : 3 ≤ r) {U : Finset R.Block}
    (hu : U.card ≤ r) (hw : R.Wrapping (by omega) U) {b : R.Block} (hb : b ∈ U)
    {x : R.Name} (hx : x ∈ R.names U) :
    (R.cornerGraph (by omega) U).Reachable (R.blockRepresentative b) (R.nameFirst x) ∧
    (R.cornerGraph (by omega) U).Reachable (R.blockRepresentative b) (R.nameSecond x) := by
  classical
  obtain ⟨c, hc, hxc⟩ := Finset.mem_biUnion.mp hx
  have hbc := R.wrapping_blocks_reachable hr hu hw hb hc
  have hc' := R.block_reachable (by omega) hc hxc
  exact ⟨hbc.trans hc'.1, hbc.trans hc'.2⟩

end RingLayout

namespace ComparisonSchemas
variable {r : ℕ} {P E : Type} (S : ComparisonSchemas r P E)

theorem wrapping_real_addresses {n : ℕ} (hr : 3 ≤ r) {U : Finset (S.layout n).Block}
    (hu : U.card ≤ r) (hw : (S.layout n).Wrapping (by omega) U)
    {cut cut' : E → Fin n} (hc : S.Avoids n U cut) (hc' : S.Avoids n U cut')
    {A A' : Fin r → Bool}
    (hA : (S.layout n).IsWrappingAddress U (S.align n cut) A)
    (hA' : (S.layout n).IsWrappingAddress U (S.align n cut') A')
    {b : (S.layout n).Block} (hb : b ∈ U)
    {d : (S.layout n).Corner} {p : P} (hd : d.1 = Sum.inl p)
    (hbd : ((S.layout n).cornerGraph (by omega) U).Reachable ((S.layout n).blockRepresentative b) d) :
    A = A' := by
  funext i
  obtain ⟨c, hcu, hci⟩ := Finset.mem_image.mp ((S.layout n).wrapping_rows hr hw i)
  have hdc := hbd.symm.trans ((S.layout n).wrapping_blocks_reachable hr hu hw hb hcu)
  have hd' : S.SameAlignment n cut cut' d.1 := by rw [hd]; exact fun _ _ => rfl
  have he := S.alignment_agreement_reachable hc hc' (by omega) hd' hdc
  have he' : (S.layout n).blockStart (S.align n cut) c =
      (S.layout n).blockStart (S.align n cut') c := by
    rw [RingLayout.blockStart_eq, RingLayout.blockStart_eq]
    exact he _ _
  rw [(hA c hcu).1, (hA' c hcu).1, hci] at he'
  exact he'

def expressAddress (e : E) (side : Bool) (a : S.DomainAddress e) : Fin r → Bool :=
  fun i => if side then (a i).val else S.mapping e i (a i)

theorem wrapping_internal_addresses {n : ℕ} (hr : 3 ≤ r) {U : Finset (S.layout n).Block}
    (hu : U.card ≤ r) (hw : (S.layout n).Wrapping (by omega) U)
    {cut cut' : E → Fin n} (hc : S.Avoids n U cut) (hc' : S.Avoids n U cut')
    {A A' : Fin r → Bool}
    (hA : (S.layout n).IsWrappingAddress U (S.align n cut) A)
    (hA' : (S.layout n).IsWrappingAddress U (S.align n cut') A')
    {b : (S.layout n).Block} (hb : b ∈ U)
    (hn : S.NoRealFrom n (by omega) U ((S.layout n).blockRepresentative b))
    {e : E} {side side' : Bool}
    (ha : S.arm n cut ((S.layout n).blockRepresentative b).1 = some (e, side))
    (ha' : S.arm n cut' ((S.layout n).blockRepresentative b).1 = some (e, side')) :
    ∃ a : S.DomainAddress e, A = S.expressAddress e side a ∧ A' = S.expressAddress e side' a := by
  classical
  have hex (i : Fin r) : ∃ c ∈ U, (S.layout n).blockRow c = i :=
    Finset.mem_image.mp ((S.layout n).wrapping_rows hr hw i)
  choose c hcu hci using hex
  have harm (i : Fin r) := (S.arm_reachable hc (by omega) hn
    ((S.layout n).wrapping_blocks_reachable hr hu hw hb (hcu i))).trans ha
  have harm' (i : Fin r) := (S.arm_reachable hc' (by omega) hn
    ((S.layout n).wrapping_blocks_reachable hr hu hw hb (hcu i))).trans ha'
  have hrow (i : Fin r) : ((S.layout n).blockRepresentative (c i)).2.1 = i :=
    ((S.layout n).representative_row (c i)).trans (hci i)
  let a : S.DomainAddress e := fun i => ⟨((S.layout n).blockRepresentative (c i)).2.2.val,
    by simpa only [hrow i] using (S.arm_label (harm i)).1⟩
  refine ⟨a, ?_, ?_⟩
  · funext i
    have he := (S.arm_label (harm i)).2
    change S.align n cut ((S.layout n).blockRepresentative (c i)) =
      (if side then (a i).val else S.permutation e ((S.layout n).blockRepresentative (c i)).2.1 (a i).val) at he
    rw [hrow i] at he
    have hs := (hA (c i) (hcu i)).1
    rw [RingLayout.blockStart_eq, hci i] at hs
    rw [← hs, he]
    change (if side then (a i).val else S.permutation e i (a i).val) = _
    rw [S.permutation_apply]
    rfl
  · funext i
    have he := (S.arm_label (harm' i)).2
    change S.align n cut' ((S.layout n).blockRepresentative (c i)) =
      (if side' then (a i).val else S.permutation e ((S.layout n).blockRepresentative (c i)).2.1 (a i).val) at he
    rw [hrow i] at he
    have hs := (hA' (c i) (hcu i)).1
    rw [RingLayout.blockStart_eq, hci i] at hs
    rw [← hs, he]
    change (if side' then (a i).val else S.permutation e i (a i).val) = _
    rw [S.permutation_apply]
    rfl

end ComparisonSchemas

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.RejectingMates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace ComparisonSchemas
variable {r : ℕ} {P E : Type} (S : ComparisonSchemas r P E)

/-- Exactly the individual scalar-image hypotheses of special-twist
sufficiency. No simultaneous choice satisfying the wires is required. -/
structure SpecialImages (b : E → Bit) where
  values : (p : P) → (Fin r → Bool) → Set (Fin (S.dimension p) → Bit)
  nonempty : ∀ p a, (values p a).Nonempty
  equation : ∀ e (a : S.DomainAddress e),
    S.left e '' values (S.source e) (S.expressAddress e true a) =
    (fun v => b e + S.right e v) '' values (S.target e) (S.expressAddress e false a)

namespace SpecialImages
variable {S} {b : E → Bit} (I : S.SpecialImages b)

theorem chooseAt (A : Fin r → Bool) (p : P) (v : Fin (S.dimension p) → Bit)
    (hv : v ∈ I.values p A) :
    ∃ q : S.RealShift, (∀ p, q p ∈ I.values p A) ∧ q p = v := by
  classical
  choose q hq using fun p => I.nonempty p A
  refine ⟨Function.update q p v, ?_, by simp⟩
  intro p'
  by_cases hp : p' = p
  · subst p'; simpa using hv
  · simpa only [Function.update_of_ne hp] using hq p'

theorem scalar_mem (e : E) (a : S.DomainAddress e) (side : Bool) (q : S.RealShift)
    (hq : ∀ p, q p ∈ I.values p (S.expressAddress e side a)) :
    (if side then S.left e (q (S.source e)) else b e + S.right e (q (S.target e))) ∈
      S.left e '' I.values (S.source e) (S.expressAddress e true a) := by
  cases side with
  | false =>
    rw [I.equation]
    exact ⟨q (S.target e), hq _, rfl⟩
  | true => exact ⟨q (S.source e), hq _, rfl⟩

theorem scalar_preimage (e : E) (a : S.DomainAddress e) (side : Bool) (s : Bit)
    (hs : s ∈ S.left e '' I.values (S.source e) (S.expressAddress e true a)) :
    ∃ q : S.RealShift, (∀ p, q p ∈ I.values p (S.expressAddress e side a)) ∧
      (if side then S.left e (q (S.source e)) else b e + S.right e (q (S.target e))) = s := by
  cases side with
  | false =>
    rw [I.equation] at hs
    obtain ⟨v, hv, he⟩ := hs
    obtain ⟨q, hq, eq⟩ := I.chooseAt _ _ v hv
    refine ⟨q, hq, ?_⟩
    change b e + S.right e (q (S.target e)) = s
    rw [eq]
    exact he
  | true =>
    obtain ⟨v, hv, he⟩ := hs
    obtain ⟨q, hq, eq⟩ := I.chooseAt _ _ v hv
    refine ⟨q, hq, ?_⟩
    change S.left e (q (S.source e)) = s
    rw [eq]
    exact he

/-- The one constrained old wrapping component lifts even if it lies entirely
inside a wire and the new cut re-expresses it at the opposite real endpoint. -/
theorem wrapping_shift_extension {n : ℕ} (hr : 3 ≤ r) {U : Finset (S.layout n).Block}
    (hu : U.card ≤ r) (hw : (S.layout n).Wrapping (by omega) U)
    {cut cut' : E → Fin n} (hc : S.Avoids n U cut) (hc' : S.Avoids n U cut')
    {A A' : Fin r → Bool}
    (hA : (S.layout n).IsWrappingAddress U (S.align n cut) A)
    (hA' : (S.layout n).IsWrappingAddress U (S.align n cut') A')
    (q : S.RealShift) (hq : ∀ p, q p ∈ I.values p A) :
    ∃ q' : S.RealShift, (∀ p, q' p ∈ I.values p A') ∧
      ∀ h : (S.layout n).HName, Sum.inl h ∈ (S.layout n).names U →
        S.starShift n cut' b q' h.1 = S.starShift n cut b q h.1 := by
  classical
  have hpos : 0 < U.card := lt_of_lt_of_le (by omega) ((S.layout n).wrapping_card hr hw)
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
  let root := (S.layout n).blockRepresentative z
  have he (q' : S.RealShift) (l : S.Link n) (hl : l ∈ (S.layout n).usedLinks U) :
      (S.layout n).firstForm l (S.starShift n cut b q ((S.layout n).first l)) +
        (S.layout n).secondForm l (S.starShift n cut b q ((S.layout n).second l)) =
      (S.layout n).firstForm l (S.starShift n cut' b q' ((S.layout n).first l)) +
        (S.layout n).secondForm l (S.starShift n cut' b q' ((S.layout n).second l)) :=
    (S.starShift_link hc b q hl).trans (S.starShift_link hc' b q' hl).symm
  by_cases hre : ∃ (d : (S.layout n).Corner) (p : P),
      ((S.layout n).cornerGraph (by omega) U).Reachable root d ∧ d.1 = Sum.inl p
  · obtain ⟨d, p, hd, hdp⟩ := hre
    have hAA := S.wrapping_real_addresses hr hu hw hc hc' hA hA' hz hdp hd
    subst A'
    refine ⟨q, hq, ?_⟩
    intro h hh
    have hpath := hd.symm.trans ((S.layout n).wrapping_names_reachable hr hu hw hz hh).1
    have hbase : S.starShift n cut b q d.1 = S.starShift n cut' b q d.1 := by rw [hdp]; rfl
    exact (S.shift_agreement_reachable (by omega) _ _ (he q)
      (fun _ _ _ _ => rfl) hbase hpath).symm
  · have hn : S.NoRealFrom n (by omega) U root := by
      intro d hd p hp
      exact hre ⟨d, p, hd, hp⟩
    have htype : ∃ (e : E) (j : Fin (n + 1)), root.1 = Sum.inr (e, j) := by
      cases ht : root.1 with
      | inl p => exact (hn root (.refl root) p ht).elim
      | inr ej => exact ⟨ej.1, ej.2, rfl⟩
    obtain ⟨e, j, ht⟩ := htype
    let side := decide (S.onLeft n cut e j)
    let side' := decide (S.onLeft n cut' e j)
    have harm : S.arm n cut root.1 = some (e, side) := by rw [ht]; rfl
    have harm' : S.arm n cut' root.1 = some (e, side') := by rw [ht]; rfl
    obtain ⟨a, hAa, hAa'⟩ := S.wrapping_internal_addresses hr hu hw hc hc' hA hA' hz hn harm harm'
    let scalar : Bit := if side then S.left e (q (S.source e)) else b e + S.right e (q (S.target e))
    have hs := I.scalar_mem e a side q (by simpa only [← hAa] using hq)
    obtain ⟨q', hq', hscalar⟩ := I.scalar_preimage e a side' scalar hs
    refine ⟨q', by simpa only [← hAa'] using hq', ?_⟩
    intro h hh
    have hpath := ((S.layout n).wrapping_names_reachable hr hu hw hz hh).1
    have hbase : S.starShift n cut b q root.1 = S.starShift n cut' b q' root.1 := by
      rw [ht]
      funext k
      change (if S.onLeft n cut e j then _ else _) = (if S.onLeft n cut' e j then _ else _)
      simpa only [scalar, side, side', decide_eq_true_eq] using hscalar.symm
    exact (S.shift_agreement_reachable (by omega) _ _ (he q')
      (fun d hd p hp => (hn d hd p hp).elim) hbase hpath).symm

end SpecialImages
end ComparisonSchemas

namespace RingLayout
variable {r : ℕ} {T L : Type} (R : RingLayout r T L)

theorem translation_eq_of_shifts {U : Finset R.Block} (old new : R.Shift) (M : R.Potential)
    (he : ∀ h : R.HName, Sum.inl h ∈ R.names U → new h.1 = old h.1)
    {b : R.Block} (hb : b ∈ U) {c : R.Coordinate} (hc : c ∈ R.coordinates b) :
    R.translation new M c = R.translation old M c := by
  have hn := R.name_present hb (R.coordinate_name_mem hc)
  cases c with
  | inl h =>
    change (R.potentialHorizontal new M h.1) h.2 = (R.potentialHorizontal old M h.1) h.2
    unfold potentialHorizontal
    rw [he h.1 hn]
  | inr v => rfl

end RingLayout

namespace ComparisonSchemas.SpecialImages
variable {r : ℕ} {P E : Type} {S : ComparisonSchemas r P E} {b : E → Bit}
    (I : S.SpecialImages b)

/-- A stronger sufficient family using globally completed cut stars. Its
address restriction is imposed only by wrapping subcollections of size r. -/
def Admissible (n : ℕ) (hr : 2 ≤ r) (U : Finset (S.layout n).Block)
    (x : (S.layout n).Coordinate → Bit) : Prop :=
  U.card ≤ r + 1 ∧ ∃ cut : E → Fin n, S.Avoids n U cut ∧
    ∃ A : Fin r → Bool, S.GoodAddress n hr U cut A ∧
      ∃ q : S.RealShift, (∀ p, q p ∈ I.values p A) ∧
        ∃ M : (S.layout n).Potential, ∀ a ∈ U, ∀ c ∈ (S.layout n).coordinates a,
          x c = (S.layout n).translation (S.starShift n cut b q) M c

theorem admissible_nonempty {n : ℕ} (hr : 3 ≤ r) (hn : r + 1 < n)
    (U : Finset (S.layout n).Block) (hu : U.card ≤ r + 1) :
    ∃ x, I.Admissible n (by omega) U x := by
  classical
  obtain ⟨cut, hc⟩ := S.exists_cuts n U (lt_of_le_of_lt hu hn)
  obtain ⟨A, hA⟩ := S.goodAddress_exists n hr hu hc
  choose q hq using fun p => I.nonempty p A
  refine ⟨(S.layout n).translation (S.starShift n cut b q) (fun _ _ => 0),
    hu, cut, hc, A, hA, q, hq, (fun _ _ => 0), ?_⟩
  exact fun _ _ _ _ => rfl

theorem admissible_restrict {n : ℕ} {hr : 2 ≤ r} {U V : Finset (S.layout n).Block}
    {x : (S.layout n).Coordinate → Bit} (hVU : V ⊆ U) (hx : I.Admissible n hr U x) :
    I.Admissible n hr V x := by
  obtain ⟨hu, cut, hc, A, hA, q, hq, M, hM⟩ := hx
  exact ⟨(Finset.card_le_card hVU).trans hu, cut, S.avoids_mono hVU hc,
    A, S.goodAddress_mono hVU hA, q, hq, M, fun a ha => hM a (hVU ha)⟩

variable [Fintype P] [Fintype E]

theorem admissible_legal {n : ℕ} {hr : 2 ≤ r} {U : Finset (S.layout n).Block}
    {x : (S.layout n).Coordinate → Bit} (hx : I.Admissible n hr U x)
    {a : (S.layout n).Block} (ha : a ∈ U) :
    ((S.layout n).affine hr).Legal (S.specialTwist n b) a (((S.layout n).affine hr).restrict a x) := by
  obtain ⟨_, cut, hc, _, _, q, _, M, hM⟩ := hx
  have he : ((S.layout n).affine hr).restrict a x =
      ((S.layout n).affine hr).restrict a ((S.layout n).translation (S.starShift n cut b q) M) := by
    funext c
    exact hM a ha c.val c.property
  rw [he]
  exact S.translation_legal hc hr b q M ha

omit [Fintype P] [Fintype E] in
theorem admissible_extend {n : ℕ} (hr : 3 ≤ r) (hn : r + 1 < n)
    {U : Finset (S.layout n).Block} {x : (S.layout n).Coordinate → Bit}
    (hu : U.card < r + 1) (hx : I.Admissible n (by omega) U x) (z : (S.layout n).Block) :
    ∃ y, I.Admissible n (by omega) (insert z U) y ∧
      ∀ a ∈ U, ∀ c ∈ (S.layout n).coordinates a, y c = x c := by
  classical
  obtain ⟨_, cut, hc, A, hA, q, hq, M, hM⟩ := hx
  have hu' : U.card ≤ r := by omega
  have hnew : (insert z U).card ≤ r + 1 := by
    have := Finset.card_insert_le z U
    omega
  obtain ⟨cut', hc'⟩ := S.exists_cuts n (insert z U) (lt_of_le_of_lt hnew hn)
  obtain ⟨A', hA'⟩ := S.goodAddress_exists n hr hnew hc'
  have hsub : U ⊆ insert z U := Finset.subset_insert _ _
  have hc'U := S.avoids_mono hsub hc'
  have finish (q' : S.RealShift) (hq' : ∀ p, q' p ∈ I.values p A')
      (N : (S.layout n).Potential)
      (hN : ∀ a ∈ U, ∀ c ∈ (S.layout n).coordinates a,
        (S.layout n).translation (S.starShift n cut' b q') N c =
          (S.layout n).translation (S.starShift n cut b q) M c) :
      ∃ y, I.Admissible n (by omega) (insert z U) y ∧
        ∀ a ∈ U, ∀ c ∈ (S.layout n).coordinates a, y c = x c := by
    refine ⟨(S.layout n).translation (S.starShift n cut' b q') N,
      ⟨hnew, cut', hc', A', hA', q', hq', N, fun _ _ _ _ => rfl⟩, ?_⟩
    intro a ha c hc
    exact (hN a ha c hc).trans (hM a ha c hc).symm
  by_cases hw : (S.layout n).Wrapping (by omega) U
  · obtain ⟨q', hq', hshift⟩ := I.wrapping_shift_extension hr hu' hw hc hc'U
      (hA U (Finset.Subset.refl _) hu' hw) (hA' U hsub hu' hw) q hq
    apply finish q' hq' M
    intro a ha c hc
    exact (S.layout n).translation_eq_of_shifts _ _ M hshift ha hc
  · choose q' hq' using fun p => I.nonempty p A'
    obtain ⟨N, hN⟩ := (S.layout n).adjust_potential hr hw (S.starShift n cut b q)
      (S.starShift n cut' b q') M (fun l hl =>
        (S.starShift_link hc b q hl).trans (S.starShift_link hc'U b q' hl).symm)
    exact finish q' hq' N hN

/-- A proved producer of the exact-projection interface, not a hypothesis
asserting that local translations happen to extend. -/
noncomputable def offsetFamily {n : ℕ} (hr : 3 ≤ r) (hn : r + 1 < n) :
    ((S.layout n).affine (by omega)).OffsetFamily (S.specialTwist n b) (r + 1) where
  admissible := I.Admissible n (by omega)
  empty := I.admissible_nonempty hr hn ∅ (by simp)
  legal := fun hx _ ha => I.admissible_legal hx ha
  restrict := I.admissible_restrict
  extend := I.admissible_extend hr hn

end ComparisonSchemas.SpecialImages

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.BufferedCircuits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace BufferAlgebra

abbrev Vector := Fin 2 → Bit

def Determined {V : Type} (Q : Set V) (f : V → Bit) : Prop :=
  ∀ v ∈ Q, ∀ w ∈ Q, f v = f w

/-- Truth fixes a coordinate to zero; false coordinates remain free. -/
def truthVectors {J : Type} (t : J → Prop) : Set (J → Bit) :=
  {v | ∀ j, t j → v j = 0}

theorem truthVectors_nonempty {J : Type} (t : J → Prop) : (truthVectors t).Nonempty :=
  ⟨fun _ => 0, fun _ _ => rfl⟩

theorem projection_truth {J : Type} [DecidableEq J] (t : J → Prop) [DecidablePred t] (j : J) :
    (fun v => v j) '' truthVectors t = if t j then {0} else Set.univ := by
  classical
  by_cases hj : t j
  · rw [ite_eq_left hj]
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv j hj
    · intro hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      exact ⟨fun _ => 0, fun _ _ => rfl, rfl⟩
  · rw [ite_eq_right hj]
    apply Set.eq_univ_of_forall
    intro x
    refine ⟨Function.update (fun _ => 0) j x, ?_, by simp⟩
    intro i hi
    have hij : i ≠ j := by rintro rfl; exact hj hi
    simp [hij]

theorem sum_truth {J : Type} [Fintype J] (t : J → Prop) [DecidablePred t] :
    (fun v => ∑ j, v j) '' truthVectors t = if ∀ j, t j then {0} else Set.univ := by
  classical
  by_cases ht : ∀ j, t j
  · rw [ite_eq_left ht]
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      simp only [Set.mem_singleton_iff]
      exact Finset.sum_eq_zero (fun j _ => hv j (ht j))
    · intro hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      exact ⟨fun _ => 0, fun _ _ => rfl, by simp⟩
  · rw [ite_eq_right ht]
    obtain ⟨j, hj⟩ := not_forall.mp ht
    apply Set.eq_univ_of_forall
    intro x
    refine ⟨Function.update (fun _ => 0) j x, ?_, ?_⟩
    · intro i hi
      have hij : i ≠ j := by rintro rfl; exact hj hi
      simp [hij]
    · dsimp only
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij; simp [Function.update_of_ne hij]
      · simp

/-- Correlated coordinates keep both input images full while prescribing the sum. -/
def correlated (D : Set Bit) : Set Vector := {v | v 0 + v 1 ∈ D}

theorem correlated_nonempty {D : Set Bit} (hD : D.Nonempty) : (correlated D).Nonempty := by
  obtain ⟨d, hd⟩ := hD
  exact ⟨![0, d], by simpa [correlated] using hd⟩

theorem correlated_projection {D : Set Bit} (hD : D.Nonempty) (j : Fin 2) :
    (fun v => v j) '' correlated D = Set.univ := by
  obtain ⟨d, hd⟩ := hD
  apply Set.eq_univ_of_forall
  intro x
  fin_cases j
  · refine ⟨![x, d + x], ?_, by simp⟩
    simpa [correlated, add_assoc, add_comm, add_left_comm, CharTwo.add_self_eq_zero] using hd
  · refine ⟨![d + x, x], ?_, by simp⟩
    simpa [correlated, add_assoc, CharTwo.add_self_eq_zero] using hd

theorem correlated_sum (D : Set Bit) :
    (fun v => v 0 + v 1) '' correlated D = D := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩; exact hv
  · intro hx
    exact ⟨![0, x], by simpa [correlated] using hx, by simp⟩

end BufferAlgebra

/-- A componentwise injection on a nonempty Boolean product domain.
Values of `mapping` off the domain are immaterial. -/
structure ProductMap (r : ℕ) where
  domain : Fin r → Finset Bool
  nonempty : ∀ i, (domain i).Nonempty
  mapping : Fin r → Bool → Bool
  injective : ∀ i, Set.InjOn (mapping i) {x | x ∈ domain i}

namespace ProductMap
variable {r : ℕ}

def identity (r : ℕ) : ProductMap r where
  domain _ := Finset.univ
  nonempty _ := ⟨false, Finset.mem_univ _⟩
  mapping _ := id
  injective _ _ _ _ _ h := h

def flip (i : Fin r) : ProductMap r where
  domain _ := Finset.univ
  nonempty _ := ⟨false, Finset.mem_univ _⟩
  mapping j b := if j = i then !b else b
  injective j x _ y _ h := by
    by_cases hj : j = i
    · simpa only [hj, ite_true, Bool.not_not] using congrArg (fun b => !b) h
    · simpa only [hj, ite_false] using h

def identityOn (D : ProductMap r) : ProductMap r where
  domain := D.domain
  nonempty := D.nonempty
  mapping _ := id
  injective _ _ _ _ _ h := h

end ProductMap

structure ProductCircuit (r : ℕ) (P E Z T : Type) where
  pointIndex : P ↪ ℕ
  edgeIndex : E ↪ ℕ
  seedIndex : Z ↪ ℕ
  testIndex : T ↪ ℕ
  dimension : P → ℕ
  dimension_bound : ∀ p, dimension p = 1 ∨ dimension p = 2
  source : E → P
  target : E → P
  port : (e : E) → Fin (dimension (target e))
  edgeMap : E → ProductMap r
  seedType : Z → P
  seed_scalar : ∀ z, dimension (seedType z) = 1
  seedMap : Z → ProductMap r
  testType : T → P
  test_scalar : ∀ t, dimension (testType t) = 1
  testMap : T → ProductMap r

namespace ProductCircuit
variable {r : ℕ} {P E Z T : Type} (C : ProductCircuit r P E Z T)

abbrev Primary (_C : ProductCircuit r P E Z T) := Option P

abbrev primaryDimension : C.Primary → ℕ
  | none => 1
  | some p => C.dimension p

def sumForm (d : ℕ) : (Fin d → Bit) →ₗ[Bit] Bit := ∑ j, LinearMap.proj j

theorem sumForm_apply (d : ℕ) (v : Fin d → Bit) : sumForm d v = ∑ j, v j := by
  simp [sumForm]

inductive Connection where
  | original (e : E)
  | test (t : T)
  | flip (i : Fin r)
  | broadcast (p : P) (j : Fin (C.dimension p))
  | self (p : C.Primary) (j : Fin (C.primaryDimension p))
  | conflict
  deriving Fintype

abbrev connectionSource : C.Connection → C.Primary
  | .original e => some (C.source e)
  | .test t => some (C.testType t)
  | .flip _ => none
  | .broadcast _ _ => none
  | .self p _ => p
  | .conflict => none

abbrev connectionMap : C.Connection → ProductMap r
  | .original e => C.edgeMap e
  | .test t => (C.testMap t).identityOn
  | .flip i => .flip i
  | .broadcast _ _ => .identity r
  | .self _ _ => .identity r
  | .conflict => .identity r

abbrev sourceForm (l : C.Connection) : (Fin (C.primaryDimension (C.connectionSource l)) → Bit) →ₗ[Bit] Bit :=
  match l with
  | .original e => sumForm (C.dimension (C.source e))
  | .test t => sumForm (C.dimension (C.testType t))
  | .flip _ => LinearMap.proj (0 : Fin 1)
  | .broadcast _ _ => LinearMap.proj (0 : Fin 1)
  | .self _ j => LinearMap.proj j
  | .conflict => LinearMap.proj (0 : Fin 1)

inductive RealType where
  | primary (p : C.Primary)
  | buffer (l : C.Connection)
  | dummy
  deriving Fintype

inductive Comparison where
  | seed (z : Z)
  | first (l : C.Connection)
  | second (l : C.Connection)
  | third (l : C.Connection)
  deriving Fintype

abbrev realDimension : C.RealType → ℕ
  | .primary p => C.primaryDimension p
  | .buffer _ => 2
  | .dummy => 1

abbrev comparisonSource : C.Comparison → C.RealType
  | .seed z => .primary (some (C.seedType z))
  | .first l => .primary (C.connectionSource l)
  | .second l => .primary (C.connectionSource l)
  | .third l => .buffer l

abbrev comparisonMap : C.Comparison → ProductMap r
  | .seed z => (C.seedMap z).identityOn
  | .first l => (C.connectionMap l).identityOn
  | .second l => (C.connectionMap l).identityOn
  | .third l => C.connectionMap l

abbrev comparisonLeft (e : C.Comparison) :
    (Fin (C.realDimension (C.comparisonSource e)) → Bit) →ₗ[Bit] Bit :=
  match e with
  | .seed z => sumForm (C.dimension (C.seedType z))
  | .first l => C.sourceForm l
  | .second l => C.sourceForm l
  | .third _ => (LinearMap.proj (0 : Fin 2) : (Fin 2 → Bit) →ₗ[Bit] Bit) + LinearMap.proj (1 : Fin 2)

/-- Exactly seeds and three comparisons per private buffer, with two distinct
copies of A's full-product identity self-connection. -/
def connectionIndexValue : C.Connection → ℕ
  | .original e => Nat.pair 0 (C.edgeIndex e)
  | .test t => Nat.pair 1 (C.testIndex t)
  | .flip i => Nat.pair 2 i.val
  | .broadcast p j => Nat.pair 3 (Nat.pair (C.pointIndex p) j.val)
  | .self p j => Nat.pair 4 (Nat.pair (NaturalCode.option C.pointIndex p) j.val)
  | .conflict => Nat.pair 5 0

def connectionIndex : C.Connection ↪ ℕ where
  toFun := C.connectionIndexValue
  inj' := by
    intro a b h
    cases a <;> cases b <;>
      simp only [connectionIndexValue, Nat.pair_eq_pair, Nat.reduceEqDiff, false_and,
        true_and] at h
    · exact congrArg Connection.original (C.edgeIndex.injective h)
    · exact congrArg Connection.test (C.testIndex.injective h)
    · exact congrArg Connection.flip (Fin.ext h)
    · obtain ⟨hp,hj⟩ := h
      have he := C.pointIndex.injective hp
      subst_vars
      have he := Fin.ext hj
      subst_vars
      rfl
    · obtain ⟨hp,hj⟩ := h
      have he := (NaturalCode.option C.pointIndex).injective hp
      subst_vars
      have he := Fin.ext hj
      subst_vars
      rfl
    · rfl

def comparisonIndexValue : C.Comparison → ℕ
  | .seed z => Nat.pair 0 (C.seedIndex z)
  | .first l => Nat.pair 1 (C.connectionIndex l)
  | .second l => Nat.pair 2 (C.connectionIndex l)
  | .third l => Nat.pair 3 (C.connectionIndex l)

def comparisonIndex : C.Comparison ↪ ℕ where
  toFun := C.comparisonIndexValue
  inj' := by
    intro a b h
    cases a <;> cases b <;>
      simp only [comparisonIndexValue, Nat.pair_eq_pair, Nat.reduceEqDiff, false_and,
        true_and] at h
    · exact congrArg Comparison.seed (C.seedIndex.injective h)
    · exact congrArg Comparison.first (C.connectionIndex.injective h)
    · exact congrArg Comparison.second (C.connectionIndex.injective h)
    · exact congrArg Comparison.third (C.connectionIndex.injective h)

end ProductCircuit

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.BinaryAddresses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace BinaryAddress

abbrev Bits (d : ℕ) := Fin d → Bool

def value : {d : ℕ} → Bits d → ℕ
  | 0, _ => 0
  | _ + 1, v => (if v 0 then 1 else 0) + 2 * value (fun i => v i.succ)

@[simp] theorem value_nil (v : Bits 0) : value v = 0 := rfl
@[simp] theorem value_cons {d : ℕ} (b : Bool) (v : Bits d) :
    value (Fin.cons b v) = (if b then 1 else 0) + 2 * value v := rfl

@[simp] theorem value_zero (d : ℕ) : value (fun _ : Fin d => false) = 0 := by
  induction d with
  | zero => rfl
  | succ d ih => simp [value, ih]

@[simp] theorem value_one (d : ℕ) : value (fun _ : Fin d => true) + 1 = 2 ^ d := by
  induction d with
  | zero => simp [value]
  | succ d ih => simp only [value, ↓reduceIte, pow_succ]; omega

theorem value_lt {d : ℕ} (v : Bits d) : value v < 2 ^ d := by
  induction d with
  | zero => simp [value]
  | succ d ih =>
    have h := ih (fun i => v i.succ)
    simp only [value, pow_succ]
    split <;> omega

theorem value_injective (d : ℕ) : Function.Injective (@value d) := by
  induction d with
  | zero => intro v w _; exact Subsingleton.elim _ _
  | succ d ih =>
    intro v w h
    have hh : v 0 = w 0 := by
      cases h1 : v 0 <;> cases h2 : w 0 <;> simp_all [value] <;> omega
    have ht : (fun i : Fin d => v i.succ) = (fun i : Fin d => w i.succ) := by
      apply ih
      simp only [value, hh] at h
      omega
    funext i
    exact Fin.cases hh (fun j => congrFun ht j) i

theorem value_surjective (d : ℕ) (n : ℕ) (hn : n < 2 ^ d) : ∃ v : Bits d, value v = n := by
  induction d generalizing n with
  | zero => refine ⟨Fin.elim0, ?_⟩; simp only [pow_zero] at hn; simp [value]; omega
  | succ d ih =>
    have hdiv : n / 2 < 2 ^ d := by rw [pow_succ] at hn; omega
    obtain ⟨v, hv⟩ := ih (n / 2) hdiv
    refine ⟨Fin.cons (decide (n % 2 = 1)) v, ?_⟩
    simp only [value_cons, hv, decide_eq_true_eq]
    split <;> omega

noncomputable def equiv (d : ℕ) : Bits d ≃ Fin (2 ^ d) :=
  Equiv.ofBijective (fun v => ⟨value v, value_lt v⟩)
    ⟨fun _ _ h => value_injective d (congrArg Fin.val h), fun ⟨n, hn⟩ => by
      obtain ⟨v, hv⟩ := value_surjective d n hn
      exact ⟨v, Fin.ext hv⟩⟩

/-- Little-endian carry without converting or enumerating the address space. -/
def advance : {d : ℕ} → Bits d → Bits d
  | 0, v => v
  | _ + 1, v => Fin.cons (!(v 0))
      (if v 0 then advance (fun i => v i.succ) else fun i => v i.succ)

/-- Each carry case fixes just the low prefix, including its first noncarry bit. -/
def Carry {d : ℕ} (h : Fin d) (b : Bool) (v : Bits d) : Prop :=
  (∀ i, i < h → v i = b) ∧ v h = !b

def flipPrefix {d : ℕ} (h : Fin d) (v : Bits d) : Bits d :=
  fun i => if i ≤ h then !(v i) else v i

end BinaryAddress

namespace BinaryAddress

/-- The executable little-endian digit map; no search through 2^d addresses. -/
def ofNat : (d : ℕ) → ℕ → Bits d
  | 0, _ => Fin.elim0
  | d + 1, n => Fin.cons (decide (n % 2 = 1)) (ofNat d (n / 2))

theorem value_ofNat (d n : ℕ) (h : n < 2 ^ d) : value (ofNat d n) = n := by
  induction d generalizing n with
  | zero => simp only [pow_zero] at h; simp only [ofNat, value_nil]; omega
  | succ d ih =>
    have ht : n / 2 < 2 ^ d := by rw [pow_succ] at h; omega
    simp only [ofNat, value_cons, decide_eq_true_eq, ih _ ht]
    split <;> omega

@[simp] theorem ofNat_zero (d : ℕ) : ofNat d 0 = fun _ => false :=
  value_injective d (by rw [value_ofNat _ _ (by positivity), value_zero])

end BinaryAddress

namespace ProductMap
variable {r : ℕ}

/-- The relation described by a table, without enumerating its product points. -/
def Rel (D : ProductMap r) (x y : Fin r → Bool) : Prop :=
  (∀ i, x i ∈ D.domain i) ∧ ∀ i, D.mapping i (x i) = y i

def singleton (x y : Fin r → Bool) : ProductMap r where
  domain i := {x i}
  nonempty i := ⟨x i, by simp⟩
  mapping i _ := y i
  injective i _ hx _ hy _ := (Finset.mem_singleton.mp hx).trans (Finset.mem_singleton.mp hy).symm

@[simp] theorem singleton_rel (x y u v : Fin r → Bool) :
    (singleton x y).Rel u v ↔ u = x ∧ v = y := by
  simp only [Rel, singleton, Finset.mem_singleton]
  rw [← funext_iff, ← funext_iff, eq_comm (a := y)]

@[simp] theorem identity_rel (x y : Fin r → Bool) : (identity r).Rel x y ↔ x = y := by
  simp [Rel, identity, funext_iff]

def concat {a b : ℕ} (D : ProductMap a) (E : ProductMap b) : ProductMap (a + b) where
  domain := Fin.append D.domain E.domain
  nonempty i := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using D.nonempty j
    · simpa only [Fin.append_right] using E.nonempty j
  mapping := Fin.append D.mapping E.mapping
  injective i := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using D.injective j
    · simpa only [Fin.append_right] using E.injective j

@[simp] theorem concat_rel {a b : ℕ} (D : ProductMap a) (E : ProductMap b)
    (x y : Fin (a + b) → Bool) :
    (D.concat E).Rel x y ↔
      D.Rel (fun i => x (Fin.castAdd b i)) (fun i => y (Fin.castAdd b i)) ∧
      E.Rel (fun i => x (Fin.natAdd a i)) (fun i => y (Fin.natAdd a i)) := by
  simp only [Rel, concat, Fin.forall_fin_add, Fin.append_left, Fin.append_right]
  tauto

def inverse (D : ProductMap r) : ProductMap r where
  domain i := (D.domain i).image (D.mapping i)
  nonempty i := (D.nonempty i).image _
  mapping i b := if false ∈ D.domain i ∧ D.mapping i false = b then false else true
  injective := by
    intro i x hx y hy h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    by_cases he : a = b
    · rw [he]
    · cases a <;> cases b <;> simp_all [D.injective i ha hb]

@[simp] theorem inverse_rel (D : ProductMap r) (x y : Fin r → Bool) :
    D.inverse.Rel x y ↔ D.Rel y x := by
  have h (i : Fin r) (b : Bool) (hb : b ∈ D.domain i) :
      D.inverse.mapping i (D.mapping i b) = b := by
    cases b with
    | false => simp [inverse, hb]
    | true =>
      have hh : ¬ (false ∈ D.domain i ∧ D.mapping i false = D.mapping i true) := by
        rintro ⟨hfalse, he⟩
        have := D.injective i hfalse hb he
        contradiction
      dsimp only [inverse]
      rw [ite_eq_right hh]
  constructor
  · rintro ⟨hx, hy⟩
    have hy' (i : Fin r) : y i ∈ D.domain i ∧ D.mapping i (y i) = x i := by
      obtain ⟨a, ha, he⟩ := Finset.mem_image.mp (hx i)
      have hh := hy i
      rw [← he, h i a ha] at hh
      exact hh ▸ ⟨ha, he⟩
    exact ⟨fun i => (hy' i).1, fun i => (hy' i).2⟩
  · rintro ⟨hy, hx⟩
    exact ⟨fun i => Finset.mem_image.mpr ⟨y i, hy i, hx i⟩,
      fun i => by rw [← hx i, h i (y i) (hy i)]⟩

end ProductMap

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.AddressArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace BinaryAddress

def carryMap {d : ℕ} (h : Fin d) : ProductMap d where
  domain i := if i < h then {true} else if i = h then {false} else Finset.univ
  nonempty i := by split <;> first | exact Finset.singleton_nonempty _ | split <;> simp
  mapping i b := if i ≤ h then !b else b
  injective i _ _ _ _ he := by
    by_cases hi : i ≤ h
    · simpa only [hi, ite_true, Bool.not_not] using congrArg (fun b => !b) he
    · simpa only [hi, ite_false] using he

@[simp] theorem carryMap_rel {d : ℕ} (h : Fin d) (x y : Bits d) :
    (carryMap h).Rel x y ↔ Carry h true x ∧ y = flipPrefix h x := by
  change ((∀ i, x i ∈ if i < h then {true} else if i = h then {false} else Finset.univ) ∧
    (∀ i, (if i ≤ h then !(x i) else x i) = y i)) ↔ _
  have he : (∀ i, (if i ≤ h then !(x i) else x i) = y i) ↔ y = flipPrefix h x := by
    rw [← funext_iff, eq_comm]; rfl
  rw [he]
  apply and_congr_left
  intro _
  constructor
  · intro hv
    refine ⟨fun i hi => ?_, ?_⟩
    · simpa only [hi, ite_true, Finset.mem_singleton] using hv i
    · simpa using hv h
  · rintro ⟨hv, hh⟩ i
    by_cases hi : i < h
    · simp [hi, hv i hi]
    · by_cases he : i = h
      · subst i; simpa using hh
      · simp [hi, he]

/-- An additional all-ones case supplies the cyclic seam for positions only. -/
def cycleMap (d : ℕ) : Option (Fin d) → ProductMap d
  | none => ProductMap.singleton (fun _ => true) (fun _ => false)
  | some h => carryMap h

noncomputable def rotation (d : ℕ) : Bits d ≃ Bits d :=
  (equiv d).trans ((finRotate (2 ^ d)).trans (equiv d).symm)

end BinaryAddress

namespace BinaryAddress

/-- A threshold request fixes its high prefix and first strictly-larger bit. -/
def aboveMap {d : ℕ} (x : Bits d) (h : Fin d) : ProductMap d where
  domain i := if h < i then {x i} else if i = h then {true} else Finset.univ
  nonempty i := by split <;> first | exact Finset.singleton_nonempty _ | split <;> simp
  mapping _ b := b
  injective _ _ _ _ _ he := he

@[simp] theorem aboveMap_rel {d : ℕ} (x : Bits d) (h : Fin d) (y z : Bits d) :
    (aboveMap x h).Rel y z ↔ y = z ∧ y h = true ∧ ∀ i, h < i → y i = x i := by
  change ((∀ i, y i ∈ if h < i then {x i} else if i = h then {true} else Finset.univ) ∧
    ∀ i, y i = z i) ↔ _
  rw [← funext_iff]
  constructor
  · rintro ⟨hy, rfl⟩
    exact ⟨rfl, by simpa using hy h, fun i hi => by simpa [hi] using hy i⟩
  · rintro ⟨rfl, hh, hhi⟩
    refine ⟨fun i => ?_, rfl⟩
    by_cases hi : h < i
    · simp [hi, hhi i hi]
    · by_cases he : i = h
      · subst i; simp [hh]
      · simp [hi, he]

abbrev ThresholdCase {d : ℕ} (x : Bits d) := Option {h : Fin d // x h = false}

def thresholdMap {d : ℕ} (x : Bits d) : ThresholdCase x → ProductMap d
  | none => ProductMap.singleton x x
  | some h => aboveMap x h.val

end BinaryAddress

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.CellularCircuits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace CellularCircuit
open BinaryAddress
variable {d : ℕ} {A Z : Type}

abbrev Address (d : ℕ) := Bits (d + d)
def time (x : Address d) : Bits d := fun i => x (Fin.castAdd d i)
def position (x : Address d) : Bits d := fun i => x (Fin.natAdd d i)
def address (t j : Bits d) : Address d := Fin.append t j

@[simp] theorem time_address (t j : Bits d) : time (address t j) = t := by funext i; exact Fin.append_left t j i
@[simp] theorem position_address (t j : Bits d) : position (address t j) = j := by funext i; exact Fin.append_right t j i
@[simp] theorem address_parts (x : Address d) : address (time x) (position x) = x := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · exact Fin.append_left (time x) (position x) j
  · exact Fin.append_right (time x) (position x) j

inductive Gate (A : Type) where
  | scalar (f : A)
  | first (a b c : A)
  | second (a b c : A)
  deriving Fintype, DecidableEq

abbrev dimension : Gate A → ℕ
  | .scalar _ => 1
  | .first _ _ _ => 2
  | .second _ _ _ => 2

inductive Connection (d : ℕ) (A : Type) where
  | left (a b c : A) (h : Fin d) (j : Option (Fin d))
  | center (a b c : A) (h : Fin d)
  | right (a b c : A) (h : Fin d) (j : Option (Fin d))
  | join (a b c : A)
  | output (a b c : A)
  deriving DecidableEq

abbrev ConnectionCode (d : ℕ) (A : Type) :=
  (A × A × A) × ((Fin d × Option (Fin d)) ⊕
    (Fin d ⊕ ((Fin d × Option (Fin d)) ⊕ (Unit ⊕ Unit))))

def Connection.encode : Connection d A → ConnectionCode d A
  | .left a b c h j => ((a, b, c), .inl (h, j))
  | .center a b c h => ((a, b, c), .inr (.inl h))
  | .right a b c h j => ((a, b, c), .inr (.inr (.inl (h, j))))
  | .join a b c => ((a, b, c), .inr (.inr (.inr (.inl ()))))
  | .output a b c => ((a, b, c), .inr (.inr (.inr (.inr ()))))

def Connection.decode : ConnectionCode d A → Connection d A
  | ((a, b, c), .inl (h, j)) => .left a b c h j
  | ((a, b, c), .inr (.inl h)) => .center a b c h
  | ((a, b, c), .inr (.inr (.inl (h, j)))) => .right a b c h j
  | ((a, b, c), .inr (.inr (.inr (.inl _)))) => .join a b c
  | ((a, b, c), .inr (.inr (.inr (.inr _)))) => .output a b c

def Connection.equiv : Connection d A ≃ ConnectionCode d A where
  toFun := Connection.encode
  invFun := Connection.decode
  left_inv e := by cases e <;> rfl
  right_inv e := by
    rcases e with ⟨⟨a, b, c⟩, e⟩
    rcases e with ⟨h, j⟩ | e
    · rfl
    rcases e with h | e
    · rfl
    rcases e with ⟨h, j⟩ | e
    · rfl
    rcases e with u | u <;> cases u <;> rfl

instance instFintypeConnection [Fintype A] : Fintype (Connection d A) := Fintype.ofEquiv _ Connection.equiv.symm

@[simp] theorem card_connection [Fintype A] : Fintype.card (Connection d A) =
    Fintype.card A ^ 3 * (2 * d ^ 2 + 3 * d + 2) := by
  rw [Fintype.card_congr Connection.equiv]
  simp only [ConnectionCode, Fintype.card_prod, Fintype.card_sum, Fintype.card_option,
    Fintype.card_fin, Fintype.card_unit]
  ring

abbrev source : Connection d A → Gate A
  | .left a _ _ _ _ => .scalar a
  | .center _ b _ _ => .scalar b
  | .right _ _ c _ _ => .scalar c
  | .join a b c => .first a b c
  | .output a b c => .second a b c

abbrev target (F : A → A → A → A) : Connection d A → Gate A
  | .left a b c _ _ => .first a b c
  | .center a b c _ => .first a b c
  | .right a b c _ _ => .second a b c
  | .join a b c => .second a b c
  | .output a b c => .scalar (F a b c)

abbrev port (F : A → A → A → A) (e : Connection d A) : Fin (dimension (target F e)) :=
  match e with
  | .left _ _ _ _ _ => 0
  | .center _ _ _ _ => 1
  | .right _ _ _ _ _ => 1
  | .join _ _ _ => 0
  | .output _ _ _ => 0

def edgeMap : Connection d A → ProductMap (d + d)
  | .left _ _ _ h j => (carryMap h).concat (cycleMap d j)
  | .center _ _ _ h => (carryMap h).concat (ProductMap.identity d)
  | .right _ _ _ h j => (carryMap h).concat (cycleMap d j).inverse
  | .join _ _ _ => ProductMap.identity _
  | .output _ _ _ => ProductMap.identity _

variable (F : A → A → A → A) (seedLetter : Z → A) (seedDomain : Z → ProductMap d)
    (accept : A → Prop)

variable [Fintype A] [Fintype Z]

noncomputable def gateIndexValue : Gate A → ℕ
  | .scalar a => Nat.pair 0 (NaturalCode.fixed A a)
  | .first a b c => Nat.pair 1 (Nat.pair (NaturalCode.fixed A a) (Nat.pair (NaturalCode.fixed A b) (NaturalCode.fixed A c)))
  | .second a b c => Nat.pair 2 (Nat.pair (NaturalCode.fixed A a) (Nat.pair (NaturalCode.fixed A b) (NaturalCode.fixed A c)))

noncomputable def gateIndex : Gate A ↪ ℕ where
  toFun := gateIndexValue
  inj' := by
    intro a b h
    cases a <;> cases b <;>
      simp only [gateIndexValue, Nat.pair_eq_pair, Nat.reduceEqDiff, false_and,
        true_and, (NaturalCode.fixed A).injective.eq_iff] at h
    all_goals simp_all

noncomputable def connectionIndex : Connection d A ↪ ℕ :=
  Connection.equiv.toEmbedding.trans (NaturalCode.prod
    (NaturalCode.prod (NaturalCode.fixed A) (NaturalCode.prod (NaturalCode.fixed A) (NaturalCode.fixed A)))
    (NaturalCode.sum (NaturalCode.prod (NaturalCode.fin d) (NaturalCode.option (NaturalCode.fin d)))
      (NaturalCode.sum (NaturalCode.fin d)
        (NaturalCode.sum (NaturalCode.prod (NaturalCode.fin d) (NaturalCode.option (NaturalCode.fin d)))
          (NaturalCode.sum NaturalCode.unit NaturalCode.unit)))))

noncomputable abbrev circuit : ProductCircuit (d + d) (Gate A) (Connection d A) Z {f : A // accept f} where
  pointIndex := gateIndex
  edgeIndex := connectionIndex
  seedIndex := NaturalCode.fixed Z
  testIndex := NaturalCode.subtype (NaturalCode.fixed A) _
  dimension := dimension
  dimension_bound p := by cases p <;> simp
  source := source
  target := target F
  port := port F
  edgeMap := edgeMap
  seedType z := .scalar (seedLetter z)
  seed_scalar _ := rfl
  seedMap z := (ProductMap.singleton (fun _ => false) (fun _ => false)).concat (seedDomain z)
  testType f := .scalar f.val
  test_scalar _ := rfl
  testMap _ := (ProductMap.singleton (fun _ => true) (fun _ => true)).concat (ProductMap.identity d)

/-- A genuine synchronous radius-one automaton on the cyclic address alphabet. -/
noncomputable def evolution (init : Bits d → A) : ℕ → Bits d → A
  | 0 => init
  | t + 1 => fun j => F (evolution init t ((rotation d).symm j))
      (evolution init t j) (evolution init t (rotation d j))

variable (init : Bits d → A)

/-- The intended input-port semantics; only scalar gates can be seeds. -/
noncomputable def SemPort : (p : Gate A) → Address d → Fin (dimension p) → Prop
  | .scalar f, x, _ => f = evolution F init (value (time x)) (position x)
  | .first a b _, x, i => 0 < value (time x) ∧
      if i = 0 then a = evolution F init (value (time x) - 1) ((rotation d).symm (position x))
      else b = evolution F init (value (time x) - 1) (position x)
  | .second a b c, x, i => 0 < value (time x) ∧
      if i = 0 then
        a = evolution F init (value (time x) - 1) ((rotation d).symm (position x)) ∧
        b = evolution F init (value (time x) - 1) (position x)
      else c = evolution F init (value (time x) - 1) (rotation d (position x))

variable {F init}

variable (F init)

/-- Exact compressed initialization, to be instantiated by singletons plus
at most d+1 threshold domains below. -/
def SeedCorrect : Prop := ∀ f x,
  (∃ z y, seedLetter z = f ∧ (seedDomain z).Rel x y) ↔ f = init x

end CellularCircuit

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.MachineCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace Machine

abbrev State (M : Machine) := Fin (M.extraStates + 3)
abbrev Symbol (M : Machine) := Fin (M.extraSymbols + 3)

/-- Extend the finite transition table by its stipulated frozen halts. -/
def action (M : Machine) (q : M.State) (a : M.Symbol) : M.State × M.Symbol × Move :=
  if q = 1 ∨ q = 2 then (q, a, .stay) else M.transition q a

@[simp] theorem action_halt (M : Machine) (q : M.State) (a : M.Symbol)
    (h : q = 1 ∨ q = 2) : M.action q a = (q, a, .stay) := ite_eq_left h

/-- The same head/tape representation on any cyclic position alphabet. -/
structure TapeConfig (M : Machine) (X : Type) where
  state : M.State
  head : X
  tape : X → M.Symbol

namespace TapeConfig
variable {M : Machine} {X : Type} [DecidableEq X]

def advance (e : X ≃ X) (c : M.TapeConfig X) : M.TapeConfig X :=
  let a := M.action c.state (c.tape c.head)
  { state := a.1
    head := match a.2.2 with
      | .left => e.symm c.head
      | .stay => c.head
      | .right => e c.head
    tape := Function.update c.tape c.head a.2.1 }

end TapeConfig

/-- The literal input convention, transferred to a finite line segment. -/
def ringInitial (M : Machine) {d : ℕ} (w : Word) : M.TapeConfig (BinaryAddress.Bits d) where
  state := 0
  head := fun _ => false
  tape j := (w[BinaryAddress.value j]?).elim 0 (inputSymbol M)

noncomputable def ringRun (M : Machine) {d : ℕ} (w : Word) (t : ℕ) :
    M.TapeConfig (BinaryAddress.Bits d) :=
  (TapeConfig.advance (BinaryAddress.rotation d))^[t] (M.ringInitial w)

end Machine

namespace Machine
open BinaryAddress

@[simp] theorem ringRun_zero (M : Machine) {d : ℕ} (w : Word) :
    @ringRun M d w 0 = M.ringInitial w := rfl

@[simp] theorem ringRun_succ (M : Machine) {d : ℕ} (w : Word) (t : ℕ) :
    @ringRun M d w (t + 1) = (M.ringRun w t).advance (rotation d) :=
  Function.iterate_succ_apply' _ _ _

end Machine

namespace BinaryAddress

def residue (d : ℕ) (z : ℤ) : Bits d := ofNat d (z % (2 ^ d : ℕ)).toNat

@[simp] theorem residue_zero (d : ℕ) : residue d 0 = fun _ => false := by
  simp [residue]

end BinaryAddress

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.MachineReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace Machine
open BinaryAddress

@[simp] theorem run_succ (M : Machine) (w : Word) (t : ℕ) :
    run M w (t + 1) = step M (run M w t) := Function.iterate_succ_apply' _ _ _

end Machine

@[ext (iff := false)] theorem Graph.ext (G H : Graph) (hn : G.order = H.order)
    (he : ∀ i j, G.edge i j = H.edge (i.cast hn) (j.cast hn)) : G = H := by
  cases G with | mk n e hs hl =>
    cases H with | mk m f ht hm =>
      simp only at hn
      subst m
      have : e = f := by funext i j; exact he i j
      subst f
      rfl

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.StackMachines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

/- A finite-alphabet parallel-stack interpreter, with local one-tape execution.
All stored registers below range over a fixed finite type; no unbounded value is
hidden in a transition table. The only unbounded data are the literal bit stk. -/
namespace StackModel

inductive Instruction (K Λ R : Type) where
  | push (k : K) (value : R → Bool) (next : Λ)
  | pop (k : K) (store : R → Option Bool → R) (next : Λ)
  | modify (store : R → R) (next : Λ)
  | branch (test : R → Bool) (yes no : Λ)
  | halt (accept : Bool)

structure Program (K Λ R : Type) where
  code : Λ → Instruction K Λ R
  main : Λ
  initialStore : R

structure Config (K Λ R : Type) where
  control : Bool ⊕ Λ
  store : R
  stk : K → List Bool

variable {K Λ R : Type} [DecidableEq K]

def step (P : Program K Λ R) (c : Config K Λ R) : Config K Λ R :=
  match c.control with
  | .inl _ => c
  | .inr l => match P.code l with
    | .push k value next => ⟨.inr next, c.store,
        Function.update c.stk k (c.stk k ++ [value c.store])⟩
    | .pop k store next => ⟨.inr next, store c.store (c.stk k).getLast?,
        Function.update c.stk k (c.stk k).dropLast⟩
    | .modify store next => ⟨.inr next, store c.store, c.stk⟩
    | .branch test yes no => ⟨.inr (if test c.store then yes else no), c.store, c.stk⟩
    | .halt b => ⟨.inl b, c.store, c.stk⟩

abbrev Alphabet (K : Type) := Option (K → Option Bool)

inductive Phase (K Λ R : Type) where
  | init
  | ready (label : Λ) (store : R)
  | push (stack : K) (label : Λ) (store : R) (value : Bool)
  | pop (stack : K) (label : Λ) (store : Option Bool → R)
  | read (stack : K) (label : Λ) (store : Option Bool → R)
  | back (label : Λ) (store : R)
  deriving Fintype

variable [Fintype K] [Fintype Λ] [Fintype R]

def emptyData : K → Option Bool := fun _ => none

def inputData (input : K) (b : Bool) : K → Option Bool :=
  Function.update emptyData input (some b)

noncomputable def symbol (input : K) (a : Alphabet K) : Fin (Fintype.card (Alphabet K) + 3) := by
  classical
  exact if a = some emptyData then 0 else if a = some (inputData input false) then 1
    else if a = some (inputData input true) then 2 else
      ⟨3 + (Fintype.equivFin (Alphabet K) a).val, by have := (Fintype.equivFin (Alphabet K) a).isLt; omega⟩

noncomputable def decodeSymbol (input : K) (a : Fin (Fintype.card (Alphabet K) + 3)) : Alphabet K :=
  if h0 : a.val = 0 then some emptyData else if h1 : a.val = 1 then some (inputData input false)
  else if h2 : a.val = 2 then some (inputData input true) else
    (Fintype.equivFin (Alphabet K)).symm ⟨a.val - 3, by omega⟩

@[simp] theorem symbol_empty (input : K) : symbol input (some emptyData) = 0 := by
  classical simp [symbol]

@[simp] theorem symbol_input (input : K) (b : Bool) : symbol input (some (inputData input b)) =
    if b then 2 else 1 := by
  classical
  have he : inputData input b ≠ emptyData := by
    intro h
    have := congrFun h input
    simp [inputData, emptyData] at this
  have hne : inputData input true ≠ inputData input false := by
    intro h
    have := congrFun h input
    simp [inputData] at this
  cases b <;> simp [symbol, he, hne]

noncomputable def state (p : Phase K Λ R) : Fin (Fintype.card (Phase K Λ R) + 3) :=
  ⟨3 + (Fintype.equivFin (Phase K Λ R) p).val, by have := (Fintype.equivFin (Phase K Λ R) p).isLt; omega⟩

omit [DecidableEq K] in
@[simp] theorem state_ne_one (p : Phase K Λ R) : state p ≠ 1 := by
  intro h; have := congrArg Fin.val h; simp only [state, Fin.val_one] at this; omega
omit [DecidableEq K] in
@[simp] theorem state_ne_two (p : Phase K Λ R) : state p ≠ 2 := by
  intro h; have := congrArg Fin.val h; simp only [state, Fin.val_two] at this; omega

noncomputable def dispatch (P : Program K Λ R) (input : K) (p : Phase K Λ R)
    (a : Fin (Fintype.card (Alphabet K) + 3)) :
    Fin (Fintype.card (Phase K Λ R) + 3) × Fin (Fintype.card (Alphabet K) + 3) × Move :=
  match p with
  | .init => (state (.ready P.main P.initialStore), symbol input none, .right)
  | .ready label s => match P.code label with
    | .push k value next => (state (.push k next s (value s)), a, .stay)
    | .pop k store next => (state (.pop k next (store s)), a, .stay)
    | .modify store next => (state (.ready next (store s)), a, .stay)
    | .branch test yes no => (state (.ready (if test s then yes else no) s), a, .stay)
    | .halt b => (if b then 1 else 2, a, .stay)
  | .push k next s value => match decodeSymbol input a with
    | none => (state p, a, .stay)
    | some d => if (d k).isSome then (state p, a, .right) else
        (state (.back next s), symbol input (some (Function.update d k (some value))), .left)
  | .pop k next store => match decodeSymbol input a with
    | none => (state p, a, .stay)
    | some d => if (d k).isSome then (state p, a, .right) else
        (state (.read k next store), a, .left)
  | .read k next store => match decodeSymbol input a with
    | none => (state (.ready next (store none)), a, .right)
    | some d => (state (.back next (store (d k))), symbol input (some (Function.update d k none)), .left)
  | .back next s => match decodeSymbol input a with
    | none => (state (.ready next s), a, .right)
    | some _ => (state p, a, .left)

/-- A concrete finite local table, using only the three frozen I/O codes and
finitely many fixed extra symbols and states. -/
noncomputable abbrev compile (P : Program K Λ R) (input : K) : Machine where
  extraSymbols := Fintype.card (Alphabet K)
  extraStates := Fintype.card (Phase K Λ R)
  transition q a := if q.val = 0 then (state .init, a, .left) else
    if h : 3 ≤ q.val then
      dispatch P input ((Fintype.equivFin (Phase K Λ R)).symm ⟨q.val - 3, by omega⟩) a
    else (q, a, .stay)

@[simp] theorem transition_state (P : Program K Λ R) (input : K) (p : Phase K Λ R)
    (a : Fin (Fintype.card (Alphabet K) + 3)) :
    (compile P input).transition (state p) a = dispatch P input p a := by
  simp [compile, state]

def column (S : K → Word) (n : ℕ) : K → Option Bool := fun k => (S k)[n]?

noncomputable def tape (input : K) (S : K → Word) (z : ℤ) : Fin (Fintype.card (Alphabet K) + 3) :=
  if z = -1 then symbol input none else
    symbol input (some (if 0 ≤ z then column S z.toNat else emptyData))

@[simp] theorem tape_marker (input : K) (S : K → Word) : tape input S (-1) = symbol input none := by
  simp [tape]

@[simp] theorem tape_nat (input : K) (S : K → Word) (n : ℕ) :
    tape input S n = symbol input (some (column S n)) := by
  simp [tape]

end StackModel

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.BoundedWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace BoundedWords.Program
variable {K : Type} [DecidableEq K]

@[simp] theorem elim_empty {A B : Type} :
    Sum.elim (fun _ : A => ([] : Word)) (fun _ : B => []) = fun _ => [] := by
  funext x; cases x <;> rfl

end BoundedWords.Program

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.WordExpressions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace WordExpressions

/-- A finite, first-order word language. Loops capture a word length; their
body sees both a unary iteration index and the previous accumulator. -/
inductive Expr : ℕ → Type where
  | var {n} (i : Fin n) : Expr n
  | nil {n} : Expr n
  | snoc {n} (e : Expr n) (b : Bool) : Expr n
  | drop {n} (e : Expr n) : Expr n
  | cases {n} (e empty zero one : Expr n) : Expr n
  | bind {n} (e : Expr n) (f : Expr (n+1)) : Expr n
  | loop {n} (count init : Expr n) (body : Expr (n+2)) : Expr n

namespace Expr

def stages {n} (f : (Fin (n+2) → Word) → Word) (S : Fin n → Word) (a : Word) : ℕ → Word
  | 0 => a
  | i+1 => f (Fin.snoc (Fin.snoc S (List.replicate i false)) (stages f S a i))

def eval : {n : ℕ} → Expr n → (Fin n → Word) → Word
  | _, .var i, S => S i
  | _, .nil, _ => []
  | _, .snoc e b, S => e.eval S ++ [b]
  | _, .drop e, S => (e.eval S).dropLast
  | _, .cases e p q r, S => match (e.eval S).getLast? with
      | none => p.eval S
      | some false => q.eval S
      | some true => r.eval S
  | _, .bind e f, S => f.eval (Fin.snoc S (e.eval S))
  | _, .loop c a f, S => stages f.eval S (a.eval S) (c.eval S).length

def Bounded : {n : ℕ} → Expr n → (Fin n → Word) → ℕ → Prop
  | _, .var i, S, B => (S i).length ≤ B
  | _, .nil, _, _ => True
  | _, .snoc e b, S, B => e.Bounded S B ∧ (e.eval S ++ [b]).length ≤ B
  | _, .drop e, S, B => e.Bounded S B
  | _, .cases e p q r, S, B => e.Bounded S B ∧ match (e.eval S).getLast? with
      | none => p.Bounded S B
      | some false => q.Bounded S B
      | some true => r.Bounded S B
  | _, .bind e f, S, B => e.Bounded S B ∧ f.Bounded (Fin.snoc S (e.eval S)) B
  | _, .loop c a f, S, B => c.Bounded S B ∧ a.Bounded S B ∧
      ∀ i < (c.eval S).length, f.Bounded (Fin.snoc (Fin.snoc S (List.replicate i false))
        (stages f.eval S (a.eval S) i)) B

theorem length_le {n} (e : Expr n) (S : Fin n → Word) (B : ℕ) (h : e.Bounded S B) :
    (e.eval S).length ≤ B := by
  induction e with
  | var i => exact h
  | nil => exact Nat.zero_le _
  | snoc e b _ => exact h.2
  | drop e ih => exact (by simpa only [eval, List.length_dropLast] using
      (Nat.sub_le _ 1).trans (ih S h))
  | cases e p q r _ hp hq hr =>
    dsimp only [eval]
    cases he : (e.eval S).getLast? with
    | none => exact hp S (by simpa only [Bounded, he] using h.2)
    | some b => cases b with
      | false => exact hq S (by simpa only [Bounded, he] using h.2)
      | true => exact hr S (by simpa only [Bounded, he] using h.2)
  | bind e f _ hf => exact hf _ h.2
  | loop c a f _ ha hf =>
    have hb : ∀ j ≤ (c.eval S).length, (stages f.eval S (a.eval S) j).length ≤ B := by
      intro j hj
      cases j with
      | zero => exact ha S h.2.1
      | succ j => exact hf _ (h.2.2 j (by omega))
    exact hb _ le_rfl

end Expr
end WordExpressions

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.ExpressionCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace ComputationBounds

def Polynomial (f : ℕ → ℕ) : Prop := ∃ C d : ℕ, ∀ n, f n ≤ C*(n+1)^d

theorem constant (c : ℕ) : Polynomial (fun _ => c) := ⟨c, 0, by simp⟩
theorem identity : Polynomial id := ⟨1, 1, by intro n; simp⟩

theorem add {f g} (hf : Polynomial f) (hg : Polynomial g) : Polynomial (fun n => f n+g n) := by
  obtain ⟨C,d,hf⟩ := hf
  obtain ⟨D,e,hg⟩ := hg
  refine ⟨C+D, max d e, ?_⟩
  intro n
  have h1 := (hf n).trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_right (by omega) (le_max_left d e)))
  have h2 := (hg n).trans (Nat.mul_le_mul_left D (Nat.pow_le_pow_right (by omega) (le_max_right d e)))
  nlinarith

theorem mul {f g} (hf : Polynomial f) (hg : Polynomial g) : Polynomial (fun n => f n*g n) := by
  obtain ⟨C,d,hf⟩ := hf
  obtain ⟨D,e,hg⟩ := hg
  refine ⟨C*D, d+e, ?_⟩
  intro n
  have hh := Nat.mul_le_mul (hf n) (hg n)
  calc
    f n*g n ≤ (C*(n+1)^d)*(D*(n+1)^e) := hh
    _ = (C*D)*(n+1)^(d+e) := by rw [pow_add]; ring

end ComputationBounds

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.ExpressionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace ComputationBounds

theorem compose {f g : ℕ → ℕ} (hf : Polynomial f) (hg : Polynomial g) :
    Polynomial (fun n => f (g n)) := by
  obtain ⟨C,d,hf⟩ := hf
  obtain ⟨D,e,hg⟩ := hg
  refine ⟨C*(D+1)^d, e*d, ?_⟩
  intro n
  have hn : 1 ≤ (n+1)^e := Nat.one_le_pow _ _ (by omega)
  have hh : g n+1 ≤ (D+1)*(n+1)^e := by have := hg n; nlinarith
  calc
    f (g n) ≤ C*(g n+1)^d := hf _
    _ ≤ C*((D+1)*(n+1)^e)^d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hh _)
    _ = C*(D+1)^d*(n+1)^(e*d) := by rw [mul_pow, ← pow_mul]; ring

end ComputationBounds

namespace WordExpressions.Expr

def liftRen {n m} (r : Fin n → Fin m) : Fin (n+1) → Fin (m+1) :=
  Fin.snoc (Fin.castSucc ∘ r) (Fin.last m)

def rename : {n m : ℕ} → (Fin n → Fin m) → Expr n → Expr m
  | _, _, r, .var i => .var (r i)
  | _, _, _, .nil => .nil
  | _, _, r, .snoc e b => .snoc (e.rename r) b
  | _, _, r, .drop e => .drop (e.rename r)
  | _, _, r, .cases e p q s => .cases (e.rename r) (p.rename r) (q.rename r) (s.rename r)
  | _, _, r, .bind e f => .bind (e.rename r) (f.rename (liftRen r))
  | _, _, r, .loop c a f => .loop (c.rename r) (a.rename r) (f.rename (liftRen (liftRen r)))

theorem snoc_liftRen {n m} (r : Fin n → Fin m) (S : Fin m → Word) (a : Word) :
    Fin.snoc S a ∘ liftRen r = Fin.snoc (S ∘ r) a := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [liftRen]

theorem stages_rename {n m} (r : Fin n → Fin m)
    (f : (Fin (n+2) → Word) → Word) (g : (Fin (m+2) → Word) → Word)
    (h : ∀ S, g S = f (S ∘ liftRen (liftRen r))) (S : Fin m → Word) (a : Word) (k : ℕ) :
    stages g S a k = stages f (S ∘ r) a k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [stages, h, snoc_liftRen, ih]

@[simp] theorem eval_rename {n m} (e : Expr n) (r : Fin n → Fin m) (S : Fin m → Word) :
    (e.rename r).eval S = e.eval (S ∘ r) := by
  induction e generalizing m with
  | var i | nil => rfl
  | snoc e b ih | drop e ih => simp only [rename, eval, ih]
  | cases e p q s he hp hq hs =>
    simp only [rename, eval, he]
    cases (e.eval (S ∘ r)).getLast? with
    | none => exact hp _ _
    | some b => cases b <;> first | exact hq _ _ | exact hs _ _
  | bind e f he hf => simp only [rename, eval, he, hf, snoc_liftRen]
  | loop c a f hc ha hf =>
    simp only [rename, eval, hc, ha]
    exact stages_rename r _ _ (hf _) _ _ _

@[simp] theorem bounded_rename {n m} (e : Expr n) (r : Fin n → Fin m) (S : Fin m → Word) (B : ℕ) :
    (e.rename r).Bounded S B ↔ e.Bounded (S ∘ r) B := by
  induction e generalizing m with
  | var i | nil => rfl
  | snoc e b ih => simp only [rename, Bounded, ih, eval_rename]
  | drop e ih => exact ih _ _
  | cases e p q s he hp hq hs =>
    simp only [rename, Bounded, he, eval_rename]
    cases (e.eval (S ∘ r)).getLast? with
    | none => rw [hp]
    | some b => cases b <;> simp only [hq, hs]
  | bind e f he hf => simp only [rename, Bounded, he, hf, eval_rename, snoc_liftRen]
  | loop c a f hc ha hf =>
    simp only [rename, Bounded, hc, ha, hf, eval_rename, snoc_liftRen,
      stages_rename r f.eval (f.rename (liftRen (liftRen r))).eval (fun S => eval_rename _ _ S)]

theorem bounded_mono {n} (e : Expr n) {S B D} (h : e.Bounded S B) (hBD : B ≤ D) :
    e.Bounded S D := by
  induction e with
  | var i => exact h.trans hBD
  | nil => trivial
  | snoc e b ih => exact ⟨ih h.1, h.2.trans hBD⟩
  | drop e ih => exact ih h
  | cases e p q r he hp hq hr =>
    refine ⟨he h.1, ?_⟩
    cases hv : (e.eval S).getLast? with
    | none => exact hp (by simpa only [hv] using h.2)
    | some b => cases b with
      | false => exact hq (by simpa only [hv] using h.2)
      | true => exact hr (by simpa only [hv] using h.2)
  | bind e f he hf => exact ⟨he h.1, hf h.2⟩
  | loop c a f hc ha hf => exact ⟨hc h.1, ha h.2.1, fun i hi => hf (h.2.2 i hi)⟩

def liftSub {n m} (s : Fin n → Expr m) : Fin (n+1) → Expr (m+1) :=
  Fin.snoc (fun i => (s i).rename Fin.castSucc) (.var (Fin.last m))

def subst : {n m : ℕ} → (Fin n → Expr m) → Expr n → Expr m
  | _, _, s, .var i => s i
  | _, _, _, .nil => .nil
  | _, _, s, .snoc e b => .snoc (e.subst s) b
  | _, _, s, .drop e => .drop (e.subst s)
  | _, _, s, .cases e p q r => .cases (e.subst s) (p.subst s) (q.subst s) (r.subst s)
  | _, _, s, .bind e f => .bind (e.subst s) (f.subst (liftSub s))
  | _, _, s, .loop c a f => .loop (c.subst s) (a.subst s) (f.subst (liftSub (liftSub s)))

theorem eval_liftSub {n m} (s : Fin n → Expr m) (S : Fin m → Word) (a : Word) :
    (fun i => (liftSub s i).eval (Fin.snoc S a)) = Fin.snoc (fun i => (s i).eval S) a := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [liftSub, eval, Function.comp_def]

theorem stages_subst {n m} (s : Fin n → Expr m)
    (f : (Fin (n+2) → Word) → Word) (g : (Fin (m+2) → Word) → Word)
    (h : ∀ S, g S = f (fun i => (liftSub (liftSub s) i).eval S))
    (S : Fin m → Word) (a : Word) (k : ℕ) :
    stages g S a k = stages f (fun i => (s i).eval S) a k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [stages, h, eval_liftSub, ih]

@[simp] theorem eval_subst {n m} (e : Expr n) (s : Fin n → Expr m) (S : Fin m → Word) :
    (e.subst s).eval S = e.eval (fun i => (s i).eval S) := by
  induction e generalizing m with
  | var i | nil => rfl
  | snoc e b ih | drop e ih => simp only [subst, eval, ih]
  | cases e p q r he hp hq hr =>
    simp only [subst, eval, he]
    cases (e.eval (fun i => (s i).eval S)).getLast? with
    | none => exact hp _ _
    | some b => cases b <;> first | exact hq _ _ | exact hr _ _
  | bind e f he hf => simp only [subst, eval, he, hf, eval_liftSub]
  | loop c a f hc ha hf =>
    simp only [subst, eval, hc, ha]
    exact stages_subst s _ _ (hf _) _ _ _

theorem bounded_liftSub {n m} (s : Fin n → Expr m) (S : Fin m → Word) (a : Word) (B : ℕ)
    (hs : ∀ i, (s i).Bounded S B) (ha : a.length ≤ B) :
    ∀ i, (liftSub s i).Bounded (Fin.snoc S a) B := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [liftSub, Bounded] using ha
  · simpa [liftSub, Function.comp_def] using hs j

theorem bounded_subst {n m} (e : Expr n) (s : Fin n → Expr m) (S : Fin m → Word) (B : ℕ)
    (hs : ∀ i, (s i).Bounded S B) (he : e.Bounded (fun i => (s i).eval S) B) :
    (e.subst s).Bounded S B := by
  induction e generalizing m with
  | var i => exact hs i
  | nil => trivial
  | snoc e b ih => exact ⟨ih _ _ hs he.1, by simpa only [eval_subst] using he.2⟩
  | drop e ih => exact ih _ _ hs he
  | cases e p q r he' hp hq hr =>
    refine ⟨he' _ _ hs he.1, ?_⟩
    simp only [eval_subst]
    cases hv : (e.eval (fun i => (s i).eval S)).getLast? with
    | none => exact hp _ _ hs (by simpa only [hv] using he.2)
    | some b => cases b with
      | false => exact hq _ _ hs (by simpa only [hv] using he.2)
      | true => exact hr _ _ hs (by simpa only [hv] using he.2)
  | bind e f ih hf =>
    refine ⟨ih _ _ hs he.1, ?_⟩
    have hs' := bounded_liftSub s S ((e.subst s).eval S) B hs
      (by rw [eval_subst]; exact e.length_le _ _ he.1)
    apply hf _ _ hs'
    simpa only [eval_liftSub, eval_subst] using he.2
  | loop c a f hc ha hf =>
    refine ⟨hc _ _ hs he.1, ha _ _ hs he.2.1, ?_⟩
    intro i hi
    have hi' : i < (c.eval (fun j => (s j).eval S)).length := by simpa only [eval_subst] using hi
    have hid : i ≤ B := (Nat.le_of_lt hi').trans (c.length_le _ _ he.1)
    have hv : (stages f.eval (fun j => (s j).eval S) (a.eval (fun j => (s j).eval S)) i).length ≤ B := by
      cases i with
      | zero => exact a.length_le _ _ he.2.1
      | succ i => exact f.length_le _ _ (he.2.2 i (by omega))
    have hst := stages_subst s f.eval (f.subst (liftSub (liftSub s))).eval
      (fun S => eval_subst _ _ S) S (a.eval (fun j => (s j).eval S)) i
    simp only [eval_subst] at *
    rw [hst]
    apply hf _ _ (bounded_liftSub _ _ _ _
      (bounded_liftSub _ _ _ _ hs (by simpa using hid)) hv)
    simpa only [eval_liftSub] using he.2.2 i hi'

end WordExpressions.Expr

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.PolynomialWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace WordExpressions
open ComputationBounds

/-- Uniform polynomial boundedness of a fixed word expression. This is a
proven realizer property, not an oracle or a unit-cost word instruction. -/
def Poly {n : ℕ} (f : (Fin n → Word) → Word) : Prop :=
  ∃ (e : Expr n) (B : ℕ → ℕ), Polynomial B ∧
    (∀ S, e.eval S = f S) ∧
    ∀ S N, (∀ i, (S i).length ≤ N) → e.Bounded S (B N)

namespace Poly

variable {n m : ℕ}

theorem congr {f g : (Fin n → Word) → Word} (h : Poly f) (he : ∀ S, f S = g S) : Poly g := by
  obtain ⟨e,B,hB,heval,hb⟩ := h
  exact ⟨e,B,hB,fun S => (heval S).trans (he S),hb⟩

theorem var (i : Fin n) : Poly (fun S : Fin n → Word => S i) :=
  ⟨.var i, id, identity, fun _ => rfl, fun _ _ h => h i⟩

theorem nil : Poly (fun _ : Fin n → Word => []) :=
  ⟨.nil, fun _ => 0, constant 0, fun _ => rfl, fun _ _ _ => trivial⟩

theorem snoc {f : (Fin n → Word) → Word} (h : Poly f) (b : Bool) : Poly (fun S => f S ++ [b]) := by
  obtain ⟨e,B,hB,he,hb⟩ := h
  refine ⟨.snoc e b, fun N => B N+1, add hB (constant 1), fun S => ?_, ?_⟩
  · simp only [Expr.eval, he]
  · intro S N hS
    try dsimp only
    have hh := hb S N hS
    refine ⟨e.bounded_mono hh (by omega), ?_⟩
    simpa only [List.length_append, List.length_singleton] using
      (Nat.add_le_add_right (e.length_le _ _ hh) 1)

theorem drop {f : (Fin n → Word) → Word} (h : Poly f) : Poly (fun S => (f S).dropLast) := by
  obtain ⟨e,B,hB,he,hb⟩ := h
  exact ⟨.drop e, B,hB,fun S => congrArg List.dropLast (he S),hb⟩

theorem const (w : Word) : Poly (fun _ : Fin n → Word => w) := by
  induction w using List.reverseRecOn with
  | nil => exact nil
  | append_singleton w b ih => exact snoc ih b

theorem cases {f p q r : (Fin n → Word) → Word} (hf : Poly f) (hp : Poly p) (hq : Poly q) (hr : Poly r) :
    Poly (fun S => match (f S).getLast? with
      | none => p S
      | some false => q S
      | some true => r S) := by
  obtain ⟨e,B,hB,he,hb⟩ := hf
  obtain ⟨a,A,hA,ha,hab⟩ := hp
  obtain ⟨c,C,hC,hc,hcb⟩ := hq
  obtain ⟨d,D,hD,hd,hdb⟩ := hr
  refine ⟨.cases e a c d, fun N => B N+A N+C N+D N, add (add (add hB hA) hC) hD, ?_, ?_⟩
  · intro S
    simp only [Expr.eval, he]
    cases (f S).getLast? with
    | none => exact ha S
    | some b => cases b <;> first | exact hc S | exact hd S
  · intro S N hS
    try dsimp only
    refine ⟨e.bounded_mono (hb S N hS) (by omega), ?_⟩
    cases (e.eval S).getLast? with
    | none => exact a.bounded_mono (hab S N hS) (by omega)
    | some b => cases b with
      | false => exact c.bounded_mono (hcb S N hS) (by omega)
      | true => exact d.bounded_mono (hdb S N hS) (by omega)

theorem rename {f : (Fin n → Word) → Word} (hf : Poly f) (r : Fin n → Fin m) :
    Poly (fun S => f (S ∘ r)) := by
  obtain ⟨e,B,hB,he,hb⟩ := hf
  exact ⟨e.rename r,B,hB,fun S => (e.eval_rename r S).trans (he _),
    fun S N hS => (e.bounded_rename r S _).mpr (hb _ _ (fun i => hS (r i)))⟩

theorem subst {f : (Fin n → Word) → Word} {g : Fin n → (Fin m → Word) → Word}
    (hf : Poly f) (hg : ∀ i, Poly (g i)) : Poly (fun S => f (fun i => g i S)) := by
  classical
  obtain ⟨e,B,hB,he,hb⟩ := hf
  choose a A hA ha hab using hg
  let D : ℕ → ℕ := fun N => ∑ i, A i N
  have hfin (s : Finset (Fin n)) : Polynomial (fun N => ∑ i ∈ s, A i N) := by
    induction s using Finset.induction_on with
    | empty => simpa using constant 0
    | @insert i s hi ih => simpa only [Finset.sum_insert hi] using add (hA i) ih
  have hD : Polynomial D := hfin Finset.univ
  have hAD (i : Fin n) (N : ℕ) : A i N ≤ D N := by
    exact Finset.single_le_sum (f := fun i => A i N) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  refine ⟨e.subst a, fun N => D N+B (D N), add hD (compose hB hD), ?_, ?_⟩
  · intro S
    simp only [Expr.eval_subst, he, ha]
  · intro S N hS
    try dsimp only
    have hs i : (a i).Bounded S (D N) := (a i).bounded_mono (hab i S N hS) (hAD i N)
    apply e.bounded_subst a S _ (fun i => (a i).bounded_mono (hs i) (by omega))
    exact e.bounded_mono (hb _ (D N) (fun i => (a i).length_le _ _ (hs i))) (by omega)

theorem stages_congr {f g : (Fin (n+2) → Word) → Word} (h : ∀ S, f S = g S)
    (S : Fin n → Word) (a : Word) (k : ℕ) : Expr.stages f S a k = Expr.stages g S a k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Expr.stages, h, ih]

/-- Polynomial bounded loop rule. The index and accumulator bounds are
mathematical invariants of the actual semantics; no execution primitive is added. -/
theorem loop {c a : (Fin n → Word) → Word} {f : (Fin (n+2) → Word) → Word}
    (hc : Poly c) (ha : Poly a) (hf : Poly f) (H : ℕ → ℕ) (hH : Polynomial H)
    (hstage : ∀ S N, (∀ j, (S j).length ≤ N) → ∀ i ≤ (c S).length,
      (Expr.stages f S (a S) i).length ≤ H N) :
    Poly (fun S => Expr.stages f S (a S) (c S).length) := by
  obtain ⟨ce,C,hC,hce,hcb⟩ := hc
  obtain ⟨ae,A,hA,hae,hab⟩ := ha
  obtain ⟨fe,F,hF,hfe,hfb⟩ := hf
  let D := fun N => C N+A N+F (N+C N+H N)
  have hp : Polynomial D := add (add hC hA) (compose hF (add (add identity hC) hH))
  refine ⟨.loop ce ae fe, D,hp,?_,?_⟩
  · intro S
    simp only [Expr.eval, hce, hae]
    exact stages_congr hfe _ _ _
  · intro S N hS
    try dsimp only
    have hcS := hcb S N hS
    have haS := hab S N hS
    refine ⟨ce.bounded_mono hcS (by dsimp [D]; omega),
      ae.bounded_mono haS (by dsimp [D]; omega), ?_⟩
    intro i hi
    apply fe.bounded_mono (hfb _ (N+C N+H N) ?_) (by dsimp [D]; omega)
    intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [Fin.snoc_last, hae, stages_congr hfe]
      have hi' : i ≤ (c S).length := by rw [← hce]; omega
      exact (hstage S N hS i hi').trans (by omega)
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simp only [Fin.snoc_castSucc, Fin.snoc_last, List.length_replicate]
        have := ce.length_le _ _ hcS
        omega
      · simpa only [Fin.snoc_castSucc] using (hS k).trans (by omega : N ≤ N+C N+H N)

end Poly
end WordExpressions

namespace WordExpressions

abbrev unary (n : ℕ) : Word := List.replicate n false
abbrev boolWord (b : Bool) : Word := [b]

def old {n : ℕ} (i : Fin n) : Fin (n+2) := i.castSucc.castSucc
def index (n : ℕ) : Fin (n+2) := (Fin.last n).castSucc
def accum (n : ℕ) : Fin (n+2) := Fin.last (n+1)

@[simp] theorem extend_old {n} (S : Fin n → Word) (u v : Word) (i : Fin n) :
    (Fin.snoc (Fin.snoc S u) v : Fin (n+2) → Word) (old i) = S i := by simp [old]
@[simp] theorem extend_index {n} (S : Fin n → Word) (u v : Word) :
    (Fin.snoc (Fin.snoc S u) v : Fin (n+2) → Word) (index n) = u := by simp [index]
@[simp] theorem extend_accum {n} (S : Fin n → Word) (u v : Word) :
    (Fin.snoc (Fin.snoc S u) v : Fin (n+2) → Word) (accum n) = v := by simp [accum]

@[simp] theorem snoc_prefix {n} (S : Fin n → Word) (u : Word) :
    (Fin.snoc S u : Fin (n+1) → Word) ∘ Fin.castSucc = S := by
  funext i; simp
@[simp] theorem extend_prefix {n} (S : Fin n → Word) (u v : Word) :
    (Fin.snoc (Fin.snoc S u) v : Fin (n+2) → Word) ∘ Fin.castSucc = Fin.snoc S u := by
  funext i; simp
@[simp] theorem extend_base {n} (S : Fin n → Word) (u v : Word) :
    (Fin.snoc (Fin.snoc S u) v : Fin (n+2) → Word) ∘ old = S := by
  funext i; simp

namespace Poly
variable {n : ℕ}

theorem branches {p : (Fin n → Word) → Bool} {f g : (Fin n → Word) → Word}
    (hp : Poly (fun S => boolWord (p S))) (hf : Poly f) (hg : Poly g) :
    Poly (fun S => if p S then f S else g S) := by
  apply (cases hp hg hg hf).congr
  intro S
  cases p S <;> rfl

theorem emptyTest {f : (Fin n → Word) → Word} (hf : Poly f) :
    Poly (fun S => boolWord (decide (f S = []))) := by
  apply (cases hf (const [true]) (const [false]) (const [false])).congr
  intro S
  cases he : (f S).getLast? with
  | none =>
    have hz : f S = [] := List.getLast?_eq_none_iff.mp he
    simp [hz, boolWord]
  | some b =>
    have hz : f S ≠ [] := by intro h; simp [h] at he
    cases b <;> simp [hz, boolWord]

theorem length (i : Fin n) : Poly (fun S : Fin n → Word => unary (S i).length) := by
  let body : (Fin (n+2) → Word) → Word := fun T => T (accum n) ++ [false]
  have hb : Poly body := snoc (var _) false
  have hs (S : Fin n → Word) (k : ℕ) : Expr.stages body S [] k = unary k := by
    induction k with
    | zero => rfl
    | succ k ih => simp only [Expr.stages, body, extend_accum, ih, unary, List.replicate_succ']
  obtain h := loop (var i) nil hb id ComputationBounds.identity (by
    intro S N hS k hk
    rw [hs]
    simpa using hk.trans (hS i))
  exact h.congr (fun S => hs S _)

theorem unaryLength {f : (Fin n → Word) → Word} (hf : Poly f) :
    Poly (fun S => unary (f S).length) := by
  have h := (length (0 : Fin 1)).subst (g := fun _ => f) (fun _ => hf)
  exact h.congr (fun _ => rfl)

theorem stages_drop {n} (S : Fin n → Word) (w : Word) (k : ℕ) :
    Expr.stages (fun T => (T (accum n)).dropLast) S w k = w.take (w.length-k) := by
  induction k with
  | zero => simp [Expr.stages]
  | succ k ih =>
    simp only [Expr.stages, extend_accum]
    rw [ih]
    simp only [List.dropLast_eq_take, List.length_take, List.take_take]
    congr 1
    omega

theorem cut (i j : Fin n) : Poly (fun S : Fin n → Word => (S i).take ((S i).length-(S j).length)) := by
  have hstep : Poly (fun T : Fin (n+2) → Word => (T (accum n)).dropLast) := drop (var _)
  have h := loop (var j) (var i) hstep id ComputationBounds.identity (by
    intro S N hS k _
    rw [stages_drop]
    simp only [List.length_take]
    exact (min_le_right _ _).trans (hS i))
  exact h.congr (fun S => stages_drop S _ _)

theorem cutOf {f g : (Fin n → Word) → Word} (hf : Poly f) (hg : Poly g) :
    Poly (fun S => (f S).take ((f S).length-(g S).length)) := by
  have h := (cut (0 : Fin 2) 1).subst (g := ![f,g]) (by intro i; fin_cases i; exacts [hf,hg])
  exact h.congr (fun _ => rfl)

theorem sub {f g : (Fin n → Word) → Word} (hf : Poly f) (hg : Poly g) :
    Poly (fun S => unary ((f S).length-(g S).length)) := by
  apply (cutOf (unaryLength hf) hg).congr
  intro S
  simp [unary, List.take_replicate]

theorem le {f g : (Fin n → Word) → Word} (hf : Poly f) (hg : Poly g) :
    Poly (fun S => boolWord (decide ((f S).length ≤ (g S).length))) := by
  apply (emptyTest (sub hf hg)).congr
  intro S
  simp [unary, Nat.sub_eq_zero_iff_le]

theorem stages_add {n} (S : Fin n → Word) (a k : ℕ) :
    Expr.stages (fun T => T (accum n) ++ [false]) S (unary a) k = unary (a+k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [Expr.stages, extend_accum, ih, unary]
    rw [← Nat.add_assoc, List.replicate_succ']

theorem add (i j : Fin n) : Poly (fun S : Fin n → Word => unary ((S i).length+(S j).length)) := by
  have h := loop (var j) (length i) (snoc (var (accum n)) false)
    (fun N => N+N) (ComputationBounds.add ComputationBounds.identity ComputationBounds.identity) (by
      intro S N hS k hk
      rw [stages_add]
      simp only [unary, List.length_replicate]
      exact Nat.add_le_add (hS i) (hk.trans (hS j)))
  exact h.congr (fun S => stages_add S _ _)

theorem addOf {f g : (Fin n → Word) → Word} (hf : Poly f) (hg : Poly g) :
    Poly (fun S => unary ((f S).length+(g S).length)) := by
  have h := (add (0 : Fin 2) 1).subst (g := ![f,g]) (by intro i; fin_cases i; exacts [hf,hg])
  exact h.congr (fun _ => rfl)

end Poly
end WordExpressions

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.WordArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace WordExpressions
abbrev NatPoly {n} (f : (Fin n → Word) → ℕ) : Prop := Poly (fun S => unary (f S))
abbrev BoolPoly {n} (p : (Fin n → Word) → Bool) : Prop := Poly (fun S => boolWord (p S))

namespace BoolPoly
variable {n : ℕ}
theorem const (b : Bool) : BoolPoly (fun _ : Fin n → Word => b) := Poly.const [b]
theorem not {p : (Fin n → Word) → Bool} (hp : BoolPoly p) : BoolPoly (fun S => !(p S)) := by
  apply (Poly.branches hp (const false) (const true)).congr
  intro S; dsimp only; cases p S <;> rfl
theorem and {p q : (Fin n → Word) → Bool} (hp : BoolPoly p) (hq : BoolPoly q) :
    BoolPoly (fun S => p S && q S) := by
  apply (Poly.branches hp hq (const false)).congr
  intro S; dsimp only; cases p S <;> rfl
theorem or {p q : (Fin n → Word) → Bool} (hp : BoolPoly p) (hq : BoolPoly q) :
    BoolPoly (fun S => p S || q S) := by
  apply (Poly.branches hp (const true) hq).congr
  intro S; dsimp only; cases p S <;> rfl
theorem rename {p : (Fin n → Word) → Bool} (hp : BoolPoly p) {m} (r : Fin n → Fin m) :
    BoolPoly (fun S => p (S ∘ r)) := Poly.rename hp r
end BoolPoly

namespace NatPoly
variable {n : ℕ}
theorem length {f : (Fin n → Word) → Word} (hf : Poly f) : NatPoly (fun S => (f S).length) :=
  Poly.unaryLength hf
theorem var (i : Fin n) : NatPoly (fun S : Fin n → Word => (S i).length) := Poly.length i
theorem const (c : ℕ) : NatPoly (fun _ : Fin n → Word => c) := Poly.const (unary c)
theorem rename {f : (Fin n → Word) → ℕ} (hf : NatPoly f) {m} (r : Fin n → Fin m) :
    NatPoly (fun S => f (S ∘ r)) := Poly.rename hf r

theorem add {f g : (Fin n → Word) → ℕ} (hf : NatPoly f) (hg : NatPoly g) : NatPoly (fun S => f S+g S) := by
  apply (Poly.addOf hf hg).congr
  intro S; simp [unary]
theorem succ {f : (Fin n → Word) → ℕ} (hf : NatPoly f) : NatPoly (fun S => f S+1) := add hf (const 1)
theorem sub {f g : (Fin n → Word) → ℕ} (hf : NatPoly f) (hg : NatPoly g) : NatPoly (fun S => f S-g S) := by
  apply (Poly.sub hf hg).congr
  intro S; simp [unary]
theorem le {f g : (Fin n → Word) → ℕ} (hf : NatPoly f) (hg : NatPoly g) :
    BoolPoly (fun S => decide (f S ≤ g S)) := by
  apply (Poly.le hf hg).congr
  intro S; simp [unary]
theorem lt {f g : (Fin n → Word) → ℕ} (hf : NatPoly f) (hg : NatPoly g) :
    BoolPoly (fun S => decide (f S < g S)) := by
  apply (le (succ hf) hg).congr
  intro S; simp
theorem eqtest {f g : (Fin n → Word) → ℕ} (hf : NatPoly f) (hg : NatPoly g) :
    BoolPoly (fun S => decide (f S = g S)) := by
  apply (BoolPoly.and (le hf hg) (le hg hf)).congr
  intro S; simp [boolWord, Nat.le_antisymm_iff]
theorem ite {p : (Fin n → Word) → Bool} {f g : (Fin n → Word) → ℕ}
    (hp : BoolPoly p) (hf : NatPoly f) (hg : NatPoly g) :
    NatPoly (fun S => if p S then f S else g S) := by
  apply (Poly.branches hp hf hg).congr
  intro S; dsimp only; cases p S <;> rfl

theorem max {f g : (Fin n → Word) → ℕ} (hf : NatPoly f) (hg : NatPoly g) :
    NatPoly (fun S => max (f S) (g S)) := by
  apply (ite (le hf hg) hg hf).congr
  intro S; by_cases h : f S ≤ g S <;> simp [h, max_def]
theorem min {f g : (Fin n → Word) → ℕ} (hf : NatPoly f) (hg : NatPoly g) :
    NatPoly (fun S => min (f S) (g S)) := by
  apply (ite (le hf hg) hf hg).congr
  intro S; by_cases h : f S ≤ g S <;> simp [h, min_def]

theorem mulVars (i j : Fin n) : NatPoly (fun S : Fin n → Word => (S i).length*(S j).length) := by
  let step : (Fin (n+2) → Word) → Word := fun T => unary ((T (accum n)).length+(T (old i)).length)
  have hs (S : Fin n → Word) (k : ℕ) : Expr.stages step S [] k = unary ((S i).length*k) := by
    induction k with
    | zero => simp [Expr.stages, unary]
    | succ k ih => simp [Expr.stages, step, ih, unary, Nat.mul_succ]
  have h := Poly.loop (Poly.var j) Poly.nil (Poly.add (accum n) (old i))
    (fun N => N*N) (ComputationBounds.mul ComputationBounds.identity ComputationBounds.identity) (by
      intro S N hS k hk
      change (Expr.stages step S [] k).length ≤ _
      rw [hs]
      simpa only [unary, List.length_replicate] using Nat.mul_le_mul (hS i) (hk.trans (hS j)))
  exact h.congr (fun S => hs S _)

theorem mul {f g : (Fin n → Word) → ℕ} (hf : NatPoly f) (hg : NatPoly g) : NatPoly (fun S => f S*g S) := by
  have h := (mulVars (0 : Fin 2) 1).subst (g := ![(fun S => unary (f S)),(fun S => unary (g S))])
    (by intro i; fin_cases i; exacts [hf,hg])
  apply h.congr
  intro S; simp [unary]

end NatPoly

namespace Poly
variable {n : ℕ}

/-- The i-th bit in left-to-right order, with a false default outside the word. -/
theorem nth {w : (Fin n → Word) → Word} {i : (Fin n → Word) → ℕ}
    (hw : Poly w) (hi : NatPoly i) : BoolPoly (fun S => (w S)[i S]?.getD false) := by
  let amount := fun S => (w S).length-(i S+1)
  have hamt : NatPoly amount := NatPoly.sub (NatPoly.length hw) (NatPoly.succ hi)
  have hcut := cutOf hw hamt
  let test : (Fin n → Word) → Word := fun S => ((w S).take ((w S).length-amount S))
  have hlast : BoolPoly (fun S => (test S).getLast?.getD false) := by
    apply (cases hcut (const [false]) (const [false]) (const [true])).congr
    intro S
    simp only [unary, List.length_replicate]
    cases (test S).getLast? with
    | none => rfl
    | some b => cases b <;> rfl
  have h := branches (NatPoly.lt hi (NatPoly.length hw)) hlast (const [false])
  apply h.congr
  intro S
  by_cases hlt : i S < (w S).length
  · simp only [decide_eq_true hlt, ite_true]
    have hn : (w S).length-amount S = i S+1 := by dsimp [amount]; omega
    dsimp only [test]
    rw [hn, List.getLast?_take]
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
    rw [List.getElem?_eq_getElem hlt]
    rfl
  · simp only [decide_eq_false hlt, Bool.false_eq_true, ↓reduceIte]
    rw [List.getElem?_eq_none (by omega)]
    rfl

/-- Polynomially bounded tabulation is implemented by captured-count iteration;
there is no list-construction oracle in the underlying Machine. -/
theorem tabulate {c : (Fin n → Word) → ℕ} {p : (Fin (n+1) → Word) → Bool}
    (hc : NatPoly c) (hp : BoolPoly p) :
    Poly (fun S => (List.range (c S)).map (fun i => p (Fin.snoc S (unary i)))) := by
  let step : (Fin (n+2) → Word) → Word := fun T => T (accum n) ++ [p (T ∘ Fin.castSucc)]
  have hstep : Poly step := by
    apply (branches (BoolPoly.rename hp Fin.castSucc) (snoc (var (accum n)) true)
      (snoc (var (accum n)) false)).congr
    intro T; dsimp [step]; cases p (T ∘ Fin.castSucc) <;> rfl
  have hs (S : Fin n → Word) (k : ℕ) : Expr.stages step S [] k =
      (List.range k).map (fun i => p (Fin.snoc S (unary i))) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [Expr.stages, step, extend_accum, ih, List.range_succ, List.map_append,
        List.map_singleton]
      congr 3
      funext j
      simp
  obtain ⟨ce,C,hC,hce,hcb⟩ := hc
  have hlen (S : Fin n → Word) (N : ℕ) (hS : ∀ i, (S i).length ≤ N) : c S ≤ C N := by
    have := ce.length_le _ _ (hcb S N hS)
    simpa only [hce, unary, List.length_replicate] using this
  have h := loop ⟨ce,C,hC,hce,hcb⟩ nil hstep C hC (by
    intro S N hS k hk
    rw [hs]
    simp only [List.length_map, List.length_range]
    exact (by simpa only [unary, List.length_replicate] using hk : k ≤ c S).trans (hlen S N hS))
  apply h.congr
  intro S
  simpa only [unary, List.length_replicate] using hs S (c S)

end Poly
end WordExpressions

namespace WordExpressions
namespace Poly
variable {n : ℕ}

theorem length_bound {f : (Fin n → Word) → Word} (hf : Poly f) :
    ∃ B : ℕ → ℕ, ComputationBounds.Polynomial B ∧
      ∀ S N, (∀ i, (S i).length ≤ N) → (f S).length ≤ B N := by
  obtain ⟨e,B,hB,he,hbound⟩ := hf
  exact ⟨B,hB,fun S N hS => by rw [← he]; exact e.length_le _ _ (hbound _ _ hS)⟩

end Poly
namespace NatPoly
variable {n : ℕ}

theorem bound {f : (Fin n → Word) → ℕ} (hf : NatPoly f) :
    ∃ B : ℕ → ℕ, ComputationBounds.Polynomial B ∧
      ∀ S N, (∀ i, (S i).length ≤ N) → f S ≤ B N := by
  simpa only [unary, List.length_replicate] using Poly.length_bound hf

/-- Natural-valued iteration, represented by literal unary words. -/
def stages (f : (Fin (n+2) → Word) → ℕ) (S : Fin n → Word) (a : ℕ) : ℕ → ℕ
  | 0 => a
  | k+1 => f (Fin.snoc (Fin.snoc S (unary k)) (unary (stages f S a k)))

theorem stages_word (f : (Fin (n+2) → Word) → ℕ) (S : Fin n → Word) (a k : ℕ) :
    Expr.stages (fun T => unary (f T)) S (unary a) k = unary (stages f S a k) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Expr.stages, ih, stages]

theorem loop {c a : (Fin n → Word) → ℕ} {f : (Fin (n+2) → Word) → ℕ}
    (hc : NatPoly c) (ha : NatPoly a) (hf : NatPoly f)
    (H : ℕ → ℕ) (hH : ComputationBounds.Polynomial H)
    (hstage : ∀ S N, (∀ j, (S j).length ≤ N) → ∀ i ≤ c S, stages f S (a S) i ≤ H N) :
    NatPoly (fun S => stages f S (a S) (c S)) := by
  have h := Poly.loop hc ha hf H hH (by
    intro S N hS i hi
    simpa only [stages_word, unary, List.length_replicate] using
      hstage S N hS i (by simpa only [unary, List.length_replicate] using hi))
  exact h.congr (fun S => by simpa only [unary, List.length_replicate] using stages_word f S (a S) (c S))

end NatPoly
namespace BoolPoly
variable {n : ℕ}

theorem boundedAll {c : (Fin n → Word) → ℕ} {p : (Fin (n+1) → Word) → Bool}
    (hc : NatPoly c) (hp : BoolPoly p) :
    BoolPoly (fun S => (List.range (c S)).all (fun i => p (Fin.snoc S (unary i)))) := by
  let f : (Fin (n+2) → Word) → Word := fun T =>
    boolWord (((T (accum n)).getLast?.getD false) && p (T ∘ Fin.castSucc))
  have hb : BoolPoly (fun T : Fin (n+2) → Word => (T (accum n)).getLast?.getD false) := by
    apply (Poly.cases (Poly.var _) (Poly.const [false]) (Poly.const [false]) (Poly.const [true])).congr
    intro T; dsimp only; cases (T (accum n)).getLast? with
    | none => rfl
    | some b => cases b <;> rfl
  have hf : Poly f := and hb (rename hp Fin.castSucc)
  have hs (S : Fin n → Word) (k : ℕ) : Expr.stages f S [true] k =
      boolWord ((List.range k).all (fun i => p (Fin.snoc S (unary i)))) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      simp [Expr.stages, f, ih, List.range_succ]
  have h := Poly.loop hc (Poly.const [true]) hf (fun _ => 1) (ComputationBounds.constant 1) (by
    intro S N hS k hk
    rw [hs]; rfl)
  exact h.congr (fun S => by simpa only [unary, List.length_replicate] using hs S (c S))

theorem boundedAny {c : (Fin n → Word) → ℕ} {p : (Fin (n+1) → Word) → Bool}
    (hc : NatPoly c) (hp : BoolPoly p) :
    BoolPoly (fun S => (List.range (c S)).any (fun i => p (Fin.snoc S (unary i)))) := by
  apply (not (boundedAll hc (not hp))).congr
  intro S
  simp [List.any_eq_not_all_not]

end BoolPoly
end WordExpressions

namespace WordExpressions
namespace Poly
variable {n m : ℕ}

theorem applyWord {f : (Fin (n+1) → Word) → Word} {g : (Fin m → Word) → Word}
    (hf : Poly f) (r : Fin n → Fin m) (hg : Poly g) :
    Poly (fun S => f (Fin.snoc (S ∘ r) (g S))) := by
  apply hf.subst
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.snoc_last] using hg
  · simpa only [Fin.snoc_castSucc, Function.comp_apply] using var (r j)

end Poly
namespace NatPoly
variable {n : ℕ}

theorem findGreatest {c : (Fin n → Word) → ℕ} {p : (Fin (n+1) → Word) → Bool}
    (hc : NatPoly c) (hp : BoolPoly p) :
    NatPoly (fun S => Nat.findGreatest (fun i => p (Fin.snoc S (unary i)) = true) (c S)) := by
  let step : (Fin (n+2) → Word) → ℕ := fun T =>
    if p (Fin.snoc (T ∘ old) (unary ((T (index n)).length+1))) then
      (T (index n)).length+1 else (T (accum n)).length
  have hp' : BoolPoly (fun T : Fin (n+2) → Word =>
      p (Fin.snoc (T ∘ old) (unary ((T (index n)).length+1)))) :=
    Poly.applyWord hp old (succ (var (index n)))
  have hstep : NatPoly step := ite hp' (succ (var (index n))) (var (accum n))
  have hs (S : Fin n → Word) (k : ℕ) : stages step S 0 k =
      Nat.findGreatest (fun i => p (Fin.snoc S (unary i)) = true) k := by
    induction k with
    | zero => rfl
    | succ k ih =>
      simp [stages, step, ih, Nat.findGreatest_succ]
  obtain ⟨C,hC,hcb⟩ := bound hc
  have h := loop hc (const 0) hstep C hC (by
    intro S N hS k hk
    rw [hs]
    exact (Nat.findGreatest_le k).trans (hk.trans (hcb S N hS)))
  apply h.congr
  intro S
  dsimp only
  rw [hs]

theorem div {f g : (Fin n → Word) → ℕ} (hf : NatPoly f) (hg : NatPoly g) :
    NatPoly (fun S => f S / g S) := by
  have hp : BoolPoly (fun T : Fin (n+1) → Word =>
      decide ((T (Fin.last n)).length*g (T ∘ Fin.castSucc) ≤ f (T ∘ Fin.castSucc))) :=
    le (mul (var (Fin.last n)) (rename hg Fin.castSucc)) (rename hf Fin.castSucc)
  have hq := findGreatest hf hp
  have hb : NatPoly (fun S =>
      if decide (g S = 0) then 0 else
        Nat.findGreatest (fun i => decide (i*g S ≤ f S) = true) (f S)) := by
    apply (ite (eqtest hg (const 0)) (const 0) hq).congr
    intro S
    simp only [unary, Fin.snoc_last, List.length_replicate]
    congr 3; funext i; simp
  apply hb.congr
  intro S
  by_cases hz : g S = 0
  · simp [hz, Nat.div_zero]
  · simp only [hz, decide_false, Bool.false_eq_true, ↓reduceIte]
    congr 1
    apply Nat.findGreatest_eq_iff.mpr
    refine ⟨Nat.div_le_self _ _, ?_, ?_⟩
    · intro _
      simp only [decide_eq_true_eq]
      exact (Nat.le_div_iff_mul_le (by omega)).mp (le_refl _)
    · intro i hi _
      simp only [decide_eq_true_eq]
      intro hmul
      have := (Nat.le_div_iff_mul_le (by omega)).mpr hmul
      omega

theorem mod {f g : (Fin n → Word) → ℕ} (hf : NatPoly f) (hg : NatPoly g) :
    NatPoly (fun S => f S % g S) := by
  simpa only [Nat.mod_eq_sub_mul_div] using sub hf (mul hg (div hf hg))

end NatPoly
end WordExpressions

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.PolynomialArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace WordExpressions
namespace Poly
variable {n : ℕ}

theorem take {w : (Fin n → Word) → Word} {c : (Fin n → Word) → ℕ}
    (hw : Poly w) (hc : NatPoly c) : Poly (fun S => (w S).take (c S)) := by
  apply (cutOf hw (NatPoly.sub (NatPoly.length hw) hc)).congr
  intro S
  simp only [unary, List.length_replicate]
  by_cases h : c S ≤ (w S).length
  · rw [Nat.sub_sub_self h]
  · rw [show (w S).length-c S = 0 by omega, Nat.sub_zero, List.take_length,
      List.take_of_length_le (by omega)]

end Poly
end WordExpressions

namespace WordExpressions.NatPoly
variable {n : ℕ}

theorem sum {c : (Fin n → Word) → ℕ} {f : (Fin (n+1) → Word) → ℕ}
    (hc : NatPoly c) (hf : NatPoly f) :
    NatPoly (fun S => ((List.range (c S)).map (fun i => f (Fin.snoc S (unary i)))).sum) := by
  let step : (Fin (n+2) → Word) → ℕ := fun T => (T (accum n)).length+f (T ∘ Fin.castSucc)
  have hstep : NatPoly step := add (var _) (rename hf _)
  have hs (S : Fin n → Word) (k : ℕ) : stages step S 0 k =
      ((List.range k).map (fun i => f (Fin.snoc S (unary i)))).sum := by
    induction k with
    | zero => rfl
    | succ k ih => simp [stages, step, ih, List.sum_range_succ]
  obtain ⟨C,hC,hcb⟩ := bound hc
  obtain ⟨F,hF,hfb⟩ := bound hf
  let H := fun N => C N*F (N+C N)
  have hH : ComputationBounds.Polynomial H :=
    ComputationBounds.mul hC (ComputationBounds.compose hF (ComputationBounds.add ComputationBounds.identity hC))
  have hstage (S : Fin n → Word) (N : ℕ) (hS : ∀ j, (S j).length ≤ N) :
      ∀ k ≤ c S, stages step S 0 k ≤ H N := by
    have heval (k : ℕ) (hk : k ≤ c S) : f (Fin.snoc S (unary k)) ≤ F (N+C N) := by
      apply hfb
      intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [Fin.snoc_last, unary, List.length_replicate]
        exact (hk.trans (hcb S N hS)).trans (Nat.le_add_left _ _)
      · simpa only [Fin.snoc_castSucc] using (hS i).trans (Nat.le_add_right _ _)
    have haux (k : ℕ) (hk : k ≤ c S) : stages step S 0 k ≤ k*F (N+C N) := by
      induction k with
      | zero => simp [stages]
      | succ k ih =>
        simp only [stages, step, extend_accum, unary, List.length_replicate, extend_prefix]
        have hi := ih (by omega)
        have he := heval k (by omega)
        change stages step S 0 k+f (Fin.snoc S (unary k)) ≤ _
        simpa only [Nat.succ_mul] using Nat.add_le_add hi he
    intro k hk
    exact (haux k hk).trans (Nat.mul_le_mul_right _ (hk.trans (hcb S N hS)))
  apply (loop hc (const 0) hstep H hH hstage).congr
  intro S
  dsimp only
  rw [hs]

end WordExpressions.NatPoly

namespace WordExpressions.NatPoly
variable {n : ℕ}

theorem pair {f g : (Fin n → Word) → ℕ} (hf : NatPoly f) (hg : NatPoly g) :
    NatPoly (fun S => Nat.pair (f S) (g S)) := by
  apply (ite (lt hf hg) (add (mul hg hg) hf) (add (add (mul hf hf) hf) hg)).congr
  intro S
  simp only [Nat.pair]
  by_cases h : f S < g S <;> simp [h]

theorem sqrt {f : (Fin n → Word) → ℕ} (hf : NatPoly f) : NatPoly (fun S => (f S).sqrt) := by
  have hp : BoolPoly (fun T : Fin (n+1) → Word =>
      decide ((T (Fin.last n)).length*(T (Fin.last n)).length ≤ f (T ∘ Fin.castSucc))) :=
    le (mul (var _) (var _)) (rename hf _)
  apply (findGreatest hf hp).congr
  intro S
  dsimp only
  apply congrArg unary
  simp only [Fin.snoc_last, unary, List.length_replicate, snoc_prefix, decide_eq_true_eq]
  apply Nat.findGreatest_eq_iff.mpr
  refine ⟨Nat.sqrt_le_self _, fun _ => Nat.sqrt_le _, ?_⟩
  intro i hi _ hsq
  have := Nat.le_sqrt.mpr hsq
  omega

theorem unpair_fst {f : (Fin n → Word) → ℕ} (hf : NatPoly f) :
    NatPoly (fun S => (Nat.unpair (f S)).1) := by
  have hs := sqrt hf
  have hr := sub hf (mul hs hs)
  apply (ite (lt hr hs) hr hs).congr
  intro S
  by_cases h : f S-(f S).sqrt*(f S).sqrt < (f S).sqrt <;> simp [Nat.unpair, h]

theorem unpair_snd {f : (Fin n → Word) → ℕ} (hf : NatPoly f) :
    NatPoly (fun S => (Nat.unpair (f S)).2) := by
  have hs := sqrt hf
  have hr := sub hf (mul hs hs)
  apply (ite (lt hr hs) hs (sub hr hs)).congr
  intro S
  by_cases h : f S-(f S).sqrt*(f S).sqrt < (f S).sqrt <;> simp [Nat.unpair, h]

end WordExpressions.NatPoly

namespace WordExpressions.NatPoly
variable {n : ℕ}

theorem cap_mul (b x c : ℕ) : Min.min (Min.min x c*b) c = Min.min (x*b) c := by
  by_cases hb : b = 0
  · simp [hb]
  have hb : 1 ≤ b := by omega
  by_cases hx : x ≤ c
  · rw [min_eq_left hx]
  · have hxc : c ≤ x := by omega
    rw [min_eq_right hxc, min_eq_right (by nlinarith), min_eq_right (by nlinarith)]

theorem cappedPow {b e c : (Fin n → Word) → ℕ} (hb : NatPoly b) (he : NatPoly e) (hc : NatPoly c) :
    NatPoly (fun S => Min.min ((b S)^(e S)) (c S)) := by
  let f : (Fin (n+2) → Word) → ℕ := fun T => Min.min ((T (accum n)).length*b (T ∘ old)) (c (T ∘ old))
  have hf : NatPoly f := min (mul (var _) (rename hb _)) (rename hc _)
  have hs (S : Fin n → Word) (k : ℕ) : stages f S (Min.min 1 (c S)) k = Min.min ((b S)^k) (c S) := by
    induction k with
    | zero => simp [stages]
    | succ k ih => simp only [stages, f, extend_accum, unary, List.length_replicate, extend_base, ih,
        cap_mul, pow_succ]
  obtain ⟨C,hC,hcb⟩ := bound hc
  apply (loop he (min (const 1) hc) hf C hC (by
    intro S N hS k _
    rw [hs]
    exact (min_le_right _ _).trans (hcb S N hS))).congr
  intro S
  dsimp only
  rw [hs]

end WordExpressions.NatPoly

namespace WordExpressions.NatPoly
variable {n : ℕ}

theorem div_cap (x y : ℕ) : x / Min.min y (x+1) = x/y := by
  by_cases hy : y ≤ x+1
  · rw [min_eq_left hy]
  · rw [min_eq_right (by omega), Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]

end WordExpressions.NatPoly

namespace WordExpressions
namespace NatPoly
variable {n : ℕ}

/-- Saturated, genuine left-to-right binary decoding. It stays unary-bounded by c. -/
def decodeCap (w : Word) (c : ℕ) : ℕ := w.foldl (fun x b => Min.min (2*x+if b then 1 else 0) c) 0

theorem decodeCap_aux (w : Word) (c x : ℕ) :
    w.foldl (fun x b => Min.min (2*x+if b then 1 else 0) c) (Min.min x c) =
      Min.min (w.foldl (fun x b => 2*x+if b then 1 else 0) x) c := by
  induction w generalizing x with
  | nil => rfl
  | cons b w ih =>
    simp only [List.foldl_cons]
    have hm : Min.min (2*Min.min x c+if b then 1 else 0) c =
        Min.min (2*x+if b then 1 else 0) c := by
      cases b
      · simpa only [Bool.false_eq_true, ↓reduceIte, add_zero, Nat.mul_comm] using cap_mul 2 x c
      · simp only [↓reduceIte]
        by_cases hx : x ≤ c
        · rw [min_eq_left hx]
        · rw [min_eq_right (by omega : c ≤ x), min_eq_right (by omega : c ≤ 2*c+1),
            min_eq_right (by omega : c ≤ 2*x+1)]
    rw [hm, ih]

theorem decodeCap_correct (w : Word) (c : ℕ) : decodeCap w c = Min.min (binaryValue w) c := by
  simpa only [decodeCap, binaryValue, zero_min] using decodeCap_aux w c 0

theorem decode {w : (Fin n → Word) → Word} {c : (Fin n → Word) → ℕ}
    (hw : Poly w) (hc : NatPoly c) : NatPoly (fun S => Min.min (binaryValue (w S)) (c S)) := by
  let f : (Fin (n+2) → Word) → ℕ := fun T =>
    Min.min (2*(T (accum n)).length+if (w (T ∘ old))[(T (index n)).length]?.getD false then 1 else 0) (c (T ∘ old))
  have hf : NatPoly f := min
    (add (mul (const 2) (var _)) (ite (Poly.nth (Poly.rename hw old) (var _)) (const 1) (const 0)))
    (rename hc old)
  have hs (S : Fin n → Word) (k : ℕ) (hk : k ≤ (w S).length) :
      stages f S 0 k = decodeCap ((w S).take k) (c S) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      have hk' : k < (w S).length := by omega
      simp only [stages, f, extend_accum, unary, List.length_replicate, extend_base, extend_index,
        List.getElem?_eq_getElem hk', Option.getD_some, ih (by omega)]
      rw [List.take_succ_eq_append_getElem hk']
      simp only [decodeCap, List.foldl_append, List.foldl_cons, List.foldl_nil]
  obtain ⟨C,hC,hcb⟩ := bound hc
  apply (loop (length hw) (const 0) hf C hC (by
    intro S N hS k hk
    rw [hs S k hk, decodeCap_correct]
    exact (min_le_right _ _).trans (hcb S N hS))).congr
  intro S
  dsimp only
  rw [hs S _ (le_refl _), List.take_length, decodeCap_correct]

end NatPoly
end WordExpressions

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.FiniteEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace NumericFinite

def elements (b : ℕ) (p : ℕ → Bool) : List ℕ := (List.range b).filter p
def count (b : ℕ) (p : ℕ → Bool) : ℕ := (elements b p).length

@[simp] theorem elements_zero (p : ℕ → Bool) : elements 0 p = [] := rfl
@[simp] theorem elements_succ (b : ℕ) (p : ℕ → Bool) :
    elements (b+1) p = elements b p ++ if p b then [b] else [] := by
  simp only [elements, List.range_succ, List.filter_append]
  cases hb : p b <;> simp [hb]

@[simp] theorem count_zero (p : ℕ → Bool) : count 0 p = 0 := rfl
@[simp] theorem count_succ (b : ℕ) (p : ℕ → Bool) :
    count (b+1) p = count b p + if p b then 1 else 0 := by
  simp only [count, elements_succ, List.length_append]
  cases p b <;> rfl

theorem mem_elements {b v : ℕ} {p : ℕ → Bool} : v ∈ elements b p ↔ v < b ∧ p v = true := by
  simp [elements, and_comm]

theorem count_mono (p : ℕ → Bool) {a b : ℕ} (h : a ≤ b) : count a p ≤ count b p := by
  induction h with
  | refl => rfl
  | @step b h ih => rw [count_succ]; omega

theorem count_strict {p : ℕ → Bool} {a b : ℕ} (h : a < b) (ha : p a = true) :
    count a p < count b p := by
  have hh := count_mono p h
  rw [count_succ, ha] at hh
  simp only [↓reduceIte] at hh
  omega

theorem rank (b : ℕ) (p : ℕ → Bool) (j : ℕ) (hj : j < (elements b p).length) :
    count (elements b p)[j] p = j := by
  induction b with
  | zero => simp at hj
  | succ b ih =>
    by_cases hp : p b = true
    · have he : elements (b+1) p = elements b p ++ [b] := by simp [hp]
      simp only [he, List.length_append, List.length_singleton] at hj
      simp only [he]
      by_cases hh : j < (elements b p).length
      · rw [List.getElem_append_left hh]
        exact ih hh
      · have hj' : j = (elements b p).length := by omega
        subst j
        simp [count]
    · have he : elements (b+1) p = elements b p := by simp [hp]
      simp only [he]
      exact ih (by simpa only [he] using hj)

def select (b : ℕ) (p : ℕ → Bool) (j : ℕ) : ℕ :=
  Nat.findGreatest (fun i => i < b ∧ p i = true ∧ count i p = j) b

theorem select_correct (b : ℕ) (p : ℕ → Bool) (j : ℕ) (hj : j < (elements b p).length) :
    select b p j = (elements b p)[j] := by
  let v := (elements b p)[j]
  have hv : v < b ∧ p v = true := mem_elements.mp (List.getElem_mem hj)
  have hr : count v p = j := rank b p j hj
  apply Nat.findGreatest_eq_iff.mpr
  refine ⟨by omega, fun _ => ⟨hv.1,hv.2,hr⟩, ?_⟩
  intro i hi _ hh
  have hlt := count_strict (p := p) hi hv.2
  exact (ne_of_gt hlt) (hh.2.2.trans hr.symm)

end NumericFinite
namespace WordExpressions.NatPoly
variable {n : ℕ}

theorem filterCount {b : (Fin n → Word) → ℕ} {p : (Fin (n+1) → Word) → Bool}
    (hb : NatPoly b) (hp : BoolPoly p) :
    NatPoly (fun S => NumericFinite.count (b S) (fun i => p (Fin.snoc S (unary i)))) := by
  apply (sum hb (ite hp (const 1) (const 0))).congr
  intro S
  dsimp only
  congr 1
  generalize b S = k
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.sum_range_succ, ih, NumericFinite.count_succ]

end WordExpressions.NatPoly
namespace ComputationBounds

/-- A single exponential with a polynomial exponent (not an iterated exponential). -/
def Exponential (f : ℕ → ℕ) : Prop := ∃ C d : ℕ, ∀ n, f n ≤ 2^(C*(n+1)^d)

end ComputationBounds

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.ExponentialComputation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace WordExpressions
namespace BoolPoly
variable {n : ℕ}

theorem allRange {b : (Fin n → Word) → ℕ} {p : (Fin n → Word) → ℕ → Bool}
    (hb : NatPoly b)
    (hp : BoolPoly (fun T => p (T ∘ Fin.castSucc) ((T (Fin.last n)).length))) :
    BoolPoly (fun S => (List.range (b S)).all (p S)) := by
  apply (boundedAll hb hp).congr
  intro S
  simp only [snoc_prefix, Fin.snoc_last, unary, List.length_replicate]

theorem anyRange {b : (Fin n → Word) → ℕ} {p : (Fin n → Word) → ℕ → Bool}
    (hb : NatPoly b)
    (hp : BoolPoly (fun T => p (T ∘ Fin.castSucc) ((T (Fin.last n)).length))) :
    BoolPoly (fun S => (List.range (b S)).any (p S)) := by
  apply (boundedAny hb hp).congr
  intro S
  simp only [snoc_prefix, Fin.snoc_last, unary, List.length_replicate]

end BoolPoly
namespace NatPoly
variable {n : ℕ}

theorem sumRange {b : (Fin n → Word) → ℕ} {f : (Fin n → Word) → ℕ → ℕ}
    (hb : NatPoly b)
    (hf : NatPoly (fun T => f (T ∘ Fin.castSucc) ((T (Fin.last n)).length))) :
    NatPoly (fun S => ((List.range (b S)).map (f S)).sum) := by
  apply (sum hb hf).congr
  intro S
  simp only [snoc_prefix, Fin.snoc_last, unary, List.length_replicate]

end NatPoly
namespace Poly
variable {n : ℕ}

theorem tabulateRange {b : (Fin n → Word) → ℕ} {p : (Fin n → Word) → ℕ → Bool}
    (hb : NatPoly b)
    (hp : BoolPoly (fun T => p (T ∘ Fin.castSucc) ((T (Fin.last n)).length))) :
    Poly (fun S => (List.range (b S)).map (p S)) := by
  apply (tabulate hb hp).congr
  intro S
  simp only [snoc_prefix, Fin.snoc_last, unary, List.length_replicate]

end Poly
end WordExpressions

/- Proof-generating syntactic closure for fixed word arithmetic.  Each leaf is
an already proved finite-word implementation, not an evaluation oracle. -/

namespace WordExpressions
namespace NatPoly
variable {n : ℕ}
theorem iteProp {p : (Fin n → Word) → Prop} [∀ S, Decidable (p S)]
    {f g : (Fin n → Word) → ℕ} (hp : BoolPoly (fun S => decide (p S)))
    (hf : NatPoly f) (hg : NatPoly g) : NatPoly (fun S => if p S then f S else g S) := by
  simpa only [decide_eq_true_eq] using ite hp hf hg
end NatPoly
namespace BoolPoly
variable {n : ℕ}
theorem ite {p f g : (Fin n → Word) → Bool} (hp : BoolPoly p) (hf : BoolPoly f) (hg : BoolPoly g) :
    BoolPoly (fun S => if p S then f S else g S) := by
  apply (Poly.branches hp hf hg).congr
  intro S
  dsimp only
  cases p S <;> rfl
theorem iteProp {p : (Fin n → Word) → Prop} [∀ S, Decidable (p S)]
    {f g : (Fin n → Word) → Bool} (hp : BoolPoly (fun S => decide (p S)))
    (hf : BoolPoly f) (hg : BoolPoly g) : BoolPoly (fun S => if p S then f S else g S) := by
  simpa only [decide_eq_true_eq] using ite hp hf hg
end BoolPoly
end WordExpressions

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.NumericKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace NumericKernel

def lookup (R : Word) (a b : ℕ) : Bool := R[Nat.pair a b]?.getD false

def digit (base v i : ℕ) : ℕ := v / base^i % base

def vectorMatch (N width : ℕ) (trans R : Word) (a z v : ℕ) : Bool :=
  (List.range width).all (fun i => (List.range N).any (fun y =>
    trans[Nat.pair a (Nat.pair z (Nat.pair i y))]?.getD false &&
      lookup R y (digit N v i)))

def countMatch (N width branch : ℕ) (active trans R : Word) (a v : ℕ) : ℕ :=
  ((List.range branch).map (fun z =>
    if lookup active a z && vectorMatch N width trans R a z v then 1 else 0)).sum

def entry (N width branch cap : ℕ) (active trans R : Word) (a b : ℕ) : Bool :=
  lookup R a b && (List.range (min (N^width) cap)).all (fun v =>
    decide (countMatch N width branch active trans R a v =
      countMatch N width branch active trans R b v))

def step (N width branch cap : ℕ) (active trans R : Word) : Word :=
  (List.range (Nat.pair N N+1)).map (fun j =>
    entry N width branch cap active trans R (Nat.unpair j).1 (Nat.unpair j).2)

def table (N width branch cap : ℕ) (active trans initial : Word) (rounds : ℕ) : Word :=
  (step N width branch cap active trans)^[rounds] initial

end NumericKernel
namespace WordExpressions.NatPoly
variable {n : ℕ}

theorem digit {b v i : (Fin n → Word) → ℕ}
    (hb : NatPoly b) (hv : NatPoly v) (hi : NatPoly i) :
    NatPoly (fun S => NumericKernel.digit (b S) (v S) (i S)) := by
  apply (mod (div hv (cappedPow hb hi (succ hv))) hb).congr
  intro S
  simp only [div_cap, NumericKernel.digit]

end WordExpressions.NatPoly

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.GraphEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace NumericGraph

/-- Row-major access, with a total default outside the matrix. -/
def edge (n : ℕ) (W : Word) (i j : ℕ) : Bool := W[i*n+j]?.getD false

def simple (n : ℕ) (W : Word) : Bool :=
  (List.range n).all (fun i => !edge n W i i &&
    (List.range n).all (fun j => decide (edge n W i j = edge n W j i)))

def iso (n cap : ℕ) (W V : Word) : Bool :=
  (List.range (min (n^n) cap)).any (fun f => (List.range n).all (fun i =>
    (List.range n).all (fun j =>
      decide ((NumericKernel.digit n f i = NumericKernel.digit n f j) = (i=j)) &&
      decide (edge n W i j = edge n V (NumericKernel.digit n f i) (NumericKernel.digit n f j)))))

/-- A canonically normalized mate: every simple graph occurs among these
masks, while diagonal/asymmetric mask bits do not admit malformed graphs. -/
def mateEdge (n mask i j : ℕ) : Bool :=
  decide (i ≠ j) && mask.testBit (min i j*n+max i j)

def mate (n mask : ℕ) : Word :=
  (List.range (n*n)).map (fun t => mateEdge n mask (t/n) (t%n))

end NumericGraph

namespace NumericGraph

/-- Entries of a rectangular row-major serialization. -/
theorem rows_entry (n m : ℕ) (f : Fin n → Fin m → Bool) (i : Fin n) (j : Fin m) :
    (((List.ofFn fun a => List.ofFn (f a)).flatten)[i.val*m+j.val]?).getD false = f i j := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    simp only [List.ofFn_succ, List.flatten_cons]
    refine Fin.cases ?_ (fun a => ?_) i
    · simp only [Fin.val_zero, zero_mul, zero_add]
      rw [List.getElem?_append_left (by simp)]
      simp
    · rw [List.getElem?_append_right (by simp only [List.length_ofFn, Fin.val_succ]; nlinarith)]
      simp only [List.length_ofFn, Fin.val_succ]
      rw [show (a.val+1)*m+j.val-m = a.val*m+j.val by simp only [Nat.add_mul, one_mul]; omega]
      exact ih (fun x => f x.succ) a

@[simp] theorem edge_matrixWord (G : Graph) (i j : Fin G.order) :
    edge G.order (matrixWord G) i j = G.edge i j := rows_entry _ _ _ i j

theorem simple_true (n : ℕ) (W : Word) : simple n W = true ↔
    (∀ i : Fin n, edge n W i i = false) ∧
    (∀ i j : Fin n, edge n W i j = edge n W j i) := by
  simp only [simple, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨fun i => by simpa using (h i i.isLt).1, fun i j => (h i i.isLt).2 j j.isLt⟩
  · rintro ⟨hl,hs⟩ i hi
    exact ⟨by simpa using hl ⟨i,hi⟩, fun j hj => hs ⟨i,hi⟩ ⟨j,hj⟩⟩

@[simp] theorem simple_matrixWord (G : Graph) : simple G.order (matrixWord G) = true :=
  (simple_true _ _).mpr ⟨fun i => by simpa using G.loopless i,
    fun i j => by simpa using G.symmetric i j⟩

@[simp] theorem edge_mate (n mask : ℕ) (i j : Fin n) :
    edge n (mate n mask) i j = mateEdge n mask i j := by
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  have hij : i.val*n+j.val < n*n := by nlinarith [i.isLt,j.isLt]
  simp only [edge, mate, List.getElem?_map, List.getElem?_range hij, Option.map_some, Option.getD_some]
  rw [Nat.mul_comm i.val n, Nat.mul_add_div hn, Nat.div_eq_of_lt j.isLt, Nat.add_zero]
  simp only [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_eq_of_lt j.isLt]

/-- Little-endian packing, used solely for proving exhaustive mask coverage. -/
def number : Word → ℕ
  | [] => 0
  | b::w => Nat.bit b (number w)

@[simp] theorem testBit_number (W : Word) (i : ℕ) :
    (number W).testBit i = W[i]?.getD false := by
  induction W generalizing i with
  | nil => simp [number]
  | cons b W ih =>
    cases i with
    | zero => simp [number]
    | succ i => simpa only [number, Nat.testBit_bit_succ, List.getElem?_cons_succ] using ih i

end NumericGraph

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.NumericRefinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace NumericWL
open NumericKernel

def left (t a : ℕ) : Bool := decide (a<t)
def code (t a : ℕ) : ℕ := if a<t then a else a-t

def pairTable (N : ℕ) (p : ℕ → ℕ → Bool) : Word :=
  (List.range (Nat.pair N N+1)).map (fun x => p x.unpair.1 x.unpair.2)

def transTable (N width branch : ℕ) (p : ℕ → ℕ → ℕ → ℕ → Bool) : Word :=
  (List.range (Nat.pair N (Nat.pair branch (Nat.pair width N))+1)).map (fun x =>
    p x.unpair.1 x.unpair.2.unpair.1 x.unpair.2.unpair.2.unpair.1 x.unpair.2.unpair.2.unpair.2)

def equalCounts (t : ℕ) (W : Word) : Bool :=
  (List.range (t+t)).all (fun a => decide (
    ((List.range t).map (fun b => if lookup W b a then 1 else 0)).sum =
    ((List.range t).map (fun b => if lookup W (t+b) a then 1 else 0)).sum))

def selectedEdge (n t : ℕ) (W V : Word) (a i j : ℕ) : Bool :=
  if left t a then NumericGraph.edge n W i j else NumericGraph.edge n V i j

def neighborActive (n : ℕ) (W V : Word) (a z : ℕ) : Bool :=
  selectedEdge n n W V a (code n a) z

def neighborTrans (n a z _i y : ℕ) : Bool :=
  decide (left n a = left n y) && decide (code n y = z)

def neighbor (n cap : ℕ) (W V : Word) : Bool :=
  let N := n+n
  equalCounts n (table N 1 n cap (pairTable N (neighborActive n W V))
    (transTable N 1 n (neighborTrans n)) (pairTable N (fun _ _ => true)) (N*N))

def tupleInitial (n k t : ℕ) (W V : Word) (a b : ℕ) : Bool :=
  (List.range k).all (fun i => (List.range k).all (fun j =>
    decide ((digit n (code t a) i = digit n (code t a) j) =
      (digit n (code t b) i = digit n (code t b) j)) &&
    decide (selectedEdge n t W V a (digit n (code t a) i) (digit n (code t a) j) =
      selectedEdge n t W V b (digit n (code t b) i) (digit n (code t b) j))))

def tupleTrans (n k t a z i y : ℕ) : Bool :=
  decide (left t a = left t y) && (List.range k).all (fun j =>
    decide (digit n (code t y) j = if j=i then z else digit n (code t a) j))

def tuple (n k cap : ℕ) (W V : Word) : Bool :=
  let t := min (n^k) cap
  let N := t+t
  equalCounts t (table N k n cap (pairTable N (fun _ _ => true))
    (transTable N k n (tupleTrans n k t)) (pairTable N (tupleInitial n k t W V)) (N*N))

def equivalent (n k cap : ℕ) (W V : Word) : Bool :=
  if k=1 then neighbor n cap W V else tuple n k cap W V

end NumericWL

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.DimensionDecider
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace DimensionDecider

def matrix (n : ℕ) (w : Word) : Word := (w.drop (n+1)).take (n*n)
def bits (n : ℕ) (w : Word) : Word := w.drop (n+1+n*n)
def valid (n : ℕ) (w : Word) : Bool :=
  decide (0<n) && decide (w.take (n+1) = List.replicate n true ++ [false]) &&
    decide ((matrix n w).length=n*n) && (bits n w)[0]?.getD false

def identifies (n k cap : ℕ) (W : Word) : Bool :=
  (List.range (min (2^(n*n)) cap)).all (fun x =>
    !(NumericWL.equivalent n k cap W (NumericGraph.mate n x)) ||
      NumericGraph.iso n cap W (NumericGraph.mate n x))

def atOrder (n cap : ℕ) (w : Word) : Bool :=
  valid n w && NumericGraph.simple n (matrix n w) &&
    identifies n (min (binaryValue (bits n w)) (max 2 n)) cap (matrix n w)

def decideWord (cap : ℕ) (w : Word) : Bool :=
  (List.range (w.length+1)).any (fun n => atOrder n cap w)

def budget (m : ℕ) : ℕ := 2^(64*(m+1)^6)

end DimensionDecider

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.FinitePresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification
/- Polynomially presented finite types. Membership refers to actual natural
codes and all iteration bounds have literal unary word realizers. -/
namespace FinitePresentation
open WordExpressions

structure Presented (A : Word → Type) where
  code : (w : Word) → A w ↪ ℕ
  bound : Word → ℕ
  good : Word → ℕ → Bool
  code_lt : ∀ w x, code w x < bound w
  good_iff : ∀ w i, good w i = true ↔ ∃ x, code w x = i
  bound_poly : NatPoly (fun S : Fin 1 → Word => bound (S 0))
  good_poly : BoolPoly (fun S : Fin 2 → Word => good (S 0) (S 1).length)

namespace Presented
variable {A B : Word → Type}

@[simp] theorem good_code (P : Presented A) (w : Word) (x : A w) : P.good w (P.code w x)=true :=
  (P.good_iff w _).mpr ⟨x,rfl⟩

theorem bound_poly_of (P : Presented A) {n} {w : (Fin n → Word) → Word} (hw : WordExpressions.Poly w) :
    NatPoly (fun S => P.bound (w S)) := by
  exact P.bound_poly.subst (g := fun _ => w) (fun _ => hw)

theorem good_poly_of (P : Presented A) {n} {w : (Fin n → Word) → Word} {i : (Fin n → Word) → ℕ}
    (hw : WordExpressions.Poly w) (hi : NatPoly i) : BoolPoly (fun S => P.good (w S) (i S)) := by
  have h := P.good_poly.subst (g := ![w, fun S => unary (i S)]) (by intro i; fin_cases i; exacts [hw,hi])
  simpa [unary] using h

noncomputable def fixed (A : Type) [Fintype A] : Presented (fun _ => A) where
  code _ := NaturalCode.fixed A
  bound _ := Fintype.card A
  good _ i := decide (i<Fintype.card A)
  code_lt _ x := (Fintype.equivFin A x).isLt
  good_iff w i := by
    simp only [decide_eq_true_eq]
    constructor
    · intro h
      exact ⟨(Fintype.equivFin A).symm ⟨i,h⟩, congrArg Fin.val ((Fintype.equivFin A).apply_symm_apply _)⟩
    · rintro ⟨x,rfl⟩; exact (Fintype.equivFin A x).isLt
  bound_poly := NatPoly.const _
  good_poly := NatPoly.lt (NatPoly.var _) (NatPoly.const _)

def fin (f : Word → ℕ) (hf : NatPoly (fun S : Fin 1 → Word => f (S 0))) :
    Presented (fun w => Fin (f w)) where
  code w := NaturalCode.fin (f w)
  bound := f
  good w i := decide (i<f w)
  code_lt _ x := x.isLt
  good_iff w i := by simp only [decide_eq_true_eq]; exact ⟨fun h => ⟨⟨i,h⟩,rfl⟩, fun ⟨x,h⟩ => h ▸ x.isLt⟩
  bound_poly := hf
  good_poly := NatPoly.lt (NatPoly.var _) (hf.rename (fun _ => 0))

def subtype (P : Presented A) (p : (w : Word) → A w → Prop) (q : Word → ℕ → Bool)
    (hq : ∀ w x, q w (P.code w x)=true ↔ p w x)
    (hp : BoolPoly (fun S : Fin 2 → Word => q (S 0) (S 1).length)) :
    Presented (fun w => {x : A w // p w x}) where
  code w := NaturalCode.subtype (P.code w) (p w)
  bound := P.bound
  good w i := P.good w i && q w i
  code_lt w x := P.code_lt w x.val
  good_iff w i := by
    simp only [Bool.and_eq_true]
    constructor
    · rintro ⟨h,hq'⟩
      obtain ⟨x,rfl⟩ := (P.good_iff w i).mp h
      exact ⟨⟨x,(hq w x).mp hq'⟩,rfl⟩
    · rintro ⟨x,rfl⟩
      exact ⟨P.good_code w x.val,(hq w x.val).mpr x.property⟩
  bound_poly := P.bound_poly
  good_poly := BoolPoly.and P.good_poly hp

def sigma (P : Presented A) (B : (w : Word) → A w → Type)
    (c : ∀ w x, B w x ↪ ℕ) (b : Word → ℕ) (q : Word → ℕ → ℕ → Bool)
    (hc : ∀ w x y, c w x y < b w)
    (hq : ∀ w x i, q w (P.code w x) i=true ↔ ∃ y, c w x y=i)
    (hb : NatPoly (fun S : Fin 1 → Word => b (S 0)))
    (hp : BoolPoly (fun S : Fin 3 → Word => q (S 0) (S 1).length (S 2).length)) :
    Presented (fun w => Σ x, B w x) where
  code w := NaturalCode.sigma (P.code w) (c w)
  bound w := Nat.pair (P.bound w) (b w)+1
  good w i := P.good w (Nat.unpair i).1 && q w (Nat.unpair i).1 (Nat.unpair i).2
  code_lt w x := by
    exact (Nat.pair_lt_pair_left _ (P.code_lt w x.1)).trans
      ((Nat.pair_lt_pair_right _ (hc w x.1 x.2)).trans_le (Nat.le_succ _))
  good_iff w i := by
    simp only [Bool.and_eq_true]
    constructor
    · rintro ⟨h,hq'⟩
      obtain ⟨x,hx⟩ := (P.good_iff w _).mp h
      rw [← hx] at hq'
      obtain ⟨y,hy⟩ := (hq w x _).mp hq'
      exact ⟨⟨x,y⟩, by change Nat.pair _ _ = i; rw [hx,hy,Nat.pair_unpair]⟩
    · rintro ⟨⟨x,y⟩,rfl⟩
      change P.good w (Nat.unpair (Nat.pair _ _)).1=true ∧ q w (Nat.unpair (Nat.pair _ _)).1 (Nat.unpair (Nat.pair _ _)).2=true
      rw [Nat.unpair_pair]
      exact ⟨P.good_code w x,(hq w x _).mpr ⟨y,rfl⟩⟩
  bound_poly := NatPoly.succ (NatPoly.pair P.bound_poly hb)
  good_poly := by
    apply BoolPoly.and
    · apply P.good_poly_of <;> (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
    · have h := hp.subst (g := ![fun S : Fin 2 → Word => S 0,
        fun S => unary (Nat.unpair (S 1).length).1, fun S => unary (Nat.unpair (S 1).length).2])
        (by intro i; fin_cases i <;> (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange))
      simpa [unary] using h

end Presented
end FinitePresentation

namespace FinitePresentation.Presented
open WordExpressions
variable {A B : Word → Type}

def retype (P : Presented A) (e : ∀ w, B w ≃ A w) : Presented B where
  code w := (e w).toEmbedding.trans (P.code w)
  bound := P.bound
  good := P.good
  code_lt w x := P.code_lt w (e w x)
  good_iff w i := (P.good_iff w i).trans ⟨fun ⟨x,h⟩ => ⟨(e w).symm x, by simpa using h⟩,
    fun ⟨x,h⟩ => ⟨e w x,h⟩⟩
  bound_poly := P.bound_poly
  good_poly := P.good_poly

def prod (P : Presented A) (Q : Presented B) : Presented (fun w => A w × B w) :=
  (P.sigma (fun w _ => B w) (fun w _ => Q.code w) Q.bound (fun w _ => Q.good w)
    (fun w _ y => Q.code_lt w y) (fun w _ i => Q.good_iff w i) Q.bound_poly
    (Q.good_poly.rename ![0,2])).retype (fun _ => Equiv.sigmaEquivProd _ _ |>.symm)

def sum (P : Presented A) (Q : Presented B) : Presented (fun w => A w ⊕ B w) where
  code w := NaturalCode.sum (P.code w) (Q.code w)
  bound w := 2*(P.bound w+Q.bound w)+2
  good w i := if i%2=0 then P.good w (i/2) else Q.good w (i/2)
  code_lt w x := by cases x with
    | inl a => have := P.code_lt w a; change 2*P.code w a < _; omega
    | inr b => have := Q.code_lt w b; change 2*Q.code w b+1 < _; omega
  good_iff w i := by
    by_cases he : i%2=0
    · simp only [he, ↓reduceIte, P.good_iff]
      constructor
      · rintro ⟨a,ha⟩
        refine ⟨.inl a, ?_⟩
        change 2*P.code w a=i
        omega
      · rintro ⟨a,ha⟩
        cases a with
        | inl a => exact ⟨a, by change 2*P.code w a=i at ha; omega⟩
        | inr b => change 2*Q.code w b+1=i at ha; omega
    · simp only [he, ↓reduceIte, Q.good_iff]
      constructor
      · rintro ⟨b,hb⟩
        refine ⟨.inr b, ?_⟩
        change 2*Q.code w b+1=i
        omega
      · rintro ⟨a,ha⟩
        cases a with
        | inl a => change 2*P.code w a=i at ha; omega
        | inr b => exact ⟨b, by change 2*Q.code w b+1=i at ha; omega⟩
  bound_poly := by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange); exact P.bound_poly; exact Q.bound_poly
  good_poly := by
    apply BoolPoly.iteProp
    · (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
    · apply P.good_poly_of <;> (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
    · apply Q.good_poly_of <;> (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)

def option (P : Presented A) : Presented (fun w => Option (A w)) where
  code w := NaturalCode.option (P.code w)
  bound w := P.bound w+1
  good w i := decide (i=0) || (decide (0 < i) && P.good w (i-1))
  code_lt w x := by cases x with
    | none => change 0 < P.bound w+1; omega
    | some a => exact Nat.succ_lt_succ (P.code_lt w a)
  good_iff w i := by
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro (rfl | ⟨hi,hg⟩)
      · exact ⟨none,rfl⟩
      · obtain ⟨a,ha⟩ := (P.good_iff w _).mp hg
        exact ⟨some a, by change P.code w a+1=i; omega⟩
    · rintro ⟨x,rfl⟩
      cases x with
      | none => exact Or.inl rfl
      | some a => exact Or.inr ⟨by change 0 < P.code w a+1; omega, by change P.good w (P.code w a+1-1)=true; simp⟩
  bound_poly := NatPoly.succ P.bound_poly
  good_poly := BoolPoly.or (NatPoly.eqtest (NatPoly.var _) (NatPoly.const _))
    (BoolPoly.and (NatPoly.lt (NatPoly.const 0) (NatPoly.var _))
      (P.good_poly_of (Poly.var _) (NatPoly.sub (NatPoly.var _) (NatPoly.const 1))))

def bool : Presented (fun _ => Bool) where
  code _ := NaturalCode.bool
  bound _ := 2
  good _ i := decide (i<2)
  code_lt _ x := by cases x <;> decide
  good_iff _ i := by
    simp only [decide_eq_true_eq]
    constructor
    · intro hi
      interval_cases i
      · exact ⟨false,rfl⟩
      · exact ⟨true,rfl⟩
    · rintro ⟨x,rfl⟩; cases x <;> decide
  bound_poly := NatPoly.const _
  good_poly := NatPoly.lt (NatPoly.var _) (NatPoly.const 2)

def unit : Presented (fun _ => Unit) where
  code _ := NaturalCode.unit
  bound _ := 1
  good _ i := decide (i=0)
  code_lt _ x := by cases x; decide
  good_iff _ i := by simp only [decide_eq_true_eq]; exact ⟨fun h => ⟨(),h.symm⟩,fun ⟨_,h⟩ => h.symm⟩
  bound_poly := NatPoly.const _
  good_poly := NatPoly.eqtest (NatPoly.var _) (NatPoly.const 0)

end FinitePresentation.Presented

namespace FinitePresentation.Presented
open WordExpressions NumericFinite
variable {A : Word → Type}

abbrev card (P : Presented A) (w : Word) := count (P.bound w) (P.good w)
abbrev select (P : Presented A) (w : Word) (i : ℕ) := NumericFinite.select (P.bound w) (P.good w) i

theorem rank_lt (P : Presented A) (w : Word) (x : A w) : count (P.code w x) (P.good w) < P.card w :=
  count_strict (P.code_lt w x) (P.good_code w x)

theorem select_good (P : Presented A) (w : Word) {i : ℕ} (hi : i<P.card w) :
    P.good w (P.select w i)=true := by
  rw [select, select_correct _ _ _ hi]
  exact (mem_elements.mp (List.getElem_mem hi)).2

theorem rank_select (P : Presented A) (w : Word) {i : ℕ} (hi : i<P.card w) :
    count (P.select w i) (P.good w)=i := by
  rw [select, select_correct _ _ _ hi]
  exact NumericFinite.rank _ _ _ hi

theorem select_rank (P : Presented A) (w : Word) (x : A w) :
    P.select w (count (P.code w x) (P.good w))=P.code w x := by
  have hr := P.rank_select w (P.rank_lt w x)
  have hg := P.select_good w (P.rank_lt w x)
  rcases lt_trichotomy (P.select w (count (P.code w x) (P.good w))) (P.code w x) with hl | he | hl
  · have := count_strict hl hg; omega
  · exact he
  · have := count_strict hl (P.good_code w x); omega

noncomputable def decode (P : Presented A) (w : Word) (i : Fin (P.card w)) : A w :=
  Classical.choose ((P.good_iff w _).mp (P.select_good w i.isLt))

theorem code_decode (P : Presented A) (w : Word) (i : Fin (P.card w)) :
    P.code w (P.decode w i)=P.select w i :=
  Classical.choose_spec ((P.good_iff w _).mp (P.select_good w i.isLt))

noncomputable def rankEquiv (P : Presented A) (w : Word) : A w ≃ Fin (P.card w) where
  toFun x := ⟨count (P.code w x) (P.good w), P.rank_lt w x⟩
  invFun := P.decode w
  left_inv x := by apply (P.code w).injective; rw [P.code_decode, P.select_rank]
  right_inv i := by apply Fin.ext; exact (congrArg (fun j => count j (P.good w)) (P.code_decode w i)).trans (P.rank_select w i.isLt)

@[simp] theorem card_eq (P : Presented A) (w : Word) [Fintype (A w)] : P.card w=Fintype.card (A w) := by
  simpa only [Fintype.card_fin] using (Fintype.card_congr (P.rankEquiv w)).symm

theorem card_poly (P : Presented A) : NatPoly (fun S : Fin 1 → Word => P.card (S 0)) := by
  apply (NatPoly.filterCount P.bound_poly P.good_poly).congr
  intro S
  simp [Fin.snoc, unary, card]

end FinitePresentation.Presented

namespace FinitePresentation
open WordExpressions
variable {A : Word → Type}

structure PresentedGraph (P : Presented A) (G : ∀ w, SimpleGraph (A w)) where
  adjacent : Word → ℕ → ℕ → Bool
  adjacent_iff : ∀ w x y, adjacent w (P.code w x) (P.code w y)=true ↔ (G w).Adj x y
  adjacent_poly : BoolPoly (fun S : Fin 3 → Word => adjacent (S 0) (S 1).length (S 2).length)

end FinitePresentation

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.PresentationArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace FinitePresentation
open WordExpressions
variable {A B C : Word → Type}

structure Number (P : Presented A) (f : ∀ w, A w → ℕ) where
  eval : Word → ℕ → ℕ
  correct : ∀ w x, eval w (P.code w x)=f w x
  poly : NatPoly (fun S : Fin 2 → Word => eval (S 0) (S 1).length)

structure Test (P : Presented A) (f : ∀ w, A w → Bool) where
  eval : Word → ℕ → Bool
  correct : ∀ w x, eval w (P.code w x)=f w x
  poly : BoolPoly (fun S : Fin 2 → Word => eval (S 0) (S 1).length)

abbrev Map (P : Presented A) (Q : Presented B) (f : ∀ w, A w → B w) :=
  Number P (fun w x => Q.code w (f w x))

namespace Number
variable {P : Presented A} {f g : ∀ w, A w → ℕ}

theorem eval_poly (F : Number P f) {n} {w : (Fin n → Word) → Word} {i : (Fin n → Word) → ℕ}
    (hw : Poly w) (hi : NatPoly i) : NatPoly (fun S => F.eval (w S) (i S)) := by
  have h := F.poly.subst (g := ![w,fun S => unary (i S)]) (by intro j; fin_cases j; exacts [hw,hi])
  simpa [unary] using h

def congr (F : Number P f) (h : ∀ w x, f w x=g w x) : Number P g :=
  { F with correct := fun w x => (F.correct w x).trans (h w x) }

def code (P : Presented A) : Number P (fun w x => P.code w x) :=
  ⟨fun _ i => i, fun _ _ => rfl, NatPoly.var 1⟩

def param (P : Presented A) (f : Word → ℕ) (h : NatPoly (fun S : Fin 1 → Word => f (S 0))) :
    Number P (fun w _ => f w) :=
  ⟨fun w _ => f w, fun _ _ => rfl, h.rename (fun _ => 0)⟩

def const (P : Presented A) (k : ℕ) : Number P (fun _ _ => k) := param P (fun _ => k) (NatPoly.const k)

def add (F : Number P f) (G : Number P g) : Number P (fun w x => f w x+g w x) :=
  ⟨fun w i => F.eval w i+G.eval w i, fun w x => by rw [F.correct,G.correct], NatPoly.add F.poly G.poly⟩
def mul (F : Number P f) (G : Number P g) : Number P (fun w x => f w x*g w x) :=
  ⟨fun w i => F.eval w i*G.eval w i, fun w x => by rw [F.correct,G.correct], NatPoly.mul F.poly G.poly⟩
def pair (F : Number P f) (G : Number P g) : Number P (fun w x => Nat.pair (f w x) (g w x)) :=
  ⟨fun w i => Nat.pair (F.eval w i) (G.eval w i), fun w x => by rw [F.correct,G.correct], NatPoly.pair F.poly G.poly⟩

def comp {Q : Presented B} {h : ∀ w, A w → B w} {f : ∀ w, B w → ℕ}
    (F : Number Q f) (H : Map P Q h) : Number P (fun w x => f w (h w x)) where
  eval w i := F.eval w (H.eval w i)
  correct w x := by rw [H.correct,F.correct]
  poly := F.eval_poly (Poly.var 0) H.poly

end Number
namespace Test
variable {P : Presented A} {f g : ∀ w, A w → Bool}

theorem eval_poly (F : Test P f) {n} {w : (Fin n → Word) → Word} {i : (Fin n → Word) → ℕ}
    (hw : Poly w) (hi : NatPoly i) : BoolPoly (fun S => F.eval (w S) (i S)) := by
  have h := F.poly.subst (g := ![w,fun S => unary (i S)]) (by intro j; fin_cases j; exacts [hw,hi])
  simpa [unary] using h

def congr (F : Test P f) (h : ∀ w x, f w x=g w x) : Test P g :=
  { F with correct := fun w x => (F.correct w x).trans (h w x) }

def const (P : Presented A) (b : Bool) : Test P (fun _ _ => b) :=
  ⟨fun _ _ => b,fun _ _ => rfl,BoolPoly.const b⟩

def not (F : Test P f) : Test P (fun w x => !(f w x)) :=
  ⟨fun w i => !(F.eval w i), fun w x => by rw [F.correct], BoolPoly.not F.poly⟩

def numEq {f g : ∀ w, A w → ℕ} (F : Number P f) (G : Number P g) : Test P (fun w x => decide (f w x=g w x)) :=
  ⟨fun w i => decide (F.eval w i=G.eval w i), fun w x => by rw [F.correct,G.correct], NatPoly.eqtest F.poly G.poly⟩

def comp {Q : Presented B} {h : ∀ w, A w → B w} {f : ∀ w, B w → Bool}
    (F : Test Q f) (H : Map P Q h) : Test P (fun w x => f w (h w x)) where
  eval w i := F.eval w (H.eval w i)
  correct w x := by rw [H.correct,F.correct]
  poly := F.eval_poly (Poly.var 0) H.poly

end Test
namespace Number
variable {P : Presented A}

def ite {p : ∀ w, A w → Bool} {f g : ∀ w, A w → ℕ}
    (H : Test P p) (F : Number P f) (G : Number P g) : Number P (fun w x => if p w x then f w x else g w x) where
  eval w i := if H.eval w i then F.eval w i else G.eval w i
  correct w x := by rw [H.correct,F.correct,G.correct]
  poly := NatPoly.ite H.poly F.poly G.poly

end Number
namespace Map

def id (P : Presented A) : Map P P (fun _ x => x) := Number.code P

def fst (P : Presented A) (Q : Presented B) : Map (P.prod Q) P (fun _ x => x.1) where
  eval _ i := (Nat.unpair i).1
  correct w x := by change (Nat.unpair (Nat.pair _ _)).1 = _; rw [Nat.unpair_pair]; rfl
  poly := NatPoly.unpair_fst (NatPoly.var _)

def snd (P : Presented A) (Q : Presented B) : Map (P.prod Q) Q (fun _ x => x.2) where
  eval _ i := (Nat.unpair i).2
  correct w x := by change (Nat.unpair (Nat.pair _ _)).2 = _; rw [Nat.unpair_pair]; rfl
  poly := NatPoly.unpair_snd (NatPoly.var _)

def pair {P : Presented A} {Q : Presented B} {R : Presented C}
    {f : ∀ w, A w → B w} {g : ∀ w, A w → C w} (F : Map P Q f) (G : Map P R g) :
    Map P (Q.prod R) (fun w x => (f w x,g w x)) := Number.pair F G

end Map
end FinitePresentation

namespace FinitePresentation
open WordExpressions
variable {A B C : Word → Type}

namespace Number
variable {P : Presented A} {Q : Presented B}

def sumCases {f : ∀ w, A w → ℕ} {g : ∀ w, B w → ℕ} (F : Number P f) (G : Number Q g) :
    Number (P.sum Q) (fun w x => x.elim (f w) (g w)) where
  eval w i := if i%2=0 then F.eval w (i/2) else G.eval w (i/2)
  correct w x := by
    cases x with
    | inl a => change (if (2*P.code w a)%2=0 then F.eval w ((2*P.code w a)/2) else G.eval w ((2*P.code w a)/2))=_; simp [F.correct]
    | inr b => change (if (2*Q.code w b+1)%2=0 then F.eval w ((2*Q.code w b+1)/2) else G.eval w ((2*Q.code w b+1)/2))=_; simp [show (2*Q.code w b+1)/2=Q.code w b by omega, G.correct]
  poly := NatPoly.iteProp (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange))
    (F.eval_poly (Poly.var _) (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange))) (G.eval_poly (Poly.var _) (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)))

def optionCases {f : ∀ w, A w → ℕ} (F : Number P f) (g : Word → ℕ)
    (hg : NatPoly (fun S : Fin 1 → Word => g (S 0))) :
    Number P.option (fun w x => x.elim (g w) (f w)) where
  eval w i := if i=0 then g w else F.eval w (i-1)
  correct w x := by cases x with
    | none => rfl
    | some a => change (if P.code w a+1=0 then g w else F.eval w (P.code w a+1-1))=_; simp [F.correct]
  poly := NatPoly.iteProp (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)) (hg.rename (fun _ => 0))
    (F.eval_poly (Poly.var _) (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)))

def envelope {f : ∀ w, A w → ℕ} (F : Number P f) (w : Word) : ℕ :=
  ((List.range (P.bound w)).map (F.eval w)).sum+1

theorem lt_envelope {f : ∀ w, A w → ℕ} (F : Number P f) (w : Word) (x : A w) :
    f w x < F.envelope w := by
  have h := List.le_sum_of_mem (List.mem_map.mpr ⟨P.code w x, List.mem_range.mpr (P.code_lt w x), F.correct w x⟩)
  exact Nat.lt_succ_of_le h

theorem envelope_poly {f : ∀ w, A w → ℕ} (F : Number P f) :
    NatPoly (fun S : Fin 1 → Word => F.envelope (S 0)) := by
  exact NatPoly.succ (NatPoly.sumRange P.bound_poly (by simpa using F.poly))

end Number
namespace Presented

def finSigma (P : Presented A) {f : ∀ w, A w → ℕ} (F : Number P f) :
    Presented (fun w => Σ x : A w, Fin (f w x)) :=
  P.sigma (fun w x => Fin (f w x)) (fun _ _ => NaturalCode.fin _) F.envelope
    (fun w i j => decide (j<F.eval w i))
    (fun w x y => y.isLt.trans (F.lt_envelope w x))
    (by intro w x i; rw [F.correct, decide_eq_true_eq]; exact ⟨fun h => ⟨⟨i,h⟩,rfl⟩,fun ⟨j,h⟩ => h ▸ j.isLt⟩)
    F.envelope_poly (NatPoly.lt (NatPoly.var 2) (F.eval_poly (Poly.var 0) (NatPoly.var 1)))

def restrict (P : Presented A) (p : ∀ w, A w → Prop) [∀ w x, Decidable (p w x)]
    (H : Test P (fun w x => decide (p w x))) : Presented (fun w => {x : A w // p w x}) :=
  P.subtype p H.eval (by intro w x; rw [H.correct, decide_eq_true_eq]) H.poly

end Presented
namespace Map
variable {P : Presented A} {Q : Presented B} {R : Presented C}

def comp {f : ∀ w, A w → B w} {g : ∀ w, B w → C w} (G : Map Q R g) (F : Map P Q f) :
    Map P R (fun w x => g w (f w x)) := Number.comp (P := P) (Q := Q) (h := f) (f := fun w y => R.code w (g w y)) G F

def none (P : Presented A) (Q : Presented B) : Map P Q.option (fun _ _ => none) := Number.const P 0

def retype (P : Presented A) (e : ∀ w, B w ≃ A w) : Map (P.retype e) P (fun w x => e w x) :=
  Number.code (P.retype e)

def sigmaFst (P : Presented A) {f : ∀ w, A w → ℕ} (F : Number P f) :
    Map (P.finSigma F) P (fun _ x => x.1) where
  eval _ i := (Nat.unpair i).1
  correct w x := by change (Nat.unpair (Nat.pair _ _)).1=_; rw [Nat.unpair_pair]
  poly := NatPoly.unpair_fst (NatPoly.var _)

end Map
namespace Test
variable {P : Presented A} {Q : Presented B}

def ite {p f g : ∀ w, A w → Bool} (H : Test P p) (F : Test P f) (G : Test P g) :
    Test P (fun w x => if p w x then f w x else g w x) where
  eval w i := if H.eval w i then F.eval w i else G.eval w i
  correct w x := by rw [H.correct,F.correct,G.correct]
  poly := BoolPoly.ite H.poly F.poly G.poly

def eq [∀ w, DecidableEq (B w)] {f g : ∀ w, A w → B w} (F : Map P Q f) (G : Map P Q g) :
    Test P (fun w x => decide (f w x=g w x)) :=
  (numEq F G).congr (by intro w x; simp only [(Q.code w).injective.eq_iff])

end Test
end FinitePresentation

namespace WordExpressions.NatPoly
variable {n : ℕ}

theorem fixedTable (b : ℕ) (f : ℕ → ℕ) {i : (Fin n → Word) → ℕ} (hi : NatPoly i) :
    NatPoly (fun S => if i S<b then f (i S) else 0) := by
  induction b with
  | zero => simpa using const (n := n) 0
  | succ b ih =>
    apply (iteProp (eqtest hi (const b)) (const (f b)) ih).congr
    intro S
    by_cases h : i S=b
    · simp [h]
    · by_cases h' : i S<b
      · simp [h,h',show i S<b+1 by omega]
      · simp [h,h',show ¬i S<b+1 by omega]

end WordExpressions.NatPoly
namespace WordExpressions.BoolPoly
variable {n : ℕ}

theorem fixedTable (b : ℕ) (f : ℕ → Bool) {i : (Fin n → Word) → ℕ} (hi : NatPoly i) :
    BoolPoly (fun S => if i S<b then f (i S) else false) := by
  apply (Poly.nth (Poly.const ((List.range b).map f)) hi).congr
  intro S
  by_cases h : i S<b
  · simp [h]
  · simp [h]

end WordExpressions.BoolPoly
namespace FinitePresentation
open WordExpressions

noncomputable def Presented.ofCode (A : Type) (code : A ↪ ℕ) (bound : ℕ)
    (good : ℕ → Bool) (hcode : ∀ a, code a<bound)
    (hgood : ∀ i, good i=true ↔ ∃ a, code a=i) : Presented (fun _ => A) where
  code _ := code
  bound _ := bound
  good _ := good
  code_lt _ := hcode
  good_iff _ := hgood
  bound_poly := NatPoly.const _
  good_poly := by
    apply (BoolPoly.fixedTable bound good (NatPoly.var 1)).congr
    intro S
    congr 1
    dsimp only
    split_ifs with h
    · rfl
    · apply Eq.symm
      apply Bool.eq_false_iff.mpr
      intro hg
      obtain ⟨a,ha⟩ := (hgood _).mp hg
      exact h (ha ▸ hcode a)

noncomputable def Number.fixed (A : Type) [Fintype A] (f : A → ℕ) :
    Number (Presented.fixed A) (fun _ x => f x) where
  eval _ i := if h : i<Fintype.card A then f ((Fintype.equivFin A).symm ⟨i,h⟩) else 0
  correct w x := by
    change (if h : (Fintype.equivFin A x).val<Fintype.card A then f ((Fintype.equivFin A).symm ⟨(Fintype.equivFin A x).val,h⟩) else _)=_
    simp
  poly := by
    apply (NatPoly.fixedTable (Fintype.card A)
      (fun i => if h : i<Fintype.card A then f ((Fintype.equivFin A).symm ⟨i,h⟩) else 0)
      (NatPoly.var 1)).congr
    intro S
    dsimp only
    split_ifs <;> simp_all

end FinitePresentation

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.LocalPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification
namespace FinitePresentation
open WordExpressions NumericFinite
variable {C B : Word → Type} [∀ w, DecidableEq (C w)]

structure Locals (CP : Presented C) (BP : Presented B) where
  coordinates : ∀ w, B w → Finset (C w)
  size : ∀ w b, (coordinates w b).card ≤ 5
  member : Test (BP.prod CP) (fun w p => decide (p.2 ∈ coordinates w p.1))

namespace Locals
variable {CP : Presented C} {BP : Presented B} (D : Locals CP BP)

abbrev Value (w : Word) (b : B w) := (c : D.coordinates w b) → Bit

def good (w : Word) (b c : ℕ) : Bool := CP.good w c && D.member.eval w (Nat.pair b c)

theorem good_iff (w : Word) (b : B w) (i : ℕ) :
    D.good w (BP.code w b) i=true ↔ ∃ x : D.coordinates w b, CP.code w x.val=i := by
  simp only [good, Bool.and_eq_true]
  constructor
  · rintro ⟨hc,hm⟩
    obtain ⟨c,rfl⟩ := (CP.good_iff w i).mp hc
    have h := D.member.correct w (b,c)
    change D.member.eval w (Nat.pair (BP.code w b) (CP.code w c))=decide (c∈D.coordinates w b) at h
    exact ⟨⟨c,of_decide_eq_true (h ▸ hm)⟩,rfl⟩
  · rintro ⟨c,rfl⟩
    refine ⟨CP.good_code w c.val,?_⟩
    have h := D.member.correct w (b,c.val)
    change D.member.eval w (Nat.pair (BP.code w b) (CP.code w c.val))=_ at h
    rw [h,decide_eq_true_eq]
    exact c.property

noncomputable def localP (w : Word) (b : B w) : Presented (fun _ => D.coordinates w b) :=
  Presented.ofCode _ (NaturalCode.subtype (CP.code w) _) (CP.bound w)
    (D.good w (BP.code w b)) (fun c => CP.code_lt w c.val) (D.good_iff w b)

def count (w : Word) (b : ℕ) : ℕ := NumericFinite.count (CP.bound w) (D.good w b)

theorem count_eq (w : Word) (b : B w) : D.count w (BP.code w b)=(D.coordinates w b).card := by
  change (D.localP w b).card [] = _
  rw [Presented.card_eq, Fintype.card_coe]

def rank (w : Word) (b c : ℕ) : ℕ := NumericFinite.count c (D.good w b)

noncomputable def valueEquiv (w : Word) (b : B w) :
    D.Value w b ≃ Fin (2^(D.count w (BP.code w b))) :=
  (Equiv.arrowCongr ((D.localP w b).rankEquiv []) (ZMod.finEquiv 2).toEquiv.symm).trans finFunctionFinEquiv

noncomputable def valueCode (w : Word) (b : B w) : D.Value w b ↪ ℕ :=
  (D.valueEquiv w b).toEmbedding.trans (NaturalCode.fin _)

def valueGood (w : Word) (b v : ℕ) : Bool := decide (v < min (2^(D.count w b)) 32)

theorem valueGood_iff (w : Word) (b : B w) (i : ℕ) :
    D.valueGood w (BP.code w b) i=true ↔ ∃ v, D.valueCode w b v=i := by
  have h : 2^(D.count w (BP.code w b)) ≤ 32 := by
    rw [D.count_eq]
    exact Nat.pow_le_pow_right (by decide) (D.size w b)
  simp only [valueGood, min_eq_left h, decide_eq_true_eq]
  exact ⟨fun hi => ⟨(D.valueEquiv w b).symm ⟨i,hi⟩, congrArg Fin.val ((D.valueEquiv w b).apply_symm_apply _)⟩,
    fun ⟨v,hv⟩ => hv ▸ (D.valueEquiv w b v).isLt⟩

theorem good_poly {n} {w : (Fin n → Word) → Word} {b c : (Fin n → Word) → ℕ}
    (hw : Poly w) (hb : NatPoly b) (hc : NatPoly c) : BoolPoly (fun S => D.good (w S) (b S) (c S)) :=
  BoolPoly.and (CP.good_poly_of hw hc) (D.member.eval_poly hw (NatPoly.pair hb hc))

theorem count_poly {n} {w : (Fin n → Word) → Word} {b : (Fin n → Word) → ℕ}
    (hw : Poly w) (hb : NatPoly b) : NatPoly (fun S => D.count (w S) (b S)) := by
  apply (NatPoly.filterCount (CP.bound_poly_of hw)
    (D.good_poly (hw.rename Fin.castSucc) (hb.rename Fin.castSucc) (NatPoly.var (Fin.last n)))).congr
  intro S
  simp only [Fin.snoc_comp_castSucc, Fin.snoc_last, unary, List.length_replicate]
  rfl

theorem rank_poly {n} {w : (Fin n → Word) → Word} {b c : (Fin n → Word) → ℕ}
    (hw : Poly w) (hb : NatPoly b) (hc : NatPoly c) : NatPoly (fun S => D.rank (w S) (b S) (c S)) := by
  apply (NatPoly.filterCount hc
    (D.good_poly (hw.rename Fin.castSucc) (hb.rename Fin.castSucc) (NatPoly.var (Fin.last n)))).congr
  intro S
  simp only [Fin.snoc_comp_castSucc, Fin.snoc_last, unary, List.length_replicate]
  rfl

noncomputable def values : Presented (fun w => Σ b : B w, D.Value w b) :=
  BP.sigma (D.Value) D.valueCode (fun _ => 32) D.valueGood
    (by intro w b v; have := (D.valueEquiv w b v).isLt
        have h := D.size w b
        rw [← D.count_eq w b] at h
        exact this.trans_le (Nat.pow_le_pow_right (by decide) h))
    D.valueGood_iff (NatPoly.const _)
    (NatPoly.lt (NatPoly.var 2) (NatPoly.cappedPow (NatPoly.const 2)
      (D.count_poly (Poly.var 0) (NatPoly.var 1)) (NatPoly.const 32)))

def read (w : Word) (b v c : ℕ) : ℕ := NumericKernel.digit 2 v (D.rank w b c)

theorem read_value (w : Word) (b : B w) (v : D.Value w b) (c : D.coordinates w b) :
    D.read w (BP.code w b) (D.valueCode w b v) (CP.code w c.val)=(v c).val := by
  have h := (D.valueEquiv w b).symm_apply_apply v
  have h' := congrArg (fun f => (f c).val) h
  exact h'

theorem read_poly {n} {w : (Fin n → Word) → Word} {b v c : (Fin n → Word) → ℕ}
    (hw : Poly w) (hb : NatPoly b) (hv : NatPoly v) (hc : NatPoly c) :
    NatPoly (fun S => D.read (w S) (b S) (v S) (c S)) :=
  NatPoly.digit (NatPoly.const 2) hv (D.rank_poly hw hb hc)

end Locals
end FinitePresentation

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.LeafPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification
namespace FinitePresentation
open WordExpressions
variable {A : Word → Type} {P : Presented A} {G : ∀ w, SimpleGraph (A w)}

namespace PresentedGraph
variable (Q : PresentedGraph P G)

theorem adjacent_poly_of {n} {w : (Fin n → Word) → Word} {i j : (Fin n → Word) → ℕ}
    (hw : Poly w) (hi : NatPoly i) (hj : NatPoly j) :
    BoolPoly (fun S => Q.adjacent (w S) (i S) (j S)) := by
  have h := Q.adjacent_poly.subst (g := ![w, fun S => unary (i S), fun S => unary (j S)])
    (by intro k; fin_cases k; exacts [hw,hi,hj])
  simpa [unary] using h

def leafAdj (w : Word) (i j : ℕ) : Bool := if i%2=0 then
  if j%2=0 then Q.adjacent w (i/2) (j/2) else decide (i/2=(Nat.unpair (j/2)).1)
  else if j%2=0 then decide ((Nat.unpair (i/2)).1=j/2) else false

def leaves {ell : ∀ w, A w → ℕ} (E : Number P ell) :
    PresentedGraph (P.sum (P.finSigma E)) (fun w => withLeaves (G w) (ell w)) where
  adjacent := Q.leafAdj
  adjacent_iff w x y := by
    cases x with
    | inl x => cases y with
      | inl y =>
        change Q.leafAdj w (2*P.code w x) (2*P.code w y)=true ↔ (G w).Adj x y
        simpa [leafAdj] using Q.adjacent_iff w x y
      | inr y =>
        change Q.leafAdj w (2*P.code w x) (2*Nat.pair (P.code w y.1) y.2.val+1)=true ↔ x=y.1
        simp [leafAdj, show (2*Nat.pair (P.code w y.1) y.2.val+1)/2=Nat.pair (P.code w y.1) y.2.val by omega,
          (P.code w).injective.eq_iff]
    | inr x => cases y with
      | inl y =>
        change Q.leafAdj w (2*Nat.pair (P.code w x.1) x.2.val+1) (2*P.code w y)=true ↔ x.1=y
        simp [leafAdj, show (2*Nat.pair (P.code w x.1) x.2.val+1)/2=Nat.pair (P.code w x.1) x.2.val by omega,
          (P.code w).injective.eq_iff]
      | inr y =>
        change Q.leafAdj w (2*Nat.pair (P.code w x.1) x.2.val+1) (2*Nat.pair (P.code w y.1) y.2.val+1)=true ↔ False
        simp [leafAdj]
  adjacent_poly := by
    unfold leafAdj
    apply BoolPoly.iteProp (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange))
    · apply BoolPoly.iteProp (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange))
      · apply Q.adjacent_poly_of <;> (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
      · (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
    · apply BoolPoly.iteProp <;> (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)

variable [∀ w, Fintype (A w)]

noncomputable def tags {color : ∀ w, A w → ℕ} (F : Number P color) :
    Number P (fun w => tagSize (color w)) :=
  (F.mul (Number.param P (fun w => P.card w+1) (NatPoly.succ P.card_poly))).congr (by
    intro w x
    simp only [tagSize, Presented.card_eq])

noncomputable def tagged {color : ∀ w, A w → ℕ} (F : Number P color) := Q.leaves (tags F)

end PresentedGraph
end FinitePresentation

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.AffinePresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification
namespace FinitePresentation
open WordExpressions

noncomputable def Presented.bit : Presented (fun _ => Bit) :=
  (Presented.fin (fun _ => 2) (NatPoly.const 2)).retype (fun _ => (ZMod.finEquiv 2).toEquiv.symm)

@[simp] theorem Presented.bit_code (w : Word) (x : Bit) : Presented.bit.code w x=x.val := rfl

variable {C B : Word → Type} [∀ w, Fintype (C w)] [∀ w, DecidableEq (C w)]
    (CP : Presented C) (BP : Presented B) (D : ∀ w, AffineBlocks (C w) (B w))

def affineLocals (size : ∀ w b, ((D w).coordinates b).card≤5)
    (member : Test (BP.prod CP) (fun w p => decide (p.2∈(D w).coordinates p.1))) : Locals CP BP :=
  ⟨fun w => (D w).coordinates, size, member⟩

attribute [local instance] Classical.propDecidable

structure AffineRealizer where
  size : ∀ w b, ((D w).coordinates b).card≤5
  member : Test (BP.prod CP) (fun w p => decide (p.2∈(D w).coordinates p.1))
  legal : Test (affineLocals CP BP D size member).values (fun w v => decide ((D w).Legal 0 v.1 v.2))
  color : Number (CP.sum BP) (fun w x => (D w).colorIndex x)

namespace AffineRealizer
variable {CP BP D} (F : AffineRealizer CP BP D)

abbrev localData : Locals CP BP := affineLocals CP BP D F.size F.member

noncomputable def legalEquiv (w : Word) :
    (Σ b, {v // (D w).Legal 0 b v}) ≃ {v : Σ b, (D w).Local b // (D w).Legal 0 v.1 v.2} where
  toFun v := ⟨⟨v.1,v.2.val⟩,v.2.property⟩
  invFun v := ⟨v.val.1,⟨v.val.2,v.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def legalPoints : Presented (fun w => Σ b, {v // (D w).Legal 0 b v}) :=
  (F.localData.values.restrict (fun w v => (D w).Legal 0 v.1 v.2) F.legal).retype (legalEquiv (D := D))

noncomputable def vertices : Presented (fun w => (D w).Vertex 0) :=
  (CP.prod Presented.bit).sum F.legalPoints

@[simp] theorem legalPoints_code (w : Word) (v : Σ b, {x // (D w).Legal 0 b x}) :
    F.legalPoints.code w v = Nat.pair (BP.code w v.1) (F.localData.valueCode w v.1 v.2.val) := rfl

@[simp] theorem vertices_code_inl (w : Word) (x : C w × Bit) :
    F.vertices.code w (.inl x) = 2*Nat.pair (CP.code w x.1) x.2.val := rfl

@[simp] theorem vertices_code_inr (w : Word) (x : Σ b, {v // (D w).Legal 0 b v}) :
    F.vertices.code w (.inr x) = 2*Nat.pair (BP.code w x.1) (F.localData.valueCode w x.1 x.2.val)+1 := rfl

def cross (w : Word) (i j : ℕ) : Bool :=
  F.member.eval w (Nat.pair (Nat.unpair j).1 (Nat.unpair i).1) &&
    decide (F.localData.read w (Nat.unpair j).1 (Nat.unpair j).2 (Nat.unpair i).1=(Nat.unpair i).2)

theorem cross_correct (w : Word) (p : C w × Bit) (v : Σ b, {x // (D w).Legal 0 b x}) :
    F.cross w ((CP.prod Presented.bit).code w p) (F.legalPoints.code w v)=true ↔
    ∃ h : p.1∈(D w).coordinates v.1, v.2.val ⟨p.1,h⟩=p.2 := by
  change F.cross w (Nat.pair (CP.code w p.1) p.2.val) (Nat.pair (BP.code w v.1) (F.localData.valueCode w v.1 v.2.val))=true ↔ _
  simp only [cross, Nat.unpair_pair]
  have hm := F.member.correct w (v.1,p.1)
  change F.member.eval w (Nat.pair (BP.code w v.1) (CP.code w p.1))=decide (p.1∈(D w).coordinates v.1) at hm
  rw [hm, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨h,he⟩
    refine ⟨h,?_⟩
    rw [F.localData.read_value w v.1 v.2.val ⟨p.1,h⟩] at he
    exact ZMod.val_injective 2 he
  · rintro ⟨h,he⟩
    refine ⟨h,?_⟩
    rw [F.localData.read_value w v.1 v.2.val ⟨p.1,h⟩]
    exact congrArg ZMod.val he

theorem cross_poly {n} {w : (Fin n → Word) → Word} {i j : (Fin n → Word) → ℕ}
    (hw : Poly w) (hi : NatPoly i) (hj : NatPoly j) : BoolPoly (fun S => F.cross (w S) (i S) (j S)) := by
  apply BoolPoly.and
  · exact F.member.eval_poly hw (NatPoly.pair (NatPoly.unpair_fst hj) (NatPoly.unpair_fst hi))
  · exact NatPoly.eqtest (F.localData.read_poly hw (NatPoly.unpair_fst hj) (NatPoly.unpair_snd hj)
      (NatPoly.unpair_fst hi)) (NatPoly.unpair_snd hi)

@[simp] theorem odd_half (n : ℕ) : (2*n+1)/2=n := by omega

def adjacent (w : Word) (i j : ℕ) : Bool :=
  if i%2=0 then if j%2=0 then false else F.cross w (i/2) (j/2)
  else if j%2=0 then F.cross w (j/2) (i/2) else false

noncomputable def base : PresentedGraph F.vertices (fun w => (D w).baseGraph 0) where
  adjacent := F.adjacent
  adjacent_iff w x y := by
    cases x with
    | inl x => cases y with
      | inl y =>
        change F.adjacent w (2*(CP.prod Presented.bit).code w x) (2*(CP.prod Presented.bit).code w y)=true ↔ False
        simp [adjacent]
      | inr y =>
        change F.adjacent w (2*(CP.prod Presented.bit).code w x) (2*F.legalPoints.code w y+1)=true ↔ _
        simpa [AffineBlocks.baseGraph, adjacent, odd_half] using F.cross_correct w x y
    | inr x => cases y with
      | inl y =>
        change F.adjacent w (2*F.legalPoints.code w x+1) (2*(CP.prod Presented.bit).code w y)=true ↔ _
        simpa [AffineBlocks.baseGraph, adjacent, odd_half] using F.cross_correct w y x
      | inr y =>
        change F.adjacent w (2*F.legalPoints.code w x+1) (2*F.legalPoints.code w y+1)=true ↔ False
        simp [adjacent]
  adjacent_poly := by
    unfold adjacent
    apply BoolPoly.iteProp (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange))
    · apply BoolPoly.iteProp (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)) (BoolPoly.const false)
      apply F.cross_poly <;> (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
    · apply BoolPoly.iteProp (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)) _ (BoolPoly.const false)
      apply F.cross_poly <;> (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)

variable [∀ w, Fintype (B w)]

noncomputable def colors : Number F.vertices (fun w x => (D w).colorNat x) where
  eval w i := F.color.eval w (if i%2=0 then 2*(Nat.unpair (i/2)).1 else 2*(Nat.unpair (i/2)).1+1)+1
  correct w x := by
    cases x with
    | inl x =>
      change F.color.eval w (if (F.vertices.code w (.inl x))%2=0 then 2*(Nat.unpair ((F.vertices.code w (.inl x))/2)).1 else 2*(Nat.unpair ((F.vertices.code w (.inl x))/2)).1+1)+1=(D w).colorIndex (.inl x.1)+1
      rw [F.vertices_code_inl]
      simp only [Nat.mul_mod_right, Nat.mul_div_cancel_left _ (by omega : 0<2), Nat.unpair_pair]
      exact congrArg (fun n => n+1) (F.color.correct w (.inl x.1))
    | inr x =>
      change F.color.eval w (if (F.vertices.code w (.inr x))%2=0 then 2*(Nat.unpair ((F.vertices.code w (.inr x))/2)).1 else 2*(Nat.unpair ((F.vertices.code w (.inr x))/2)).1+1)+1=(D w).colorIndex (.inr x.1)+1
      rw [F.vertices_code_inr]
      simp only [show (2*Nat.pair (BP.code w x.1) (F.localData.valueCode w x.1 x.2.val)+1)%2≠0 by omega, ite_false,
        show (2*Nat.pair (BP.code w x.1) (F.localData.valueCode w x.1 x.2.val)+1)/2=Nat.pair (BP.code w x.1) (F.localData.valueCode w x.1 x.2.val) by omega, Nat.unpair_pair]
      exact congrArg (fun n => n+1) (F.color.correct w (.inr x.1))
  poly := NatPoly.succ (F.color.eval_poly (Poly.var 0) (by apply NatPoly.iteProp <;> (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)))

noncomputable def uncolored := F.base.tagged F.colors

end AffineRealizer
end FinitePresentation

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.TypedArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification
namespace FinitePresentation
open WordExpressions
variable {A B C : Word → Type}
namespace Map
variable {P : Presented A} {Q : Presented B} {R : Presented C}

def optionCases {f : ∀ w, A w → B w} {g : ∀ w, B w}
    (F : Map P Q f) (h : NatPoly (fun S : Fin 1 → Word => Q.code (S 0) (g (S 0)))) :
    Map P.option Q (fun w x => x.elim (g w) (f w)) :=
  (Number.optionCases F (fun w => Q.code w (g w)) h).congr (by intro w x; cases x <;> rfl)

def const (P : Presented A) (Q : Presented B) (f : ∀ w, B w)
    (h : NatPoly (fun S : Fin 1 → Word => Q.code (S 0) (f (S 0)))) :
    Map P Q (fun w _ => f w) := Number.param P _ h

def boolOfTest {p : ∀ w, A w → Bool} (H : Test P p) : Map P Presented.bool p :=
  (Number.ite H (Number.const P 1) (Number.const P 0)).congr (by intro w x; cases p w x <;> rfl)

end Map
namespace Number
variable {P : Presented A} {Q : Presented B}

def retype {f : ∀ w, A w → ℕ} (F : Number P f) (e : ∀ w, B w ≃ A w) :
    Number (P.retype e) (fun w x => f w (e w x)) := F.comp (Map.retype P e)

end Number
namespace Test
variable {P : Presented A}

def ofBoolMap {f : ∀ w, A w → Bool} (F : Map P Presented.bool f) : Test P f :=
  (numEq F (Number.const P 1)).congr (by intro w x; cases f w x <;> rfl)

end Test
end FinitePresentation

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.RingPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification
namespace FinitePresentation
open WordExpressions
attribute [local instance] Classical.propDecidable Classical.decEq

def vectorTwo (d : ℕ) (x : Bit × Bit) (j : Fin d) : Bit := if j.val=0 then x.1 else x.2

structure RingRealizer {T L : Word → Type} (TP : Presented T) (LP : Presented L)
    (r : Word → ℕ) (rp : NatPoly (fun S : Fin 1 → Word => r (S 0)))
    (R : ∀ w, RingLayout (r w) (T w) (L w)) where
  typeIndex : Number TP (fun w t => (R w).typeIndex t)
  linkIndex : Number LP (fun w e => (R w).linkIndex e)
  dimension : Number TP (fun w t => (R w).dimension t)
  labels : Test (TP.prod ((Presented.fin r rp).prod Presented.bool)) (fun w x => decide (x.2.2∈(R w).labels x.1 x.2.1))
  matching : Test (LP.prod ((Presented.fin r rp).prod Presented.bool)) (fun w x => decide (x.2.2∈(R w).matchLabels x.1 x.2.1))
  first : Map LP TP (fun w => (R w).first)
  second : Map LP TP (fun w => (R w).second)
  firstLabel : Word → ℕ → ℕ → ℕ → ℕ
  secondLabel : Word → ℕ → ℕ → ℕ → ℕ
  firstLabel_eq : ∀ w e i (a : (R w).Match e i), firstLabel w (LP.code w e) i.val (NaturalCode.bool a.val)=NaturalCode.bool ((R w).firstLabel e i a).val
  secondLabel_eq : ∀ w e i (a : (R w).Match e i), secondLabel w (LP.code w e) i.val (NaturalCode.bool a.val)=NaturalCode.bool ((R w).secondLabel e i a).val
  firstLabel_poly : NatPoly (fun S : Fin 4 → Word => firstLabel (S 0) (S 1).length (S 2).length (S 3).length)
  secondLabel_poly : NatPoly (fun S : Fin 4 → Word => secondLabel (S 0) (S 1).length (S 2).length (S 3).length)
  firstForm : Number (LP.prod (Presented.bit.prod Presented.bit)) (fun w x => ((R w).firstForm x.1 (vectorTwo _ x.2)).val)
  secondForm : Number (LP.prod (Presented.bit.prod Presented.bit)) (fun w x => ((R w).secondForm x.1 (vectorTwo _ x.2)).val)

namespace RingRealizer
variable {T L : Word → Type} {TP : Presented T} {LP : Presented L}
    {r : Word → ℕ} {rp : NatPoly (fun S : Fin 1 → Word => r (S 0))}
    {R : ∀ w, RingLayout (r w) (T w) (L w)} (F : RingRealizer TP LP r rp R)

abbrev rowP (_F : RingRealizer TP LP r rp R) := Presented.fin r rp
abbrev hBase := TP.prod (F.rowP.prod (Presented.bool.prod Presented.bool))
abbrev vBase := LP.prod (F.rowP.prod Presented.bool)
abbrev sBase := LP.prod (F.rowP.prod (Presented.bool.prod Presented.bool))

def nextRow (_F : RingRealizer TP LP r rp R) (w : Word) (i : ℕ) := if i+1<r w then i+1 else 0

theorem nextRow_eq (w : Word) (i : Fin (r w)) : F.nextRow w i.val=(finRotate (r w) i).val := by
  simp only [nextRow, CycleRows.rotate_val]

theorem nextRow_poly {n} {w : (Fin n → Word) → Word} {i : (Fin n → Word) → ℕ}
    (hw : Poly w) (hi : NatPoly i) : NatPoly (fun S => F.nextRow (w S) (i S)) := by
  unfold nextRow
  exact NatPoly.iteProp (NatPoly.lt (NatPoly.succ hi) (F.rowP.bound_poly_of hw)) (NatPoly.succ hi) (NatPoly.const 0)

def hAllowed (_F : RingRealizer TP LP r rp R) (w : Word) (h : T w × (Fin (r w) × (Bool × Bool))) : Prop :=
  h.2.2.1∈(R w).labels h.1 h.2.1 ∧ h.2.2.2∈(R w).labels h.1 (finRotate (r w) h.2.1)

def sAllowed (_F : RingRealizer TP LP r rp R) (w : Word) (h : L w × (Fin (r w) × (Bool × Bool))) : Prop :=
  h.2.2.1∈(R w).matchLabels h.1 h.2.1 ∧ h.2.2.2∈(R w).matchLabels h.1 (finRotate (r w) h.2.1)

@[simp] theorem hBase_code (w : Word) (x : T w × (Fin (r w) × (Bool × Bool))) :
    F.hBase.code w x=Nat.pair (TP.code w x.1) (Nat.pair x.2.1.val (Nat.pair (NaturalCode.bool x.2.2.1) (NaturalCode.bool x.2.2.2))) := rfl
@[simp] theorem sBase_code (w : Word) (x : L w × (Fin (r w) × (Bool × Bool))) :
    F.sBase.code w x=Nat.pair (LP.code w x.1) (Nat.pair x.2.1.val (Nat.pair (NaturalCode.bool x.2.2.1) (NaturalCode.bool x.2.2.2))) := rfl

def labelsPair (H : Test (TP.prod (F.rowP.prod Presented.bool)) (fun w x => decide (x.2.2∈(R w).labels x.1 x.2.1))) :
    Test F.hBase (fun w x => decide (F.hAllowed w x)) where
  eval w i := H.eval w (Nat.pair (Nat.unpair i).1 (Nat.pair (Nat.unpair (Nat.unpair i).2).1 (Nat.unpair (Nat.unpair (Nat.unpair i).2).2).1)) &&
    H.eval w (Nat.pair (Nat.unpair i).1 (Nat.pair (F.nextRow w (Nat.unpair (Nat.unpair i).2).1) (Nat.unpair (Nat.unpair (Nat.unpair i).2).2).2))
  correct w x := by
    simp only [F.hBase_code, Nat.unpair_pair, F.nextRow_eq]
    rw [show H.eval w (Nat.pair (TP.code w x.1) (Nat.pair x.2.1.val (NaturalCode.bool x.2.2.1)))=decide (x.2.2.1∈(R w).labels x.1 x.2.1) from H.correct w (x.1,x.2.1,x.2.2.1)]
    rw [show H.eval w (Nat.pair (TP.code w x.1) (Nat.pair (finRotate (r w) x.2.1).val (NaturalCode.bool x.2.2.2)))=decide (x.2.2.2∈(R w).labels x.1 (finRotate (r w) x.2.1)) from H.correct w (x.1,finRotate (r w) x.2.1,x.2.2.2)]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true,decide_eq_true_eq]
    rfl
  poly := BoolPoly.and (H.eval_poly (Poly.var 0)
    (NatPoly.pair (NatPoly.unpair_fst (NatPoly.var 1)) (NatPoly.pair
      (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.var 1)))
      (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.var 1)))))))
    (H.eval_poly (Poly.var 0) (NatPoly.pair (NatPoly.unpair_fst (NatPoly.var 1))
      (NatPoly.pair (F.nextRow_poly (Poly.var 0) (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.var 1))))
      (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.var 1)))))))

noncomputable def hEquiv (w : Word) : (R w).HName ≃ {h // F.hAllowed w h} where
  toFun h := ⟨(h.1,h.2.1,h.2.2.1.val,h.2.2.2.val),h.2.2.1.property,h.2.2.2.property⟩
  invFun h := ⟨h.val.1,h.val.2.1,⟨h.val.2.2.1,h.property.1⟩,⟨h.val.2.2.2,h.property.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def hP : Presented (fun w => (R w).HName) :=
  (F.hBase.restrict F.hAllowed (F.labelsPair F.labels)).retype F.hEquiv

@[simp] theorem hP_code (w : Word) (h : (R w).HName) : F.hP.code w h=
    Nat.pair (TP.code w h.1) (Nat.pair h.2.1.val (Nat.pair (NaturalCode.bool h.2.2.1.val) (NaturalCode.bool h.2.2.2.val))) := rfl

def matchingPair (H : Test (LP.prod (F.rowP.prod Presented.bool)) (fun w x => decide (x.2.2∈(R w).matchLabels x.1 x.2.1))) :
    Test F.sBase (fun w x => decide (F.sAllowed w x)) where
  eval w i := H.eval w (Nat.pair (Nat.unpair i).1 (Nat.pair (Nat.unpair (Nat.unpair i).2).1 (Nat.unpair (Nat.unpair (Nat.unpair i).2).2).1)) &&
    H.eval w (Nat.pair (Nat.unpair i).1 (Nat.pair (F.nextRow w (Nat.unpair (Nat.unpair i).2).1) (Nat.unpair (Nat.unpair (Nat.unpair i).2).2).2))
  correct w x := by
    simp only [F.sBase_code, Nat.unpair_pair, F.nextRow_eq]
    rw [show H.eval w (Nat.pair (LP.code w x.1) (Nat.pair x.2.1.val (NaturalCode.bool x.2.2.1)))=decide (x.2.2.1∈(R w).matchLabels x.1 x.2.1) from H.correct w (x.1,x.2.1,x.2.2.1)]
    rw [show H.eval w (Nat.pair (LP.code w x.1) (Nat.pair (finRotate (r w) x.2.1).val (NaturalCode.bool x.2.2.2)))=decide (x.2.2.2∈(R w).matchLabels x.1 (finRotate (r w) x.2.1)) from H.correct w (x.1,finRotate (r w) x.2.1,x.2.2.2)]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true,decide_eq_true_eq]
    rfl
  poly := BoolPoly.and (H.eval_poly (Poly.var 0)
    (NatPoly.pair (NatPoly.unpair_fst (NatPoly.var 1)) (NatPoly.pair
      (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.var 1)))
      (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.var 1)))))))
    (H.eval_poly (Poly.var 0) (NatPoly.pair (NatPoly.unpair_fst (NatPoly.var 1))
      (NatPoly.pair (F.nextRow_poly (Poly.var 0) (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.var 1))))
      (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.var 1)))))))

noncomputable def sEquiv (w : Word) : (R w).Square ≃ {h // F.sAllowed w h} where
  toFun h := ⟨(h.1,h.2.1,h.2.2.1.val,h.2.2.2.val),h.2.2.1.property,h.2.2.2.property⟩
  invFun h := ⟨h.val.1,h.val.2.1,⟨h.val.2.2.1,h.property.1⟩,⟨h.val.2.2.2,h.property.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def sP : Presented (fun w => (R w).Square) :=
  (F.sBase.restrict F.sAllowed (F.matchingPair F.matching)).retype F.sEquiv

@[simp] theorem sP_code (w : Word) (h : (R w).Square) : F.sP.code w h=
    Nat.pair (LP.code w h.1) (Nat.pair h.2.1.val (Nat.pair (NaturalCode.bool h.2.2.1.val) (NaturalCode.bool h.2.2.2.val))) := rfl

noncomputable def vEquiv (w : Word) : (R w).VName ≃ {h : L w × (Fin (r w) × Bool) // h.2.2∈(R w).matchLabels h.1 h.2.1} where
  toFun h := ⟨(h.1,h.2.1,h.2.2.val),h.2.2.property⟩
  invFun h := ⟨h.val.1,h.val.2.1,⟨h.val.2.2,h.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def vP : Presented (fun w => (R w).VName) :=
  (F.vBase.restrict (fun w h => h.2.2∈(R w).matchLabels h.1 h.2.1) F.matching).retype (vEquiv (R := R))

@[simp] theorem vP_code (w : Word) (h : (R w).VName) : F.vP.code w h=
    Nat.pair (LP.code w h.1) (Nat.pair h.2.1.val (NaturalCode.bool h.2.2.val)) := rfl

noncomputable def hDim : Number F.hP (fun w x => (R w).dimension x.1) where
  eval w i := F.dimension.eval w (Nat.unpair i).1
  correct w x := by rw [F.hP_code,Nat.unpair_pair]; exact F.dimension.correct w x.1
  poly := F.dimension.eval_poly (Poly.var 0) (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange))

noncomputable def cP : Presented (fun w => (R w).Coordinate) := (F.hP.finSigma F.hDim).sum F.vP
noncomputable def bP : Presented (fun w => (R w).Block) := F.hP.sum F.sP

@[simp] theorem cP_inl (w : Word) (h : Σ h : (R w).HName, Fin ((R w).dimension h.1)) :
    F.cP.code w (.inl h)=2*Nat.pair (F.hP.code w h.1) h.2.val := rfl
@[simp] theorem cP_inr (w : Word) (v : (R w).VName) : F.cP.code w (.inr v)=2*F.vP.code w v+1 := rfl
@[simp] theorem bP_inl (w : Word) (h : (R w).HName) : F.bP.code w (.inl h)=2*F.hP.code w h := rfl
@[simp] theorem bP_inr (w : Word) (b : (R w).Square) : F.bP.code w (.inr b)=2*F.sP.code w b+1 := rfl

end RingRealizer
end FinitePresentation

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.TypedCases
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification
namespace FinitePresentation
open WordExpressions
variable {A B C D : Word → Type}
namespace Presented
@[simp] theorem prod_code (P : Presented A) (Q : Presented B) (w : Word) (x : A w × B w) :
    (P.prod Q).code w x=Nat.pair (P.code w x.1) (Q.code w x.2) := rfl
@[simp] theorem sum_inl_code (P : Presented A) (Q : Presented B) (w : Word) (x : A w) :
    (P.sum Q).code w (.inl x)=2*P.code w x := rfl
@[simp] theorem sum_inr_code (P : Presented A) (Q : Presented B) (w : Word) (x : B w) :
    (P.sum Q).code w (.inr x)=2*Q.code w x+1 := rfl
@[simp] theorem retype_code (P : Presented A) (e : ∀ w,B w≃A w) (w : Word) (x : B w) :
    (P.retype e).code w x=P.code w (e w x) := rfl
@[simp] theorem fin_code (d : Word → ℕ) (h) (w : Word) (i : Fin (d w)) :
    (Presented.fin d h).code w i=i.val := rfl
@[simp] theorem bool_code (w : Word) (a : Bool) : Presented.bool.code w a=NaturalCode.bool a := rfl
end Presented
namespace Number
variable {P : Presented A} {Q : Presented B} {R : Presented C}

def sumFst {f : ∀ w,A w × C w → ℕ} {g : ∀ w,B w × C w → ℕ}
    (F : Number (P.prod R) f) (G : Number (Q.prod R) g) :
    Number ((P.sum Q).prod R) (fun w x => x.1.elim (fun a => f w (a,x.2)) (fun b => g w (b,x.2))) where
  eval w i := if (Nat.unpair i).1%2=0 then F.eval w (Nat.pair ((Nat.unpair i).1/2) (Nat.unpair i).2)
    else G.eval w (Nat.pair ((Nat.unpair i).1/2) (Nat.unpair i).2)
  correct w x := by
    rcases x with ⟨x,y⟩
    cases x <;> simp only [Presented.prod_code,Presented.sum_inl_code,Presented.sum_inr_code,Nat.unpair_pair]
    · simpa using F.correct w (_,y)
    · simpa [AffineRealizer.odd_half] using G.correct w (_,y)
  poly := NatPoly.iteProp (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange))
    (F.eval_poly (Poly.var 0) (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange))) (G.eval_poly (Poly.var 0) (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)))

def retypeFst {f : ∀ w,A w × C w → ℕ} (F : Number (P.prod R) f) (e : ∀ w,B w ≃ A w) :
    Number ((P.retype e).prod R) (fun w x => f w (e w x.1,x.2)) where
  eval := F.eval
  correct w x := F.correct w (e w x.1,x.2)
  poly := F.poly

end Number
namespace Test
variable {P : Presented A} {Q : Presented B} {R : Presented C}

def sumFst {f : ∀ w,A w × C w → Bool} {g : ∀ w,B w × C w → Bool}
    (F : Test (P.prod R) f) (G : Test (Q.prod R) g) :
    Test ((P.sum Q).prod R) (fun w x => x.1.elim (fun a => f w (a,x.2)) (fun b => g w (b,x.2))) where
  eval w i := if (Nat.unpair i).1%2=0 then F.eval w (Nat.pair ((Nat.unpair i).1/2) (Nat.unpair i).2)
    else G.eval w (Nat.pair ((Nat.unpair i).1/2) (Nat.unpair i).2)
  correct w x := by
    rcases x with ⟨x,y⟩
    cases x <;> simp only [Presented.prod_code,Presented.sum_inl_code,Presented.sum_inr_code,Nat.unpair_pair]
    · simpa using F.correct w (_,y)
    · simpa [AffineRealizer.odd_half] using G.correct w (_,y)
  poly := BoolPoly.iteProp (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange))
    (F.eval_poly (Poly.var 0) (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange))) (G.eval_poly (Poly.var 0) (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)))

def retype {f : ∀ w,A w → Bool} (F : Test P f) (e : ∀ w,B w ≃ A w) :
    Test (P.retype e) (fun w x => f w (e w x)) := F.comp (Map.retype P e)

def retypeFst {f : ∀ w,A w × C w → Bool} (F : Test (P.prod R) f) (e : ∀ w,B w ≃ A w) :
    Test ((P.retype e).prod R) (fun w x => f w (e w x.1,x.2)) where
  eval := F.eval
  correct w x := F.correct w (e w x.1,x.2)
  poly := F.poly

end Test
end FinitePresentation
end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.CircuitPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification
namespace FinitePresentation
open WordExpressions
attribute [local instance] Classical.propDecidable Classical.decEq

structure CircuitRealizer {P E Z T : Word → Type} (PP : Presented P) (EP : Presented E)
    (ZP : Presented Z) (TP : Presented T) (r : Word → ℕ)
    (rp : NatPoly (fun X : Fin 1 → Word => r (X 0)))
    (C : ∀ w, ProductCircuit (r w) (P w) (E w) (Z w) (T w)) where
  pointIndex : Number PP (fun w p => (C w).pointIndex p)
  edgeIndex : Number EP (fun w e => (C w).edgeIndex e)
  seedIndex : Number ZP (fun w z => (C w).seedIndex z)
  testIndex : Number TP (fun w t => (C w).testIndex t)
  dimension : Number PP (fun w p => (C w).dimension p)
  source : Map EP PP (fun w => (C w).source)
  target : Map EP PP (fun w => (C w).target)
  port : Number EP (fun w e => ((C w).port e).val)
  seedType : Map ZP PP (fun w => (C w).seedType)
  testType : Map TP PP (fun w => (C w).testType)
  edgeDomain : Test (EP.prod ((Presented.fin r rp).prod Presented.bool))
    (fun w x => decide (x.2.2∈((C w).edgeMap x.1).domain x.2.1))
  seedDomain : Test (ZP.prod ((Presented.fin r rp).prod Presented.bool))
    (fun w x => decide (x.2.2∈((C w).seedMap x.1).domain x.2.1))
  testDomain : Test (TP.prod ((Presented.fin r rp).prod Presented.bool))
    (fun w x => decide (x.2.2∈((C w).testMap x.1).domain x.2.1))
  edgeMapping : Map (EP.prod ((Presented.fin r rp).prod Presented.bool)) Presented.bool
    (fun w x => ((C w).edgeMap x.1).mapping x.2.1 x.2.2)

namespace CircuitRealizer
variable {P E Z T : Word → Type} {PP : Presented P} {EP : Presented E}
    {ZP : Presented Z} {TP : Presented T} {r : Word → ℕ}
    {rp : NatPoly (fun X : Fin 1 → Word => r (X 0))}
    {C : ∀ w, ProductCircuit (r w) (P w) (E w) (Z w) (T w)}
    (F : CircuitRealizer PP EP ZP TP r rp C)

abbrev rowP (_F : CircuitRealizer PP EP ZP TP r rp C) := Presented.fin r rp
abbrev primaryP (_F : CircuitRealizer PP EP ZP TP r rp C) := PP.option
noncomputable def primaryDim : Number F.primaryP (fun w p => (C w).primaryDimension p) :=
  (F.dimension.optionCases (fun _ => 1) (NatPoly.const 1)).congr (by intro w p; cases p <;> rfl)
abbrev broadcastP := PP.finSigma F.dimension
noncomputable abbrev selfP := F.primaryP.finSigma F.primaryDim
noncomputable abbrev connectionBase := EP.sum (TP.sum (F.rowP.sum (F.broadcastP.sum (F.selfP.sum Presented.unit))))

def connectionEquiv (w : Word) : (C w).Connection ≃ (E w ⊕ (T w ⊕ (Fin (r w) ⊕
    ((Σ p : P w,Fin ((C w).dimension p)) ⊕ ((Σ p : (C w).Primary,Fin ((C w).primaryDimension p)) ⊕ Unit))))) where
  toFun
    | .original e => .inl e
    | .test t => .inr (.inl t)
    | .flip i => .inr (.inr (.inl i))
    | .broadcast p j => .inr (.inr (.inr (.inl ⟨p,j⟩)))
    | .self p j => .inr (.inr (.inr (.inr (.inl ⟨p,j⟩))))
    | .conflict => .inr (.inr (.inr (.inr (.inr ()))))
  invFun
    | .inl e => .original e
    | .inr (.inl t) => .test t
    | .inr (.inr (.inl i)) => .flip i
    | .inr (.inr (.inr (.inl p))) => .broadcast p.1 p.2
    | .inr (.inr (.inr (.inr (.inl p)))) => .self p.1 p.2
    | .inr (.inr (.inr (.inr (.inr _)))) => .conflict
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with e|t|i|p|p|u <;> rfl

noncomputable def connectionP : Presented (fun w => (C w).Connection) := F.connectionBase.retype (connectionEquiv (C := C))

noncomputable def casesNumber {f : ∀ w,(C w).Connection → ℕ}
    (o : Number EP (fun w e => f w (.original e)))
    (t : Number TP (fun w t => f w (.test t)))
    (i : Number F.rowP (fun w i => f w (.flip i)))
    (b : Number F.broadcastP (fun w p => f w (.broadcast p.1 p.2)))
    (s : Number F.selfP (fun w p => f w (.self p.1 p.2)))
    (c : Number Presented.unit (fun w _ => f w .conflict)) : Number F.connectionP f :=
  ((Number.sumCases o (Number.sumCases t (Number.sumCases i (Number.sumCases b (Number.sumCases s c))))).retype
    (connectionEquiv (C := C))).congr (by intro w x; cases x <;> rfl)

noncomputable def casesNumberFst {A : Word → Type} (AP : Presented A) {f : ∀ w,(C w).Connection × A w → ℕ}
    (o : Number (EP.prod AP) (fun w x => f w (.original x.1,x.2)))
    (t : Number (TP.prod AP) (fun w x => f w (.test x.1,x.2)))
    (i : Number (F.rowP.prod AP) (fun w x => f w (.flip x.1,x.2)))
    (b : Number (F.broadcastP.prod AP) (fun w x => f w (.broadcast x.1.1 x.1.2,x.2)))
    (s : Number (F.selfP.prod AP) (fun w x => f w (.self x.1.1 x.1.2,x.2)))
    (c : Number (Presented.unit.prod AP) (fun w x => f w (.conflict,x.2))) : Number (F.connectionP.prod AP) f :=
  ((Number.sumFst o (Number.sumFst t (Number.sumFst i (Number.sumFst b (Number.sumFst s c))))).retypeFst
    (connectionEquiv (C := C))).congr (by intro w x; rcases x with ⟨x,y⟩; cases x <;> rfl)

noncomputable def casesTestFst {A : Word → Type} (AP : Presented A) {f : ∀ w,(C w).Connection × A w → Bool}
    (o : Test (EP.prod AP) (fun w x => f w (.original x.1,x.2)))
    (t : Test (TP.prod AP) (fun w x => f w (.test x.1,x.2)))
    (i : Test (F.rowP.prod AP) (fun w x => f w (.flip x.1,x.2)))
    (b : Test (F.broadcastP.prod AP) (fun w x => f w (.broadcast x.1.1 x.1.2,x.2)))
    (s : Test (F.selfP.prod AP) (fun w x => f w (.self x.1.1 x.1.2,x.2)))
    (c : Test (Presented.unit.prod AP) (fun w x => f w (.conflict,x.2))) : Test (F.connectionP.prod AP) f :=
  ((Test.sumFst o (Test.sumFst t (Test.sumFst i (Test.sumFst b (Test.sumFst s c))))).retypeFst
    (connectionEquiv (C := C))).congr (by intro w x; rcases x with ⟨x,y⟩; cases x <;> rfl)

noncomputable abbrev comparisonBase := ZP.sum (F.connectionP.sum (F.connectionP.sum F.connectionP))
def comparisonEquiv (w : Word) : (C w).Comparison ≃ (Z w ⊕ ((C w).Connection ⊕ ((C w).Connection ⊕ (C w).Connection))) where
  toFun | .seed z => .inl z | .first l => .inr (.inl l) | .second l => .inr (.inr (.inl l)) | .third l => .inr (.inr (.inr l))
  invFun | .inl z => .seed z | .inr (.inl l) => .first l | .inr (.inr (.inl l)) => .second l | .inr (.inr (.inr l)) => .third l
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with z|l|l|l <;> rfl
noncomputable def comparisonP : Presented (fun w => (C w).Comparison) := F.comparisonBase.retype (comparisonEquiv (C := C))

noncomputable def comparisonCases {f : ∀ w,(C w).Comparison → ℕ}
    (z : Number ZP (fun w z => f w (.seed z)))
    (a : Number F.connectionP (fun w l => f w (.first l)))
    (b : Number F.connectionP (fun w l => f w (.second l)))
    (c : Number F.connectionP (fun w l => f w (.third l))) : Number F.comparisonP f :=
  ((Number.sumCases z (Number.sumCases a (Number.sumCases b c))).retype (comparisonEquiv (C := C))).congr
    (by intro w x; cases x <;> rfl)

noncomputable def comparisonNumberFst {A : Word → Type} (AP : Presented A) {f : ∀ w,(C w).Comparison × A w → ℕ}
    (z : Number (ZP.prod AP) (fun w x => f w (.seed x.1,x.2)))
    (a : Number (F.connectionP.prod AP) (fun w x => f w (.first x.1,x.2)))
    (b : Number (F.connectionP.prod AP) (fun w x => f w (.second x.1,x.2)))
    (c : Number (F.connectionP.prod AP) (fun w x => f w (.third x.1,x.2))) : Number (F.comparisonP.prod AP) f :=
  ((Number.sumFst z (Number.sumFst a (Number.sumFst b c))).retypeFst (comparisonEquiv (C := C))).congr
    (by intro w x; rcases x with ⟨x,y⟩; cases x <;> rfl)
noncomputable def comparisonTestFst {A : Word → Type} (AP : Presented A) {f : ∀ w,(C w).Comparison × A w → Bool}
    (z : Test (ZP.prod AP) (fun w x => f w (.seed x.1,x.2)))
    (a : Test (F.connectionP.prod AP) (fun w x => f w (.first x.1,x.2)))
    (b : Test (F.connectionP.prod AP) (fun w x => f w (.second x.1,x.2)))
    (c : Test (F.connectionP.prod AP) (fun w x => f w (.third x.1,x.2))) : Test (F.comparisonP.prod AP) f :=
  ((Test.sumFst z (Test.sumFst a (Test.sumFst b c))).retypeFst (comparisonEquiv (C := C))).congr
    (by intro w x; rcases x with ⟨x,y⟩; cases x <;> rfl)

end CircuitRealizer
end FinitePresentation
end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.CircuitCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification
namespace FinitePresentation
open WordExpressions
attribute [local instance] Classical.propDecidable Classical.decEq
namespace Number
variable {A : Word → Type} {P : Presented A}

def sigmaSnd {d : ∀ w,A w → ℕ} (D : Number P d) : Number (P.finSigma D) (fun _ x => x.2.val) where
  eval _ i := (Nat.unpair i).2
  correct w x := by change (Nat.unpair (Nat.pair _ _)).2=_; rw [Nat.unpair_pair]; rfl
  poly := NatPoly.unpair_snd (NatPoly.var 1)

end Number
namespace CircuitRealizer
variable {P E Z T : Word → Type} {PP : Presented P} {EP : Presented E}
    {ZP : Presented Z} {TP : Presented T} {r : Word → ℕ}
    {rp : NatPoly (fun X : Fin 1 → Word => r (X 0))}
    {C : ∀ w, ProductCircuit (r w) (P w) (E w) (Z w) (T w)}
    (F : CircuitRealizer PP EP ZP TP r rp C)

noncomputable def primaryIndex : Number F.primaryP (fun w p => NaturalCode.option (C w).pointIndex p) :=
  ((F.pointIndex.add (Number.const PP 1)).optionCases (fun _ => 0) (NatPoly.const 0)).congr (by intro w p; cases p <;> rfl)

noncomputable def connectionIndex : Number F.connectionP (fun w l => (C w).connectionIndex l) := by
  apply F.casesNumber
  · exact (Number.const EP 0).pair F.edgeIndex
  · exact (Number.const TP 1).pair F.testIndex
  · exact (Number.const F.rowP 2).pair (Number.code F.rowP)
  · exact (Number.const F.broadcastP 3).pair ((F.pointIndex.comp (Map.sigmaFst PP F.dimension)).pair (Number.sigmaSnd F.dimension))
  · exact (Number.const F.selfP 4).pair ((F.primaryIndex.comp (Map.sigmaFst F.primaryP F.primaryDim)).pair (Number.sigmaSnd F.primaryDim))
  · exact Number.const Presented.unit (Nat.pair 5 0)

noncomputable def comparisonIndex : Number F.comparisonP (fun w e => (C w).comparisonIndex e) := by
  apply F.comparisonCases
  · exact (Number.const ZP 0).pair F.seedIndex
  · exact (Number.const F.connectionP 1).pair F.connectionIndex
  · exact (Number.const F.connectionP 2).pair F.connectionIndex
  · exact (Number.const F.connectionP 3).pair F.connectionIndex

noncomputable def connectionDomain : Test (F.connectionP.prod (F.rowP.prod Presented.bool))
    (fun w x => decide (x.2.2∈((C w).connectionMap x.1).domain x.2.1)) := by
  apply F.casesTestFst
  · exact F.edgeDomain
  · exact F.testDomain
  all_goals exact (Test.const _ true).congr (by intro w x; simp only [ProductCircuit.connectionMap,ProductMap.flip,ProductMap.identity,Finset.mem_univ,decide_true])

noncomputable def rightBit {A : Word → Type} (AP : Presented A) :
    Map (AP.prod (F.rowP.prod Presented.bool)) Presented.bool (fun _ x => x.2.2) :=
  (Map.snd F.rowP Presented.bool).comp (Map.snd AP (F.rowP.prod Presented.bool))

noncomputable def comparisonDomain : Test (F.comparisonP.prod (F.rowP.prod Presented.bool))
    (fun w x => decide (x.2.2∈((C w).comparisonMap x.1).domain x.2.1)) := by
  apply F.comparisonTestFst
  · exact F.seedDomain
  · exact F.connectionDomain
  · exact F.connectionDomain
  · exact F.connectionDomain

end CircuitRealizer
end FinitePresentation

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.CircuitForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification
namespace FinitePresentation
open WordExpressions
attribute [local instance] Classical.propDecidable Classical.decEq
namespace Number
variable {A : Word → Type} (AP : Presented A)

noncomputable def vectorFirst : Number (AP.prod (Presented.bit.prod Presented.bit)) (fun _ x => x.2.1.val) where
  eval _ i := (Nat.unpair (Nat.unpair i).2).1
  correct w x := by simp only [Presented.prod_code,Presented.bit_code,Nat.unpair_pair]
  poly := by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)

theorem sum_vector (d : ℕ) (hd : d=1 ∨ d=2) (a b : Bit) :
    (ProductCircuit.sumForm d (vectorTwo d (a,b))).val = if d=1 then a.val else (a.val+b.val)%2 := by
  rcases hd with rfl|rfl
  · simp [ProductCircuit.sumForm_apply,vectorTwo]
  · simp [ProductCircuit.sumForm_apply,Fin.sum_univ_two,vectorTwo,ZMod.val_add]

end Number
end FinitePresentation
end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.ProductPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification
namespace FinitePresentation
open WordExpressions
attribute [local instance] Classical.propDecidable Classical.decEq

structure ProductRealizer {A : Word → Type} (AP : Presented A) (d : Word → ℕ)
    (dp : NatPoly (fun X : Fin 1 → Word => d (X 0))) (D : ∀ w,A w → ProductMap (d w)) where
  domain : Test (AP.prod ((Presented.fin d dp).prod Presented.bool)) (fun w x => decide (x.2.2∈(D w x.1).domain x.2.1))
  mapping : Map (AP.prod ((Presented.fin d dp).prod Presented.bool)) Presented.bool (fun w x => (D w x.1).mapping x.2.1 x.2.2)

namespace ProductRealizer
variable {A B : Word → Type} {AP : Presented A} {BP : Presented B}
    {d e : Word → ℕ} {dp : NatPoly (fun X : Fin 1 → Word => d (X 0))}
    {ep : NatPoly (fun X : Fin 1 → Word => e (X 0))}
    {D : ∀ w,A w → ProductMap (d w)}

noncomputable def comp (F : ProductRealizer AP d dp D) {f : ∀ w,B w → A w} (G : Map BP AP f) :
    ProductRealizer BP d dp (fun w b => D w (f w b)) where
  domain := F.domain.comp (Map.pair (G.comp (Map.fst _ _)) (Map.snd _ _))
  mapping := F.mapping.comp (Map.pair (G.comp (Map.fst _ _)) (Map.snd _ _))

noncomputable def sumCases (F : ProductRealizer AP d dp D) {E : ∀ w,B w → ProductMap (d w)}
    (G : ProductRealizer BP d dp E) : ProductRealizer (AP.sum BP) d dp (fun w x => x.elim (D w) (E w)) where
  domain := (Test.sumFst F.domain G.domain).congr (by intro w x; rcases x with ⟨x,y⟩; cases x <;> rfl)
  mapping := (Number.sumFst F.mapping G.mapping).congr (by intro w x; rcases x with ⟨x,y⟩; cases x <;> rfl)

noncomputable def identity (AP : Presented A) (d : Word → ℕ) (dp : NatPoly (fun X : Fin 1 → Word => d (X 0))) :
    ProductRealizer AP d dp (fun w _ => ProductMap.identity (d w)) where
  domain := (Test.const _ true).congr (by intro w x; simp [ProductMap.identity])
  mapping := (Map.snd _ _).comp (Map.snd _ _)

noncomputable def concat (F : ProductRealizer AP d dp D) {E : ∀ w,A w → ProductMap (e w)}
    (G : ProductRealizer AP e ep E) : ProductRealizer AP (fun w => d w+e w) (NatPoly.add dp ep)
      (fun w a => (D w a).concat (E w a)) where
  domain := {
    eval w v := if (Nat.unpair (Nat.unpair v).2).1<d w then F.domain.eval w v
      else G.domain.eval w (Nat.pair (Nat.unpair v).1 (Nat.pair ((Nat.unpair (Nat.unpair v).2).1-d w) (Nat.unpair (Nat.unpair v).2).2))
    correct w x := by
      rcases x with ⟨a,i,b⟩
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [Presented.prod_code,Presented.fin_code,Nat.unpair_pair,Fin.val_castAdd,j.isLt,ite_true]
        simpa only [Presented.prod_code,Presented.fin_code,ProductMap.concat,Fin.append_left] using F.domain.correct w (a,j,b)
      · simp only [Presented.prod_code,Presented.fin_code,Nat.unpair_pair,Fin.val_natAdd,show ¬d w+j.val<d w by omega,ite_false,Nat.add_sub_cancel_left]
        simpa only [Presented.prod_code,Presented.fin_code,ProductMap.concat,Fin.append_right] using G.domain.correct w (a,j,b)
    poly := BoolPoly.iteProp (NatPoly.lt (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.var 1))) (dp.rename (fun _ => 0))) F.domain.poly
      (G.domain.eval_poly (Poly.var 0) (NatPoly.pair (NatPoly.unpair_fst (NatPoly.var 1)) (NatPoly.pair
        (NatPoly.sub (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.var 1))) (dp.rename (fun _ => 0)))
        (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.var 1)))))) }
  mapping := {
    eval w v := if (Nat.unpair (Nat.unpair v).2).1<d w then F.mapping.eval w v
      else G.mapping.eval w (Nat.pair (Nat.unpair v).1 (Nat.pair ((Nat.unpair (Nat.unpair v).2).1-d w) (Nat.unpair (Nat.unpair v).2).2))
    correct w x := by
      rcases x with ⟨a,i,b⟩
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [Presented.prod_code,Presented.fin_code,Nat.unpair_pair,Fin.val_castAdd,j.isLt,ite_true]
        simpa only [Presented.prod_code,Presented.fin_code,ProductMap.concat,Fin.append_left] using F.mapping.correct w (a,j,b)
      · simp only [Presented.prod_code,Presented.fin_code,Nat.unpair_pair,Fin.val_natAdd,show ¬d w+j.val<d w by omega,ite_false,Nat.add_sub_cancel_left]
        simpa only [Presented.prod_code,Presented.fin_code,ProductMap.concat,Fin.append_right] using G.mapping.correct w (a,j,b)
    poly := NatPoly.iteProp (NatPoly.lt (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.var 1))) (dp.rename (fun _ => 0))) F.mapping.poly
      (G.mapping.eval_poly (Poly.var 0) (NatPoly.pair (NatPoly.unpair_fst (NatPoly.var 1)) (NatPoly.pair
        (NatPoly.sub (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.var 1))) (dp.rename (fun _ => 0)))
        (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.var 1)))))) }

noncomputable def inverse (F : ProductRealizer AP d dp D) : ProductRealizer AP d dp (fun w a => (D w a).inverse) where
  domain := {
    eval w v := (F.domain.eval w (Nat.pair (Nat.unpair v).1 (Nat.pair (Nat.unpair (Nat.unpair v).2).1 0)) &&
      decide (F.mapping.eval w (Nat.pair (Nat.unpair v).1 (Nat.pair (Nat.unpair (Nat.unpair v).2).1 0))=(Nat.unpair (Nat.unpair v).2).2)) ||
      (F.domain.eval w (Nat.pair (Nat.unpair v).1 (Nat.pair (Nat.unpair (Nat.unpair v).2).1 1)) &&
      decide (F.mapping.eval w (Nat.pair (Nat.unpair v).1 (Nat.pair (Nat.unpair (Nat.unpair v).2).1 1))=(Nat.unpair (Nat.unpair v).2).2))
    correct w x := by
      simp only [Presented.prod_code,Presented.fin_code,Nat.unpair_pair]
      have hdf := F.domain.correct w (x.1,x.2.1,false)
      have hdt := F.domain.correct w (x.1,x.2.1,true)
      have hmf := F.mapping.correct w (x.1,x.2.1,false)
      have hmt := F.mapping.correct w (x.1,x.2.1,true)
      simp only [Presented.prod_code,Presented.fin_code,Presented.bool_code] at hdf hdt hmf hmt
      simp only [show NaturalCode.bool false=0 from rfl,show NaturalCode.bool true=1 from rfl] at hdf hdt hmf hmt
      simp only [Presented.bool_code]
      rw [hdf,hdt,hmf,hmt]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,(NaturalCode.bool).injective.eq_iff,
        ProductMap.inverse,Finset.mem_image,Bool.exists_bool]
    poly := by
      have hk (b : ℕ) : NatPoly (fun X : Fin 2 → Word => Nat.pair (Nat.unpair (X 1).length).1 (Nat.pair (Nat.unpair (Nat.unpair (X 1).length).2).1 b)) :=
        NatPoly.pair (NatPoly.unpair_fst (NatPoly.var 1)) (NatPoly.pair (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.var 1))) (NatPoly.const b))
      exact BoolPoly.or (BoolPoly.and (F.domain.eval_poly (Poly.var 0) (hk 0))
        (NatPoly.eqtest (F.mapping.eval_poly (Poly.var 0) (hk 0)) (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.var 1)))))
        (BoolPoly.and (F.domain.eval_poly (Poly.var 0) (hk 1))
        (NatPoly.eqtest (F.mapping.eval_poly (Poly.var 0) (hk 1)) (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.var 1))))) }
  mapping := {
    eval w v := if (F.domain.eval w (Nat.pair (Nat.unpair v).1 (Nat.pair (Nat.unpair (Nat.unpair v).2).1 0)) &&
      decide (F.mapping.eval w (Nat.pair (Nat.unpair v).1 (Nat.pair (Nat.unpair (Nat.unpair v).2).1 0))=(Nat.unpair (Nat.unpair v).2).2)) then 0 else 1
    correct w x := by
      simp only [Presented.prod_code,Presented.fin_code,Nat.unpair_pair]
      have hdf := F.domain.correct w (x.1,x.2.1,false)
      have hmf := F.mapping.correct w (x.1,x.2.1,false)
      simp only [Presented.prod_code,Presented.fin_code,Presented.bool_code] at hdf hmf
      simp only [show NaturalCode.bool false=0 from rfl] at hdf hmf
      simp only [Presented.bool_code]
      rw [hdf,hmf]
      simp only [Bool.and_eq_true,decide_eq_true_eq,(NaturalCode.bool).injective.eq_iff]
      change (if _ then 0 else 1)=NaturalCode.bool (if _ then false else true)
      split <;> rfl
    poly := NatPoly.ite (BoolPoly.and
      (F.domain.eval_poly (Poly.var 0) (NatPoly.pair (NatPoly.unpair_fst (NatPoly.var 1)) (NatPoly.pair (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.var 1))) (NatPoly.const 0))))
      (NatPoly.eqtest (F.mapping.eval_poly (Poly.var 0) (NatPoly.pair (NatPoly.unpair_fst (NatPoly.var 1)) (NatPoly.pair (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.var 1))) (NatPoly.const 0))))
        (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.var 1))))) (NatPoly.const 0) (NatPoly.const 1) }

end ProductRealizer
end FinitePresentation
end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.CarryPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification
namespace FinitePresentation
open WordExpressions
attribute [local instance] Classical.propDecidable Classical.decEq
namespace Presented
@[simp] theorem option_none_code {A : Word → Type} (P : Presented A) (w : Word) : P.option.code w none=0 := rfl
@[simp] theorem option_some_code {A : Word → Type} (P : Presented A) (w : Word) (a : A w) : P.option.code w (some a)=P.code w a+1 := rfl
end Presented
namespace Number
variable {A B : Word → Type} {AP : Presented A} {BP : Presented B}
def optionFst {f : ∀ w,A w × B w → ℕ} {g : ∀ w,B w → ℕ}
    (F : Number (AP.prod BP) f) (G : Number BP g) :
    Number (AP.option.prod BP) (fun w x => x.1.elim (g w x.2) (fun a => f w (a,x.2))) where
  eval w i := if (Nat.unpair i).1=0 then G.eval w (Nat.unpair i).2 else F.eval w (Nat.pair ((Nat.unpair i).1-1) (Nat.unpair i).2)
  correct w x := by
    rcases x with ⟨x,y⟩
    cases x with
    | none => simpa only [Presented.prod_code,Nat.unpair_pair,Presented.option_none_code,ite_true,Option.elim_none] using G.correct w y
    | some a => simpa only [Presented.prod_code,Nat.unpair_pair,Presented.option_some_code,Nat.add_one_ne_zero,ite_false,Nat.add_sub_cancel,Option.elim_some] using F.correct w (a,y)
  poly := NatPoly.iteProp (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)) (G.eval_poly (Poly.var 0) (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)))
    (F.eval_poly (Poly.var 0) (NatPoly.pair (NatPoly.sub (NatPoly.unpair_fst (NatPoly.var 1)) (NatPoly.const 1)) (NatPoly.unpair_snd (NatPoly.var 1))))
end Number
namespace Test
variable {A B : Word → Type} {AP : Presented A} {BP : Presented B}
def optionFst {f : ∀ w,A w × B w → Bool} {g : ∀ w,B w → Bool}
    (F : Test (AP.prod BP) f) (G : Test BP g) :
    Test (AP.option.prod BP) (fun w x => x.1.elim (g w x.2) (fun a => f w (a,x.2))) where
  eval w i := if (Nat.unpair i).1=0 then G.eval w (Nat.unpair i).2 else F.eval w (Nat.pair ((Nat.unpair i).1-1) (Nat.unpair i).2)
  correct w x := by
    rcases x with ⟨x,y⟩
    cases x with
    | none => simpa only [Presented.prod_code,Nat.unpair_pair,Presented.option_none_code,ite_true,Option.elim_none] using G.correct w y
    | some a => simpa only [Presented.prod_code,Nat.unpair_pair,Presented.option_some_code,Nat.add_one_ne_zero,ite_false,Nat.add_sub_cancel,Option.elim_some] using F.correct w (a,y)
  poly := BoolPoly.iteProp (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)) (G.eval_poly (Poly.var 0) (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)))
    (F.eval_poly (Poly.var 0) (NatPoly.pair (NatPoly.sub (NatPoly.unpair_fst (NatPoly.var 1)) (NatPoly.const 1)) (NatPoly.unpair_snd (NatPoly.var 1))))
end Test
namespace ProductRealizer
variable {A : Word → Type} {AP : Presented A} {d : Word → ℕ}
    {dp : NatPoly (fun X : Fin 1 → Word => d (X 0))} {D : ∀ w,A w → ProductMap (d w)}
noncomputable def optionCases (F : ProductRealizer AP d dp D) (E : ∀ w,ProductMap (d w))
    (dom : Test ((Presented.fin d dp).prod Presented.bool) (fun w x => decide (x.2∈(E w).domain x.1)))
    (map : Map ((Presented.fin d dp).prod Presented.bool) Presented.bool (fun w x => (E w).mapping x.1 x.2)) :
    ProductRealizer AP.option d dp (fun w x => x.elim (E w) (D w)) where
  domain := (Test.optionFst F.domain dom).congr (by intro w x; rcases x with ⟨x,y⟩; cases x <;> rfl)
  mapping := (Number.optionFst F.mapping map).congr (by intro w x; rcases x with ⟨x,y⟩; cases x <;> rfl)

noncomputable def singletonConstant (AP : Presented A) (d : Word → ℕ) (dp : NatPoly (fun X : Fin 1 → Word => d (X 0))) (a b : Bool) :
    ProductRealizer AP d dp (fun _ _ => ProductMap.singleton (fun _ => a) (fun _ => b)) where
  domain := (Test.eq ((Map.snd _ _).comp (Map.snd _ _)) (Map.const _ Presented.bool (fun _ => a) (NatPoly.const (NaturalCode.bool a)))).congr (by intro w x; simp only [ProductMap.singleton,Finset.mem_singleton])
  mapping := (Number.const _ (NaturalCode.bool b)).congr (by intro w x; rfl)

noncomputable def carry (d : Word → ℕ) (dp : NatPoly (fun X : Fin 1 → Word => d (X 0))) :
    ProductRealizer (Presented.fin d dp) d dp (fun _ h => BinaryAddress.carryMap h) where
  domain := {
    eval _ v := if (Nat.unpair (Nat.unpair v).2).1<(Nat.unpair v).1 then decide ((Nat.unpair (Nat.unpair v).2).2=1)
      else if (Nat.unpair (Nat.unpair v).2).1=(Nat.unpair v).1 then decide ((Nat.unpair (Nat.unpair v).2).2=0) else true
    correct w x := by
      simp only [Presented.prod_code,Presented.fin_code,Presented.bool_code,Nat.unpair_pair]
      rcases x with ⟨h,i,b⟩
      change (if i.val<h.val then _ else if i.val=h.val then _ else _)=_
      by_cases hi : i<h
      · simp [hi,show i.val<h.val from hi,BinaryAddress.carryMap,NaturalCode.bool]
      · by_cases he : i=h
        · subst i; simp [BinaryAddress.carryMap,NaturalCode.bool]
        · simp [hi,show ¬i.val<h.val from hi,he,show i.val≠h.val from fun hv => he (Fin.ext hv),BinaryAddress.carryMap]
    poly := BoolPoly.iteProp
      (NatPoly.lt (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.var 1))) (NatPoly.unpair_fst (NatPoly.var 1)))
      (NatPoly.eqtest (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.var 1))) (NatPoly.const 1))
      (BoolPoly.iteProp (NatPoly.eqtest (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.var 1))) (NatPoly.unpair_fst (NatPoly.var 1)))
        (NatPoly.eqtest (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.var 1))) (NatPoly.const 0)) (BoolPoly.const true)) }
  mapping := {
    eval _ v := if (Nat.unpair (Nat.unpair v).2).1≤(Nat.unpair v).1 then 1-(Nat.unpair (Nat.unpair v).2).2 else (Nat.unpair (Nat.unpair v).2).2
    correct w x := by
      simp only [Presented.prod_code,Presented.fin_code,Presented.bool_code,Nat.unpair_pair]
      rcases x with ⟨h,i,b⟩
      change (if i.val≤h.val then _ else _)=NaturalCode.bool (if i≤h then !b else b)
      by_cases hi : i≤h <;> cases b <;> simp [hi,show (i.val≤h.val) = (i≤h) from rfl,NaturalCode.bool]
    poly := NatPoly.iteProp (NatPoly.le (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.var 1))) (NatPoly.unpair_fst (NatPoly.var 1)))
      (NatPoly.sub (NatPoly.const 1) (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.var 1))))
      (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.var 1))) }

noncomputable def congr (F : ProductRealizer AP d dp D) {E : ∀ w,A w → ProductMap (d w)}
    (h : ∀ w a,D w a=E w a) : ProductRealizer AP d dp E where
  domain := F.domain.congr (by intro w x; rw [h w x.1])
  mapping := F.mapping.congr (by intro w x; dsimp only; rw [h w x.1])

noncomputable def cycle (d : Word → ℕ) (dp : NatPoly (fun X : Fin 1 → Word => d (X 0))) :
    ProductRealizer (Presented.fin d dp).option d dp (fun w j => BinaryAddress.cycleMap (d w) j) := by
  let S := singletonConstant Presented.unit d dp true false
  let P := Map.pair (Map.const ((Presented.fin d dp).prod Presented.bool) Presented.unit (fun _ => ()) (NatPoly.const 0)) (Map.id _)
  exact ((carry d dp).optionCases (fun _ => ProductMap.singleton (fun _ => true) (fun _ => false))
    (S.domain.comp P) (S.mapping.comp P)).congr (by intro w x; cases x <;> rfl)

end ProductRealizer
end FinitePresentation
end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.CellularPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification
namespace FinitePresentation
open WordExpressions
attribute [local instance] Classical.propDecidable Classical.decEq
namespace CellularRealizer
open CellularCircuit
variable (A : Type) [Fintype A] (d : Word → ℕ) (dp : NatPoly (fun X : Fin 1 → Word => d (X 0)))
noncomputable abbrev pointP := Presented.fixed (Gate A)
noncomputable abbrev tripleP := Presented.fixed (A × A × A)
abbrev digitP := Presented.fin d dp
abbrev kindP := ((digitP d dp).prod (digitP d dp).option).sum ((digitP d dp).sum
  (((digitP d dp).prod (digitP d dp).option).sum (Presented.unit.sum Presented.unit)))
noncomputable abbrev edgeBase := (kindP d dp).prod (tripleP A)
def edgeEquiv (w : Word) : Connection (d w) A ≃
    (((Fin (d w) × Option (Fin (d w))) ⊕ (Fin (d w) ⊕ ((Fin (d w) × Option (Fin (d w))) ⊕ (Unit ⊕ Unit)))) × (A × A × A)) :=
  Connection.equiv.trans (Equiv.prodComm _ _)
noncomputable def edgeP : Presented (fun w => Connection (d w) A) := (edgeBase A d dp).retype (edgeEquiv A d)

noncomputable def casesNumber {f : ∀ w,Connection (d w) A → ℕ}
    (l : Number (((digitP d dp).prod (digitP d dp).option).prod (tripleP A))
      (fun w x => f w (.left x.2.1 x.2.2.1 x.2.2.2 x.1.1 x.1.2)))
    (c : Number ((digitP d dp).prod (tripleP A))
      (fun w x => f w (.center x.2.1 x.2.2.1 x.2.2.2 x.1)))
    (r : Number (((digitP d dp).prod (digitP d dp).option).prod (tripleP A))
      (fun w x => f w (.right x.2.1 x.2.2.1 x.2.2.2 x.1.1 x.1.2)))
    (j : Number (Presented.unit.prod (tripleP A))
      (fun w x => f w (.join x.2.1 x.2.2.1 x.2.2.2)))
    (o : Number (Presented.unit.prod (tripleP A))
      (fun w x => f w (.output x.2.1 x.2.2.1 x.2.2.2))) : Number (edgeP A d dp) f :=
  ((Number.sumFst l (Number.sumFst c (Number.sumFst r (Number.sumFst j o)))).retype (edgeEquiv A d)).congr
    (by intro w x; cases x <;> rfl)

noncomputable def pointIndex : Number (pointP A) (fun _ p => gateIndex p) := Number.fixed _ gateIndex
noncomputable def dimension : Number (pointP A) (fun _ p => dimension p) := Number.fixed (Gate A) CellularCircuit.dimension

noncomputable def edgeIndex : Number (edgeP A d dp) (fun _ e => connectionIndex e) :=
  ((Number.pair ((Number.fixed (A × A × A) (fun a => Nat.pair (NaturalCode.fixed A a.1)
    (Nat.pair (NaturalCode.fixed A a.2.1) (NaturalCode.fixed A a.2.2)))).comp (Map.snd _ _))
    (Number.code (kindP d dp) |>.comp (Map.fst _ _))).retype (edgeEquiv A d)).congr
    (by intro w x; cases x <;> rfl)

noncomputable def source : Map (edgeP A d dp) (pointP A) (fun _ => CellularCircuit.source) := by
  apply casesNumber
  · exact (Number.fixed _ (fun a : A × A × A => NaturalCode.fixed (Gate A) (.scalar a.1))).comp (Map.snd _ _)
  · exact (Number.fixed _ (fun a : A × A × A => NaturalCode.fixed (Gate A) (.scalar a.2.1))).comp (Map.snd _ _)
  · exact (Number.fixed _ (fun a : A × A × A => NaturalCode.fixed (Gate A) (.scalar a.2.2))).comp (Map.snd _ _)
  · exact (Number.fixed _ (fun a : A × A × A => NaturalCode.fixed (Gate A) (.first a.1 a.2.1 a.2.2))).comp (Map.snd _ _)
  · exact (Number.fixed _ (fun a : A × A × A => NaturalCode.fixed (Gate A) (.second a.1 a.2.1 a.2.2))).comp (Map.snd _ _)

noncomputable def target (F : A → A → A → A) : Map (edgeP A d dp) (pointP A) (fun _ => CellularCircuit.target F) := by
  apply casesNumber
  · exact (Number.fixed _ (fun a : A × A × A => NaturalCode.fixed (Gate A) (.first a.1 a.2.1 a.2.2))).comp (Map.snd _ _)
  · exact (Number.fixed _ (fun a : A × A × A => NaturalCode.fixed (Gate A) (.first a.1 a.2.1 a.2.2))).comp (Map.snd _ _)
  · exact (Number.fixed _ (fun a : A × A × A => NaturalCode.fixed (Gate A) (.second a.1 a.2.1 a.2.2))).comp (Map.snd _ _)
  · exact (Number.fixed _ (fun a : A × A × A => NaturalCode.fixed (Gate A) (.second a.1 a.2.1 a.2.2))).comp (Map.snd _ _)
  · exact (Number.fixed _ (fun a : A × A × A => NaturalCode.fixed (Gate A) (.scalar (F a.1 a.2.1 a.2.2)))).comp (Map.snd _ _)

noncomputable def port (F : A → A → A → A) : Number (edgeP A d dp) (fun _ e => (CellularCircuit.port F e).val) := by
  apply casesNumber
  · exact Number.const _ 0
  · exact Number.const _ 1
  · exact Number.const _ 1
  · exact Number.const _ 0
  · exact Number.const _ 0

noncomputable def edgeMap : ProductRealizer (edgeP A d dp) (fun w => d w+d w) (NatPoly.add dp dp)
    (fun _ => CellularCircuit.edgeMap) := by
  let C := ProductRealizer.carry d dp
  let R := ProductRealizer.cycle d dp
  let I := ProductRealizer.identity (digitP d dp) d dp
  let L := (C.comp (Map.fst _ _)).concat (R.comp (Map.snd _ _))
  let H := C.concat I
  let B := (C.comp (Map.fst _ _)).concat (R.inverse.comp (Map.snd _ _))
  let J := ProductRealizer.identity Presented.unit (fun w => d w+d w) (NatPoly.add dp dp)
  exact (((L.sumCases (H.sumCases (B.sumCases (J.sumCases J)))).comp (Map.fst _ _)).comp
    (Map.retype (edgeBase A d dp) (edgeEquiv A d))).congr (by intro w x; cases x <;> rfl)

end CellularRealizer
end FinitePresentation
end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.SeedBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification
namespace BinaryAddress
 theorem ofNat_apply (d n : ℕ) (i : Fin d) : ofNat d n i=decide (n/2^i.val%2=1) := by
  induction d generalizing n with
  | zero => exact Fin.elim0 i
  | succ d ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [ofNat,Fin.cons_zero,Fin.val_zero,pow_zero,Nat.div_one]
    · simp only [ofNat,Fin.cons_succ,Fin.val_succ,ih,pow_succ,Nat.div_div_eq_div_mul,Nat.mul_comm]
end BinaryAddress

end WLIdentification

end OAI
end


