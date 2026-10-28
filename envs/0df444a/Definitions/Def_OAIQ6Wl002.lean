-- Prove2me | Definitions.Def_OAIQ6Wl002
-- name    : OAIQ6Wl002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T01:57:25.113924+00:00
-- url     : https://prove2.me/theorems/f6a6c3ae-7457-4be3-a9cf-8967e5642ec1
-- title:
--   Definitions bundle OAIQ6Wl002 of the split of OpenAI, Variable-dimension Weisfeiler–Leman equivalence on general and subcubic graphs
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.VariableWL.main`, carved from OpenAI's openai/math development (OpenAI, *Variable-dimension Weisfeiler–Leman equivalence on general and subcubic graphs*, OpenAI Math Release, September 25, 2026, result family 133, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 240 declarations of OpenAI's Lean: 144 definitions, 5 instances and 91 theorems. The definitions and types are `OAI.VariableWL.Descriptor.Presentation.fixed`, `OAI.VariableWL.Encoding.fromMatrix`, `OAI.VariableWL.Encoding.graph`, `OAI.VariableWL.Encoding.pair`, `OAI.VariableWL.Encoding.readMatrix`, `OAI.VariableWL.Game.Fits`, `OAI.VariableWL.Game.FullStable`, `OAI.VariableWL.Game.GhostFamily`, `OAI.VariableWL.Game.PartialIso`, `OAI.VariableWL.Game.Position`, `OAI.VariableWL.Game.Realizes`, `OAI.VariableWL.Game.Ring`, `OAI.VariableWL.Game.RingLists`, `OAI.VariableWL.Game.Subposition`, `OAI.VariableWL.Game.Winning`, `OAI.VariableWL.Game.WinningFamily`, `OAI.VariableWL.Game.active`, `OAI.VariableWL.Game.swap`, `OAI.VariableWL.InputDecision.capped`, `OAI.VariableWL.MachineCellular.acceptCode`, `OAI.VariableWL.MachineCellular.acceptProgram`, `OAI.VariableWL.MachineCellular.base`, `OAI.VariableWL.MachineCellular.bitProgram`, `OAI.VariableWL.MachineCellular.comparisonPresentation`, `OAI.VariableWL.MachineCellular.dimensionProgram`, `OAI.VariableWL.MachineCellular.fixedPower`, `OAI.VariableWL.MachineCellular.graphListing`, `OAI.VariableWL.MachineCellular.initial`, `OAI.VariableWL.MachineCellular.inputProgram`, `OAI.VariableWL.MachineCellular.letterInput`, `OAI.VariableWL.MachineCellular.listing`, `OAI.VariableWL.MachineCellular.pairProgram`, `OAI.VariableWL.MachineCellular.presentation`, `OAI.VariableWL.MachineCellular.realPresentation`, `OAI.VariableWL.MachineCellular.ruleCode`, `OAI.VariableWL.MachineCellular.ruleProgram`, `OAI.VariableWL.MachineReduction.Comparison`, `OAI.VariableWL.MachineReduction.Real`, `OAI.VariableWL.MachineReduction.circuit`, `OAI.VariableWL.MachineReduction.imageInstance` and 104 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `VariableWL_Affine`, `VariableWL_BlockImages`, `VariableWL_Blocks`, `VariableWL_CircuitCatalog`, `VariableWL_Completeness`, `VariableWL_Decision`, `VariableWL_ExponentialRecipe`, `VariableWL_GeneralGame`, `VariableWL_GeneralReduction`, `VariableWL_MachineCellular`, `VariableWL_MachineReduction`, `VariableWL_NumericProgram`, `VariableWL_NumericRefinement`, `VariableWL_PortGame`, `VariableWL_PortGraph`, `VariableWL_PrefixGame`, `VariableWL_PrefixListing`, `VariableWL_PrefixParts`, `VariableWL_PrefixWiring`, `VariableWL_ProductImages`, `VariableWL_Refinement`, `VariableWL_RefinementTable`, `VariableWL_StackSimulation`, `VariableWL_SubcubicGame`, `VariableWL_Subdivision`, `VariableWL_TypedGame`, `VariableWL_Wrapping`.
--
--   **Imports.** It imports the published bundle `Def_VariableWL`; the bundles `OAIQ6Wl000` and `OAIQ6Wl001` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.VariableWL.general_hard`, `OAI.VariableWL.main` and `OAI.VariableWL.subcubic_hard`.
-- source:
--   OpenAI, Variable-dimension Weisfeiler–Leman equivalence on general and subcubic graphs, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 133; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Variable-dimension-Weisfeiler-Leman-equivalence-on-general-and-subcubic-graphs-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_VariableWL
import Definitions.Def_OAIQ6Wl000
import Definitions.Def_OAIQ6Wl001

section
-- module Solutions.OAIQ6_WL.VariableWL_Affine
attribute [-instance] _root_.OAI.VariableWL.BlockCoordinates.defaultProperNumberings _root_.OAI.VariableWL.Circuit.ProductCellular.powTwoNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6

namespace VariableWL

noncomputable instance (priority := 5) defaultFiniteNumberings (A : Type uVariable3) (B : A → Type uVariable6)
    [∀a,Fintype (B a)] : (a : A) → FiniteNumbering (B a) :=
  fun a=>defaultFiniteNumbering (B a)
end VariableWL

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Refinement
attribute [-instance] _root_.OAI.VariableWL.Circuit.ProductCellular.powTwoNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6

namespace VariableWL

def defaultColor (k : ℕ) : (s : ℕ) → Color k s
  | 0 => fun _ _ => (false, false)
  | s + 1 => (defaultColor k s, 0)

instance colorInhabited (k s : ℕ) : Inhabited (Color k s) := ⟨defaultColor k s⟩

abbrev TaggedTuple (G H : Graph) (k : ℕ) := Tuple G k ⊕ Tuple H k

noncomputable def tagColor (G H : Graph) (k s : ℕ) : TaggedTuple G H k → Color k s :=
  Sum.elim (color G k s) (color H k s)

def liftColor {k s t : ℕ} (f : Color k s → Color k t) : Color k (s+1) → Color k (t+1) :=
  fun c => (f c.1, c.2.map (fun a => f ∘ a))

def StableAt (G H : Graph) (k s : ℕ) : Prop :=
  (tagColor G H k (s+1)).FactorsThrough (tagColor G H k s)

noncomputable def samePairs (G H : Graph) (k s : ℕ) :
    Finset (TaggedTuple G H k × TaggedTuple G H k) := by
  classical
  exact Finset.univ.filter (fun p => tagColor G H k s p.1 = tagColor G H k s p.2)

end VariableWL

namespace VariableWL

noncomputable def permColor {k : ℕ} (e : Equiv.Perm (Fin k)) :
    (s : ℕ) → Color k s → Color k s
  | 0, c => fun i j => c (e i) (e j)
  | s+1, c => (permColor e s c.1,
      c.2.map (fun p i => permColor e s (p (e i))))

def StableEq {G H : Graph} {k : ℕ} (v : Tuple G k) (w : Tuple H k) : Prop :=
  ∀ s, color G k s v = color H k s w

end VariableWL

universe uGame1 uGame2 uGame3 uGame4 uGame5 uGame6 uGame7

namespace VariableWL.Game

abbrev Position (G H : Graph) (q : ℕ) := Fin q → Option (Fin G.order × Fin H.order)

def PartialIso {G H : Graph} {q : ℕ} (p : Position G H q) : Prop :=
  ∀ i j a b, p i = some a → p j = some b →
    (a.1 = b.1 ↔ a.2 = b.2) ∧ (G.graph.Adj a.1 b.1 ↔ H.graph.Adj a.2 b.2)

def Subposition {G H : Graph} {q : ℕ} (p' p : Position G H q) : Prop :=
  ∀ i a, p' i = some a → p i = some a

def WinningFamily {G H : Graph} {q : ℕ} (S : Set (Position G H q)) : Prop :=
  (∀ p ∈ S, PartialIso p) ∧
  (∀ p ∈ S, ∀ p', Subposition p' p → p' ∈ S) ∧
  (∀ p ∈ S, ∀ i, p i = none → ∃ e : Fin G.order ≃ Fin H.order,
    ∀ v, Function.update p i (some (v, e v)) ∈ S)

def Winning {G H : Graph} {q : ℕ} (p : Position G H q) : Prop :=
  ∃ S, p ∈ S ∧ WinningFamily S

theorem Winning.partialIso {G H : Graph} {q : ℕ} {p : Position G H q}
    (h : Winning p) : PartialIso p := by
  obtain ⟨S, hp, hS⟩ := h
  exact hS.1 p hp

theorem Winning.discard {G H : Graph} {q : ℕ} {p p' : Position G H q}
    (h : Winning p) (hp' : Subposition p' p) : Winning p' := by
  obtain ⟨S, hp, hS⟩ := h
  exact ⟨S, hS.2.1 p hp p' hp', hS⟩

theorem Winning.move {G H : Graph} {q : ℕ} {p : Position G H q}
    (h : Winning p) (i : Fin q) (hi : p i = none) :
    ∃ e : Fin G.order ≃ Fin H.order, ∀ v,
      Winning (Function.update p i (some (v, e v))) := by
  obtain ⟨S, hp, hS⟩ := h
  obtain ⟨e, he⟩ := hS.2.2 p hp i hi
  exact ⟨e, fun v => ⟨S, he v, hS⟩⟩

theorem clear_subposition {G H : Graph} {q : ℕ} (p : Position G H q) (j : Fin q) :
    Subposition (Function.update p j none) p := by
  intro i a hi
  by_cases h : i = j
  · subst i; simp at hi
  · simpa [Function.update_of_ne h] using hi

def Realizes {G H : Graph} {q k : ℕ} (p : Position G H q)
    (σ : Fin k → Fin q) (v : Tuple G k) (w : Tuple H k) : Prop :=
  ∀ i, p (σ i) = some (v i, w i)

end VariableWL.Game

namespace VariableWL.Game

theorem Subposition.refl {G H : Graph} {q : ℕ} (p : Position G H q) :
    Subposition p p := fun _ _ => id

theorem Subposition.trans {G H : Graph} {q : ℕ} {p₁ p₂ p₃ : Position G H q}
    (h₁ : Subposition p₁ p₂) (h₂ : Subposition p₂ p₃) : Subposition p₁ p₃ :=
  fun i a ha => h₂ i a (h₁ i a ha)

theorem place_extends {G H : Graph} {q : ℕ} (p : Position G H q) (i : Fin q)
    (hi : p i = none) (a : Fin G.order × Fin H.order) :
    Subposition p (Function.update p i (some a)) := by
  intro j b hj
  by_cases hji : j = i
  · subst j; rw [hi] at hj; contradiction
  · simpa [Function.update_of_ne hji] using hj

theorem Winning.fill {G H : Graph} {q : ℕ} {p : Position G H q} (hp : Winning p)
    (n : ℕ) (σ : Fin n → Fin q) (hσ : Function.Injective σ)
    (hfree : ∀ i, p (σ i) = none) :
    ∃ E : Tuple G n ≃ Tuple H n, ∀ v, ∃ p' : Position G H q,
      Winning p' ∧ Subposition p p' ∧ Realizes p' σ v (E v) := by
  classical
  induction n generalizing p with
  | zero =>
    refine ⟨Equiv.piCongrRight (fun i : Fin 0 => Fin.elim0 i), ?_⟩
    intro v
    exact ⟨p, hp, Subposition.refl p, fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨e, he⟩ := hp.move (σ 0) (hfree 0)
    have ht (z : Fin G.order) :
        ∃ E : Tuple G n ≃ Tuple H n, ∀ v, ∃ p' : Position G H q,
          Winning p' ∧ Subposition (Function.update p (σ 0) (some (z, e z))) p' ∧
          Realizes p' (σ ∘ Fin.succ) v (E v) := by
      apply ih (he z) (σ ∘ Fin.succ) (hσ.comp (Fin.succ_injective n))
      intro i
      rw [Function.update_of_ne]
      · exact hfree i.succ
      · intro h
        exact Fin.succ_ne_zero i (hσ h)
    choose E hE using ht
    let F : Tuple G (n+1) ≃ Tuple H (n+1) :=
      (Fin.consEquiv (fun _ : Fin (n+1) => Fin G.order)).symm |>.trans
        ((triangularEquiv e E).trans (Fin.consEquiv (fun _ : Fin (n+1) => Fin H.order)))
    refine ⟨F, ?_⟩
    intro v
    obtain ⟨p', hp', hsub, hreal⟩ := hE (v 0) (Fin.tail v)
    refine ⟨p', hp', (place_extends p (σ 0) (hfree 0) _).trans hsub, ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change p' (σ 0) = some (v 0, e (v 0))
      exact hsub (σ 0) _ (by simp)
    · exact hreal j

end VariableWL.Game

namespace VariableWL.Game

def FullStable {G H : Graph} {k : ℕ}
    (v : Fin (k+1) → Fin G.order) (w : Fin (k+1) → Fin H.order) : Prop :=
  ∀ σ : Fin k ↪ Fin (k+1), StableEq (v ∘ σ) (w ∘ σ)

end VariableWL.Game

namespace VariableWL.Game

def Fits {G H : Graph} {k : ℕ} (p : Position G H (k+1))
    (v : Fin (k+1) → Fin G.order) (w : Fin (k+1) → Fin H.order) : Prop :=
  ∀ i a, p i = some a → v i = a.1 ∧ w i = a.2

def GhostFamily (G H : Graph) (k : ℕ) : Set (Position G H (k+1)) :=
  {p | ∃ v w, FullStable v w ∧ Fits p v w}

end VariableWL.Game

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Subdivision
attribute [-instance] _root_.OAI.VariableWL.Circuit.ProductCellular.powTwoNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9

namespace VariableWL.Subdivision

variable {P : Type uVariable1} {E : Type uVariable2} {n : ℕ}

def owner (src dst : E → P) (cut : E → Fin (n+1)) : Vertex P E n → P
  | .inl p => p
  | .inr (e,j) => if j.val < (cut e).val then src e else dst e

@[simp] theorem owner_real (src dst : E → P) (cut : E → Fin (n+1)) (p : P) :
    owner src dst cut (.inl p) = p := rfl

end VariableWL.Subdivision

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Wrapping
attribute [-instance] _root_.OAI.VariableWL.Circuit.ProductCellular.powTwoNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10 uVariable11

namespace VariableWL.Wrapping.RowDiagram
open scoped CharTwo
open Markers
variable {I : Type uVariable6} {V : Type uVariable7} {L : Type uVariable8} [DecidableEq I] [DecidableEq L]
    {G : SimpleGraph V} {next : Equiv.Perm I} (D : RowDiagram G next)

def Labeled (label : V → L) (first last : I → L) : Prop :=
  ∀ u v, G.Adj u v →
    match D.horizontal u v with
    | none => (D.boundary u, label u) = (D.boundary v, label v)
    | some i =>
      ((D.boundary u, label u) = (i, first i) ∧
        (D.boundary v, label v) = (next i, last i)) ∨
      ((D.boundary v, label v) = (i, first i) ∧
        (D.boundary u, label u) = (next i, last i))

end VariableWL.Wrapping.RowDiagram

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_ProductImages
attribute [-instance] _root_.OAI.VariableWL.AffineAlphabet.linearFintype _root_.OAI.VariableWL.BlockCoordinates.coordinateFintype _root_.OAI.VariableWL.BlockCoordinates.defaultProperNumberings _root_.OAI.VariableWL.Blocks.blockFintype _root_.OAI.VariableWL.Blocks.rawValueAddCommGroup _root_.OAI.VariableWL.Blocks.rawValueFintype _root_.OAI.VariableWL.Blocks.readoutValueAddCommGroup _root_.OAI.VariableWL.Blocks.readoutValueFintype _root_.OAI.VariableWL.Blocks.valuationFintype _root_.OAI.VariableWL.Circuit.ProductCellular.powTwoNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6

namespace VariableWL.ProductImages
open scoped CharTwo
open VariableWL.Affine

variable (r : ℕ) (P : Type uVariable1) (E : Type uVariable2)

namespace Instance
variable {r : ℕ} {P : Type uVariable3} {E : Type uVariable4} (J : Instance r P E)

def Consistent : Prop := Nonempty J.Witness

open Subdivision

end Instance
end VariableWL.ProductImages

namespace VariableWL.ProductImages.Instance
open VariableWL.Affine Subdivision
variable {r n : ℕ} {P : Type uVariable5} {E : Type uVariable6} (J : ProductImages.Instance r P E)

def cutShifts (cut : E → Fin (n+1)) (v : ∀ p, Vec (J.dimension p)) : J.Shifts n :=
  (v, fun (e,j) => if j.val < (cut e).val then J.leftForm e (v (J.source e))
    else J.rightForm e (v (J.target e)))

end VariableWL.ProductImages.Instance

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Blocks
attribute [-instance] _root_.OAI.VariableWL.AffineAlphabet.linearFintype _root_.OAI.VariableWL.BlockCoordinates.coordinateFintype _root_.OAI.VariableWL.BlockCoordinates.defaultProperNumberings _root_.OAI.VariableWL.Blocks.blockFintype _root_.OAI.VariableWL.Blocks.rawValueAddCommGroup _root_.OAI.VariableWL.Blocks.rawValueFintype _root_.OAI.VariableWL.Blocks.readoutValueAddCommGroup _root_.OAI.VariableWL.Blocks.readoutValueFintype _root_.OAI.VariableWL.Blocks.valuationFintype _root_.OAI.VariableWL.Circuit.ProductCellular.powTwoNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10 uVariable11 uVariable12 uVariable13 uVariable14 uVariable15 uVariable16 uVariable17 uVariable18

namespace VariableWL.ProductImages.Instance
open VariableWL.Affine Subdivision
variable {r n : ℕ} {P : Type uVariable17} {E : Type uVariable18} (J : ProductImages.Instance r P E)

def AgreeAt (h g : J.Shifts n) : Vertex P E n → Prop
  | .inl p => h.1 p = g.1 p
  | .inr q => h.2 q = g.2 q

end VariableWL.ProductImages.Instance

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_BlockImages
attribute [-instance] _root_.OAI.VariableWL.AffineAlphabet.linearFintype _root_.OAI.VariableWL.BlockCoordinates.coordinateFintype _root_.OAI.VariableWL.BlockCoordinates.defaultProperNumberings _root_.OAI.VariableWL.Blocks.blockFintype _root_.OAI.VariableWL.Blocks.rawValueAddCommGroup _root_.OAI.VariableWL.Blocks.rawValueFintype _root_.OAI.VariableWL.Blocks.readoutValueAddCommGroup _root_.OAI.VariableWL.Blocks.readoutValueFintype _root_.OAI.VariableWL.Blocks.valuationFintype _root_.OAI.VariableWL.Circuit.ProductCellular.powTwoNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10 uVariable11 uVariable12

namespace VariableWL.Markers
open scoped CharTwo
variable {V : Type uVariable4} {G : SimpleGraph V}

@[simp] theorem walkSum_copy (ω : V → V → Bit) {u v u' v' : V}
    (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    walkSum ω (p.copy hu hv) = walkSum ω p := by
  subst u'; subst v'; rfl

end VariableWL.Markers

namespace VariableWL.ProductImages.Instance
open VariableWL.Affine Subdivision
variable {r n : ℕ} {P : Type uVariable9} {E : Type uVariable10} (J : ProductImages.Instance r P E)

noncomputable def replaceInternal (hn : 0 < n) (S : Set (Link E n))
    (root : Vertex P E n) (a : Bit) (h : J.Shifts n) : J.Shifts n := by
  classical
  exact (h.1, fun q => if (supportGraph hn J.source J.target S).Reachable root (.inr q)
    then a else h.2 q)

end VariableWL.ProductImages.Instance

namespace VariableWL.ProductImages.Instance
open Subdivision
variable {r n : ℕ} {P : Type uVariable11} {E : Type uVariable12} (J : ProductImages.Instance r P E)

noncomputable def transport (l : Link E n) (i : Fin r) : Equiv.Perm Bool :=
  if l.2.val = n then J.ambient l.1 i else Equiv.refl _

noncomputable def relativeAlignment (cut cut' : E → Fin (n+1))
    (v : Vertex P E n) (i : Fin r) : Equiv.Perm Bool :=
  J.alignment cut v i * (J.alignment cut' v i)⁻¹

end VariableWL.ProductImages.Instance

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_GeneralGame
attribute [-instance] _root_.OAI.VariableWL.Circuit.ProductCellular.powTwoNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6

namespace VariableWL.Game
attribute [local instance] Classical.propDecidable

theorem Winning.neighborhood_bijection {G H : Graph} {q : ℕ} (hq : 2 ≤ q)
    {p : Position G H q} (hp : Winning p) {i : Fin q}
    {a : Fin G.order} {b : Fin H.order} (hi : p i = some (a,b)) :
    ∃ e : Fin G.order ≃ Fin H.order, ∀ v, G.graph.Adj a v ↔ H.graph.Adj b (e v) := by
  classical
  let : Nontrivial (Fin q) := Fin.nontrivial_iff_two_le.mpr hq
  obtain ⟨j,hj⟩ := exists_ne i
  let one : Position G H q := Function.update (fun _ => none) i (some (a,b))
  have hs : Subposition one p := by
    intro l c hc
    by_cases hl : l = i
    · subst l
      have hc' : (a,b) = c := by simpa [one] using hc
      simpa only [← hc'] using hi
    · simp [one,Function.update_of_ne hl] at hc
  have hone := hp.discard hs
  obtain ⟨e,he⟩ := hone.move j (by simp [one,Function.update_of_ne hj])
  refine ⟨e,fun v => ?_⟩
  exact ((he v).partialIso i j (a,b) (v,e v)
    (by simp [Function.update_of_ne hj.symm,one]) (by simp)).2

theorem Winning.degree_eq {G H : Graph} {q : ℕ} (hq : 2 ≤ q)
    {p : Position G H q} (hp : Winning p) {i : Fin q}
    {a : Fin G.order} {b : Fin H.order} (hi : p i = some (a,b)) :
    G.graph.degree a = H.graph.degree b := by
  classical
  obtain ⟨e,he⟩ := hp.neighborhood_bijection hq hi
  let f : G.graph.neighborSet a ≃ H.graph.neighborSet b := {
    toFun := fun v => ⟨e v.val, (he v.val).mp v.property⟩
    invFun := fun w => ⟨e.symm w.val, (he (e.symm w.val)).mpr (by simpa only [Equiv.apply_symm_apply,SimpleGraph.mem_neighborSet] using w.property)⟩
    left_inv := fun v => Subtype.ext (e.symm_apply_apply v.val)
    right_inv := fun w => Subtype.ext (e.apply_symm_apply w.val) }
  simpa only [SimpleGraph.card_neighborSet_eq_degree] using Fintype.card_congr f
end VariableWL.Game

namespace VariableWL.Game
variable {G H : Graph} {q : ℕ} {B : Type uVariable5} [DecidableEq B]

def active (part : Fin G.order → B) (p : Position G H q) : Finset B :=
  (Finset.univ.image (fun i => (p i).map (fun a => part a.1))).eraseNone

end VariableWL.Game

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_GeneralReduction
attribute [-instance] _root_.OAI.VariableWL.Circuit.ProductCellular.powTwoNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10

namespace VariableWL.Game
variable {G H : Graph} {r : ℕ} {B : Type uVariable7} {Z : B → Type uVariable9}
variable (query : B → Fin G.order) (response : (Σ b, Z b) → Fin H.order)

def Ring (v : Fin r → Σ b, Z b) : Prop :=
  ∃ p : Position G H (r+1), Winning p ∧
    ∃ σ : Fin r → Fin (r+1), Function.Injective σ ∧
      ∀ i, p (σ i) = some (query (v i).1,response (v i))

variable
  (recognize : ∀ (p : Position G H (r+1)), Winning p → ∀ i b w,
    p i = some (query b,w) → ∃ z : Z b, w = response ⟨b,z⟩)
  (rel : (Σ b, Z b) → (Σ b, Z b) → Prop)
  (agree : ∀ (p : Position G H (r+1)), Winning p → ∀ i j v w,
    p i = some (query v.1,response v) → p j = some (query w.1,response w) → rel v w)

include recognize in
theorem ring_nonempty
    (hwin : Winning (fun _ : Fin (r+1) => none : Position G H (r+1))) (b : Fin r → B) :
    ∃ z : ∀ i, Z (b i), Ring query response (fun i => ⟨b i,z i⟩) := by
  obtain ⟨E,hE⟩ := hwin.fill r Fin.castSucc (Fin.castSucc_injective r) (fun _ => rfl)
  obtain ⟨p,hp,_,hreal⟩ := hE (fun i => query (b i))
  have hz := fun i => recognize p hp (Fin.castSucc i) (b i) (E (fun j => query (b j)) i) (hreal i)
  choose z hz using hz
  refine ⟨z,p,hp,Fin.castSucc,Fin.castSucc_injective r,?_⟩
  intro i
  simpa only [hz i] using hreal i

include agree in
theorem Ring.compatible {v : Fin r → Σ b, Z b} (hv : Ring query response v) (i j : Fin r) :
    rel (v i) (v j) := by
  obtain ⟨p,hp,σ,_,hσ⟩ := hv
  exact agree p hp (σ i) (σ j) (v i) (v j) (hσ i) (hσ j)

include recognize agree in

theorem Ring.replace {v : Fin r → Σ b, Z b} (hv : Ring query response v)
    (i : Fin r) (b : B) :
    ∃ z : Z b, Ring query response (Function.update v i ⟨b,z⟩) ∧
      ∀ j, rel (v j) ⟨b,z⟩ := by
  classical
  obtain ⟨p,hp,σ,hσ,hreal⟩ := hv
  obtain ⟨fresh,hfresh⟩ := exists_fresh σ
  let p0 := Function.update p fresh none
  have hp0 : Winning p0 := hp.discard (clear_subposition p fresh)
  have hreal0 (j : Fin r) : p0 (σ j) = some (query (v j).1,response (v j)) := by
    simpa only [p0,Function.update_of_ne (hfresh j)] using hreal j
  obtain ⟨e,he⟩ := hp0.move fresh (by simp [p0])
  let p1 := Function.update p0 fresh (some (query b,e (query b)))
  have hp1 : Winning p1 := he (query b)
  obtain ⟨z,hz⟩ := recognize p1 hp1 fresh b (e (query b)) (by simp [p1])
  have hnew : p1 fresh = some (query b,response ⟨b,z⟩) := by simp [p1,hz]
  have hold (j : Fin r) : p1 (σ j) = some (query (v j).1,response (v j)) := by
    simpa only [p1,Function.update_of_ne (hfresh j)] using hreal0 j
  refine ⟨z,⟨p1,hp1,Function.update σ i fresh,update_injective_of_fresh hσ i fresh hfresh,?_⟩,
    fun j => agree p1 hp1 (σ j) fresh (v j) ⟨b,z⟩ (hold j) hnew⟩
  intro j
  by_cases hj : j = i
  · subst j
    simpa only [Function.update_self] using hnew
  · simpa only [Function.update_of_ne hj] using hold j

include recognize agree in

theorem Ring.replace_all {v : Fin r → Σ b, Z b} (hv : Ring query response v) (b : Fin r → B) :
    ∃ w : Fin r → Σ b, Z b, Ring query response w ∧
      ∀ i, (w i).1 = b i ∧ rel (v i) (w i) := by
  classical
  have aux (s : Finset (Fin r)) : ∃ w : Fin r → Σ b, Z b, Ring query response w ∧
      (∀ i ∈ s, (w i).1 = b i ∧ rel (v i) (w i)) ∧ ∀ i ∉ s, w i = v i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨v,hv,by simp,fun _ _ => rfl⟩
    | @insert i s hi ih =>
      obtain ⟨w,hw,hinside,houtside⟩ := ih
      obtain ⟨z,hz,hrel⟩ := hw.replace query response recognize rel agree i (b i)
      refine ⟨Function.update w i ⟨b i,z⟩,hz,?_,?_⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with hji | hj
        · subst j
          simpa only [Function.update_self,houtside i hi] using And.intro (rfl : (⟨b i,z⟩ : Σ b, Z b).1 = b i) (hrel i)
        · by_cases hji : j = i
          · subst j; exact False.elim (hi hj)
          · simpa only [Function.update_of_ne hji] using hinside j hj
      · intro j hj
        have hji : j ≠ i := fun h => hj (h ▸ Finset.mem_insert_self _ _)
        rw [Function.update_of_ne hji]
        exact houtside j (fun h => hj (Finset.mem_insert_of_mem h))
  obtain ⟨w,hw,hs,_⟩ := aux Finset.univ
  exact ⟨w,hw,fun i => hs i (Finset.mem_univ _)⟩
end VariableWL.Game

namespace VariableWL.Game
variable {G H : Graph} {r : ℕ} {B : Type uVariable8} {Z Y : B → Type uVariable10}
variable (query : B → Fin G.order) (response : (Σ b, Z b) → Fin H.order)
variable (decode : ∀ b, Z b → Y b)

def RingLists (b : Fin r → B) : Set (∀ i, Y (b i)) :=
  {y | ∃ v : Fin r → Σ b, Z b, Ring query response v ∧
    ∀ i, decodeSigma decode (v i) = ⟨b i,y i⟩}

variable
  (recognize : ∀ (p : Position G H (r+1)), Winning p → ∀ i b w,
    p i = some (query b,w) → ∃ z : Z b, w = response ⟨b,z⟩)
  (rel : (Σ b, Y b) → (Σ b, Y b) → Prop)
  (agree : ∀ (p : Position G H (r+1)), Winning p → ∀ i j v w,
    p i = some (query v.1,response v) → p j = some (query w.1,response w) →
      rel (decodeSigma decode v) (decodeSigma decode w))

include recognize in
theorem ringLists_nonempty
    (hwin : Winning (fun _ : Fin (r+1) => none : Position G H (r+1))) (b : Fin r → B) :
    (RingLists query response decode b).Nonempty := by
  obtain ⟨z,hz⟩ := ring_nonempty query response recognize hwin b
  exact ⟨fun i => decode (b i) (z i),fun i => ⟨b i,z i⟩,hz,fun _ => rfl⟩

include agree in
theorem ringLists_compatible {b : Fin r → B} {y : ∀ i, Y (b i)}
    (hy : y ∈ RingLists query response decode b) (i j : Fin r) :
    rel ⟨b i,y i⟩ ⟨b j,y j⟩ := by
  obtain ⟨v,hv,he⟩ := hy
  have h := hv.compatible query response
    (fun v w => rel (decodeSigma decode v) (decodeSigma decode w)) agree i j
  simpa only [he] using h

include recognize agree in
theorem ringLists_transfer {b : Fin r → B} {y : ∀ i, Y (b i)}
    (hy : y ∈ RingLists query response decode b) (c : Fin r → B) :
    ∃ z ∈ RingLists query response decode c, ∀ i, rel ⟨b i,y i⟩ ⟨c i,z i⟩ := by
  obtain ⟨v,hv,hvY⟩ := hy
  obtain ⟨w,hw,hwc⟩ := hv.replace_all query response recognize
    (fun v w => rel (decodeSigma decode v) (decodeSigma decode w)) agree c
  let z : ∀ i, Y (c i) := fun i => (hwc i).1 ▸ decode (w i).1 (w i).2
  have he (i : Fin r) : decodeSigma decode (w i) = ⟨c i,z i⟩ :=
    sigma_eq_cast (decodeSigma decode (w i)) (hwc i).1
  refine ⟨z,⟨w,hw,he⟩,?_⟩
  intro i
  simpa only [hvY i,he i] using (hwc i).2
end VariableWL.Game

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_PortGraph
attribute [-instance] _root_.OAI.VariableWL.Circuit.ProductCellular.powTwoNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9

namespace VariableWL.SubcubicRealization
attribute [local instance] Classical.propDecidable

namespace Vertex
variable {V : Type uVariable4} {color : V → ℕ}

def triangle (v : V) (j : Fin 3) : Vertex color := ⟨v,j,0,by omega⟩
def connector (v : V) (j : Fin 3) : Vertex color := ⟨v,j,1,by omega⟩

end Vertex

variable {V : Type uVariable5} (Y : PortGraph V) (color : V → ℕ)

theorem triangle_adj_triangle (v w : V) (j k : Fin 3) :
    (graph Y color).Adj (Vertex.triangle v j) (Vertex.triangle w k) ↔ v = w ∧ j ≠ k := by
  simp [graph,Internal,External,Vertex.triangle]

theorem triangle_adj {x : Vertex color} (v : V) (j : Fin 3) :
    (graph Y color).Adj (Vertex.triangle v j) x ↔
      (x.owner = v ∧ x.level = 0 ∧ x.port ≠ j) ∨ x = Vertex.connector v j := by
  constructor
  · intro h
    rcases h with ⟨ho,(⟨_,hx,hp⟩ | ⟨hp,hl⟩)⟩ | ⟨hx,_,_⟩
    · exact Or.inl ⟨ho.symm,hx,hp.symm⟩
    · right
      apply Vertex.ext (x := x) (y := Vertex.connector v j) ho.symm hp.symm
      have : x.level = 1 := by change 0+1=x.level ∨ x.level+1=0 at hl; omega
      exact this
    · change (0 : ℕ) = 1 at hx
      omega
  · rintro (⟨ho,hx,hp⟩ | rfl)
    · exact Or.inl ⟨ho.symm,Or.inl ⟨rfl,hx,hp.symm⟩⟩
    · exact Or.inl ⟨rfl,Or.inr ⟨rfl,Or.inl rfl⟩⟩

theorem triangle_characterization (x : Vertex color) :
    (∃ y z, (graph Y color).Adj x y ∧ (graph Y color).Adj y z ∧ (graph Y color).Adj z x) ↔
      x.level = 0 := by
  constructor
  · rintro ⟨y,z,hxy,hyz,hzx⟩
    by_contra hx
    have hxz := (graph Y color).symm.symm _ _ hzx
    rcases hxy with hxy | hxy <;> rcases hxz with hxz | hxz
    · obtain ⟨hoy,hpy,hly⟩ : x.owner=y.owner ∧ x.port=y.port ∧
          (x.level+1=y.level ∨ y.level+1=x.level) := by
        rcases hxy with ⟨ho,h | h⟩
        · exact (hx h.1).elim
        · exact ⟨ho,h⟩
      obtain ⟨hoz,hpz,hlz⟩ : x.owner=z.owner ∧ x.port=z.port ∧
          (x.level+1=z.level ∨ z.level+1=x.level) := by
        rcases hxz with ⟨ho,h | h⟩
        · exact (hx h.1).elim
        · exact ⟨ho,h⟩
      rcases hyz with ⟨_,h | h⟩ | h
      · exact h.2.2 (hpy.symm.trans hpz)
      · omega
      · exact Y.different h.2.2 (hoy.symm.trans hoz)
    · have ho : x.owner ≠ z.owner := Y.different hxz.2.2
      have hy : y.owner = x.owner := hxy.1.symm
      rcases hyz with hyz | hyz
      · exact ho (hy.symm.trans hyz.1)
      · have hx1 : x.level = 1 := hxz.1
        have hlev : y.level = 1 := hyz.1
        rcases hxy.2 with h | h
        · omega
        · omega
    · have ho : x.owner ≠ y.owner := Y.different hxy.2.2
      have hz : z.owner = x.owner := hxz.1.symm
      rcases hyz with hyz | hyz
      · exact ho (hz.symm.trans hyz.1.symm)
      · have hx1 : x.level = 1 := hxy.1
        have hlev : z.level = 1 := hyz.2.1
        rcases hxz.2 with h | h
        · omega
        · omega
    · have he := Y.unique hxy.2.2 hxz.2.2
      have hyz' : y = z := Vertex.ext (congrArg Prod.fst he) (congrArg Prod.snd he)
        (hxy.2.1.trans hxz.2.1.symm)
      subst z
      exact (graph Y color).loopless.irrefl _ hyz
  · intro hx
    have hj : ∃ j k : Fin 3, j ≠ x.port ∧ k ≠ x.port ∧ j ≠ k := by
      generalize x.port = p
      fin_cases p <;> decide
    obtain ⟨j,k,hj,hk,hjk⟩ := hj
    refine ⟨Vertex.triangle x.owner j,Vertex.triangle x.owner k,?_,?_,?_⟩
    · exact Or.inl ⟨rfl,Or.inl ⟨hx,rfl,hj.symm⟩⟩
    · exact (triangle_adj_triangle Y color _ _ _ _).mpr ⟨rfl,hjk⟩
    · exact Or.inl ⟨rfl,Or.inl ⟨rfl,hx,hk⟩⟩

end VariableWL.SubcubicRealization

namespace VariableWL.SubcubicRealization
attribute [local instance] Classical.propDecidable
variable {V : Type uVariable6} (Y : PortGraph V) (color : V → ℕ)

noncomputable def neighborSlot (x y : Vertex color) : Fin 3 := by
  classical
  exact if x.level = 0 then (if y.level = 0 then y.port else x.port)
    else if y.owner = x.owner then (if y.level < x.level then 0 else 1) else 2

theorem internal_of_nontriangle {x y : Vertex color} (hx : x.level ≠ 0)
    (h : Internal color x y) : x.owner=y.owner ∧ x.port=y.port ∧
      (x.level+1=y.level ∨ y.level+1=x.level) := by
  rcases h with ⟨ho,h | h⟩
  · exact (hx h.1).elim
  · exact ⟨ho,h⟩

theorem neighborSlot_injective (x : Vertex color) :
    Function.Injective (fun y : (graph Y color).neighborSet x => neighborSlot color x y.val) := by
  classical
  rintro ⟨y,hy⟩ ⟨z,hz⟩ he
  apply Subtype.ext
  have hy' : (graph Y color).Adj x y := hy
  have hz' : (graph Y color).Adj x z := hz
  by_cases hx : x.level = 0
  · have hxt : x = Vertex.triangle x.owner x.port := Vertex.ext rfl rfl hx
    rw [hxt,triangle_adj] at hy' hz'
    rcases hy' with ⟨hoy,hly,hpy⟩ | rfl <;> rcases hz' with ⟨hoz,hlz,hpz⟩ | rfl
    · apply Vertex.ext (hoy.trans hoz.symm) _ (hly.trans hlz.symm)
      simpa only [neighborSlot,ite_eq_left hx,ite_eq_left hly,ite_eq_left hlz] using he
    · have he' : y.port = x.port := by simpa [neighborSlot,hx,hly,Vertex.connector] using he
      exact (hpy he').elim
    · have he' : z.port = x.port := by simpa [neighborSlot,hx,hlz,Vertex.connector] using he.symm
      exact (hpz he').elim
    · rfl
  · rcases hy' with hy' | hy' <;> rcases hz' with hz' | hz'
    · obtain ⟨hoy,hpy,hly⟩ := internal_of_nontriangle color hx hy'
      obtain ⟨hoz,hpz,hlz⟩ := internal_of_nontriangle color hx hz'
      apply Vertex.ext (hoy.symm.trans hoz) (hpy.symm.trans hpz)
      simp only [neighborSlot,ite_eq_right hx,ite_eq_left hoy.symm,ite_eq_left hoz.symm] at he
      split_ifs at he <;> try {have := congrArg Fin.val he; norm_num at this}
      all_goals omega
    · obtain ⟨hoy,_,hly⟩ := internal_of_nontriangle color hx hy'
      have hoz := (Y.different hz'.2.2).symm
      simp only [neighborSlot,ite_eq_right hx,ite_eq_left hoy.symm,ite_eq_right hoz] at he
      split_ifs at he <;> cases (by simpa using congrArg Fin.val he : False)
    · obtain ⟨hoz,_,hlz⟩ := internal_of_nontriangle color hx hz'
      have hoy := (Y.different hy'.2.2).symm
      simp only [neighborSlot,ite_eq_right hx,ite_eq_right hoy,ite_eq_left hoz.symm] at he
      split_ifs at he <;> cases (by simpa using congrArg Fin.val he : False)
    · have hpair := Y.unique hy'.2.2 hz'.2.2
      exact Vertex.ext (congrArg Prod.fst hpair) (congrArg Prod.snd hpair)
        (hy'.2.1.trans hz'.2.1.symm)

theorem degree_le_three [Fintype V] (x : Vertex color) : (graph Y color).degree x ≤ 3 := by
  classical
  have hc := Fintype.card_le_of_injective _ (neighborSlot_injective Y color x)
  simpa only [SimpleGraph.card_neighborSet_eq_degree,Fintype.card_fin] using hc

end VariableWL.SubcubicRealization

namespace VariableWL.SubcubicRealization
attribute [local instance] Classical.propDecidable
variable {V : Type uVariable7} (Y : PortGraph V) (color : V → ℕ)

theorem high_adj {x y : Vertex color} (hx : 2 ≤ x.level) :
    (graph Y color).Adj x y ↔ x.owner=y.owner ∧ x.port=y.port ∧
      (x.level+1=y.level ∨ y.level+1=x.level) := by
  constructor
  · rintro (h | h)
    · exact internal_of_nontriangle color (by omega) h
    · have := h.1; omega
  · rintro ⟨ho,hp,hl⟩
    exact Or.inl ⟨ho,Or.inr ⟨hp,hl⟩⟩

theorem high_degree_le_two [Fintype V] (x : Vertex color) (hx : 2 ≤ x.level) :
    (graph Y color).degree x ≤ 2 := by
  classical
  let f : (graph Y color).neighborSet x → Fin 2 :=
    fun y => if y.val.level < x.level then 0 else 1
  have hf : Function.Injective f := by
    rintro ⟨y,hy⟩ ⟨z,hz⟩ he
    obtain ⟨hoy,hpy,hly⟩ := (high_adj Y color hx).mp hy
    obtain ⟨hoz,hpz,hlz⟩ := (high_adj Y color hx).mp hz
    apply Subtype.ext
    apply Vertex.ext (hoy.symm.trans hoz) (hpy.symm.trans hpz)
    dsimp [f] at he
    split_ifs at he <;> try {have := congrArg Fin.val he; norm_num at this}
    all_goals omega
  simpa only [Fintype.card_fin,SimpleGraph.card_neighborSet_eq_degree] using
    Fintype.card_le_of_injective f hf

theorem terminal_degree [Fintype V] (hcolor : ∀ v, 0 < color v) (x : Vertex color)
    (hx : x.level = color x.owner+1) : (graph Y color).degree x = 1 := by
  classical
  have hl : 2 ≤ x.level := by have := hcolor x.owner; omega
  let y : Vertex color := ⟨x.owner,x.port,x.level-1,by have := x.bound; omega⟩
  apply SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr
  refine ⟨y,?_,?_⟩
  · exact (high_adj Y color hl).mpr ⟨rfl,rfl,Or.inr (by dsimp [y]; omega)⟩
  · intro z hz
    obtain ⟨ho,hp,hh⟩ := (high_adj Y color hl).mp hz
    apply Vertex.ext (x := z) (y := y) ho.symm hp.symm
    have hb := z.bound
    rw [← ho] at hb
    dsimp only [y]
    omega

theorem intermediate_degree [Fintype V] (x : Vertex color)
    (hx : 2 ≤ x.level) (hb : x.level < color x.owner+1) : (graph Y color).degree x = 2 := by
  classical
  apply Nat.le_antisymm (high_degree_le_two Y color x hx)
  let lo : Vertex color := ⟨x.owner,x.port,x.level-1,by have := x.bound; omega⟩
  let hi : Vertex color := ⟨x.owner,x.port,x.level+1,by omega⟩
  let f : Fin 2 → (graph Y color).neighborSet x := fun i =>
    if i = 0 then ⟨lo,(high_adj Y color hx).mpr ⟨rfl,rfl,Or.inr (by dsimp [lo]; omega)⟩⟩
    else ⟨hi,(high_adj Y color hx).mpr ⟨rfl,rfl,Or.inl rfl⟩⟩
  have hf : Function.Injective f := by
    intro i j he
    have h := congrArg (fun z => z.val.level) he
    fin_cases i <;> fin_cases j <;> simp [f,lo,hi] at h ⊢
    omega
  simpa only [Fintype.card_fin,SimpleGraph.card_neighborSet_eq_degree] using
    Fintype.card_le_of_injective f hf

theorem connector_used_degree [Fintype V] (hcolor : ∀ v, 0 < color v)
    {v w : V} {j k : Fin 3} (he : Y.edge (v,j) (w,k)) :
    (graph Y color).degree (Vertex.connector v j) = 3 := by
  classical
  apply Nat.le_antisymm (degree_le_three Y color _)
  let first : Vertex color := ⟨v,j,2,by have := hcolor v; omega⟩
  let f : Fin 3 → (graph Y color).neighborSet (Vertex.connector v j) := fun i =>
    if i = 0 then ⟨Vertex.triangle v j,Or.inl ⟨rfl,Or.inr ⟨rfl,Or.inr rfl⟩⟩⟩
    else if i = 1 then ⟨first,Or.inl ⟨rfl,Or.inr ⟨rfl,Or.inl rfl⟩⟩⟩
    else ⟨Vertex.connector w k,Or.inr ⟨rfl,rfl,he⟩⟩
  have hf : Function.LeftInverse (fun z => neighborSlot color (Vertex.connector v j) z.val) f := by
    intro i
    have hw : w ≠ v := (Y.different he).symm
    fin_cases i <;> simp [f,neighborSlot,Vertex.connector,Vertex.triangle,first,hw]
  simpa only [Fintype.card_fin,SimpleGraph.card_neighborSet_eq_degree] using
    Fintype.card_le_of_injective f hf.injective

end VariableWL.SubcubicRealization

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_TypedGame
attribute [-instance] _root_.OAI.VariableWL.Circuit.ProductCellular.powTwoNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9

namespace VariableWL.TypedGame
attribute [local instance] Classical.propDecidable
variable {V : Type uVariable1} {W : Type uVariable2} [Fintype V] [Fintype W]

noncomputable def encode {q : ℕ} (p : Position V W q) :
    Game.Position (numbered (⊥ : SimpleGraph V)) (numbered (⊥ : SimpleGraph W)) q :=
  fun i => (p i).map (fun z => (Fintype.equivFin V z.1,Fintype.equivFin W z.2))

noncomputable def decode {q : ℕ}
    (p : Game.Position (numbered (⊥ : SimpleGraph V)) (numbered (⊥ : SimpleGraph W)) q) :
    Position V W q :=
  fun i => (p i).map (fun z => ((Fintype.equivFin V).symm z.1,(Fintype.equivFin W).symm z.2))

theorem encode_decode {q : ℕ}
    (p : Game.Position (numbered (⊥ : SimpleGraph V)) (numbered (⊥ : SimpleGraph W)) q) :
    encode (decode p) = p := by
  funext i
  cases h : p i <;> simp [encode,decode,h]

def Winning (G : SimpleGraph V) (H : SimpleGraph W) {q : ℕ} (p : Position V W q) : Prop :=
  Game.Winning (G := numbered G) (H := numbered H) (encode p)

theorem Winning.partialIso {G : SimpleGraph V} {H : SimpleGraph W} {q : ℕ}
    {p : Position V W q} (hp : Winning G H p) {i j : Fin q} {a c : V} {b d : W}
    (hi : p i = some (a,b)) (hj : p j = some (c,d)) :
    (a=c ↔ b=d) ∧ (G.Adj a c ↔ H.Adj b d) := by
  have hh := Game.Winning.partialIso hp i j (Fintype.equivFin V a,Fintype.equivFin W b)
    (Fintype.equivFin V c,Fintype.equivFin W d) (by simp [encode,hi]) (by simp [encode,hj])
  simpa only [(Fintype.equivFin V).injective.eq_iff,(Fintype.equivFin W).injective.eq_iff,
    SimpleGraph.comap_adj,Equiv.symm_apply_apply] using hh

theorem Winning.discard {G : SimpleGraph V} {H : SimpleGraph W} {q : ℕ}
    {p p' : Position V W q} (hp : Winning G H p)
    (hs : ∀ i a, p' i = some a → p i = some a) : Winning G H p' := by
  apply Game.Winning.discard hp
  intro i a ha
  obtain ⟨b,hb,rfl⟩ := Option.map_eq_some_iff.mp ha
  simp [encode,hs i b hb]

theorem encode_update {q : ℕ} (p : Position V W q) (i : Fin q) (a : V) (b : W) :
    encode (Function.update p i (some (a,b))) =
      Function.update (encode p) i (some (Fintype.equivFin V a,Fintype.equivFin W b)) := by
  classical
  funext j
  by_cases hij : j=i <;> simp [encode,hij]

theorem Winning.move {G : SimpleGraph V} {H : SimpleGraph W} {q : ℕ}
    {p : Position V W q} (hp : Winning G H p) (i : Fin q) (hi : p i = none) :
    ∃ e : V ≃ W, ∀ v, Winning G H (Function.update p i (some (v,e v))) := by
  obtain ⟨e,he⟩ := Game.Winning.move hp i (by simp [encode,hi])
  let f := (Fintype.equivFin V).trans (e.trans (Fintype.equivFin W).symm)
  refine ⟨f,fun v => ?_⟩
  change Game.Winning _
  rw [encode_update]
  simpa only [f,Equiv.trans_apply,Equiv.apply_symm_apply] using he (Fintype.equivFin V v)

theorem Winning.degree_eq {G : SimpleGraph V} {H : SimpleGraph W} {q : ℕ}
    (hq : 2 ≤ q) {p : Position V W q} (hp : Winning G H p) {i : Fin q} {a : V} {b : W}
    (hi : p i = some (a,b)) : G.degree a = H.degree b := by
  have hh := Game.Winning.degree_eq hq hp (i := i) (a := Fintype.equivFin V a) (b := Fintype.equivFin W b) (by simp only [encode,hi,Option.map_some])
  exact ((numbering G).degree_eq a).symm.trans (hh.trans ((numbering H).degree_eq b))

theorem Winning.keep {G : SimpleGraph V} {H : SimpleGraph W} {q : ℕ}
    {p : Position V W q} (hp : Winning G H p) (s : Finset (Fin q)) : Winning G H (keep p s) := by
  apply hp.discard
  intro i a ha
  by_cases hi : i ∈ s
  · simpa [TypedGame.keep,hi] using ha
  · simp [TypedGame.keep,hi] at ha

end VariableWL.TypedGame

namespace VariableWL.Game

def swap {G H : Graph} {q : ℕ} (p : Position G H q) : Position H G q :=
  fun i => (p i).map Prod.swap

theorem swap_swap {G H : Graph} {q : ℕ} (p : Position G H q) : swap (swap p) = p := by
  funext i
  cases h : p i <;> simp [swap,h]

theorem swap_update {G H : Graph} {q : ℕ} (p : Position G H q)
    (i : Fin q) (a : Fin G.order) (b : Fin H.order) :
    swap (Function.update p i (some (a,b))) = Function.update (swap p) i (some (b,a)) := by
  classical
  funext j
  by_cases h : j=i <;> simp [swap,h]

theorem Winning.symm {G H : Graph} {q : ℕ} {p : Position G H q} (hp : Winning p) : Winning (swap p) := by
  classical
  refine ⟨{s | Winning (swap s)},?_,?_,?_,?_⟩
  · simpa only [Set.mem_ofPred_eq,swap_swap] using hp
  · intro s hs i j a b hi hj
    have ha : swap s i = some (a.2,a.1) := by simp [swap,hi,Prod.swap]
    have hb : swap s j = some (b.2,b.1) := by simp [swap,hj,Prod.swap]
    have h := hs.partialIso i j _ _ ha hb
    exact ⟨h.1.symm,h.2.symm⟩
  · intro s hs s' hsub
    apply hs.discard
    intro i a ha
    obtain ⟨b,hb,he⟩ := Option.map_eq_some_iff.mp ha
    simp only [swap,hsub i b hb,Option.map_some,he]
  · intro s hs i hi
    obtain ⟨e,he⟩ := hs.move i (by simp [swap,hi])
    refine ⟨e.symm,fun v => ?_⟩
    change Winning (swap (Function.update s i (some (v,e.symm v))))
    rw [swap_update]
    simpa only [Equiv.apply_symm_apply] using he (e.symm v)
end VariableWL.Game

namespace VariableWL.TypedGame
attribute [local instance] Classical.propDecidable
variable {V : Type uVariable5} {W : Type uVariable6} [Fintype V] [Fintype W]

theorem Winning.symm {G : SimpleGraph V} {H : SimpleGraph W} {q : ℕ}
    {p : Position V W q} (hp : Winning G H p) : Winning H G (swap p) := by
  have he : encode (swap p) = Game.swap (encode p) := by
    funext i
    cases h : p i <;> simp [encode,swap,Game.swap,h]
  change Game.Winning _
  rw [he]
  exact Game.Winning.symm hp

theorem Winning.triangle_forward {G : SimpleGraph V} {H : SimpleGraph W} {q : ℕ}
    (hq : 3 ≤ q) {p : Position V W q} (hp : Winning G H p)
    {i : Fin q} {v : V} {w : W} (hi : p i = some (v,w)) (hv : Triangle G v) : Triangle H w := by
  classical
  obtain ⟨a,b,hva,hab,hbv⟩ := hv
  obtain ⟨j,hji,_⟩ := spare hq i i
  obtain ⟨l,hli,hlj⟩ := spare hq i j
  let p0 := TypedGame.keep p {i}
  have h0 := hp.keep {i}
  obtain ⟨e,he⟩ := h0.move j (by simp [TypedGame.keep,hji])
  let p1 := Function.update p0 j (some (a,e a))
  have h1 : Winning G H p1 := he a
  have hi1 : p1 i = some (v,w) := by simp [p1,p0,TypedGame.keep,Function.update_of_ne hji.symm,hi]
  have hj1 : p1 j = some (a,e a) := by simp [p1]
  obtain ⟨f,hf⟩ := h1.move l (by simp [p1,p0,TypedGame.keep,hlj,hli])
  let p2 := Function.update p1 l (some (b,f b))
  have h2 : Winning G H p2 := hf b
  have hi2 : p2 i = some (v,w) := by simp [p2,Function.update_of_ne hli.symm,hi1]
  have hj2 : p2 j = some (a,e a) := by simp [p2,Function.update_of_ne hlj.symm,hj1]
  have hl2 : p2 l = some (b,f b) := by simp [p2]
  exact ⟨e a,f b,(h2.partialIso hi2 hj2).2.mp hva,
    (h2.partialIso hj2 hl2).2.mp hab,(h2.partialIso hl2 hi2).2.mp hbv⟩

theorem Winning.triangle_iff {G : SimpleGraph V} {H : SimpleGraph W} {q : ℕ}
    (hq : 3 ≤ q) {p : Position V W q} (hp : Winning G H p)
    {i : Fin q} {v : V} {w : W} (hi : p i = some (v,w)) : Triangle G v ↔ Triangle H w := by
  refine ⟨hp.triangle_forward hq hi,?_⟩
  exact hp.symm.triangle_forward hq (i := i) (by simp [TypedGame.swap,hi])

theorem Winning.tail_forward {G : SimpleGraph V} {H : SimpleGraph W} {q : ℕ}
    (hq : 3 ≤ q) (n : ℕ) {p : Position V W q} (hp : Winning G H p)
    {i j : Fin q} {a b : V} {c d : W} (hi : p i = some (a,c)) (hj : p j = some (b,d)) :
    Tail G n a b → Tail H n c d := by
  classical
  induction n generalizing p i j a b c d with
  | zero => intro hh; change H.degree d = 1; exact (hp.degree_eq (by omega) hj).symm.trans hh
  | succ n ih =>
    rintro ⟨hd,v,hva,hbv,hv⟩
    refine ⟨(hp.degree_eq (by omega) hj).symm.trans hd,?_⟩
    obtain ⟨l,hli,hlj⟩ := spare hq i j
    let p0 := TypedGame.keep p {i,j}
    have h0 := hp.keep {i,j}
    obtain ⟨e,he⟩ := h0.move l (by simp [TypedGame.keep,hli,hlj])
    let p1 := Function.update p0 l (some (v,e v))
    have h1 : Winning G H p1 := he v
    have hi1 : p1 i = some (a,c) := by simp [p1,p0,TypedGame.keep,Function.update_of_ne hli.symm,hi]
    have hj1 : p1 j = some (b,d) := by simp [p1,p0,TypedGame.keep,Function.update_of_ne hlj.symm,hj]
    have hl1 : p1 l = some (v,e v) := by simp [p1]
    exact ⟨e v,fun h => hva ((h1.partialIso hl1 hi1).1.mpr h),
      (h1.partialIso hj1 hl1).2.mp hbv,ih h1 hj1 hl1 hv⟩

end VariableWL.TypedGame

namespace VariableWL.TypedGame
attribute [local instance] Classical.propDecidable
variable {V : Type uVariable7} {W : Type uVariable8} [Fintype V] [Fintype W]

theorem Winning.colorTag_forward {G : SimpleGraph V} {H : SimpleGraph W} {q : ℕ}
    (hq : 3 ≤ q) {p : Position V W q} (hp : Winning G H p) {t : ℕ}
    {i : Fin q} {v : V} {w : W} (hi : p i = some (v,w)) : ColorTag G t v → ColorTag H t w := by
  classical
  rintro ⟨ht,htv,c,hvc,hct,y,hcy,hyv,hdy,htail⟩
  refine ⟨ht,(hp.triangle_iff hq hi).mp htv,?_⟩
  obtain ⟨j,hji,_⟩ := spare hq i i
  obtain ⟨l,hli,hlj⟩ := spare hq i j
  let p0 := TypedGame.keep p {i}
  have h0 := hp.keep {i}
  obtain ⟨e,he⟩ := h0.move j (by simp [TypedGame.keep,hji])
  let p1 := Function.update p0 j (some (c,e c))
  have h1 : Winning G H p1 := he c
  have hi1 : p1 i = some (v,w) := by simp [p1,p0,TypedGame.keep,Function.update_of_ne hji.symm,hi]
  have hj1 : p1 j = some (c,e c) := by simp [p1]
  refine ⟨e c,(h1.partialIso hi1 hj1).2.mp hvc,fun h => hct ((h1.triangle_iff hq hj1).mpr h),?_⟩
  obtain ⟨f,hf⟩ := h1.move l (by simp [p1,p0,TypedGame.keep,hlj,hli])
  let p2 := Function.update p1 l (some (y,f y))
  have h2 : Winning G H p2 := hf y
  have hi2 : p2 i = some (v,w) := by simp [p2,Function.update_of_ne hli.symm,hi1]
  have hj2 : p2 j = some (c,e c) := by simp [p2,Function.update_of_ne hlj.symm,hj1]
  have hl2 : p2 l = some (y,f y) := by simp [p2]
  refine ⟨f y,(h2.partialIso hj2 hl2).2.mp hcy,fun h => hyv ((h2.partialIso hl2 hi2).1.mpr h),?_,?_⟩
  · rw [← h2.degree_eq (by omega) hl2]; exact hdy
  · exact h2.tail_forward hq (t-1) hj2 hl2 htail

end VariableWL.TypedGame

namespace VariableWL.SubcubicRealization
attribute [local instance] Classical.propDecidable
variable {V : Type uVariable9} [Fintype V] (Y : PortGraph V) (color : V → ℕ)
variable (hcolor : ∀ v, 0 < color v)
include hcolor

theorem high_degree_one_iff (x : Vertex color) (hx : 2 ≤ x.level) :
    (graph Y color).degree x = 1 ↔ x.level = color x.owner+1 := by
  constructor
  · intro hd
    by_contra he
    have hb : x.level < color x.owner+1 := by have := x.bound; omega
    have ht := intermediate_degree Y color x hx hb
    omega
  · exact terminal_degree Y color hcolor x

theorem tail_iff (m : ℕ) (prev x : Vertex color) (hx : 2 ≤ x.level)
    (ho : prev.owner=x.owner) (hp : prev.port=x.port) (hl : prev.level+1=x.level) :
    TypedGame.Tail (graph Y color) m prev x ↔ m+x.level=color x.owner+1 := by
  induction m generalizing prev x with
  | zero => simpa only [TypedGame.Tail,zero_add] using high_degree_one_iff Y color hcolor x hx
  | succ m ih =>
    constructor
    · rintro ⟨_,y,hyp,ha,ht⟩
      obtain ⟨hoy,hpy,hly⟩ := (high_adj Y color hx).mp ha
      have hyup : x.level+1=y.level := by
        rcases hly with h | h
        · exact h
        · exfalso
          apply hyp
          exact Vertex.ext (hoy.symm.trans ho.symm) (hpy.symm.trans hp.symm) (by omega)
      have hh := (ih x y (by omega) hoy hpy hyup).mp ht
      rw [← hoy] at hh
      omega
    · intro hh
      have hxb : x.level < color x.owner+1 := by omega
      let y : Vertex color := ⟨x.owner,x.port,x.level+1,by omega⟩
      refine ⟨intermediate_degree Y color x hx hxb,y,?_,?_,?_⟩
      · intro he
        have := congrArg Vertex.level he
        dsimp [y] at this
        omega
      · exact (high_adj Y color hx).mpr ⟨rfl,rfl,Or.inl rfl⟩
      · apply (ih x y (by dsimp [y]; omega) rfl rfl rfl).mpr
        dsimp [y]
        omega

omit hcolor [Fintype V] in
theorem connector_adj (v : V) (j : Fin 3) (y : Vertex color) :
    (graph Y color).Adj (Vertex.connector v j) y ↔
    y = Vertex.triangle v j ∨
      (y.owner=v ∧ y.port=j ∧ y.level=2) ∨
      (y.level=1 ∧ Y.edge (v,j) (y.owner,y.port)) := by
  constructor
  · rintro (h | h)
    · obtain ⟨ho,hp,hl⟩ := internal_of_nontriangle color (by simp [Vertex.connector]) h
      rcases hl with hl | hl
      · exact Or.inr (Or.inl ⟨ho.symm,hp.symm,hl.symm⟩)
      · exact Or.inl (Vertex.ext ho.symm hp.symm (by change y.level+1=1 at hl; dsimp [Vertex.triangle]; omega))
    · exact Or.inr (Or.inr ⟨h.2.1,h.2.2⟩)
  · rintro (rfl | ⟨ho,hp,hl⟩ | ⟨hl,he⟩)
    · exact Or.inl ⟨rfl,Or.inr ⟨rfl,Or.inr rfl⟩⟩
    · exact Or.inl ⟨ho.symm,Or.inr ⟨hp.symm,Or.inl hl.symm⟩⟩
    · exact Or.inr ⟨rfl,hl,he⟩

theorem first_path_recognized {v : V} {j : Fin 3} {y : Vertex color}
    (ha : (graph Y color).Adj (Vertex.connector v j) y)
    (hne : y ≠ Vertex.triangle v j) (hd : (graph Y color).degree y ≤ 2) :
    y.owner=v ∧ y.port=j ∧ y.level=2 := by
  rcases (connector_adj Y color v j y).mp ha with h | h | ⟨hl,he⟩
  · exact (hne h).elim
  · exact h
  · have hy : y = Vertex.connector y.owner y.port := Vertex.ext rfl rfl hl
    have hdeg := connector_used_degree Y color hcolor (Y.symm he)
    rw [hy] at hd
    omega

theorem colorTag_iff (t : ℕ) (x : Vertex color) :
    TypedGame.ColorTag (graph Y color) t x ↔ x.level=0 ∧ t=color x.owner := by
  constructor
  · rintro ⟨ht,htri,c,hxc,hct,y,hcy,hyx,hdy,htail⟩
    have hx := (triangle_characterization Y color x).mp htri
    have hxe : x = Vertex.triangle x.owner x.port := Vertex.ext rfl rfl hx
    have hc : c = Vertex.connector x.owner x.port := by
      rw [hxe] at hxc
      rcases (triangle_adj Y color _ _).mp hxc with ⟨_,hc0,_⟩ | hc
      · exact (hct ((triangle_characterization Y color _).mpr hc0)).elim
      · exact hc
    subst c
    have hy := first_path_recognized Y color hcolor hcy (by simpa only [← hxe] using hyx) hdy
    have hlen := (tail_iff Y color hcolor (t-1) (Vertex.connector x.owner x.port) y (by omega)
      hy.1.symm hy.2.1.symm (by dsimp [Vertex.connector]; omega)).mp htail
    rw [hy.1] at hlen
    exact ⟨hx,by omega⟩
  · rintro ⟨hx,rfl⟩
    let y : Vertex color := ⟨x.owner,x.port,2,by have := hcolor x.owner; omega⟩
    refine ⟨hcolor x.owner,(triangle_characterization Y color x).mpr hx,
      Vertex.connector x.owner x.port,?_,?_,y,?_,?_,high_degree_le_two Y color y (by rfl),?_⟩
    · exact Or.inl ⟨rfl,Or.inr ⟨rfl,Or.inl (by dsimp [Vertex.connector]; omega)⟩⟩
    · change ¬ (∃ a b, (graph Y color).Adj (Vertex.connector x.owner x.port) a ∧
          (graph Y color).Adj a b ∧ (graph Y color).Adj b (Vertex.connector x.owner x.port))
      rw [triangle_characterization]
      simp [Vertex.connector]
    · exact Or.inl ⟨rfl,Or.inr ⟨rfl,Or.inl rfl⟩⟩
    · intro he
      have := congrArg Vertex.level he
      dsimp [y] at this
      omega
    · apply (tail_iff Y color hcolor _ (Vertex.connector x.owner x.port) y (by rfl) rfl rfl rfl).mpr
      dsimp [y]
      have := hcolor x.owner
      omega

end VariableWL.SubcubicRealization

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_PortGame
attribute [-instance] _root_.OAI.VariableWL.Circuit.ProductCellular.powTwoNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7

namespace VariableWL.TypedGame
attribute [local instance] Classical.propDecidable
variable {V : Type uVariable1} {W : Type uVariable2} [Fintype V] [Fintype W]

def Preserved (G : SimpleGraph V) (H : SimpleGraph W) (q : ℕ)
    (R : V → V → Prop) (S : W → W → Prop) : Prop :=
  ∀ (p : Position V W q), Winning G H p → ∀ {i j a b c d},
    p i = some (a,c) → p j = some (b,d) → R a b → S c d

theorem Preserved.compose {G : SimpleGraph V} {H : SimpleGraph W} {q : ℕ} (hq : 3 ≤ q)
    {R R' : V → V → Prop} {S S' : W → W → Prop}
    (hR : Preserved G H q R S) (hT : Preserved G H q R' S') :
    Preserved G H q (Compose R R') (Compose S S') := by
  classical
  intro p hp i j a b c d hi hj hm
  obtain ⟨m,ham,hmb⟩ := hm
  obtain ⟨l,hli,hlj⟩ := spare hq i j
  let p0 := TypedGame.keep p {i,j}
  have h0 := hp.keep {i,j}
  obtain ⟨e,he⟩ := h0.move l (by simp [TypedGame.keep,hli,hlj])
  let p1 := Function.update p0 l (some (m,e m))
  have h1 : Winning G H p1 := he m
  have hi1 : p1 i = some (a,c) := by simp [p1,p0,TypedGame.keep,Function.update_of_ne hli.symm,hi]
  have hj1 : p1 j = some (b,d) := by simp [p1,p0,TypedGame.keep,Function.update_of_ne hlj.symm,hj]
  have hl1 : p1 l = some (m,e m) := by simp [p1]
  exact ⟨e m,hR p1 h1 hi1 hl1 ham,hT p1 h1 hl1 hj1 hmb⟩

theorem Preserved.flip {G : SimpleGraph V} {H : SimpleGraph W} {q : ℕ}
    {R : V → V → Prop} {S : W → W → Prop} (h : Preserved G H q R S) :
    Preserved G H q (fun a b => R b a) (fun a b => S b a) := by
  intro p hp i j a b c d hi hj hr
  exact h p hp hj hi hr

theorem adjacency_preserved (G : SimpleGraph V) (H : SimpleGraph W) (q : ℕ) :
    Preserved G H q G.Adj H.Adj := by
  intro p hp i j a b c d hi hj ha
  exact (hp.partialIso hi hj).2.mp ha

theorem sameTriangle_preserved {G : SimpleGraph V} {H : SimpleGraph W} {q : ℕ} (hq : 3 ≤ q) :
    Preserved G H q (SameTriangle G) (SameTriangle H) := by
  intro p hp i j a b c d hi hj h
  refine ⟨(hp.triangle_iff hq hi).mp h.1,(hp.triangle_iff hq hj).mp h.2.1,?_⟩
  rcases h.2.2 with he | ha
  · exact Or.inl ((hp.partialIso hi hj).1.mp he)
  · exact Or.inr ((hp.partialIso hi hj).2.mp ha)

theorem exit_preserved {G : SimpleGraph V} {H : SimpleGraph W} {q : ℕ} (hq : 3 ≤ q) :
    Preserved G H q (Exit G) (Exit H) := by
  intro p hp i j a b c d hi hj h
  exact ⟨(hp.triangle_iff hq hi).mp h.1,fun hh => h.2.1 ((hp.triangle_iff hq hj).mpr hh),
    (hp.partialIso hi hj).2.mp h.2.2⟩

theorem access_preserved {G : SimpleGraph V} {H : SimpleGraph W} {q : ℕ} (hq : 3 ≤ q) :
    Preserved G H q (Access G) (Access H) :=
  (sameTriangle_preserved hq).compose hq (exit_preserved hq)

theorem underlyingEdge_preserved {G : SimpleGraph V} {H : SimpleGraph W} {q : ℕ} (hq : 3 ≤ q) :
    Preserved G H q (UnderlyingEdge G) (UnderlyingEdge H) :=
  (access_preserved hq).compose hq ((adjacency_preserved G H q).compose hq (access_preserved hq).flip)

end VariableWL.TypedGame

namespace VariableWL.SubcubicRealization
attribute [local instance] Classical.propDecidable
variable {V : Type uVariable4} [Fintype V] (Y : PortGraph V) (color : V → ℕ)

omit [Fintype V] in
theorem sameTriangle_iff (x y : Vertex color) :
    TypedGame.SameTriangle (graph Y color) x y ↔ x.level=0 ∧ y.level=0 ∧ x.owner=y.owner := by
  constructor
  · rintro ⟨hx,hy,h⟩
    have hx0 := (triangle_characterization Y color x).mp hx
    have hy0 := (triangle_characterization Y color y).mp hy
    refine ⟨hx0,hy0,?_⟩
    rcases h with rfl | h
    · rfl
    · rcases h with h | h
      · exact h.1
      · have := h.1; omega
  · rintro ⟨hx,hy,ho⟩
    refine ⟨(triangle_characterization Y color x).mpr hx,(triangle_characterization Y color y).mpr hy,?_⟩
    by_cases hp : x.port=y.port
    · exact Or.inl (Vertex.ext ho hp (hx.trans hy.symm))
    · exact Or.inr (Or.inl ⟨ho,Or.inl ⟨hx,hy,hp⟩⟩)

omit [Fintype V] in
theorem exit_iff (x y : Vertex color) :
    TypedGame.Exit (graph Y color) x y ↔ x.level=0 ∧ y = Vertex.connector x.owner x.port := by
  constructor
  · rintro ⟨hx,hy,ha⟩
    have hx0 := (triangle_characterization Y color x).mp hx
    have hxe : x = Vertex.triangle x.owner x.port := Vertex.ext rfl rfl hx0
    rw [hxe] at ha
    refine ⟨hx0,?_⟩
    rcases (triangle_adj Y color _ _).mp ha with h | h
    · exact (hy ((triangle_characterization Y color y).mpr h.2.1)).elim
    · exact h
  · rintro ⟨hx,rfl⟩
    refine ⟨(triangle_characterization Y color x).mpr hx,?_,?_⟩
    · intro h
      have := (triangle_characterization Y color _).mp h
      change 1=0 at this
      omega
    · exact Or.inl ⟨rfl,Or.inr ⟨rfl,Or.inl (by dsimp [Vertex.connector]; omega)⟩⟩

omit [Fintype V] in
theorem access_iff (x y : Vertex color) :
    TypedGame.Access (graph Y color) x y ↔ x.level=0 ∧ y.level=1 ∧ x.owner=y.owner := by
  constructor
  · rintro ⟨t,hxt,hty⟩
    obtain ⟨hx,_,ho⟩ := (sameTriangle_iff Y color x t).mp hxt
    obtain ⟨_,hy⟩ := (exit_iff Y color t y).mp hty
    exact ⟨hx,by rw [hy]; rfl,by rw [hy]; exact ho⟩
  · rintro ⟨hx,hy,ho⟩
    refine ⟨Vertex.triangle x.owner y.port,(sameTriangle_iff Y color _ _).mpr ⟨hx,rfl,rfl⟩,?_⟩
    exact (exit_iff Y color _ _).mpr ⟨rfl,Vertex.ext ho.symm rfl hy⟩

omit [Fintype V] in
theorem underlyingEdge_iff (x y : Vertex color) :
    TypedGame.UnderlyingEdge (graph Y color) x y ↔
      x.level=0 ∧ y.level=0 ∧ Y.graph.Adj x.owner y.owner := by
  constructor
  · rintro ⟨c,hxc,d,hcd,hyd⟩
    obtain ⟨hx,hc,hoc⟩ := (access_iff Y color x c).mp hxc
    obtain ⟨hy,hd,hod⟩ := (access_iff Y color y d).mp hyd
    refine ⟨hx,hy,?_⟩
    rcases hcd with h | h
    · rcases h.2 with h | h
      · omega
      · omega
    · exact ⟨c.port,d.port,by rw [hoc,hod]; exact h.2.2⟩
  · rintro ⟨hx,hy,j,k,he⟩
    exact ⟨Vertex.connector x.owner j,(access_iff Y color _ _).mpr ⟨hx,rfl,rfl⟩,
      Vertex.connector y.owner k,Or.inr ⟨rfl,rfl,he⟩,(access_iff Y color _ _).mpr ⟨hy,rfl,rfl⟩⟩

end VariableWL.SubcubicRealization

namespace VariableWL.SubcubicRealization
attribute [local instance] Classical.propDecidable
variable {V : Type uVariable5} {W : Type uVariable6} [Fintype V] [Fintype W]
variable (Y : PortGraph V) (Z : PortGraph W) (color : V → ℕ) (color' : W → ℕ)

theorem winning_color {q : ℕ} (hq : 3 ≤ q)
    (hc : ∀ v, 0 < color v) (hc' : ∀ w, 0 < color' w)
    {p : TypedGame.Position (Vertex color) (Vertex color') q}
    (hp : TypedGame.Winning (graph Y color) (graph Z color') p)
    {i : Fin q} {x : Vertex color} {y : Vertex color'}
    (hi : p i = some (x,y)) (hx : x.level=0) :
    y.level=0 ∧ color x.owner=color' y.owner := by
  have ht := (colorTag_iff Y color hc (color x.owner) x).mpr ⟨hx,rfl⟩
  exact (colorTag_iff Z color' hc' _ y).mp (hp.colorTag_forward hq hi ht)

theorem winning_sortWalk {q : ℕ} (hq : 3 ≤ q)
    (hc : ∀ v, 0 < color v) (hc' : ∀ w, 0 < color' w)
    (ts : List ℕ) :
    TypedGame.Preserved (graph Y color) (graph Z color') q
      (fun x y => x.level=0 ∧ y.level=0 ∧ SortWalk Y.graph color ts x.owner y.owner)
      (fun x y => x.level=0 ∧ y.level=0 ∧ SortWalk Z.graph color' ts x.owner y.owner) := by
  induction ts using List.twoStepInduction with
  | nil => intro p hp i j x y x' y' hi hj h; exact h.2.2.elim
  | singleton t =>
    intro p hp i j x y x' y' hi hj h
    obtain ⟨hx',hcx⟩ := winning_color Y Z color color' hq hc hc' hp hi h.1
    obtain ⟨hy',_⟩ := winning_color Y Z color color' hq hc hc' hp hj h.2.1
    have hs := TypedGame.sameTriangle_preserved (G := graph Y color) (H := graph Z color') hq p hp hi hj
      ((sameTriangle_iff Y color x y).mpr ⟨h.1,h.2.1,h.2.2.1⟩)
    have ho := (sameTriangle_iff Z color' x' y').mp hs
    exact ⟨hx',hy',ho.2.2,hcx.symm.trans h.2.2.2⟩
  | cons_cons t u ts _ ih =>
    intro p hp i j x y x' y' hi hj h
    obtain ⟨hx',hcx⟩ := winning_color Y Z color color' hq hc hc' hp hi h.1
    obtain ⟨hy',_⟩ := winning_color Y Z color color' hq hc hc' hp hj h.2.1
    obtain ⟨hct,z,hxz,hzy⟩ := h.2.2
    let z0 : Vertex color := Vertex.triangle z 0
    have hm : TypedGame.Compose (TypedGame.UnderlyingEdge (graph Y color))
        (fun a b => a.level=0 ∧ b.level=0 ∧ SortWalk Y.graph color (u::ts) a.owner b.owner) x y :=
      ⟨z0,(underlyingEdge_iff Y color x z0).mpr ⟨h.1,rfl,hxz⟩,rfl,h.2.1,hzy⟩
    have hz := (TypedGame.underlyingEdge_preserved (G := graph Y color) (H := graph Z color') hq).compose
      hq (ih u) p hp hi hj hm
    obtain ⟨z',hxz',hz'⟩ := hz
    have ha := (underlyingEdge_iff Z color' x' z').mp hxz'
    exact ⟨hx',hy',hcx.symm.trans hct,z'.owner,ha.2.2,hz'.2.2⟩

end VariableWL.SubcubicRealization

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_PrefixParts
attribute [-instance] _root_.OAI.VariableWL.AffineAlphabet.linearFintype _root_.OAI.VariableWL.Circuit.ProductCellular.powTwoNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.PrefixParts
open VariableWL.Affine
open scoped CharTwo
attribute [local instance] Classical.propDecidable

namespace Data

variable (D : Data)

variable {D}

variable (D)

theorem treeTranslation_step (ξ : D.Valuation 1) (t u : D.Tree 0) :
    TreeStep (D.treeTranslation ξ t) (D.treeTranslation ξ u) ↔ TreeStep t u := by
  change (t.channel=u.channel ∧ t.height+1=u.height ∧
    truncate t.height (u.bits+truncate u.height (ξ.val ∘ D.order u.channel))=
      t.bits+truncate t.height (ξ.val ∘ D.order t.channel)) ↔ _
  constructor
  · rintro ⟨hc,hh,hb⟩
    refine ⟨hc,hh,?_⟩
    rw [truncate_add,truncate_truncate (by omega),← hc] at hb
    exact add_right_cancel hb
  · rintro ⟨hc,hh,hb⟩
    refine ⟨hc,hh,?_⟩
    rw [truncate_add,truncate_truncate (by omega),← hc,hb]

theorem vertexTranslation_forward (ξ : D.Valuation 1) (x y : D.Vertex 0) :
    Forward (D.vertexTranslation ξ x) (D.vertexTranslation ξ y) ↔ Forward x y := by
  cases x with
  | inl x => cases y with
    | inl y => rfl
    | inr y => cases y <;> rfl
  | inr x =>
    cases x with
    | inl x =>
      cases y with
      | inl y => rfl
      | inr y => cases y with
        | inl y => exact and_congr Iff.rfl (D.translate ξ).injective.eq_iff
        | inr y => rfl
    | inr x =>
      cases y with
      | inl y => rfl
      | inr y => cases y with
        | inr y => exact D.treeTranslation_step ξ x y
        | inl y =>
          rcases y with ⟨c,z⟩
          change (x.channel=c ∧ x.height=D.dimension ∧
            x.bits+truncate x.height (ξ.val ∘ D.order x.channel)=
              (z.val+ξ.val) ∘ D.order c) ↔ _
          constructor
          · rintro ⟨hc,hh,hb⟩
            refine ⟨hc,hh,?_⟩
            rw [hc,hh,truncate_full] at hb
            exact add_right_cancel (show x.bits+ξ.val ∘ D.order c=(z.val ∘ D.order c)+ξ.val ∘ D.order c from hb)
          · rintro ⟨hc,hh,hb⟩
            refine ⟨hc,hh,?_⟩
            rw [hc,hh,truncate_full,hb]
            rfl

noncomputable def translationIso (ξ : D.Valuation 1) : D.graph 0 ≃g D.graph 1 where
  toEquiv := D.vertexTranslation ξ
  map_rel_iff' := by intro x y; exact or_congr (D.vertexTranslation_forward ξ x y) (D.vertexTranslation_forward ξ y x)

end Data
end VariableWL.PrefixParts

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_PrefixWiring
attribute [-instance] _root_.OAI.VariableWL.AffineAlphabet.linearFintype _root_.OAI.VariableWL.BlockCoordinates.defaultProperNumberings _root_.OAI.VariableWL.Circuit.ProductCellular.powTwoNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9

namespace VariableWL.PrefixParts.Wiring
open VariableWL.Affine VariableWL.SubcubicRealization
attribute [local instance] Classical.propDecidable
variable {B : Type uVariable6} [Fintype B] (D : B → Data) (W : Wiring D)

variable [FiniteNumbering B] [FiniteNumbering (SortTag D)]

omit [FiniteNumbering B] in
theorem color_pos {ε : Bit} (x : Vertex D ε) : 0 < color D x := Nat.zero_lt_succ _

end VariableWL.PrefixParts.Wiring

namespace VariableWL.PrefixParts.Wiring
open VariableWL.Affine VariableWL.SubcubicRealization
attribute [local instance] Classical.propDecidable
variable {B : Type uVariable7} [Fintype B] [FiniteNumbering B] (D : B → Data) [FiniteNumbering (SortTag D)] (W : Wiring D)

def CompatiblePair (ξ : ∀ b, (D b).Valuation 1) (b c : B) : Prop :=
  ∀ d : Channel D, d.1=b → (W.mate d).1=c → rootShift D ξ d=rootShift D ξ (W.mate d)

end VariableWL.PrefixParts.Wiring

namespace VariableWL.PrefixParts.Wiring
open VariableWL.Affine VariableWL.SubcubicRealization
attribute [local instance] Classical.propDecidable
variable {B : Type uVariable8} [Fintype B] [FiniteNumbering B] (D : B → Data) [FiniteNumbering (SortTag D)] (W : Wiring D)

noncomputable def partHom (ε : Bit) (b : B) : (D b).graph ε →g (W.ports D ε).graph where
  toFun x := ⟨b,x⟩
  map_rel' {x y} h := ⟨Data.slot x y,Data.slot y x,Or.inl ⟨rfl,h,rfl,rfl⟩⟩

noncomputable def uncoloredTranslation (ξ : ∀ b, (D b).Valuation 1) :
    UncoloredVertex D 0 ≃ UncoloredVertex D 1 :=
  SubcubicRealization.vertexEquiv (vertexTranslation D ξ) (localPorts D ξ) (color_translation D ξ)

end VariableWL.PrefixParts.Wiring

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_PrefixGame
attribute [-instance] _root_.OAI.VariableWL.AffineAlphabet.linearFintype _root_.OAI.VariableWL.BlockCoordinates.defaultProperNumberings _root_.OAI.VariableWL.Circuit.ProductCellular.powTwoNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4

namespace VariableWL.PrefixParts.Data
open VariableWL.Affine
attribute [local instance] Classical.propDecidable
variable {D : Data} {ε : Bit}

def Live (c : Fin D.channels) : D.Vertex ε → Prop
  | .inl _ => False
  | .inr (.inl _) => True
  | .inr (.inr t) => t.channel=c

def observation (c : Fin D.channels) : D.Vertex ε → Vec D.dimension
  | .inl _ => 0
  | .inr (.inl (_,z)) => truncate (D.root c) (z.val ∘ D.order c)
  | .inr (.inr t) => truncate (D.root c) t.bits

theorem live_of_sort {δ : Bit} (c : Fin D.channels) {x : D.Vertex ε} {y : D.Vertex δ}
    (h : sort x=sort y) (hx : Live c x) : Live c y := by
  rcases x with x | (⟨d,z⟩ | t) <;> rcases y with y | (⟨e,w⟩ | u)
  all_goals simp only [sort,Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl] at h
  all_goals try contradiction
  · trivial
  · change t.channel=c at hx
    change u.channel=c
    exact (congrArg Sigma.fst h).symm.trans hx

theorem observation_adj (c : Fin D.channels) {x y : D.Vertex ε}
    (hx : Live c x) (hy : Live c y) (h : (D.graph ε).Adj x y) :
    observation c x=observation c y := by
  rcases x with x | (⟨d,z⟩ | t)
  · exact hx.elim
  · rcases y with y | (⟨e,w⟩ | u)
    · exact hy.elim
    · have hz : z=w := by
        rcases h with h | h
        · exact h.2
        · exact h.2.symm
      subst w
      rfl
    · have he : u.channel=d ∧ u.height=D.dimension ∧ u.bits=z.val ∘ D.order d := by
        simpa only [graph,Forward,false_or] using h
      change u.channel=c at hy
      have hd : d=c := he.1.symm.trans hy
      subst d
      change truncate (D.root c) (z.val ∘ D.order c)=truncate (D.root c) u.bits
      rw [he.2.2]
  · rcases y with y | (⟨e,w⟩ | u)
    · exact hy.elim
    · have he : t.channel=e ∧ t.height=D.dimension ∧ t.bits=w.val ∘ D.order e := by
        simpa only [graph,Forward,or_false] using h
      change t.channel=c at hx
      have hc : e=c := he.1.symm.trans hx
      subst e
      change truncate (D.root c) t.bits=truncate (D.root c) (w.val ∘ D.order c)
      rw [he.2.2]
    · have ht : D.root c ≤ t.height := by rw [← hx]; exact t.property.1
      have hu : D.root c ≤ u.height := by rw [← hy]; exact u.property.1
      change truncate (D.root c) t.bits=truncate (D.root c) u.bits
      rcases h with h | h
      · calc
          _ = truncate (D.root c) (truncate t.height u.bits) := congrArg _ h.2.2.symm
          _ = _ := truncate_truncate ht _
      · calc
          _ = truncate (D.root c) (truncate u.height t.bits) := (truncate_truncate hu _).symm
          _ = _ := congrArg _ h.2.2

end VariableWL.PrefixParts.Data

namespace VariableWL.PrefixParts.Data
open VariableWL.Affine
attribute [local instance] Classical.propDecidable
variable {D : Data} {ε : Bit}

abbrev LiveVertex (c : Fin D.channels) (ε : Bit) := {x : D.Vertex ε // Live c x}
def liveGraph (c : Fin D.channels) (ε : Bit) : SimpleGraph (LiveVertex c ε) :=
  (D.graph ε).induce (Live c)

def liveSpine (c d : Fin D.channels) (z : D.Valuation ε) : LiveVertex c ε :=
  ⟨.inr (.inl (d,z)),trivial⟩

def liveTree (c : Fin D.channels) (h : ℕ) (hq : D.root c ≤ h) (ha : h ≤ D.dimension)
    (z : D.Valuation ε) : LiveVertex c ε := ⟨.inr (.inr (Tree.ofValuation c h hq ha z)),rfl⟩

theorem live_tree_to_leaf (c : Fin D.channels) (z : D.Valuation ε) :
    ∀ h (hq : D.root c ≤ h) (ha : h ≤ D.dimension),
    (liveGraph c ε).Reachable (liveTree c h hq ha z)
      (liveTree c D.dimension (D.root_le c) le_rfl z) := by
  intro h hq ha
  induction hd : D.dimension-h generalizing h with
  | zero => have he : h=D.dimension := by omega
            subst h
            exact SimpleGraph.Reachable.refl _
  | succ d ih =>
    have hlt : h<D.dimension := by omega
    have hs : (liveGraph c ε).Adj (liveTree c h hq ha z)
        (liveTree c (h+1) (by omega) (by omega) z) := by
      refine Or.inl ⟨rfl,rfl,?_⟩
      change truncate h (truncate (h+1) (z.val ∘ D.order c))=truncate h (z.val ∘ D.order c)
      exact truncate_truncate (by omega) _
    exact hs.reachable.trans (ih (h+1) (by omega) (by omega) (by omega))

theorem live_spine_to_zero (c d : Fin D.channels) (z : D.Valuation ε) :
    (liveGraph c ε).Reachable (liveSpine c d z) (liveSpine c ⟨0,D.positive⟩ z) := by
  induction hd : d.val generalizing d with
  | zero => have he : d=⟨0,D.positive⟩ := Fin.ext hd
            subst d; exact SimpleGraph.Reachable.refl _
  | succ k ih =>
    let e : Fin D.channels := ⟨k,by omega⟩
    have hs : (liveGraph c ε).Adj (liveSpine c d z) (liveSpine c e z) := Or.inr ⟨hd.symm,rfl⟩
    exact hs.reachable.trans (ih e rfl)

theorem live_to_root (c : Fin D.channels) (z : D.Valuation ε) :
    (liveGraph c ε).Reachable (liveSpine c ⟨0,D.positive⟩ z)
      (liveTree c (D.root c) le_rfl (D.root_le c) z) := by
  have hl : (liveGraph c ε).Adj (liveTree c D.dimension (D.root_le c) le_rfl z) (liveSpine c c z) :=
    Or.inl ⟨rfl,rfl,truncate_full _⟩
  exact (live_spine_to_zero c c z).symm.trans
    (hl.reachable.symm.trans (live_tree_to_leaf c z (D.root c) le_rfl (D.root_le c)).symm)

theorem zero_legal (D : Data) : 0 ∈ D.legal 0 := by
  obtain ⟨ξ,hξ⟩ := D.nonempty 1
  exact (D.coset ξ hξ 0).mpr (by rw [zero_add]; exact hξ)

def zeroValuation (D : Data) : D.Valuation 0 := ⟨0,zero_legal D⟩

end VariableWL.PrefixParts.Data

namespace VariableWL.PrefixParts.Wiring
open VariableWL.Affine VariableWL.SubcubicRealization
attribute [local instance] Classical.propDecidable
variable {B : Type uVariable2} [Fintype B] [FiniteNumbering B] (D : B → Data) [FiniteNumbering (SortTag D)] (W : Wiring D)

def Live (sel : ∀ b, Fin (D b).channels) {ε : Bit} (x : Vertex D ε) : Prop :=
  Data.Live (sel x.1) x.2

def observation (sel : ∀ b, Fin (D b).channels) {ε : Bit} (x : Vertex D ε) : ℕ → Bit :=
  pad (Data.observation (sel x.1) x.2)

omit [FiniteNumbering B] in
theorem live_of_color (sel : ∀ b, Fin (D b).channels) {ε δ : Bit}
    {x : Vertex D ε} {y : Vertex D δ} (h : color D x=color D y) (hx : Live D sel x) : Live D sel y := by
  have hs := (color_eq_iff D x y).mp h
  rcases x with ⟨b,x⟩
  rcases y with ⟨c,y⟩
  have hb : b=c := congrArg Sigma.fst hs
  subst c
  have ht := eq_of_heq (Sigma.mk.inj_iff.mp hs).2
  exact Data.live_of_sort (sel b) ht hx

omit [Fintype B] in
theorem root_observation (sel : ∀ b, Fin (D b).channels) {ε : Bit} (x : RootLabel D ε)
    (hx : Live D sel (rootVertex D x)) : observation D sel (rootVertex D x)=pad x.2.val.bits := by
  change x.2.val.channel=sel x.1.1 at hx
  have hc : x.1.2.val=sel x.1.1 := x.2.property.1.symm.trans hx
  have hh : (D x.1.1).root (sel x.1.1)=x.2.val.height :=
    (congrArg (D x.1.1).root hc.symm).trans x.2.property.2.symm
  change pad (Data.truncate ((D x.1.1).root (sel x.1.1)) x.2.val.bits)=_
  rw [hh,x.2.val.truncated]

omit [FiniteNumbering (SortTag D)] in

theorem observation_adj (sel : ∀ b, Fin (D b).channels) {ε : Bit} {x y : Vertex D ε}
    (hx : Live D sel x) (hy : Live D sel y) (h : (W.ports D ε).graph.Adj x y) :
    observation D sel x=observation D sel y := by
  obtain ⟨i,j,h⟩ := h
  rcases h with hi | hr | ha
  · rcases x with ⟨b,x⟩
    rcases y with ⟨c,y⟩
    obtain ⟨hb,he⟩ := hi
    change b=c at hb
    subst c
    exact congrArg pad (Data.observation_adj (sel b) hx hy he.1)
  · obtain ⟨u,v,hu,hv,_,he⟩ := hr
    have hxu : x=rootVertex D u := congrArg Prod.fst hu
    have hyv : y=rootVertex D v := congrArg Prod.fst hv
    subst x
    subst y
    rw [root_observation D sel u hx,root_observation D sel v hy]
    exact he
  · rcases ha with ⟨b,c,hb,_,_⟩ | ⟨b,c,_,hb,_⟩
    all_goals
      have hxb : x=anchor D ε _ := congrArg Prod.fst hb
      subst x
      exact hx.elim

abbrev LiveVertex (sel : ∀ b, Fin (D b).channels) (ε : Bit) := {x : Vertex D ε // Live D sel x}
noncomputable def liveGraph (sel : ∀ b, Fin (D b).channels) (ε : Bit) :
    SimpleGraph (LiveVertex D sel ε) := (W.ports D ε).graph.induce (Live D sel)

noncomputable def livePartHom (sel : ∀ b, Fin (D b).channels) (ε : Bit) (b : B) :
    Data.liveGraph (sel b) ε →g liveGraph D W sel ε where
  toFun v := ⟨⟨b,v.val⟩,v.property⟩
  map_rel' h := (partHom D W ε b).map_adj h

end VariableWL.PrefixParts.Wiring

namespace VariableWL.PrefixParts.Wiring
open VariableWL.Affine VariableWL.SubcubicRealization
attribute [local instance] Classical.propDecidable
variable {B : Type uVariable3} [Fintype B] [FiniteNumbering B] (D : B → Data) [FiniteNumbering (SortTag D)] (W : Wiring D)

theorem word_of_live_reachable (sel : ∀ b, Fin (D b).channels) {ε δ : Bit}
    {x y : LiveVertex D sel ε} (h : (liveGraph D W sel ε).Reachable x y) :
    ∃ ts, SortWalk (W.ports D ε).graph (color D) ts x.val y.val ∧
      ∀ t ∈ ts, ∀ z : Vertex D δ, color D z=t → Live D sel z := by
  obtain ⟨p⟩ := h
  refine ⟨p.support.map (fun z => color D z.val),?_,?_⟩
  · induction p with
    | nil => exact ⟨rfl,rfl⟩
    | @cons u v w ha p ih =>
      change SortWalk _ _ (color D u.val :: p.support.map (fun z => color D z.val)) u.val w.val
      rw [← p.cons_tail_support] at ih ⊢
      exact ⟨rfl,v.val,ha,ih⟩
  · intro t ht z hz
    obtain ⟨v,_,hv⟩ := List.mem_map.mp ht
    exact live_of_color D sel (hv.trans hz.symm) v.property

theorem observation_sortWalk (sel : ∀ b, Fin (D b).channels) {ε : Bit} (ts : List ℕ)
    (hl : ∀ t ∈ ts, ∀ z : Vertex D ε, color D z=t → Live D sel z)
    {x y : Vertex D ε} (h : SortWalk (W.ports D ε).graph (color D) ts x y) :
    Live D sel x ∧ Live D sel y ∧ observation D sel x=observation D sel y := by
  induction ts using List.twoStepInduction generalizing x y with
  | nil => exact h.elim
  | singleton t =>
    obtain ⟨rfl,hx⟩ := h
    exact ⟨hl t (by simp) x hx,hl t (by simp) x hx,rfl⟩
  | cons_cons t u ts _ ih =>
    obtain ⟨hx,z,hxz,hzy⟩ := h
    have hxL := hl t (by simp) x hx
    have hi := ih u (fun a ha => hl a (List.mem_cons_of_mem t ha)) hzy
    exact ⟨hxL,hi.2.1,(observation_adj D W sel hxL hi.1 hxz).trans hi.2.2⟩

omit [Fintype B] in
def rootOfValuation {ε : Bit} (c : Channel D) (z : (D c.1).Valuation ε) : RootLabel D ε :=
  ⟨c,⟨Data.Tree.ofValuation c.2.val ((D c.1).root c.2.val) le_rfl ((D c.1).root_le _) z,rfl,rfl⟩⟩

omit [Fintype B] in
theorem zero_root_bits (c : Channel D) :
    pad (rootOfValuation D c (Data.zeroValuation (D c.1))).2.val.bits=0 := by
  change pad (Data.truncate ((D c.1).root c.2.val) ((0 : Vec (D c.1).dimension) ∘ (D c.1).order c.2.val))=0
  ext j
  simp [pad,Data.truncate]

omit [Fintype B] in
def queryOwner (b : B) {ε : Bit} (z : (D b).Valuation ε) : Vertex D ε :=
  ⟨b,.inr (.inl (⟨0,(D b).positive⟩,z))⟩

noncomputable def selection (c : Channel D) (b : B) : Fin (D b).channels :=
  if h : b=c.1 then h.symm ▸ c.2.val
  else if h : b=(W.mate c).1 then h.symm ▸ (W.mate c).2.val
  else ⟨0,(D b).positive⟩

omit [Fintype B] in
theorem selection_self (c : Channel D) : selection D W c c.1=c.2.val := by
  simp [selection]

omit [Fintype B] in
theorem selection_mate (c : Channel D) : selection D W c (W.mate c).1=(W.mate c).2.val := by
  simp [selection,W.different c]

omit [FiniteNumbering (SortTag D)] in
theorem zero_queries_reachable (c : Channel D) :
    (liveGraph D W (selection D W c) 0).Reachable
      ⟨queryOwner D c.1 (Data.zeroValuation (D c.1)),trivial⟩
      ⟨queryOwner D (W.mate c).1 (Data.zeroValuation (D (W.mate c).1)),trivial⟩ := by
  let sel := selection D W c
  let x := rootOfValuation D c (Data.zeroValuation (D c.1))
  let y := rootOfValuation D (W.mate c) (Data.zeroValuation (D (W.mate c).1))
  have hx : Live D sel (rootVertex D x) := (selection_self D W c).symm
  have hy : Live D sel (rootVertex D y) := (selection_mate D W c).symm
  have he : (liveGraph D W sel 0).Adj ⟨rootVertex D x,hx⟩ ⟨rootVertex D y,hy⟩ := by
    refine ⟨0,0,Or.inr (Or.inl ⟨x,y,rfl,rfl,rfl,?_⟩)⟩
    exact (zero_root_bits D c).trans (zero_root_bits D (W.mate c)).symm
  have hleft := (Data.live_to_root (sel c.1) (Data.zeroValuation (D c.1))).map
    (livePartHom D W sel 0 c.1)
  have hright := (Data.live_to_root (sel (W.mate c).1) (Data.zeroValuation (D (W.mate c).1))).map
    (livePartHom D W sel 0 (W.mate c).1)
  have hxl : (livePartHom D W sel 0 c.1)
      (Data.liveTree (sel c.1) ((D c.1).root (sel c.1)) le_rfl ((D c.1).root_le _) (Data.zeroValuation (D c.1))) =
      ⟨rootVertex D x,hx⟩ := by
    apply Subtype.ext
    simp only [livePartHom,Data.liveTree,rootVertex,x,rootOfValuation,sel,selection_self]
    rfl
  have hyr : (livePartHom D W sel 0 (W.mate c).1)
      (Data.liveTree (sel (W.mate c).1) ((D (W.mate c).1).root (sel (W.mate c).1)) le_rfl
        ((D (W.mate c).1).root_le _) (Data.zeroValuation (D (W.mate c).1))) =
      ⟨rootVertex D y,hy⟩ := by
    apply Subtype.ext
    simp only [livePartHom,Data.liveTree,rootVertex,y,rootOfValuation,sel,selection_mate]
    rfl
  rw [hxl] at hleft
  rw [hyr] at hright
  exact hleft.trans (he.reachable.trans hright.symm)

theorem readout_word (c : Channel D) :
    ∃ ts, SortWalk (W.ports D 0).graph (color D) ts
      (queryOwner D c.1 (Data.zeroValuation (D c.1)))
      (queryOwner D (W.mate c).1 (Data.zeroValuation (D (W.mate c).1))) ∧
    ∀ x y : Vertex D 1, SortWalk (W.ports D 1).graph (color D) ts x y →
      observation D (selection D W c) x=observation D (selection D W c) y := by
  obtain ⟨ts,hs,ht⟩ := word_of_live_reachable D W (selection D W c) (δ := 1)
    (zero_queries_reachable D W c)
  exact ⟨ts,hs,fun x y h => (observation_sortWalk D W _ ts ht h).2.2⟩

end VariableWL.PrefixParts.Wiring

namespace VariableWL.PrefixParts.Wiring
open VariableWL.Affine VariableWL.SubcubicRealization
attribute [local instance] Classical.propDecidable
variable {B : Type uVariable4} [Fintype B] [FiniteNumbering B] (D : B → Data) [FiniteNumbering (SortTag D)] (W : Wiring D)

noncomputable def query (b : B) : UncoloredVertex D 0 :=
  SubcubicRealization.Vertex.triangle (queryOwner D b (Data.zeroValuation (D b))) 0

abbrev Response (b : B) := (D b).Valuation 1 × Fin 3

noncomputable def response (v : Σ b, Response D b) : UncoloredVertex D 1 :=
  SubcubicRealization.Vertex.triangle (queryOwner D v.1 v.2.1) v.2.2

omit [FiniteNumbering B] in
theorem queryOwner_recognized (b : B) (y : Vertex D 1)
    (h : color D (queryOwner D b (Data.zeroValuation (D b)))=color D y) :
    ∃ z : (D b).Valuation 1, y=queryOwner D b z := by
  have hs := (color_eq_iff D _ _).mp h
  rcases y with ⟨c,y⟩
  have hb : b=c := congrArg Sigma.fst hs
  subst c
  have ht := eq_of_heq (Sigma.mk.inj_iff.mp hs).2
  rcases y with u | (⟨d,z⟩ | t)
  · cases ht
  · have hd : (⟨0,(D b).positive⟩ : Fin (D b).channels)=d := Sum.inl.inj (Sum.inr.inj ht)
    subst d
    exact ⟨z,rfl⟩
  · cases ht

theorem winning_query_recognized {q : ℕ} (hq : 3 ≤ q)
    {p : TypedGame.Position (UncoloredVertex D 0) (UncoloredVertex D 1) q}
    (hp : TypedGame.Winning (uncolored D W 0) (uncolored D W 1) p)
    {i : Fin q} {b : B} {w : UncoloredVertex D 1} (hi : p i=some (query D b,w)) :
    ∃ z : Response D b, w=response D ⟨b,z⟩ := by
  obtain ⟨hw,hc⟩ := winning_color (W.ports D 0) (W.ports D 1) (color D) (color D)
    hq (color_pos D) (color_pos D) hp hi rfl
  obtain ⟨z,hz⟩ := queryOwner_recognized D b w.owner hc
  exact ⟨(z,w.port),SubcubicRealization.Vertex.ext hz rfl hw⟩

theorem winning_readout {q : ℕ} (hq : 3 ≤ q)
    {p : TypedGame.Position (UncoloredVertex D 0) (UncoloredVertex D 1) q}
    (hp : TypedGame.Winning (uncolored D W 0) (uncolored D W 1) p)
    (c : Channel D) (z : Response D c.1) (z' : Response D (W.mate c).1)
    {i j : Fin q} (hi : p i=some (query D c.1,response D ⟨c.1,z⟩))
    (hj : p j=some (query D (W.mate c).1,response D ⟨(W.mate c).1,z'⟩)) :
    pad (Data.truncate ((D c.1).root c.2.val) (z.1.val ∘ (D c.1).order c.2.val))=
    pad (Data.truncate ((D (W.mate c).1).root (W.mate c).2.val)
      (z'.1.val ∘ (D (W.mate c).1).order (W.mate c).2.val)) := by
  obtain ⟨ts,hs,ht⟩ := readout_word D W c
  have h := winning_sortWalk (W.ports D 0) (W.ports D 1) (color D) (color D)
    hq (color_pos D) (color_pos D) ts p hp hi hj ⟨rfl,rfl,hs⟩
  have he := ht _ _ h.2.2
  change pad (Data.truncate ((D c.1).root (selection D W c c.1))
      (z.1.val ∘ (D c.1).order (selection D W c c.1)))=
    pad (Data.truncate ((D (W.mate c).1).root (selection D W c (W.mate c).1))
      (z'.1.val ∘ (D (W.mate c).1).order (selection D W c (W.mate c).1))) at he
  simpa only [selection_self,selection_mate] using he

end VariableWL.PrefixParts.Wiring

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_SubcubicGame
attribute [-instance] _root_.OAI.VariableWL.AffineAlphabet.linearFintype _root_.OAI.VariableWL.Circuit.ProductCellular.powTwoNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6

namespace VariableWL.Subcubic
open VariableWL.Affine VariableWL.Blocks VariableWL.PrefixParts VariableWL.PrefixParts.Wiring
open VariableWL.BlockCoordinates
attribute [local instance] Classical.propDecidable
variable {r n : ℕ} {P : Type uVariable1} {E : Type uVariable2} [Fintype P] [Fintype E]
  (J : ProductImages.Instance r P E) [∀ b : Block (n := n) J, FiniteNumbering (Proper J b)] [FiniteNumbering (Block (n := n) J)] (hr : 2 ≤ r) (hn : 0 < n) (marked : Fin r)
  [FiniteNumbering (SortTag (data (n := n) J hr hn marked))]

noncomputable abbrev Vertex (ε : Bit) := UncoloredVertex (data (n := n) J hr hn marked) ε

noncomputable def translation (ξ : ∀ b : Block (n := n) J, Valuation J marked 1 b) :
    Vertex J hr hn marked 0 ≃ Vertex J hr hn marked 1 :=
  uncoloredTranslation (data J hr hn marked) (encodeList J hr hn marked ξ)

noncomputable def numberedTranslation (ξ : ∀ b : Block (n := n) J, Valuation J marked 1 b) :
    Fin (finiteGraph J hr hn marked 0).order ≃ Fin (finiteGraph J hr hn marked 1).order :=
  (Fintype.equivFin _).symm.trans ((translation J hr hn marked ξ).trans (Fintype.equivFin _))

noncomputable def numberedPart (v : Fin (finiteGraph J hr hn marked 0).order) : Block (n := n) J :=
  ((Fintype.equivFin (Vertex J hr hn marked 0)).symm v).owner.1

end VariableWL.Subcubic

namespace VariableWL.Subcubic
open VariableWL.Affine VariableWL.Blocks VariableWL.PrefixParts VariableWL.PrefixParts.Wiring
open VariableWL.BlockCoordinates
attribute [local instance] Classical.propDecidable
variable {r n : ℕ} {P : Type uVariable3} {E : Type uVariable4} [Fintype P] [Fintype E]
  (J : ProductImages.Instance r P E) [∀ b : Block (n := n) J, FiniteNumbering (Proper J b)] [FiniteNumbering (Block (n := n) J)] (hr : 2 ≤ r) (hn : 0 < n) (marked : Fin r)
  [FiniteNumbering (SortTag (data (n := n) J hr hn marked))]

abbrev Response (b : Block (n := n) J) := Valuation J marked 1 b × Fin 3

noncomputable def zeroQuery (b : Block (n := n) J) : Fin (finiteGraph J hr hn marked 0).order :=
  Fintype.equivFin _ (Wiring.query (data J hr hn marked) b)

noncomputable def valuationQuery (b : Block (n := n) J) (z : Response J marked b) :
    Fin (finiteGraph J hr hn marked 1).order :=
  Fintype.equivFin _ (Wiring.response (data J hr hn marked)
    ⟨b,valuationEquiv J hr hn marked b 1 z.1,z.2⟩)

theorem valuationQuery_injective (b : Block (n := n) J) :
    Function.Injective (valuationQuery J hr hn marked b) := by
  intro z w he
  have h0 := (Fintype.equivFin (Vertex J hr hn marked 1)).injective he
  have ho := congrArg SubcubicRealization.Vertex.owner h0
  have hv := eq_of_heq (Sigma.mk.inj_iff.mp ho).2
  have hz : valuationEquiv J hr hn marked b 1 z.1=valuationEquiv J hr hn marked b 1 w.1 :=
    congrArg Prod.snd (Sum.inl.inj (Sum.inr.inj hv))
  have hp : z.2=w.2 := congrArg SubcubicRealization.Vertex.port h0
  exact Prod.ext ((valuationEquiv J hr hn marked b 1).injective hz) hp

theorem decode_winning {q : ℕ}
    {p : Game.Position (finiteGraph J hr hn marked 0) (finiteGraph J hr hn marked 1) q}
    (hp : Game.Winning p) :
    TypedGame.Winning (graph J hr hn marked 0) (graph J hr hn marked 1) (TypedGame.decode p) := by
  change Game.Winning (G := finiteGraph J hr hn marked 0)
    (H := finiteGraph J hr hn marked 1) (TypedGame.encode (TypedGame.decode p))
  rw [TypedGame.encode_decode]
  exact hp

theorem zeroQuery_recognized {q : ℕ} (hq : 3 ≤ q)
    {p : Game.Position (finiteGraph J hr hn marked 0) (finiteGraph J hr hn marked 1) q}
    (hp : Game.Winning p) {i : Fin q} {b : Block (n := n) J} {w : Fin (finiteGraph J hr hn marked 1).order}
    (hi : p i=some (zeroQuery J hr hn marked b,w)) :
    ∃ z : Response J marked b, w=valuationQuery J hr hn marked b z := by
  have hi' : TypedGame.decode p i=some (Wiring.query (data J hr hn marked) b,
      (Fintype.equivFin (Vertex J hr hn marked 1)).symm w) := by
    simp only [TypedGame.decode,hi,Option.map_some,zeroQuery,Equiv.symm_apply_apply]
  obtain ⟨z,hz⟩ := winning_query_recognized (data J hr hn marked) (wiring J hr hn marked)
    hq (decode_winning J hr hn marked hp) hi'
  refine ⟨((valuationEquiv J hr hn marked b 1).symm z.1,z.2),?_⟩
  apply (Fintype.equivFin (Vertex J hr hn marked 1)).symm.injective
  simpa only [valuationQuery,Equiv.symm_apply_apply,Equiv.apply_symm_apply] using hz

theorem zeroQuery_agree {q : ℕ} (hq : 3 ≤ q)
    {p : Game.Position (finiteGraph J hr hn marked 0) (finiteGraph J hr hn marked 1) q}
    (hp : Game.Winning p) {i j : Fin q} {b c : Block (n := n) J}
    {z : Response J marked b} {w : Response J marked c}
    (hi : p i=some (zeroQuery J hr hn marked b,valuationQuery J hr hn marked b z))
    (hj : p j=some (zeroQuery J hr hn marked c,valuationQuery J hr hn marked c w)) :
    General.Agree J marked ⟨b,z.1⟩ ⟨c,w.1⟩ := by
  intro a hb hc
  by_cases hbc : b=c
  · subst c
    have hzw := valuationQuery_injective J hr hn marked b ((hp.partialIso i j _ _ hi hj).1.mp rfl)
    exact congrArg (fun t : Response J marked b => readout J t.1.val hb) hzw
  · have hi' : TypedGame.decode p i=some (Wiring.query (data J hr hn marked) b,
        Wiring.response (data J hr hn marked) ⟨b,valuationEquiv J hr hn marked b 1 z.1,z.2⟩) := by
      simp only [TypedGame.decode,hi,Option.map_some,zeroQuery,valuationQuery,Equiv.symm_apply_apply]
    have hj' : TypedGame.decode p j=some (Wiring.query (data J hr hn marked) c,
        Wiring.response (data J hr hn marked) ⟨c,valuationEquiv J hr hn marked c 1 w.1,w.2⟩) := by
      simp only [TypedGame.decode,hj,Option.map_some,zeroQuery,valuationQuery,Equiv.symm_apply_apply]
    let d : Proper J b := ⟨⟨c,Ne.symm hbc⟩,a,hb,hc⟩
    let e : Proper J c := ⟨⟨b,hbc⟩,a,hc,hb⟩
    have test := winning_readout (data J hr hn marked) (wiring J hr hn marked)
      hq (decode_winning J hr hn marked hp) (channelEquiv J hr hn marked ⟨b,d⟩)
    rw [mate_channel] at test
    have he := test (valuationEquiv J hr hn marked b 1 z.1,z.2)
      (valuationEquiv J hr hn marked c 1 w.1,w.2) hi' hj'
    change pad (Data.truncate ((data J hr hn marked b).root (properNumber J b d).val)
      ((valuationEquiv J hr hn marked b 1 z.1).val ∘
        (data J hr hn marked b).order (properNumber J b d).val)) =
      pad (Data.truncate ((data J hr hn marked c).root (properNumber J c e).val)
      ((valuationEquiv J hr hn marked c 1 w.1).val ∘
        (data J hr hn marked c).order (properNumber J c e).val)) at he
    rw [data_prefix,data_prefix] at he
    exact (readoutEquiv J a).injective (pad_injective he)

end VariableWL.Subcubic

namespace VariableWL.Subcubic
open VariableWL.Affine VariableWL.Blocks VariableWL.PrefixParts VariableWL.PrefixParts.Wiring
open VariableWL.BlockCoordinates
attribute [local instance] Classical.propDecidable
variable {r n : ℕ} {P : Type uVariable5} {E : Type uVariable6} [Fintype P] [Fintype E]
  (J : ProductImages.Instance r P E) [∀ b : Block (n := n) J, FiniteNumbering (Proper J b)] [FiniteNumbering (Block (n := n) J)] (hr : 2 ≤ r) (hn : 0 < n) (marked : Fin r)
  [FiniteNumbering (SortTag (data (n := n) J hr hn marked))]

noncomputable def attainedRings
    (hwin : Game.Winning (fun _ : Fin (r+1) => none :
      Game.Position (finiteGraph J hr hn marked 0) (finiteGraph J hr hn marked 1) (r+1))) :
    RingSystem J marked (n := n) := by
  let query := zeroQuery J hr hn marked
  let response := fun v : Σ b : Block (n := n) J, Response J marked b =>
    valuationQuery J hr hn marked v.1 v.2
  let decode := fun (b : Block (n := n) J) (z : Response J marked b) => z.1
  have recognize : ∀ p : Game.Position (finiteGraph J hr hn marked 0) (finiteGraph J hr hn marked 1) (r+1),
      Game.Winning p → ∀ i b w, p i=some (query b,w) → ∃ z : Response J marked b, w=response ⟨b,z⟩ :=
    fun p hp i b w hi => zeroQuery_recognized J hr hn marked (by omega) hp hi
  have agreement : ∀ p : Game.Position (finiteGraph J hr hn marked 0) (finiteGraph J hr hn marked 1) (r+1),
      Game.Winning p → ∀ i j v w, p i=some (query v.1,response v) → p j=some (query w.1,response w) →
        General.Agree J marked (Game.decodeSigma decode v) (Game.decodeSigma decode w) := by
    intro p hp i j v w hi hj
    exact zeroQuery_agree J hr hn marked (by omega) hp hi hj
  exact {
    lists := Game.RingLists query response decode
    nonempty := Game.ringLists_nonempty query response decode recognize hwin
    compatible := fun b y hy i j => Game.ringLists_compatible query response decode (General.Agree J marked) agreement hy i j
    transfer := fun b y hy c => Game.ringLists_transfer query response decode recognize (General.Agree J marked) agreement hy c }

end VariableWL.Subcubic

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_StackSimulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10 uVariable11 uVariable12 uVariable13 uVariable14 uVariable15 uVariable16 uVariable17 uVariable18 uVariable19

namespace VariableWL.OneHead
variable {Q : Type uVariable5} {Γ : Type uVariable6} {m d : ℕ}

noncomputable def product (M : Program Q Γ) (blank : Γ) (w : Fin m → Γ)
    (hfit : m < 2^d) : Circuit.ProductCellular.Data (Cell Q Γ) d m where
  rule := M.rule
  input := markedInput M w
  blank := (blank,none)
  accepting := M.acceptingCell
  fits := hfit

end VariableWL.OneHead

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_MachineReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6

namespace VariableWL.MachineReduction
open MachineOneHead
attribute [local instance] Classical.propDecidable
variable (M : Machine) (c d : ℕ)

noncomputable def circuit (w : Word) : Circuit.ProductCellular.Data (Letter M)
    (bits M c d w) (input M w).length :=
  OneHead.product (oneHead M) default (fun j : Fin (input M w).length => (input M w)[j]) (fits M c d w)

abbrev Real (w : Word) := Circuit.Description.Real
  (S := Letter M) (A := Circuit.Cellular.Triple (Letter M) × Bool)
  (E := Circuit.ProductCellular.Edge (Letter M) (bits M c d w))
abbrev Comparison (w : Word) := Circuit.Description.Comparison
  (E := Circuit.ProductCellular.Edge (Letter M) (bits M c d w))
  (R := (circuit M c d w).Request)

noncomputable def imageInstance (w : Word) : ProductImages.Instance (dimension M c d w)
    (Real M c d w) (Comparison M c d w) := (circuit M c d w).description.consistency

noncomputable instance realFintype (w : Word) : Fintype (Real M c d w) := inferInstance
noncomputable instance comparisonFintype (w : Word) : Fintype (Comparison M c d w) := by
  classical
  letI : Fintype (Circuit.ProductCellular.Edge (Letter M) (bits M c d w)) := inferInstance
  letI : Fintype {h : Fin (bits M c d w) // (circuit M c d w).threshold h=false} := Fintype.ofFinite _
  letI : Fintype {f : Letter M // f ∈ (circuit M c d w).accepting} := Fintype.ofFinite _
  unfold Comparison Circuit.Description.Comparison Circuit.ProductCellular.Data.Request
  infer_instance
instance realNonempty (w : Word) : Nonempty (Real M c d w) := ⟨.inr (.inr ())⟩

end VariableWL.MachineReduction

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_RefinementTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.RefinementTable
attribute [local instance] Classical.propDecidable

variable (G H : Graph) (k : ℕ)
abbrev Entry := TaggedTuple G H k
abbrev Vector := Fin k → Entry G H k

def neighbors : Entry G H k → List (Vector G H k)
  | .inl v => List.ofFn fun z : Fin G.order => fun i => Sum.inl (Function.update v i z)
  | .inr v => List.ofFn fun z : Fin H.order => fun i => Sum.inr (Function.update v i z)

def vectorEqual (R : Entry G H k → Entry G H k → Bool) (x y : Vector G H k) : Bool :=
  (List.finRange k).all fun i => R (x i) (y i)

def update (R : Entry G H k → Entry G H k → Bool) (x y : Entry G H k) : Bool :=
  R x y && sameCounts (vectorEqual G H k R) (neighbors G H k x) (neighbors G H k y)

noncomputable def initial (x y : Entry G H k) : Bool :=
  decide (tagColor G H k 0 x=tagColor G H k 0 y)

noncomputable def table : ℕ → Entry G H k → Entry G H k → Bool
  | 0 => initial G H k
  | s+1 => update G H k (table s)

noncomputable def histogramEqual (R : Entry G H k → Entry G H k → Bool) : Bool :=
  sameCounts R ((Finset.univ : Finset (Tuple G k)).toList.map Sum.inl)
    ((Finset.univ : Finset (Tuple H k)).toList.map Sum.inr)

noncomputable def accepts : Bool := histogramEqual G H k (table G H k ((G.order^k+H.order^k)^2))

end VariableWL.RefinementTable

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Decision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.Encoding
attribute [local instance] Classical.propDecidable

def fromMatrix (n : ℕ) (v : Word) (h : MatrixValid n v) : Graph where
  order := n
  graph := {
    Adj := fun i j => entry n v i j=true
    symm := ⟨fun {i j} hij => (h.2.1 j i).trans hij⟩
    loopless := ⟨fun i hi => by have hf := h.2.2 i; rw [hf] at hi; contradiction⟩ }

 theorem entry_matrix (G : Graph) (i j : Fin G.order) :
    entry G.order (matrix G) i j=decide (G.graph.Adj i j) := by
  classical
  have hn : 0<G.order := Nat.zero_lt_of_lt i.isLt
  have hp : i.val*G.order+j.val<G.order*G.order := by
    have := Nat.mul_le_mul_right G.order (Nat.succ_le_of_lt i.isLt)
    nlinarith [j.isLt]
  unfold entry matrix
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hp),List.getElem_ofFn]
  have hd : (⟨i.val*G.order+j.val,hp⟩ : Fin (G.order*G.order)).divNat=i := by
    apply Fin.ext
    simp [Fin.divNat,Nat.add_div,Nat.div_eq_of_lt j.isLt,hn,Nat.mod_lt _ hn]
  have hm : (⟨i.val*G.order+j.val,hp⟩ : Fin (G.order*G.order)).modNat=j := by
    apply Fin.ext
    simp [Fin.modNat,Nat.add_mod,Nat.mod_eq_of_lt j.isLt]
  rw [hd,hm]

 theorem matrix_valid (G : Graph) : MatrixValid G.order (matrix G) := by
  refine ⟨matrix_length G,?_,?_⟩
  · intro i j
    rw [entry_matrix,entry_matrix]
    exact decide_eq_decide.mpr (G.graph.adj_comm i j)
  · intro i
    rw [entry_matrix]
    simp

noncomputable def readMatrix (n : ℕ) (v : Word) : Option Graph :=
  if h : MatrixValid n v then some (fromMatrix n v h) else none

noncomputable def graph (w : Word) : Option (Graph × Word) :=
  match integer w with
  | none => none
  | some (n,u) => (readMatrix n (u.take (n*n))).map fun G => (G,u.drop (n*n))

noncomputable def pair (w : Word) : Option (Graph × Graph × ℕ) :=
  match graph w with
  | none => none
  | some (G,u) => match graph u with
    | none => none
    | some (H,v) => match integer v with
      | none => none
      | some (k,t) => if t=[] then some (G,H,k) else none

end VariableWL.Encoding

namespace VariableWL.RefinementArray
open RefinementTable
variable (G H : Graph) (k : ℕ)

def count : ℕ := G.order^k+H.order^k

def numbering : Entry G H k ≃ Fin (count G H k) :=
  (Equiv.sumCongr finFunctionFinEquiv finFunctionFinEquiv).trans finSumFinEquiv

def pack (R : Entry G H k → Entry G H k → Bool) : Word :=
  List.ofFn fun p : Fin (count G H k*count G H k) =>
    R ((numbering G H k).symm p.divNat) ((numbering G H k).symm p.modNat)

def lookup (w : Word) (x y : Entry G H k) : Bool :=
  w.getD ((numbering G H k x).val*count G H k+(numbering G H k y).val) false

noncomputable def array : ℕ → Word
  | 0 => pack G H k (RefinementTable.initial G H k)
  | s+1 => pack G H k (update G H k (lookup G H k (array s)))

noncomputable def accepts : Bool :=
  histogramEqual G H k (lookup G H k (array G H k ((count G H k)^2)))

end VariableWL.RefinementArray

namespace VariableWL.InputDecision

def capped (G : Graph) (k : ℕ) : ℕ := min k (max 2 G.order)

end VariableWL.InputDecision

namespace VariableWL.PromiseDecision
attribute [local instance] Classical.propDecidable
variable (G : Graph)

noncomputable def reach : ℕ → Fin G.order → Fin G.order → Bool
  | 0,u,v => decide (u=v)
  | t+1,u,v => reach t u v || (List.finRange G.order).any fun z =>
      decide (G.graph.Adj u z) && reach t z v

noncomputable def connected : Bool := decide (0<G.order) &&
  (List.finRange G.order).all fun u => (List.finRange G.order).all fun v => reach G G.order u v

noncomputable def neighbors (u : Fin G.order) : List (Fin G.order) :=
  (List.finRange G.order).filter fun v => decide (G.graph.Adj u v)

noncomputable def subcubic : Bool := (List.finRange G.order).all fun u => decide ((neighbors G u).length≤3)

end VariableWL.PromiseDecision

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_NumericRefinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.NumericRefinement

def Data.leftCount (D : Data) := D.leftOrder^D.dimension
def Data.rightCount (D : Data) := D.rightOrder^D.dimension
def Data.count (D : Data) := D.leftCount+D.rightCount

def Data.isLeft (D : Data) (a : ℕ) : Bool := decide (a<D.leftCount)
def Data.order (D : Data) (a : ℕ) := if D.isLeft a then D.leftOrder else D.rightOrder
def Data.offset (D : Data) (a : ℕ) := if D.isLeft a then 0 else D.leftCount
def Data.coordinate (D : Data) (a i : ℕ) := TupleAddress.digit (D.order a) (a-D.offset a) i

def Data.replacement (D : Data) (a z i : ℕ) :=
  D.offset a+TupleAddress.replace (D.order a) (a-D.offset a) i z

def Data.edge (D : Data) (a i j : ℕ) : Bool :=
  (if D.isLeft a then D.leftMatrix else D.rightMatrix).getD
    (D.coordinate a i*D.order a+D.coordinate a j) false

def Data.initial (D : Data) (a b : ℕ) : Bool :=
  (List.range D.dimension).all fun i => (List.range D.dimension).all fun j =>
    decide ((D.coordinate a i=D.coordinate a j) ↔ (D.coordinate b i=D.coordinate b j)) &&
      decide (D.edge a i j=D.edge b i j)

def Data.get (D : Data) (R : Word) (a b : ℕ) : Bool := R.getD (a*D.count+b) false

def Data.profile (D : Data) (R : Word) (x y : ℕ × ℕ) : Bool :=
  (List.range D.dimension).all fun i => D.get R (D.replacement x.1 x.2 i) (D.replacement y.1 y.2 i)

def Data.neighbors (D : Data) (a : ℕ) : List (ℕ × ℕ) := (List.range (D.order a)).map (a,·)

def Data.update (D : Data) (R : Word) (a b : ℕ) : Bool :=
  D.get R a b && RefinementTable.sameCounts (D.profile R) (D.neighbors a) (D.neighbors b)

def Data.pack (D : Data) (f : ℕ → ℕ → Bool) : Word :=
  (List.range (D.count*D.count)).map fun p => f (p/D.count) (p%D.count)

def Data.array (D : Data) : ℕ → Word
  | 0 => D.pack D.initial
  | s+1 => D.pack (D.update (D.array s))

def Data.histogram (D : Data) (R : Word) : Bool :=
  RefinementTable.sameCounts (D.get R) (List.range D.leftCount)
    ((List.range D.rightCount).map (D.leftCount+·))

def Data.accepts (D : Data) : Bool := D.histogram (D.array (D.count^2))

open RefinementTable
attribute [local instance] Classical.propDecidable
variable (G H : Graph) (k : ℕ)

noncomputable def data : Data := ⟨G.order,H.order,k,Encoding.matrix G,Encoding.matrix H⟩

def address (x : Entry G H k) := (RefinementArray.numbering G H k x).val

end VariableWL.NumericRefinement

namespace VariableWL.NumericRefinement
open RefinementTable
attribute [local instance] Classical.propDecidable
variable (G H : Graph) (k : ℕ)

abbrev Key := (Tuple G k × Fin G.order) ⊕ (Tuple H k × Fin H.order)

def keyPair : Key G H k → ℕ × ℕ
  | .inl (v,z) => (address G H k (.inl v),z.val)
  | .inr (v,z) => (address G H k (.inr v),z.val)

def keyVector : Key G H k → Vector G H k
  | .inl (v,z) => fun i => .inl (Function.update v i z)
  | .inr (v,z) => fun i => .inr (Function.update v i z)

def keys : Entry G H k → List (Key G H k)
  | .inl v => List.ofFn fun z : Fin G.order => .inl (v,z)
  | .inr v => List.ofFn fun z : Fin H.order => .inr (v,z)

end VariableWL.NumericRefinement

namespace VariableWL.NumericRefinement
open RefinementTable
attribute [local instance] Classical.propDecidable

variable (G H : Graph) (k : ℕ)

def leftEntries : List (Entry G H k) := List.ofFn fun p : Fin (G.order^k) =>
  Sum.inl (finFunctionFinEquiv.symm p)
def rightEntries : List (Entry G H k) := List.ofFn fun p : Fin (H.order^k) =>
  Sum.inr (finFunctionFinEquiv.symm p)

end VariableWL.NumericRefinement

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_NumericProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.NumericProgram
open Computation.Stack Computation.Stack.Recipe Computation.Stack.PolyRecipe
variable {n m : ℕ}

def Data.Good (D : Data n) (v : Env n) : Prop :=
  1≤D.capacity.number v ∧ D.leftOrder.number v^D.dimension.number v≤D.capacity.number v ∧
    D.rightOrder.number v^D.dimension.number v≤D.capacity.number v

end VariableWL.NumericProgram

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_ExponentialRecipe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.NumericPromise
attribute [local instance] Classical.propDecidable

def connected (n : ℕ) (A : Word) : Bool := decide (0<n) &&
  (List.range n).all fun a=>(List.range n).all fun b=>get n (array n A n) a b

def subcubic (n : ℕ) (A : Word) : Bool :=
  (List.range n).all fun a=>decide ((List.range n).countP (fun b=>get n A a b)≤3)

end VariableWL.NumericPromise

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_PrefixListing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1

namespace VariableWL.PrefixDescriptor.Program
attribute [local instance] Classical.propDecidable
open Computation.Stack.PolyRecipe Computation.Stack.Recipe
variable {n : ℕ}

def RawExpr.eval (x : RawExpr n) (v : Env n) : Raw :=
  ⟨x.block.number v,x.kind.number v,x.channel.number v,x.height.number v,x.vector.number v⟩

namespace Listing
variable (D : Listing n)
def eval (v : Env n) : Data where
  blocks := D.blocks.number v
  validBlock i := D.validBlock.bit (cons (List.replicate i true) v)
  channelBound := D.channelBound.number v
  dimension i := D.dimension.number (cons (List.replicate i true) v)
  channels i := D.channels.number (cons (List.replicate i true) v)
  root i j := D.root.number (cons (List.replicate i true) (cons (List.replicate j true) v))
  order i j := D.order.number (cons (List.replicate i true) (cons (List.replicate j true) v))
  legal i j := D.legal.bit (cons (List.replicate i true) (cons (List.replicate j true) v))
  matching i j := D.matching.bit (cons (List.replicate i true) (cons (List.replicate j true) v))
end Listing
end VariableWL.PrefixDescriptor.Program

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_CircuitCatalog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10 uVariable11

namespace VariableWL.Descriptor.Presentation
attribute [local instance] Classical.propDecidable
noncomputable def fixed (A : Type uVariable3) [Fintype A] : Presentation A :=
  ofEncoding (Fintype.card A) (fun _=>true) (fun a=>(Fintype.equivFin A a).val)
    (fun a=>(Fintype.equivFin A a).isLt) (fun _=>rfl)
    (fun _ _ h=>(Fintype.equivFin A).injective (Fin.ext h))
    (fun i hi _=>⟨(Fintype.equivFin A).symm ⟨i,hi⟩,by simp only [Equiv.apply_symm_apply]⟩)
end VariableWL.Descriptor.Presentation

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_MachineCellular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.MachineCellular
open MachineOneHead MachineReduction Descriptor Computation.Stack.PolyRecipe Computation.Stack.Recipe VariableWL.NumericProgram
attribute [local instance] Classical.propDecidable
variable (M : Machine)
noncomputable def presentation : Presentation (Letter M) := Presentation.fixed (Letter M)
noncomputable def initial (v : Word) : List (Alphabet M) := match v with
  | [] => [(true,fun _=>none)]
  | b::bs => alpha M true b :: bs.map (alpha M false)
noncomputable def letterInput (v : Word) (j : ℕ) : Letter M :=
  if j=0 then if v.length=0 then emptyLetter M else headLetter M (v.getD j false)
  else tailLetter M (v.getD j false)
noncomputable def inputProgram : Expr 2 :=
  choose (eq (input 0) (numeral 0))
    (choose (eq (input 1) (numeral 0)) (numeral ((presentation M).encode (emptyLetter M)))
      (choose (lookup (input 1) (input 0)) (numeral ((presentation M).encode (headLetter M true)))
        (numeral ((presentation M).encode (headLetter M false)))))
    (choose (lookup (input 1) (input 0)) (numeral ((presentation M).encode (tailLetter M true)))
      (numeral ((presentation M).encode (tailLetter M false))))

def fixedPower {n : ℕ} (X : Expr n) : ℕ → Expr n
  | 0 => numeral 1
  | k+1 => mul (fixedPower X k) X
noncomputable def bitProgram (c d : ℕ) : Expr 1 :=
  add (add (numeral (quadraticConstant M+3))
    (mul (numeral 2) (mul (numeral (c+1)) (fixedPower (add (input 0) (numeral 1)) (d+1))))) (numeral 2)
noncomputable def ruleCode (a b c : ℕ) : ℕ :=
  if ha : a<(presentation M).bound then if hb : b<(presentation M).bound then if hc : c<(presentation M).bound then
    (presentation M).encode ((oneHead M).rule ((Fintype.equivFin (Letter M)).symm ⟨a,ha⟩)
      ((Fintype.equivFin (Letter M)).symm ⟨b,hb⟩) ((Fintype.equivFin (Letter M)).symm ⟨c,hc⟩)) else 0 else 0 else 0
noncomputable def ruleProgram : Expr 4 :=
  table₃ (presentation M).bound (presentation M).bound (presentation M).bound (ruleCode M) (input 0) (input 1) (input 2)
noncomputable def acceptCode (a : ℕ) : Bool :=
  decide (∃f,(presentation M).encode f=a ∧ (oneHead M).acceptingCell f)
noncomputable def acceptProgram : Expr 2 :=
  choose (lt (input 0) (numeral (presentation M).bound))
    (fixedBool (presentation M).bound (fun i=>acceptCode M i.val) (input 0)) (literal [])
noncomputable def listing (c d : ℕ) (ε : Affine.Bit) : CellularCatalog.Program.Listing 1 where
  bits := bitProgram M c d
  inputLength := add (numeral 1) (sub (input 0) (numeral 1))
  letters := numeral (presentation M).bound
  internal := mul (numeral 4) (add (add (bitProgram M c d) (bitProgram M c d)) (numeral 1))
  rule := ruleProgram M
  input := inputProgram M
  blank := numeral ((presentation M).encode (default,none))
  accepting := acceptProgram M
  marked := numeral 0
  epsilon := numeral ε.val
end VariableWL.MachineCellular

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Completeness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2

namespace VariableWL.MachineCellular
open Computation.Stack.PolyRecipe Computation.Stack.Recipe VariableWL.NumericProgram
variable (M : Machine) (c d : ℕ)
noncomputable def graphListing (ε : Affine.Bit) : GraphListing 1 := (listing M c d ε).graph
noncomputable def base (v : Env 1) : AffineCatalog.Data := ((listing M c d 0).eval v).catalog.affine
end VariableWL.MachineCellular

namespace VariableWL.MachineCellular
open Descriptor Computation.Stack.PolyRecipe Computation.Stack.Recipe
attribute [local instance] Classical.propDecidable
variable (M : Machine) (c d : ℕ)
noncomputable def realPresentation (w : Word) : Presentation (MachineReduction.Real M c d w) :=
  CircuitCatalog.real (presentation M) (CellularCatalog.ands (presentation M))
    (CellularCatalog.edge (d := MachineReduction.bits M c d w) (presentation M))
noncomputable def comparisonPresentation (w : Word) : Presentation (MachineReduction.Comparison M c d w) :=
  CircuitCatalog.comparison (CellularCatalog.edge (d := MachineReduction.bits M c d w) (presentation M))
    (CellularCatalog.request (presentation M) (MachineReduction.circuit M c d w))
noncomputable def dimensionProgram : Expr 1 := add (bitProgram M c d) (bitProgram M c d)
noncomputable def pairProgram : Expr 1 := append (graphListing M c d 0).code
  (append (graphListing M c d 1).code (integerEncode (dimensionProgram M c d)))
end VariableWL.MachineCellular

end OAI
end


