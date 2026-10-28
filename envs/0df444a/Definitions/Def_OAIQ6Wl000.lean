-- Prove2me | Definitions.Def_OAIQ6Wl000
-- name    : OAIQ6Wl000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T01:55:00.704759+00:00
-- url     : https://prove2.me/theorems/40aa305e-68b5-423c-a909-a73d4f663ef7
-- title:
--   Definitions bundle OAIQ6Wl000 of the split of OpenAI, Variable-dimension Weisfeiler–Leman equivalence on general and subcubic graphs
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.VariableWL.main`, carved from OpenAI's openai/math development (OpenAI, *Variable-dimension Weisfeiler–Leman equivalence on general and subcubic graphs*, OpenAI Math Release, September 25, 2026, result family 133, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1632 declarations of OpenAI's Lean: 914 definitions, 56 inductive types or structures, 19 instances and 643 theorems. The definitions and types are `OAI.VariableWL.Affine.Bit`, `OAI.VariableWL.Affine.Fiber`, `OAI.VariableWL.Affine.SquareVal`, `OAI.VariableWL.Affine.Vec`, `OAI.VariableWL.Affine.boundary`, `OAI.VariableWL.AffineAlphabet.Form`, `OAI.VariableWL.AffineAlphabet.Program.horizontalLegal`, `OAI.VariableWL.AffineAlphabet.Program.horizontalOrder`, `OAI.VariableWL.AffineAlphabet.Program.squareLegal`, `OAI.VariableWL.AffineAlphabet.Program.squareLegalBody`, `OAI.VariableWL.AffineAlphabet.Program.squareOrder`, `OAI.VariableWL.AffineAlphabet.Program.zeroOrder`, `OAI.VariableWL.AffineAlphabet.SquareCoordinate`, `OAI.VariableWL.AffineAlphabet.encodeForm`, `OAI.VariableWL.AffineAlphabet.extend`, `OAI.VariableWL.AffineAlphabet.formCount`, `OAI.VariableWL.AffineAlphabet.formNumber`, `OAI.VariableWL.AffineAlphabet.horizontalEmbedding`, `OAI.VariableWL.AffineAlphabet.horizontalEncode`, `OAI.VariableWL.AffineAlphabet.horizontalLegal`, `OAI.VariableWL.AffineAlphabet.horizontalOrder`, `OAI.VariableWL.AffineAlphabet.leftEmbedding`, `OAI.VariableWL.AffineAlphabet.rightEmbedding`, `OAI.VariableWL.AffineAlphabet.scalarEmbedding`, `OAI.VariableWL.AffineAlphabet.squareCoordinate`, `OAI.VariableWL.AffineAlphabet.squareEncode`, `OAI.VariableWL.AffineAlphabet.squareLegal`, `OAI.VariableWL.AffineAlphabet.squareOrder`, `OAI.VariableWL.AffineAlphabet.zeroOrder`, `OAI.VariableWL.AffineCatalog.Data`, `OAI.VariableWL.AffineCatalog.Data.constant`, `OAI.VariableWL.AffineCatalog.Data.core`, `OAI.VariableWL.AffineCatalog.Data.descriptor`, `OAI.VariableWL.AffineCatalog.Data.dimension`, `OAI.VariableWL.AffineCatalog.Data.horizontalDimension`, `OAI.VariableWL.AffineCatalog.Data.legal`, `OAI.VariableWL.AffineCatalog.Data.linkLeft`, `OAI.VariableWL.AffineCatalog.Data.linkLeftConstant`, `OAI.VariableWL.AffineCatalog.Data.linkRight`, `OAI.VariableWL.AffineCatalog.Data.linkRightConstant` and 930 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `VariableWL_Affine`, `VariableWL_AffineCatalog`, `VariableWL_Binary`, `VariableWL_BinaryMachine`, `VariableWL_BlockCatalog`, `VariableWL_BlockCoordinates`, `VariableWL_BlockDescriptor`, `VariableWL_BlockExtensions`, `VariableWL_BlockGame`, `VariableWL_BlockImages`, `VariableWL_BlockListing`, `VariableWL_Blocks`, `VariableWL_BoundedLoop`, `VariableWL_CellularCatalog`, `VariableWL_CellularCircuit`, `VariableWL_CellularListing`, `VariableWL_CertifiedRecipe`, `VariableWL_Circuit`, `VariableWL_CircuitCatalog`, `VariableWL_Completeness`, `VariableWL_Coordinates`, `VariableWL_Decision`, `VariableWL_Descriptor`, `VariableWL_Encoding`, `VariableWL_ExactProjection`, `VariableWL_ExponentialRecipe`, `VariableWL_GeneralGame`, `VariableWL_GeneralReduction`, `VariableWL_MachineReduction`, `VariableWL_MatrixOutput`, `VariableWL_NumericProgram`, `VariableWL_NumericRefinement`, `VariableWL_OneHead`, `VariableWL_PolyRecipe`, `VariableWL_PortGraph`, `VariableWL_PortListing`, `VariableWL_PrefixAlphabet`, `VariableWL_PrefixDescriptor`, `VariableWL_PrefixListing`, `VariableWL_PrefixParts`, `VariableWL_PrefixWiring`, `VariableWL_Procedure`, `VariableWL_ProductCellular`, `VariableWL_ProductImages`, `VariableWL_Program`, `VariableWL_Recipe`, `VariableWL_Refinement`, `VariableWL_Stack`, `VariableWL_StackSimulation`, `VariableWL_SubcubicGame`, `VariableWL_Subdivision`, `VariableWL_TypedGame`, `VariableWL_UnaryPower`, `VariableWL_Wrapping`.
--
--   **Imports.** It imports the published bundle `Def_VariableWL`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ6Wl002`.
-- source:
--   OpenAI, Variable-dimension Weisfeiler–Leman equivalence on general and subcubic graphs, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 133; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Variable-dimension-Weisfeiler-Leman-equivalence-on-general-and-subcubic-graphs-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_VariableWL

section
-- module Solutions.OAIQ6_WL.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Affine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6

namespace VariableWL

class FiniteNumbering (A : Type uVariable1) [Fintype A] where
  equiv : A ≃ Fin (Fintype.card A)

noncomputable instance (priority := 10) defaultFiniteNumbering (A : Type uVariable2) [Fintype A] :
    FiniteNumbering A := ⟨Fintype.equivFin A⟩
noncomputable def enumeration (A : Type uVariable4) [Fintype A] [FiniteNumbering A] :
    A ≃ Fin (Fintype.card A) := FiniteNumbering.equiv
end VariableWL

namespace VariableWL.Affine

abbrev Bit := ZMod 2
abbrev Vec (d : ℕ) := Fin d → Bit
abbrev SquareVal (d e : ℕ) := (Vec d × Vec e) × (Bit × Bit)

open scoped CharTwo

variable {d e : ℕ}

def boundary (L : Vec d →ₗ[Bit] Bit) (R : Vec e →ₗ[Bit] Bit)
    (z : SquareVal d e) : Bit :=
  L z.1.1 + R z.1.2 + z.2.1 + z.2.2

def Fiber (L : Vec d →ₗ[Bit] Bit) (R : Vec e →ₗ[Bit] Bit) (c : Bit) :=
  { z : SquareVal d e | boundary L R z = c }

@[simp] theorem boundary_add (L : Vec d →ₗ[Bit] Bit) (R : Vec e →ₗ[Bit] Bit)
    (z w : SquareVal d e) : boundary L R (z + w) = boundary L R z + boundary L R w := by
  simp only [boundary, Prod.fst_add, Prod.snd_add, map_add]
  ring

@[simp] theorem boundary_zero (L : Vec d →ₗ[Bit] Bit) (R : Vec e →ₗ[Bit] Bit) :
    boundary L R 0 = 0 := by
  simp [boundary]

theorem fiber_nonempty (L : Vec d →ₗ[Bit] Bit) (R : Vec e →ₗ[Bit] Bit) (c : Bit) :
    (Fiber L R c).Nonempty := by
  exact ⟨((0, 0), (c, 0)), by simp [Fiber, boundary]⟩

end VariableWL.Affine

namespace VariableWL.Markers

abbrev Bit := ZMod 2
open scoped CharTwo

variable {V : Type uVariable5} {G : SimpleGraph V}

def walkSum (ω : V → V → Bit) : {u v : V} → G.Walk u v → Bit
  | _, _, .nil => 0
  | u, _, .cons (v := v) _ p => ω u v + walkSum ω p

@[simp] theorem walkSum_nil (ω : V → V → Bit) (u : V) :
    walkSum ω (SimpleGraph.Walk.nil : G.Walk u u) = 0 := rfl

@[simp] theorem walkSum_cons (ω : V → V → Bit) {u v w : V}
    (h : G.Adj u v) (p : G.Walk v w) :
    walkSum ω (.cons h p) = ω u v + walkSum ω p := rfl

@[simp] theorem walkSum_append (ω : V → V → Bit) {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) :
    walkSum ω (p.append q) = walkSum ω p + walkSum ω q := by
  induction p with
  | nil => simp [walkSum]
  | cons h p ih => simp [SimpleGraph.Walk.cons_append, walkSum, ih, add_assoc]

@[simp] theorem walkSum_reverse (ω : V → V → Bit)
    (hsym : ∀ u v, G.Adj u v → ω u v = ω v u) {u v : V} (p : G.Walk u v) :
    walkSum ω p.reverse = walkSum ω p := by
  induction p with
  | nil => simp [walkSum]
  | @cons u v w h p ih =>
      simp only [SimpleGraph.Walk.reverse_cons, walkSum_append, ih, walkSum_cons,
        walkSum_nil, add_zero]
      rw [← hsym u v h, add_comm]

end VariableWL.Markers

namespace VariableWL.ScalarImages

abbrev Bit := ZMod 2
abbrev Pair := Bit × Bit

def sum (x : Pair) : Bit := x.1 + x.2

def buffer (D : Set Bit) : Set Pair := {x | sum x ∈ D}

open scoped CharTwo

theorem buffer_nonempty {D : Set Bit} (hD : D.Nonempty) : (buffer D).Nonempty := by
  rcases hD with ⟨a, ha⟩
  exact ⟨(0, a), by simpa [buffer, sum] using ha⟩

theorem buffer_image_sum (D : Set Bit) : sum '' buffer D = D := by
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro ha
    exact ⟨(0, a), by simpa [buffer, sum] using ha, by simp [sum]⟩

theorem buffer_image_fst {D : Set Bit} (hD : D.Nonempty) :
    Prod.fst '' buffer D = Set.univ := by
  rcases hD with ⟨d, hd⟩
  apply Set.eq_univ_of_forall
  intro a
  refine ⟨(a, d + a), ?_, rfl⟩
  simpa [buffer, sum, add_comm, add_left_comm] using hd

theorem buffer_image_snd {D : Set Bit} (hD : D.Nonempty) :
    Prod.snd '' buffer D = Set.univ := by
  rcases hD with ⟨d, hd⟩
  apply Set.eq_univ_of_forall
  intro a
  refine ⟨(d + a, a), ?_, rfl⟩
  simpa [buffer, sum, add_assoc] using hd

def andWitness (p q : Prop) : Set Pair :=
  {x | (p → x.1 = 0) ∧ (q → x.2 = 0)}

theorem andWitness_nonempty (p q : Prop) : (andWitness p q).Nonempty :=
  ⟨(0, 0), ⟨fun _ => rfl, fun _ => rfl⟩⟩

theorem andWitness_fst (p q : Prop) :
    Prod.fst '' andWitness p q = {a : Bit | p → a = 0} := by
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx.1
  · intro ha
    exact ⟨(a, 0), ⟨ha, fun _ => rfl⟩, rfl⟩

theorem andWitness_snd (p q : Prop) :
    Prod.snd '' andWitness p q = {a : Bit | q → a = 0} := by
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx.2
  · intro ha
    exact ⟨(0, a), ⟨fun _ => rfl, ha⟩, rfl⟩

theorem andWitness_sum (p q : Prop) :
    sum '' andWitness p q = {a : Bit | p ∧ q → a = 0} := by
  classical
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩ ⟨hp, hq⟩
    simp [sum, hx.1 hp, hx.2 hq]
  · intro ha
    by_cases hp : p
    · refine ⟨(0, a), ⟨fun _ => rfl, fun hq => ha ⟨hp, hq⟩⟩, ?_⟩
      simp [sum]
    · refine ⟨(a, 0), ⟨fun h => (hp h).elim, fun _ => rfl⟩, ?_⟩
      simp [sum]

end VariableWL.ScalarImages

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Refinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6

namespace VariableWL

@[simp] theorem histogram_card (G : Graph) (k s : ℕ) :
    (histogram G k s).card = G.order ^ k := by
  simp [histogram, Tuple]

end VariableWL

namespace VariableWL

@[simp] theorem histogram_fst (G : Graph) (k s : ℕ) :
    (histogram G k (s+1)).map Prod.fst = histogram G k s := by
  exact (Multiset.map_map Prod.fst (color G k (s+1)) Finset.univ.val)

end VariableWL

universe uGame1 uGame2 uGame3 uGame4 uGame5 uGame6 uGame7

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Subdivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9

namespace VariableWL.Subdivision

variable {P : Type uVariable1} {E : Type uVariable2} {n : ℕ}

abbrev Vertex (P : Type uVariable3) (E : Type uVariable4) (n : ℕ) := P ⊕ (E × Fin n)
abbrev Link (E : Type uVariable5) (n : ℕ) := E × Fin (n+1)

def left (src : E → P) (l : Link E n) : Vertex P E n :=
  if h : l.2.val = 0 then .inl (src l.1)
  else .inr (l.1, ⟨l.2.val - 1, by omega⟩)

def right (dst : E → P) (l : Link E n) : Vertex P E n :=
  if h : l.2.val = n then .inl (dst l.1)
  else .inr (l.1, ⟨l.2.val, by omega⟩)

theorem endpoints_ne (hn : 0 < n) (src dst : E → P) (l : Link E n) :
    left src l ≠ right dst l := by
  unfold left right
  split_ifs with h₀ h₁ h₁
  · omega
  · simp
  · simp
  · intro h
    have hh := congrArg (fun x : Vertex P E n =>
      match x with | .inl _ => 0 | .inr x => x.2.val) h
    simp only at hh
    omega

def supportGraph (hn : 0 < n) (src dst : E → P) (S : Set (Link E n)) :
    SimpleGraph (Vertex P E n) where
  Adj v w := ∃ l ∈ S,
    (v = left src l ∧ w = right dst l) ∨ (v = right dst l ∧ w = left src l)
  symm := ⟨by
    rintro v w ⟨l, hl, h⟩
    exact ⟨l, hl, h.elim (fun h => Or.inr h.symm) (fun h => Or.inl h.symm)⟩⟩
  loopless := ⟨by
    rintro v ⟨l, _, h⟩
    exact endpoints_ne hn src dst l (h.elim (fun h => h.1.symm.trans h.2)
      (fun h => h.2.symm.trans h.1))⟩

end VariableWL.Subdivision

namespace VariableWL.Markers
open scoped CharTwo
variable {V : Type uVariable9} {G : SimpleGraph V}

@[simp] theorem walkSum_zero {u v : V} (p : G.Walk u v) :
    walkSum (fun _ _ => 0) p = 0 := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp [walkSum, ih]

end VariableWL.Markers

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Wrapping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10 uVariable11

namespace VariableWL.Wrapping
open scoped CharTwo
open Markers
abbrev Bit := ZMod 2

variable {I : Type uVariable1} {V : Type uVariable2} [DecidableEq I] {G : SimpleGraph V}

structure RowDiagram (G : SimpleGraph V) (next : Equiv.Perm I) where
  boundary : V → I
  horizontal : V → V → Option I
  symmetric : ∀ u v, G.Adj u v → horizontal u v = horizontal v u
  shape : ∀ u v, G.Adj u v →
    match horizontal u v with
    | none => boundary u = boundary v
    | some i => (boundary u = i ∧ boundary v = next i) ∨
        (boundary v = i ∧ boundary u = next i)

namespace RowDiagram

variable {next : Equiv.Perm I} (D : RowDiagram G next)

def rowWeight (i : I) (u v : V) : Bit := if D.horizontal u v = some i then 1 else 0

def Wraps (marked : I) : Prop :=
  ∃ v : V, ∃ p : G.Walk v v, walkSum (D.rowWeight marked) p = 1

end RowDiagram

end VariableWL.Wrapping

namespace VariableWL.Wrapping
variable {I : Type uVariable9} {B : Type uVariable10} {L : Type uVariable11} [Fintype I] [DecidableEq I] [DecidableEq B]

theorem finRotate_no_fixed {r : ℕ} (hr : 2 ≤ r) (i : Fin r) : finRotate r i ≠ i := by
  have h : i ∈ (finRotate r).support := by
    rw [support_finRotate_of_le hr]
    exact Finset.mem_univ i
  exact Equiv.Perm.mem_support.mp h

end VariableWL.Wrapping

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_ProductImages
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

structure Instance where
  dimension : P → ℕ
  dimension_one_or_two : ∀ p, dimension p = 1 ∨ dimension p = 2
  source : E → P
  target : E → P
  domain : E → Fin r → Finset Bool
  domain_nonempty : ∀ e i, (domain e i).Nonempty
  map : E → Fin r → Bool → Bool
  map_injective : ∀ e i, Set.InjOn (map e i) (domain e i)
  linearLeft : ∀ e, Vec (dimension (source e)) →ₗ[Bit] Bit
  linearRight : ∀ e, Vec (dimension (target e)) →ₗ[Bit] Bit
  constantLeft : E → Bit
  constantRight : E → Bit

namespace Instance
variable {r : ℕ} {P : Type uVariable3} {E : Type uVariable4} (J : Instance r P E)

abbrev Address (r : ℕ) := Fin r → Bool

def Allowed (e : E) (a : Address r) : Prop := ∀ i, a i ∈ J.domain e i

def mapAddress (e : E) (a : Address r) : Address r := fun i => J.map e i (a i)

def leftForm (e : E) (v : Vec (J.dimension (J.source e))) : Bit :=
  J.linearLeft e v + J.constantLeft e

def rightForm (e : E) (v : Vec (J.dimension (J.target e))) : Bit :=
  J.linearRight e v + J.constantRight e

structure Witness where
  values : ∀ p : P, Address r → Set (Vec (J.dimension p))
  nonempty : ∀ p a, (values p a).Nonempty
  images : ∀ e a, J.Allowed e a →
    J.leftForm e '' values (J.source e) a =
      J.rightForm e '' values (J.target e) (J.mapAddress e a)

namespace Witness
variable {J} (Q : J.Witness)

def wireValues (e : E) (a : Address r) : Set Bit :=
  J.leftForm e '' Q.values (J.source e) a

end Witness

theorem exists_ambient (e : E) (i : Fin r) :
    ∃ f : Equiv.Perm Bool, ∀ a ∈ J.domain e i, f a = J.map e i a := by
  obtain ⟨f,hf⟩ := Equiv.Perm.exists_extending_pair
    (fun a : {a // a ∈ J.domain e i} => a.val)
    (fun a : {a // a ∈ J.domain e i} => J.map e i a.val)
    Subtype.val_injective (fun a b h => Subtype.ext (J.map_injective e i a.property b.property h))
  exact ⟨f, fun a ha => hf ⟨a,ha⟩⟩

noncomputable def ambient (e : E) (i : Fin r) : Equiv.Perm Bool :=
  (J.exists_ambient e i).choose

open Subdivision
variable {n : ℕ}

def labels : Vertex P E n → Fin r → Finset Bool
  | .inl _, _ => Finset.univ
  | .inr (e,_), i => J.domain e i

def Matches (l : Link E n) (i : Fin r) (a b : Bool) : Prop :=
  a ∈ J.domain l.1 i ∧ b = if l.2.val = n then J.map l.1 i a else a

theorem matches_left (l : Link E n) (i : Fin r) {a b : Bool} (h : J.Matches l i a b) :
    a ∈ J.labels (left J.source l) i := by
  unfold left
  split_ifs <;> simp only [labels]
  · exact Finset.mem_univ _
  · exact h.1

theorem matches_right (l : Link E n) (i : Fin r) {a b : Bool} (h : J.Matches l i a b) :
    b ∈ J.labels (right J.target l) i := by
  unfold right
  split_ifs with hn
  · exact Finset.mem_univ _
  · simp only [labels]
    rw [h.2, ite_eq_right hn]
    exact h.1

noncomputable def alignment (cut : E → Fin (n+1)) :
    Vertex P E n → Fin r → Equiv.Perm Bool
  | .inl _, _ => Equiv.refl _
  | .inr (e,j), i => if j.val < (cut e).val then Equiv.refl _ else J.ambient e i

end Instance
end VariableWL.ProductImages

namespace VariableWL.ProductImages.Instance
open VariableWL.Affine Subdivision
variable {r n : ℕ} {P : Type uVariable5} {E : Type uVariable6} (J : ProductImages.Instance r P E)

abbrev Shifts (n : ℕ) := (∀ p, Vec (J.dimension p)) × (E × Fin n → Bit)

def shiftLeft (h : J.Shifts n) (l : Link E n) : Bit :=
  if h₀ : l.2.val = 0 then J.leftForm l.1 (h.1 (J.source l.1))
  else h.2 (l.1, ⟨l.2.val-1, by omega⟩)

def shiftRight (h : J.Shifts n) (l : Link E n) : Bit :=
  if h₁ : l.2.val = n then J.rightForm l.1 (h.1 (J.target l.1))
  else h.2 (l.1, ⟨l.2.val, by omega⟩)

def ShiftSystem (S : Set (Link E n)) (h : J.Shifts n) : Prop :=
  ∀ l ∈ S, J.shiftLeft h l = J.shiftRight h l

end VariableWL.ProductImages.Instance

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Blocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10 uVariable11 uVariable12 uVariable13 uVariable14 uVariable15 uVariable16 uVariable17 uVariable18

namespace VariableWL.Blocks
open Subdivision
variable {r n : ℕ} {P : Type uVariable1} {E : Type uVariable2}

structure Horizontal (r n : ℕ) (P : Type uVariable3) (E : Type uVariable4) where
  row : Fin r
  type : Vertex P E n
  first : Bool
  last : Bool
  deriving DecidableEq

structure Vertical (r n : ℕ) (E : Type uVariable5) where
  row : Fin r
  link : Link E n
  label : Bool
  deriving DecidableEq

structure Square (r n : ℕ) (E : Type uVariable6) where
  row : Fin r
  link : Link E n
  first : Bool
  last : Bool
  deriving DecidableEq

abbrev Corner (r n : ℕ) (P : Type uVariable7) (E : Type uVariable8) := Fin r × Vertex P E n × Bool
abbrev Readout (r n : ℕ) (P : Type uVariable9) (E : Type uVariable10) := Horizontal r n P E ⊕ Vertical r n E
abbrev RawBlock (r n : ℕ) (P : Type uVariable11) (E : Type uVariable12) := Horizontal r n P E ⊕ Square r n E

variable (J : ProductImages.Instance r P E)

def matchOutput (l : Link E n) (i : Fin r) (a : Bool) : Bool :=
  if l.2.val = n then J.map l.1 i a else a

def ValidHorizontal (h : Horizontal r n P E) : Prop :=
  h.first ∈ J.labels h.type h.row ∧ h.last ∈ J.labels h.type (finRotate r h.row)

def ValidSquare (s : Square r n E) : Prop :=
  s.first ∈ J.domain s.link.1 s.row ∧ s.last ∈ J.domain s.link.1 (finRotate r s.row)

def Valid : RawBlock r n P E → Prop
  | .inl h => ValidHorizontal J h
  | .inr s => ValidSquare J s

abbrev Block := { b : RawBlock r n P E // Valid J b }

def row : RawBlock r n P E → Fin r
  | .inl h => h.row
  | .inr s => s.row

def squareLeft (s : Square r n E) : Horizontal r n P E :=
  ⟨s.row, left J.source s.link, s.first, s.last⟩

def squareRight (s : Square r n E) : Horizontal r n P E :=
  ⟨s.row, right J.target s.link, matchOutput J s.link s.row s.first,
    matchOutput J s.link (finRotate r s.row) s.last⟩

def squareBottom (s : Square r n E) : Vertical r n E := ⟨s.row, s.link, s.first⟩
def squareTop (s : Square r n E) : Vertical r n E := ⟨finRotate r s.row, s.link, s.last⟩

def HasReadout : RawBlock r n P E → Readout r n P E → Prop
  | .inl h, a => a = .inl h
  | .inr s, a => a = .inl (squareLeft J s) ∨ a = .inl (squareRight J s) ∨
      a = .inr (squareBottom s) ∨ a = .inr (squareTop s)

def end0 : Readout r n P E → Corner r n P E
  | .inl h => (h.row, h.type, h.first)
  | .inr v => (v.row, left J.source v.link, v.label)

def end1 : Readout r n P E → Corner r n P E
  | .inl h => (finRotate r h.row, h.type, h.last)
  | .inr v => (v.row, right J.target v.link, matchOutput J v.link v.row v.label)

theorem readout_ne (hr : 2 ≤ r) (hn : 0 < n) (a : Readout r n P E) :
    end0 J a ≠ end1 J a := by
  cases a with
  | inl h =>
    intro he
    exact Wrapping.finRotate_no_fixed hr h.row (congrArg Prod.fst he).symm
  | inr v =>
    intro he
    exact endpoints_ne hn J.source J.target v.link (congrArg (fun c => c.2.1) he)

def diagram (hr : 2 ≤ r) (hn : 0 < n) (U : Set (Block (n := n) J)) :
    SimpleGraph (Corner r n P E) where
  Adj v w := ∃ b ∈ U, ∃ a, HasReadout J b.val a ∧
    ((v = end0 J a ∧ w = end1 J a) ∨ (v = end1 J a ∧ w = end0 J a))
  symm := ⟨by
    rintro v w ⟨b,hb,a,ha,h⟩
    exact ⟨b,hb,a,ha,h.elim (fun h => Or.inr h.symm) (fun h => Or.inl h.symm)⟩⟩
  loopless := ⟨by
    rintro v ⟨b,hb,a,ha,h⟩
    exact readout_ne J hr hn a (h.elim (fun h => h.1.symm.trans h.2)
      (fun h => h.2.symm.trans h.1))⟩

theorem finRotate_twice_ne (hr : 3 ≤ r) (i : Fin r) : finRotate r (finRotate r i) ≠ i := by
  have : NeZero r := ⟨by omega⟩
  intro he
  have hh : (1 : Fin r) + 1 = 0 := by
    apply add_left_cancel (a := i)
    simpa only [finRotate_apply, add_assoc, add_zero] using he
  have hval := congrArg Fin.val hh
  have h1 : 1 % r = 1 := Nat.mod_eq_of_lt (by omega)
  have h2 : 2 % r = 2 := Nat.mod_eq_of_lt (by omega)
  norm_num [Fin.val_add, Fin.val_one, h1, h2] at hval

def horizontalTag (v w : Corner r n P E) : Option (Fin r) :=
  if w.1 = finRotate r v.1 then some v.1
  else if v.1 = finRotate r w.1 then some w.1 else none

theorem horizontalTag_readout (hr : 3 ≤ r) (a : Readout r n P E) :
    horizontalTag (end0 J a) (end1 J a) =
      (match a with | .inl h => some h.row | .inr _ => none) ∧
    horizontalTag (end1 J a) (end0 J a) =
      (match a with | .inl h => some h.row | .inr _ => none) := by
  cases a with
  | inl h =>
    dsimp only [horizontalTag, end0, end1]
    simp only [ite_eq_right (finRotate_twice_ne hr h.row).symm]
    exact ⟨rfl,rfl⟩
  | inr v =>
    have hne := (Wrapping.finRotate_no_fixed (by omega) v.row).symm
    dsimp only [horizontalTag, end0, end1]
    simp only [ite_eq_right hne, and_self]

def rowDiagram (hr : 3 ≤ r) (hn : 0 < n) (U : Set (Block (n := n) J)) :
    Wrapping.RowDiagram (diagram J (by omega) hn U) (finRotate r) where
  boundary := Prod.fst
  horizontal := horizontalTag
  symmetric := by
    rintro v w ⟨b,hb,a,ha,h⟩
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact (horizontalTag_readout J hr a).1.trans (horizontalTag_readout J hr a).2.symm
    · exact (horizontalTag_readout J hr a).2.trans (horizontalTag_readout J hr a).1.symm
  shape := by
    rintro v w ⟨b,hb,a,ha,h⟩
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · rw [(horizontalTag_readout J hr a).1]
      cases a with
      | inl h => exact Or.inl ⟨rfl,rfl⟩
      | inr v => rfl
    · rw [(horizontalTag_readout J hr a).2]
      cases a with
      | inl h => exact Or.inr ⟨rfl,rfl⟩
      | inr v => rfl

end VariableWL.Blocks

namespace VariableWL.Blocks
open Subdivision
variable {r n : ℕ} {P : Type uVariable13} {E : Type uVariable14} (J : ProductImages.Instance r P E)

def linksOf : RawBlock r n P E → Finset (Link E n)
  | .inl _ => ∅
  | .inr s => {s.link}

noncomputable def supportLinks (U : Finset (Block (n := n) J)) : Finset (Link E n) :=
  by classical exact U.biUnion (fun b => linksOf b.val)

theorem square_link_mem (U : Finset (Block (n := n) J)) {b : Block (n := n) J}
    (hb : b ∈ U) {s : Square r n E} (hs : b.val = .inr s) :
    s.link ∈ supportLinks J U := by
  classical
  apply Finset.mem_biUnion.mpr
  exact ⟨b,hb,by simp [hs, linksOf]⟩

noncomputable def aligned (cut : E → Fin (n+1)) (v : Corner r n P E) : Bool :=
  J.alignment cut v.2.1 v.1 v.2.2

noncomputable def firstLabel (cut : E → Fin (n+1)) : RawBlock r n P E → Bool
  | .inl h => J.alignment cut h.type h.row h.first
  | .inr s => J.alignment cut (left J.source s.link) s.row s.first

noncomputable def lastLabel (cut : E → Fin (n+1)) : RawBlock r n P E → Bool
  | .inl h => J.alignment cut h.type (finRotate r h.row) h.last
  | .inr s => J.alignment cut (left J.source s.link) (finRotate r s.row) s.last

end VariableWL.Blocks

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_BlockImages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10 uVariable11 uVariable12

namespace VariableWL.Blocks
open scoped CharTwo
open VariableWL.Affine Subdivision
variable {r n : ℕ} {P : Type uVariable1} {E : Type uVariable2} (J : ProductImages.Instance r P E)

def dimension : Vertex P E n → ℕ
  | .inl p => J.dimension p
  | .inr _ => 1

abbrev Value (t : Vertex P E n) := Vec (dimension J t)

def vectorShift (h : J.Shifts n) : ∀ t : Vertex P E n, Value J t
  | .inl p => h.1 p
  | .inr q => fun _ => h.2 q

def linkLeft (l : Link E n) : Value J (left J.source l) →ₗ[Bit] Bit := by
  unfold left
  split_ifs with hz
  · rw [dite_eq_left hz]
    exact J.linearLeft l.1
  · rw [dite_eq_right hz]
    exact LinearMap.proj (0 : Fin 1)

def linkRight (l : Link E n) : Value J (right J.target l) →ₗ[Bit] Bit := by
  unfold right
  split_ifs with hz
  · rw [dite_eq_left hz]
    exact J.linearRight l.1
  · rw [dite_eq_right hz]
    exact LinearMap.proj (0 : Fin 1)

def leftConstant (l : Link E n) : Bit := if l.2.val = 0 then J.constantLeft l.1 else 0
def rightConstant (l : Link E n) : Bit := if l.2.val = n then J.constantRight l.1 else 0

def linkConstant (l : Link E n) : Bit := leftConstant J l + rightConstant J l

theorem dependent_linear_apply {A : Type uVariable3} (d : A → ℕ) {i j : A} (he : i = j)
    (L : Vec (d i) →ₗ[Bit] Bit) (v : ∀ t, Vec (d t)) :
    (cast (congrArg (fun t => Vec (d t) →ₗ[Bit] Bit) he) L) (v j) = L (v i) := by
  subst j; rfl

theorem linkLeft_eval (h : J.Shifts n) (l : Link E n) :
    linkLeft J l (vectorShift J h (left J.source l)) + leftConstant J l =
      J.shiftLeft h l := by
  by_cases hz : l.2.val = 0
  · have he := dependent_linear_apply (dimension J) (i := .inl (J.source l.1))
      (j := left J.source l) (by simp only [left, dite_eq_left hz])
      (J.linearLeft l.1) (vectorShift J h)
    simp only [linkLeft, dite_eq_left hz, leftConstant, ite_eq_left hz,
      ProductImages.Instance.shiftLeft, ProductImages.Instance.leftForm]
    exact congrArg (fun z => z + J.constantLeft l.1) he
  · simp only [linkLeft, dite_eq_right hz, leftConstant, ite_eq_right hz, add_zero,
      ProductImages.Instance.shiftLeft]
    exact dependent_linear_apply (dimension J)
      (i := .inr (l.1, ⟨l.2.val-1, by omega⟩)) (j := left J.source l)
      (by simp only [left, dite_eq_right hz]) (LinearMap.proj (0 : Fin 1)) (vectorShift J h)

theorem linkRight_eval (h : J.Shifts n) (l : Link E n) :
    linkRight J l (vectorShift J h (right J.target l)) + rightConstant J l =
      J.shiftRight h l := by
  by_cases hz : l.2.val = n
  · have he := dependent_linear_apply (dimension J) (i := .inl (J.target l.1))
      (j := right J.target l) (by simp only [right, dite_eq_left hz])
      (J.linearRight l.1) (vectorShift J h)
    simp only [linkRight, dite_eq_left hz, rightConstant, ite_eq_left hz,
      ProductImages.Instance.shiftRight, ProductImages.Instance.rightForm]
    exact congrArg (fun z => z + J.constantRight l.1) he
  · simp only [linkRight, dite_eq_right hz, rightConstant, ite_eq_right hz, add_zero,
      ProductImages.Instance.shiftRight]
    exact dependent_linear_apply (dimension J)
      (i := .inr (l.1, ⟨l.2.val, by omega⟩)) (j := right J.target l)
      (by simp only [right, dite_eq_right hz]) (LinearMap.proj (0 : Fin 1)) (vectorShift J h)

theorem link_equation_iff (h : J.Shifts n) (l : Link E n) :
    linkLeft J l (vectorShift J h (left J.source l)) +
        linkRight J l (vectorShift J h (right J.target l)) = linkConstant J l ↔
      J.shiftLeft h l = J.shiftRight h l := by
  rw [← linkLeft_eval J h l, ← linkRight_eval J h l]
  unfold linkConstant
  constructor <;> intro he
  · have hh := congrArg (fun z => z + linkRight J l (vectorShift J h (right J.target l)) +
        leftConstant J l) he
    simpa [add_assoc, add_comm, add_left_comm] using hh
  · have hh := congrArg (fun z => z + leftConstant J l +
        linkRight J l (vectorShift J h (right J.target l))) he
    simpa [add_assoc, add_comm, add_left_comm] using hh

abbrev ReadoutValue : Readout r n P E → Type
  | .inl h => Value J h.type
  | .inr _ => Bit

abbrev Potentials := ∀ v : Corner r n P E, Value J v.2.1

def marker (marked i : Fin r) : Bit := if i = marked then 1 else 0

def potentialValues (marked : Fin r) (h : J.Shifts n) (M : Potentials (n := n) J) :
    ∀ a : Readout r n P E, ReadoutValue J a
  | .inl x => M (x.row, x.type, x.first) + M (finRotate r x.row, x.type, x.last) +
      marker marked x.row • vectorShift J h x.type
  | .inr y => linkLeft J y.link (M (y.row, left J.source y.link, y.label)) +
      linkRight J y.link (M (y.row, right J.target y.link, matchOutput J y.link y.row y.label))

theorem potential_square (marked : Fin r) (h : J.Shifts n) (M : Potentials (n := n) J)
    (s : Square r n E) (hs : J.shiftLeft h s.link = J.shiftRight h s.link) :
    linkLeft J s.link (potentialValues J marked h M (.inl (squareLeft J s))) +
      linkRight J s.link (potentialValues J marked h M (.inl (squareRight J s))) +
      potentialValues J marked h M (.inr (squareBottom s)) +
      potentialValues J marked h M (.inr (squareTop s)) =
        marker marked s.row * linkConstant J s.link := by
  have he := (link_equation_iff J h s.link).mpr hs
  dsimp only [potentialValues, squareLeft, squareRight, squareBottom, squareTop, end0, end1]
  simp only [map_add, map_smul, smul_eq_mul]
  have ht : (2 : Bit) = 0 := by decide
  linear_combination (marker marked s.row) * he +
    (linkLeft J s.link (M (s.row, left J.source s.link, s.first)) +
      linkLeft J s.link (M (finRotate r s.row, left J.source s.link, s.last)) +
      linkRight J s.link (M (s.row, right J.target s.link,
        matchOutput J s.link s.row s.first)) +
      linkRight J s.link (M (finRotate r s.row, right J.target s.link,
        matchOutput J s.link (finRotate r s.row) s.last))) * ht

def gaugePotentials (h g : J.Shifts n) (M : Potentials (n := n) J) (s : Corner r n P E → Bit) :
    Potentials (n := n) J := fun v => M v + s v • (vectorShift J g v.2.1 + vectorShift J h v.2.1)

end VariableWL.Blocks

namespace VariableWL.Blocks
open scoped CharTwo
open VariableWL.Affine Subdivision
variable {r n : ℕ} {P : Type uVariable7} {E : Type uVariable8} (J : ProductImages.Instance r P E)

theorem diagram_mono (hr : 2 ≤ r) (hn : 0 < n) {U V : Set (Block (n := n) J)}
    (h : U ⊆ V) : diagram J hr hn U ≤ diagram J hr hn V := by
  rintro u v ⟨b,hb,a,ha,hh⟩
  exact ⟨b,h hb,a,ha,hh⟩

end VariableWL.Blocks

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_BlockCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10 uVariable11 uVariable12 uVariable13 uVariable14 uVariable15 uVariable16 uVariable17 uVariable18 uVariable19 uVariable20 uVariable21

namespace VariableWL.Blocks
open Subdivision
variable {r n : ℕ} {P : Type uVariable4} {E : Type uVariable5} (J : ProductImages.Instance r P E)

def anchor : RawBlock r n P E → Corner r n P E
  | .inl h => end0 J (.inl h)
  | .inr s => end0 J (.inl (squareLeft J s))

end VariableWL.Blocks

namespace VariableWL.Blocks
open Subdivision
variable {r n : ℕ} {P : Type uVariable8} {E : Type uVariable9} (J : ProductImages.Instance r P E)

noncomputable def componentBlocks (hr : 2 ≤ r) (hn : 0 < n)
    (U : Finset (Block (n := n) J)) (c : (diagram J hr hn U).ConnectedComponent) :
    Finset (Block (n := n) J) := by
  classical
  exact U.filter fun b => (diagram J hr hn U).connectedComponentMk (anchor J b.val) = c

theorem mem_componentBlocks (hr : 2 ≤ r) (hn : 0 < n)
    (U : Finset (Block (n := n) J)) (c : (diagram J hr hn U).ConnectedComponent)
    (b : Block (n := n) J) : b ∈ componentBlocks J hr hn U c ↔
      b ∈ U ∧ (diagram J hr hn U).connectedComponentMk (anchor J b.val) = c := by
  classical
  exact Finset.mem_filter

end VariableWL.Blocks

namespace VariableWL.Blocks
open Subdivision
variable {r n : ℕ} {P : Type uVariable15} {E : Type uVariable16} (J : ProductImages.Instance r P E)

noncomputable def typesOf : RawBlock r n P E → Finset (Vertex P E n) := by
  classical
  exact fun b => match b with
    | .inl h => {h.type}
    | .inr s => {left J.source s.link, right J.target s.link}

noncomputable def supportTypes (U : Finset (Block (n := n) J)) : Finset (Vertex P E n) := by
  classical
  exact U.biUnion fun b => typesOf J b.val

noncomputable def addressAt (cut : E → Fin (n+1)) (a : Fin r → Bool)
    (t : Vertex P E n) : Fin r → Bool := fun i => (J.alignment cut t i).symm (a i)

def Recovers (cut : E → Fin (n+1)) (U : Finset (Block (n := n) J))
    (a : Fin r → Bool) : Prop := ∀ b ∈ U,
    firstLabel J cut b.val = a (row b.val) ∧
      lastLabel J cut b.val = a (finRotate r (row b.val))

end VariableWL.Blocks

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_BlockExtensions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8

namespace VariableWL.Blocks
open Subdivision ProductImages.Instance
variable {r n : ℕ} {P : Type uVariable1} {E : Type uVariable2} (J : ProductImages.Instance r P E)

def SupportConnected (hn : 0 < n) (C : Finset (Block (n := n) J)) : Prop :=
  ∀ t ∈ supportTypes J C, ∀ u ∈ supportTypes J C,
    (supportGraph hn J.source J.target (supportLinks J C)).Reachable t u

def NoReal (C : Finset (Block (n := n) J)) : Prop :=
  ∀ p, (.inl p : Vertex P E n) ∉ supportTypes J C

def Avoids (cut : E → Fin (n+1)) (C : Finset (Block (n := n) J)) : Prop :=
  ∀ l ∈ supportLinks J C, l.2 ≠ cut l.1

def AddressCondition (Q : J.Witness) (cut : E → Fin (n+1))
    (C : Finset (Block (n := n) J)) (a : Address r) (h : J.Shifts n) : Prop :=
  (∀ p, Sum.inl p ∈ supportTypes J C → h.1 p ∈ Q.values p (addressAt J cut a (.inl p))) ∧
  (NoReal J C → ∀ q, Sum.inr q ∈ supportTypes J C →
    h.2 q ∈ Q.wireValues q.1 (addressAt J cut a (.inr q)))

def Admissible (hr : 3 ≤ r) (hn : 0 < n) (marked : Fin r) (Q : J.Witness)
    (cut : E → Fin (n+1)) (C : Finset (Block (n := n) J)) (h : J.Shifts n) : Prop :=
  J.ShiftSystem (supportLinks J C) h ∧
  ∀ W ⊆ C, W.card = r → (rowDiagram J hr hn W).Wraps marked →
    ∀ a, Recovers J cut W a → AddressCondition J Q cut C a h

@[simp] theorem addressAt_real (cut : E → Fin (n+1)) (a : Address r) (p : P) :
    addressAt J cut a (.inl p) = a := rfl

end VariableWL.Blocks

namespace VariableWL.Blocks
open Subdivision ProductImages.Instance
variable {r n : ℕ} {P : Type uVariable7} {E : Type uVariable8} (J : ProductImages.Instance r P E)

def componentMap (hr : 2 ≤ r) (hn : 0 < n)
    {V U : Finset (Block (n := n) J)} (h : V ⊆ U) :
    (diagram J hr hn V).ConnectedComponent → (diagram J hr hn U).ConnectedComponent :=
  SimpleGraph.ConnectedComponent.map (SimpleGraph.Hom.ofLE (diagram_mono J hr hn h))

@[simp] theorem componentMap_mk (hr : 2 ≤ r) (hn : 0 < n)
    {V U : Finset (Block (n := n) J)} (h : V ⊆ U) (v : Corner r n P E) :
    componentMap J hr hn h ((diagram J hr hn V).connectedComponentMk v) =
      (diagram J hr hn U).connectedComponentMk v := rfl

abbrev ReadoutValues := ∀ a : Readout r n P E, ReadoutValue J a

def OffsetFamily (hr : 3 ≤ r) (hn : 0 < n) (marked : Fin r) (Q : J.Witness)
    (U : Finset (Block (n := n) J)) (F : ReadoutValues (n := n) J) : Prop :=
  ∃ cut : E → Fin (n+1), Avoids J cut U ∧
  ∃ h : (diagram J (by omega) hn U).ConnectedComponent → J.Shifts n,
  ∃ M : Potentials (n := n) J,
    (∀ c, Admissible J hr hn marked Q cut (componentBlocks J (by omega) hn U c) (h c)) ∧
    ∀ b ∈ U, ∀ a, HasReadout J b.val a →
      F a = potentialValues J marked (h ((diagram J (by omega) hn U).connectedComponentMk
        (anchor J b.val))) M a

def representedValues (hr : 2 ≤ r) (hn : 0 < n) (marked : Fin r)
    (U : Finset (Block (n := n) J))
    (h : (diagram J hr hn U).ConnectedComponent → J.Shifts n)
    (M : Potentials (n := n) J) : ReadoutValues (n := n) J :=
  fun a => potentialValues J marked (h ((diagram J hr hn U).connectedComponentMk (end0 J a))) M a

end VariableWL.Blocks

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_ExactProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10

namespace VariableWL.Blocks
open scoped CharTwo
open Subdivision ProductImages.Instance VariableWL.Affine
variable {r n : ℕ} {P : Type uVariable3} {E : Type uVariable4} (J : ProductImages.Instance r P E)

def RawValue : RawBlock r n P E → Type
  | .inl h => Value J h.type
  | .inr s => SquareVal (dimension J (left J.source s.link)) (dimension J (right J.target s.link))

instance rawValueAddCommGroup (b : RawBlock r n P E) : AddCommGroup (RawValue J b) := by
  cases b <;> dsimp only [RawValue] <;> infer_instance

noncomputable instance rawValueFintype (b : RawBlock r n P E) : Fintype (RawValue J b) := by
  cases b <;> dsimp only [RawValue] <;> infer_instance

def boundaryMap (b : RawBlock r n P E) : RawValue J b →+ Bit := by
  cases b with
  | inl h => exact 0
  | inr s =>
    exact { toFun := boundary (linkLeft J s.link) (linkRight J s.link)
            map_zero' := boundary_zero _ _
            map_add' := boundary_add _ _ }

def inhomogeneity (marked : Fin r) : RawBlock r n P E → Bit
  | .inl _ => 0
  | .inr s => marker marked s.row * linkConstant J s.link

def LegalValue (marked : Fin r) (ε : Bit) (b : RawBlock r n P E) (z : RawValue J b) : Prop :=
  boundaryMap J b z = ε * inhomogeneity J marked b

abbrev Valuation (marked : Fin r) (ε : Bit) (b : Block (n := n) J) :=
  {z : RawValue J b.val // LegalValue J marked ε b.val z}

noncomputable instance valuationFintype (marked : Fin r) (ε : Bit) (b : Block (n := n) J) :
    Fintype (Valuation J marked ε b) := Fintype.ofFinite _

theorem legal_nonempty (marked : Fin r) (ε : Bit) (b : RawBlock r n P E) :
    ∃ z : RawValue J b, LegalValue J marked ε b z := by
  cases b with
  | inl h => exact ⟨0,by simp [LegalValue, inhomogeneity, boundaryMap]⟩
  | inr s =>
    exact fiber_nonempty (linkLeft J s.link) (linkRight J s.link)
      (ε * (marker marked s.row * linkConstant J s.link))

def valueOfReadouts (F : ReadoutValues (n := n) J) : (b : RawBlock r n P E) → RawValue J b
  | .inl h => F (.inl h)
  | .inr s => ((F (.inl (squareLeft J s)), F (.inl (squareRight J s))),
      (F (.inr (squareBottom s)), F (.inr (squareTop s))))

def Carries (b : RawBlock r n P E) (z : RawValue J b)
    (a : Readout r n P E) (v : ReadoutValue J a) : Prop :=
  match b with
  | .inl h => a = .inl h ∧ HEq v z
  | .inr s =>
      (a = .inl (squareLeft J s) ∧ HEq v z.1.1) ∨
      (a = .inl (squareRight J s) ∧ HEq v z.1.2) ∨
      (a = .inr (squareBottom s) ∧ HEq v z.2.1) ∨
      (a = .inr (squareTop s) ∧ HEq v z.2.2)

theorem carries_hasReadout {b : RawBlock r n P E} {z : RawValue J b}
    {a : Readout r n P E} {v : ReadoutValue J a} (h : Carries J b z a v) : HasReadout J b a := by
  cases b with
  | inl _ => exact h.1
  | inr _ =>
    exact h.elim (fun h => Or.inl h.1)
      (fun h => h.elim (fun h => Or.inr (Or.inl h.1))
        (fun h => h.elim (fun h => Or.inr (Or.inr (Or.inl h.1)))
          (fun h => Or.inr (Or.inr (Or.inr h.1)))))

theorem carries_exists {b : RawBlock r n P E} (z : RawValue J b)
    {a : Readout r n P E} (ha : HasReadout J b a) : ∃ v, Carries J b z a v := by
  cases b with
  | inl h => cases ha; exact ⟨z,rfl,HEq.rfl⟩
  | inr s =>
    rcases ha with rfl | rfl | rfl | rfl
    · exact ⟨z.1.1,Or.inl ⟨rfl,HEq.rfl⟩⟩
    · exact ⟨z.1.2,Or.inr (Or.inl ⟨rfl,HEq.rfl⟩)⟩
    · exact ⟨z.2.1,Or.inr (Or.inr (Or.inl ⟨rfl,HEq.rfl⟩))⟩
    · exact ⟨z.2.2,Or.inr (Or.inr (Or.inr ⟨rfl,HEq.rfl⟩))⟩

theorem offsetFamily_legal (hr : 3 ≤ r) (hn : 0 < n) (marked : Fin r) (Q : J.Witness)
    (U : Finset (Block (n := n) J)) {F : ReadoutValues (n := n) J}
    (hF : OffsetFamily J hr hn marked Q U F) {b : Block (n := n) J} (hb : b ∈ U) :
    LegalValue J marked 1 b.val (valueOfReadouts J F b.val) := by
  obtain ⟨cut,hc,h,M,hh,hrep⟩ := hF
  let c := (diagram J (by omega) hn U).connectedComponentMk (anchor J b.val)
  have hbC : b ∈ componentBlocks J (by omega) hn U c :=
    (mem_componentBlocks J (by omega) hn U c b).mpr ⟨hb,rfl⟩
  have hsys := (hh c).1
  obtain ⟨b,hvalid⟩ := b
  cases b with
  | inl x => simp [LegalValue, boundaryMap, inhomogeneity]
  | inr s =>
    have hl := square_link_mem J (componentBlocks J (by omega) hn U c) hbC rfl
    have h0 := hrep ⟨.inr s,hvalid⟩ hb (.inl (squareLeft J s)) (Or.inl rfl)
    have h1 := hrep ⟨.inr s,hvalid⟩ hb (.inl (squareRight J s)) (Or.inr (Or.inl rfl))
    have h2 := hrep ⟨.inr s,hvalid⟩ hb (.inr (squareBottom s)) (Or.inr (Or.inr (Or.inl rfl)))
    have h3 := hrep ⟨.inr s,hvalid⟩ hb (.inr (squareTop s)) (Or.inr (Or.inr (Or.inr rfl)))
    change linkLeft J s.link (F (.inl (squareLeft J s))) +
      linkRight J s.link (F (.inl (squareRight J s))) + F (.inr (squareBottom s)) +
        F (.inr (squareTop s)) = 1 * (marker marked s.row * linkConstant J s.link)
    rw [h0,h1,h2,h3,one_mul]
    exact potential_square J marked (h c) M s (hsys s.link hl)

noncomputable def familyList (hr : 3 ≤ r) (hn : 0 < n) (marked : Fin r) (Q : J.Witness)
    (U : Finset (Block (n := n) J)) {F : ReadoutValues (n := n) J}
    (hF : OffsetFamily J hr hn marked Q U F) : ∀ b : ↑U, Valuation J marked 1 b.val :=
  fun b => ⟨valueOfReadouts J F b.val.val, offsetFamily_legal J hr hn marked Q U hF b.property⟩
end VariableWL.Blocks

namespace VariableWL.Blocks
open Subdivision ProductImages.Instance VariableWL.Affine
variable {r n : ℕ} {P : Type uVariable5} {E : Type uVariable6} (J : ProductImages.Instance r P E)

def OffsetLists (hr : 3 ≤ r) (hn : 0 < n) (marked : Fin r) (Q : J.Witness)
    (U : Finset (Block (n := n) J)) : Set (∀ b : ↑U, Valuation J marked 1 b.val) :=
  {ξ | ∃ F : ReadoutValues (n := n) J, OffsetFamily J hr hn marked Q U F ∧
    ∀ b : ↑U, (ξ b).val = valueOfReadouts J F b.val.val}

def restrictList (marked : Fin r) {U V : Finset (Block (n := n) J)} (hVU : V ⊆ U)
    (ξ : ∀ b : ↑U, Valuation J marked 1 b.val) : ∀ b : ↑V, Valuation J marked 1 b.val :=
  fun b => ξ ⟨b.val,hVU b.property⟩

end VariableWL.Blocks

namespace VariableWL.Blocks
open Subdivision ProductImages.Instance VariableWL.Affine
variable {r n : ℕ} {P : Type uVariable7} {E : Type uVariable8} (J : ProductImages.Instance r P E)

instance readoutValueAddCommGroup (a : Readout r n P E) : AddCommGroup (ReadoutValue J a) := by
  cases a <;> dsimp only [ReadoutValue] <;> infer_instance

noncomputable instance readoutValueFintype (a : Readout r n P E) : Fintype (ReadoutValue J a) := by
  cases a <;> dsimp only [ReadoutValue] <;> infer_instance

theorem squareLeft_ne_right (hn : 0 < n) (s : Square r n E) :
    squareLeft J s ≠ squareRight J s := by
  intro h
  exact endpoints_ne hn J.source J.target s.link (congrArg Horizontal.type h)

theorem squareBottom_ne_top (hr : 2 ≤ r) (s : Square r n E) :
    squareBottom s ≠ squareTop s := by
  intro h
  exact Wrapping.finRotate_no_fixed hr s.row (congrArg Vertical.row h).symm

theorem carries_unique (hr : 2 ≤ r) (hn : 0 < n) {b : RawBlock r n P E}
    {z : RawValue J b} {a : Readout r n P E} {v w : ReadoutValue J a}
    (hv : Carries J b z a v) (hw : Carries J b z a w) : v = w := by
  cases b with
  | inl h => exact eq_of_heq (hv.2.trans hw.2.symm)
  | inr s =>
    have hlr := squareLeft_ne_right J hn s
    have hbt := squareBottom_ne_top hr s
    rcases hv with ⟨hv,hv'⟩ | ⟨hv,hv'⟩ | ⟨hv,hv'⟩ | ⟨hv,hv'⟩ <;>
      rcases hw with ⟨hw,hw'⟩ | ⟨hw,hw'⟩ | ⟨hw,hw'⟩ | ⟨hw,hw'⟩
    all_goals first | exact eq_of_heq (hv'.trans hw'.symm) | exfalso; aesop

noncomputable def readout {b : RawBlock r n P E} (z : RawValue J b)
    {a : Readout r n P E} (ha : HasReadout J b a) : ReadoutValue J a :=
  (carries_exists J z ha).choose

theorem readout_carries {b : RawBlock r n P E} (z : RawValue J b)
    {a : Readout r n P E} (ha : HasReadout J b a) : Carries J b z a (readout J z ha) :=
  (carries_exists J z ha).choose_spec

theorem readout_eq (hr : 2 ≤ r) (hn : 0 < n) {b : RawBlock r n P E}
    {z : RawValue J b} {a : Readout r n P E} (ha : HasReadout J b a)
    {v : ReadoutValue J a} (hv : Carries J b z a v) : readout J z ha = v :=
  carries_unique J hr hn (readout_carries J z ha) hv

end VariableWL.Blocks

namespace VariableWL.Blocks
variable {r n : ℕ} {P : Type uVariable9} {E : Type uVariable10} [Fintype P] [Fintype E]

noncomputable instance horizontalFintype : Fintype (Horizontal r n P E) := by
  classical
  refine Fintype.ofInjective (fun h => (h.row,h.type,h.first,h.last)) ?_
  rintro ⟨a,b,c,d⟩ ⟨a',b',c',d'⟩ h
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  rfl

noncomputable instance verticalFintype : Fintype (Vertical r n E) := by
  classical
  refine Fintype.ofInjective (fun h => (h.row,h.link,h.label)) ?_
  rintro ⟨a,b,c⟩ ⟨a',b',c'⟩ h
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨rfl,rfl,rfl⟩
  rfl

noncomputable instance squareFintype : Fintype (Square r n E) := by
  classical
  refine Fintype.ofInjective (fun h => (h.row,h.link,h.first,h.last)) ?_
  rintro ⟨a,b,c,d⟩ ⟨a',b',c',d'⟩ h
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  rfl

noncomputable instance blockFintype (J : ProductImages.Instance r P E) : Fintype (Block (n := n) J) :=
  Fintype.ofFinite _
end VariableWL.Blocks

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_GeneralGame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6

namespace VariableWL.General
open Blocks VariableWL.Affine
variable {r n : ℕ} {P : Type uVariable1} {E : Type uVariable2} (J : ProductImages.Instance r P E)
variable (marked : Fin r)

abbrev Base (ε : Bit) := Σ b : Block (n := n) J, Valuation J marked ε b

def Agree {ε ε' : Bit} (v : Base (n := n) J marked ε) (w : Base (n := n) J marked ε') : Prop :=
  ∀ a (hv : HasReadout J v.1.val a) (hw : HasReadout J w.1.val a),
    readout J v.2.val hv = readout J w.2.val hw

end VariableWL.General

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_GeneralReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10

namespace VariableWL.Blocks
attribute [local instance] Classical.propDecidable
open VariableWL.Affine
variable {r n : ℕ} {P : Type uVariable1} {E : Type uVariable2} (J : ProductImages.Instance r P E) (marked : Fin r)

noncomputable def completeList (U : Finset (Block (n := n) J))
    (ξ : ∀ b : ↑U, Valuation J marked 1 b.val) : ∀ b : Block (n := n) J, Valuation J marked 1 b := by
  classical
  exact fun b => if h : b ∈ U then ξ ⟨b,h⟩ else
    ⟨Classical.choose (legal_nonempty J marked 1 b.val),Classical.choose_spec (legal_nonempty J marked 1 b.val)⟩

def GlobalPool (hr : 3 ≤ r) (hn : 0 < n) (Q : J.Witness)
    (U : Finset (Block (n := n) J)) : Set (∀ b : Block (n := n) J, Valuation J marked 1 b) :=
  {ξ | (fun b : ↑U => ξ b.val) ∈ OffsetLists J hr hn marked Q U}

end VariableWL.Blocks

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_BlockGame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7

namespace VariableWL.Blocks
open scoped CharTwo
open Subdivision VariableWL.Affine
variable {r n : ℕ} {P : Type uVariable1} {E : Type uVariable2} (J : ProductImages.Instance r P E) (marked : Fin r)

structure RingSystem where
  lists : (b : Fin r → Block (n := n) J) → Set (∀ i, Valuation J marked 1 (b i))
  nonempty : ∀ b, (lists b).Nonempty
  compatible : ∀ b y, y ∈ lists b → ∀ i j, General.Agree J marked ⟨b i,y i⟩ ⟨b j,y j⟩
  transfer : ∀ b y, y ∈ lists b → ∀ c,
    ∃ z ∈ lists c, ∀ i, General.Agree J marked ⟨b i,y i⟩ ⟨c i,z i⟩

abbrev TypeAddress (t : Vertex P E n) :=
  {a : Fin r → Bool // ∀ i, a i ∈ J.labels t i}

def siteRing (t : Vertex P E n) (a : TypeAddress J t) (i : Fin r) : Block (n := n) J :=
  ⟨.inl ⟨i,t,a.val i,a.val (finRotate r i)⟩,a.property i,a.property (finRotate r i)⟩

def leftAddress (l : Link E n) (a : ProductImages.Instance.Address r) (ha : J.Allowed l.1 a) :
    TypeAddress J (left J.source l) :=
  ⟨a,fun i => J.matches_left l i ⟨ha i,rfl⟩⟩

def rightAddress (l : Link E n) (a : ProductImages.Instance.Address r) (ha : J.Allowed l.1 a) :
    TypeAddress J (right J.target l) :=
  ⟨fun i => matchOutput J l i (a i),fun i => J.matches_right l i ⟨ha i,rfl⟩⟩

def squareRing (l : Link E n) (a : ProductImages.Instance.Address r) (ha : J.Allowed l.1 a)
    (i : Fin r) : Block (n := n) J :=
  ⟨.inr ⟨i,l,a i,a (finRotate r i)⟩,ha i,ha (finRotate r i)⟩

noncomputable def ringSum {t : Vertex P E n} {a : TypeAddress J t}
    (y : ∀ i, Valuation J marked 1 (siteRing J t a i)) : Value J t := ∑ i, (y i).val

def Attained (F : RingSystem J marked (n := n)) (t : Vertex P E n) (a : TypeAddress J t) :
    Set (Value J t) := ringSum J marked '' F.lists (siteRing J t a)

theorem attained_nonempty (F : RingSystem J marked (n := n)) (t : Vertex P E n) (a : TypeAddress J t) :
    (Attained J marked F t a).Nonempty := (F.nonempty _).image _

theorem agree_carries (hr : 2 ≤ r) (hn : 0 < n) {ε ε' : Bit}
    {b c : Block (n := n) J} {y : Valuation J marked ε b} {z : Valuation J marked ε' c}
    (h : General.Agree J marked ⟨b,y⟩ ⟨c,z⟩) {a : Readout r n P E}
    {v w : ReadoutValue J a} (hv : Carries J b.val y.val a v)
    (hw : Carries J c.val z.val a w) : v = w := by
  have hh := h a (carries_hasReadout J hv) (carries_hasReadout J hw)
  exact (readout_eq J hr hn _ hv).symm.trans (hh.trans (readout_eq J hr hn _ hw))

theorem copy_left (hr : 2 ≤ r) (hn : 0 < n) (l : Link E n)
    (a : ProductImages.Instance.Address r) (ha : J.Allowed l.1 a) (i : Fin r)
    (y : Valuation J marked 1 (siteRing J _ (leftAddress J l a ha) i))
    (z : Valuation J marked 1 (squareRing J l a ha i))
    (h : General.Agree J marked ⟨_,y⟩ ⟨_,z⟩) : y.val = z.val.1.1 := by
  exact agree_carries J marked hr hn h (a := .inl (squareLeft J ⟨i,l,a i,a (finRotate r i)⟩))
    ⟨rfl,HEq.rfl⟩ (Or.inl ⟨rfl,HEq.rfl⟩)

theorem copy_right (hr : 2 ≤ r) (hn : 0 < n) (l : Link E n)
    (a : ProductImages.Instance.Address r) (ha : J.Allowed l.1 a) (i : Fin r)
    (y : Valuation J marked 1 (siteRing J _ (rightAddress J l a ha) i))
    (z : Valuation J marked 1 (squareRing J l a ha i))
    (h : General.Agree J marked ⟨_,y⟩ ⟨_,z⟩) : y.val = z.val.1.2 := by
  exact agree_carries J marked hr hn h (a := .inl (squareRight J ⟨i,l,a i,a (finRotate r i)⟩))
    ⟨rfl,HEq.rfl⟩ (Or.inr (Or.inl ⟨rfl,HEq.rfl⟩))

theorem squareRing_vertical (hr : 2 ≤ r) (hn : 0 < n) (F : RingSystem J marked (n := n))
    (l : Link E n) (a : ProductImages.Instance.Address r) (ha : J.Allowed l.1 a)
    {z : ∀ i, Valuation J marked 1 (squareRing J l a ha i)} (hz : z ∈ F.lists _)
    (i : Fin r) : (z i).val.2.2 = (z (finRotate r i)).val.2.1 := by
  exact agree_carries J marked hr hn (F.compatible _ z hz i (finRotate r i))
    (a := .inr (squareTop ⟨i,l,a i,a (finRotate r i)⟩))
    (Or.inr (Or.inr (Or.inr ⟨rfl,HEq.rfl⟩)))
    (Or.inr (Or.inr (Or.inl ⟨rfl,HEq.rfl⟩)))

theorem squareRing_equation (hr : 2 ≤ r) (hn : 0 < n) (F : RingSystem J marked (n := n))
    (l : Link E n) (a : ProductImages.Instance.Address r) (ha : J.Allowed l.1 a)
    {z : ∀ i, Valuation J marked 1 (squareRing J l a ha i)} (hz : z ∈ F.lists _) :
    linkLeft J l (∑ i, (z i).val.1.1) + linkRight J l (∑ i, (z i).val.1.2) = linkConstant J l := by
  have he (i : Fin r) : linkLeft J l (z i).val.1.1 + linkRight J l (z i).val.1.2 +
      (z i).val.2.1 + (z i).val.2.2 = marker marked i * linkConstant J l := by
    have h := (z i).property
    change linkLeft J l (z i).val.1.1 + linkRight J l (z i).val.1.2 +
      (z i).val.2.1 + (z i).val.2.2 = 1 * (marker marked i * linkConstant J l) at h
    simpa only [one_mul] using h
  have hs := congrArg (fun f : Fin r → Bit => ∑ i, f i) (funext he)
  simp only [Finset.sum_add_distrib] at hs
  have hv : (∑ i, (z i).val.2.2) = ∑ i, (z i).val.2.1 := by
    simp_rw [squareRing_vertical J marked hr hn F l a ha hz]
    exact Equiv.sum_comp (finRotate r) (fun i => (z i).val.2.1)
  rw [hv] at hs
  have hm : (∑ i, marker marked i * linkConstant J l) = linkConstant J l := by
    simp [marker]
  rw [hm] at hs
  simpa only [map_sum,add_assoc,CharTwo.add_self_eq_zero,add_zero] using hs

theorem agree_symm {ε ε' : Bit} {v : General.Base (n := n) J marked ε}
    {w : General.Base (n := n) J marked ε'} (h : General.Agree J marked v w) :
    General.Agree J marked w v := fun a hw hv => (h a hv hw).symm

theorem attained_link_forward (hr : 2 ≤ r) (hn : 0 < n) (F : RingSystem J marked (n := n))
    (l : Link E n) (a : ProductImages.Instance.Address r) (ha : J.Allowed l.1 a)
    {v : Value J (left J.source l)} (hv : v ∈ Attained J marked F _ (leftAddress J l a ha)) :
    ∃ w ∈ Attained J marked F _ (rightAddress J l a ha),
      linkLeft J l v + linkRight J l w = linkConstant J l := by
  obtain ⟨y,hy,rfl⟩ := hv
  obtain ⟨z,hz,hyz⟩ := F.transfer _ y hy (squareRing J l a ha)
  obtain ⟨w,hw,hzw⟩ := F.transfer _ z hz (siteRing J _ (rightAddress J l a ha))
  refine ⟨ringSum J marked w,⟨w,hw,rfl⟩,?_⟩
  have hl := fun i => copy_left J marked hr hn l a ha i (y i) (z i) (hyz i)
  have hr' := fun i => copy_right J marked hr hn l a ha i (w i) (z i) (agree_symm J marked (hzw i))
  simpa only [ringSum,hl,hr'] using squareRing_equation J marked hr hn F l a ha hz

theorem attained_link_reverse (hr : 2 ≤ r) (hn : 0 < n) (F : RingSystem J marked (n := n))
    (l : Link E n) (a : ProductImages.Instance.Address r) (ha : J.Allowed l.1 a)
    {w : Value J (right J.target l)} (hw : w ∈ Attained J marked F _ (rightAddress J l a ha)) :
    ∃ v ∈ Attained J marked F _ (leftAddress J l a ha),
      linkLeft J l v + linkRight J l w = linkConstant J l := by
  obtain ⟨y,hy,rfl⟩ := hw
  obtain ⟨z,hz,hyz⟩ := F.transfer _ y hy (squareRing J l a ha)
  obtain ⟨w,hw,hzw⟩ := F.transfer _ z hz (siteRing J _ (leftAddress J l a ha))
  refine ⟨ringSum J marked w,⟨w,hw,rfl⟩,?_⟩
  have hr' := fun i => copy_right J marked hr hn l a ha i (y i) (z i) (hyz i)
  have hl := fun i => copy_left J marked hr hn l a ha i (w i) (z i) (agree_symm J marked (hzw i))
  simpa only [ringSum,hl,hr'] using squareRing_equation J marked hr hn F l a ha hz
end VariableWL.Blocks

namespace VariableWL.Blocks
open scoped CharTwo
open Subdivision VariableWL.Affine
variable {r n : ℕ} {P : Type uVariable3} {E : Type uVariable4} (J : ProductImages.Instance r P E) (marked : Fin r)

theorem affine_of_boundary (a b c d : Bit) (h : a+b=c+d) : a+c=b+d := by
  have ht : (2 : Bit) = 0 := by decide
  linear_combination h+(c-b)*ht

theorem attained_link_images (hr : 2 ≤ r) (hn : 0 < n) (F : RingSystem J marked (n := n))
    (l : Link E n) (a : ProductImages.Instance.Address r) (ha : J.Allowed l.1 a) :
    (fun v => linkLeft J l v + leftConstant J l) '' Attained J marked F _ (leftAddress J l a ha) =
    (fun v => linkRight J l v + rightConstant J l) '' Attained J marked F _ (rightAddress J l a ha) := by
  ext x
  constructor
  · rintro ⟨v,hv,rfl⟩
    obtain ⟨w,hw,he⟩ := attained_link_forward J marked hr hn F l a ha hv
    exact ⟨w,hw,(affine_of_boundary _ _ _ _ he).symm⟩
  · rintro ⟨w,hw,rfl⟩
    obtain ⟨v,hv,he⟩ := attained_link_reverse J marked hr hn F l a ha hw
    exact ⟨v,hv,affine_of_boundary _ _ _ _ he⟩

def realAddress (p : P) (a : ProductImages.Instance.Address r) : TypeAddress J (n := n) (.inl p) :=
  ⟨a,fun _ => Finset.mem_univ _⟩

def internalAddress (e : E) (j : Fin n) (a : ProductImages.Instance.Address r) (ha : J.Allowed e a) :
    TypeAddress J (.inr (e,j)) := ⟨a,ha⟩

def realAttained (F : RingSystem J marked (n := n)) (p : P) (a : ProductImages.Instance.Address r) :
    Set (Vec (J.dimension p)) := Attained J marked F (.inl p) (realAddress J p a)

def scalarAttained (F : RingSystem J marked (n := n)) (e : E) (j : Fin n)
    (a : ProductImages.Instance.Address r) (ha : J.Allowed e a) : Set Bit :=
  (fun v => v (0 : Fin 1)) '' Attained J marked F (.inr (e,j)) (internalAddress J e j a ha)

def addressedAttained (F : RingSystem J marked (n := n)) (t : Vertex P E n)
    (a : ProductImages.Instance.Address r) : Set (Value J t) :=
  {v | ∃ h : ∀ i, a i ∈ J.labels t i, v ∈ Attained J marked F t ⟨a,h⟩}

theorem addressedAttained_eq (F : RingSystem J marked (n := n)) (t : Vertex P E n)
    (a : TypeAddress J t) : addressedAttained J marked F t a.val = Attained J marked F t a := by
  ext v
  exact ⟨fun ⟨_,h⟩ => h,fun h => ⟨a.property,h⟩⟩

theorem dependent_linear_image {A : Type uVariable5} (d : A → ℕ) {i j : A} (he : i = j)
    (L : Vec (d i) →ₗ[Bit] Bit) (Q : ∀ t, Set (Vec (d t))) (c : Bit) :
    (fun v => (cast (congrArg (fun t => Vec (d t) →ₗ[Bit] Bit) he) L) v + c) '' Q j =
      (fun v => L v + c) '' Q i := by
  subst j
  rfl

theorem left_image_evaluation (F : RingSystem J marked (n := n))
    (l : Link E n) (a : ProductImages.Instance.Address r) :
    (fun v => linkLeft J l v + leftConstant J l) '' addressedAttained J marked F (left J.source l) a =
    if h : l.2.val = 0 then J.leftForm l.1 '' addressedAttained J marked F (.inl (J.source l.1)) a
    else (fun v => v (0 : Fin 1)) '' addressedAttained J marked F (.inr (l.1,⟨l.2.val-1,by omega⟩)) a := by
  by_cases hz : l.2.val = 0
  · have he := dependent_linear_image (dimension J) (i := .inl (J.source l.1))
      (j := left J.source l) (by simp only [left,dite_eq_left hz])
      (J.linearLeft l.1) (fun t => addressedAttained J marked F t a) (J.constantLeft l.1)
    simp only [linkLeft,dite_eq_left hz,leftConstant,ite_eq_left hz]
    exact he
  · have he := dependent_linear_image (dimension J) (i := .inr (l.1,⟨l.2.val-1,by omega⟩))
      (j := left J.source l) (by simp only [left,dite_eq_right hz])
      (LinearMap.proj (0 : Fin 1)) (fun t => addressedAttained J marked F t a) 0
    simp only [linkLeft,dite_eq_right hz,leftConstant,ite_eq_right hz,add_zero]
    simp only [add_zero] at he
    exact he

theorem right_image_evaluation (F : RingSystem J marked (n := n))
    (l : Link E n) (a : ProductImages.Instance.Address r) :
    (fun v => linkRight J l v + rightConstant J l) '' addressedAttained J marked F (right J.target l) a =
    if h : l.2.val = n then J.rightForm l.1 '' addressedAttained J marked F (.inl (J.target l.1)) a
    else (fun v => v (0 : Fin 1)) '' addressedAttained J marked F (.inr (l.1,⟨l.2.val,by omega⟩)) a := by
  by_cases hz : l.2.val = n
  · have he := dependent_linear_image (dimension J) (i := .inl (J.target l.1))
      (j := right J.target l) (by simp only [right,dite_eq_left hz])
      (J.linearRight l.1) (fun t => addressedAttained J marked F t a) (J.constantRight l.1)
    simp only [linkRight,dite_eq_left hz,rightConstant,ite_eq_left hz]
    exact he
  · have he := dependent_linear_image (dimension J) (i := .inr (l.1,⟨l.2.val,by omega⟩))
      (j := right J.target l) (by simp only [right,dite_eq_right hz])
      (LinearMap.proj (0 : Fin 1)) (fun t => addressedAttained J marked F t a) 0
    simp only [linkRight,dite_eq_right hz,rightConstant,ite_eq_right hz,add_zero]
    simp only [add_zero] at he
    exact he

theorem wire_images (hr : 2 ≤ r) (hn : 0 < n) (F : RingSystem J marked (n := n))
    (l : Link E n) (a : ProductImages.Instance.Address r) (ha : J.Allowed l.1 a) :
    (if h : l.2.val = 0 then J.leftForm l.1 '' addressedAttained J marked F (.inl (J.source l.1)) a
     else (fun v => v (0 : Fin 1)) '' addressedAttained J marked F (.inr (l.1,⟨l.2.val-1,by omega⟩)) a) =
    (if h : l.2.val = n then J.rightForm l.1 '' addressedAttained J marked F (.inl (J.target l.1))
        (fun i => matchOutput J l i (a i))
     else (fun v => v (0 : Fin 1)) '' addressedAttained J marked F (.inr (l.1,⟨l.2.val,by omega⟩))
        (fun i => matchOutput J l i (a i))) := by
  rw [← left_image_evaluation J marked F l a,← right_image_evaluation J marked F l]
  exact (congrArg (Set.image _) (addressedAttained_eq J marked F _ (leftAddress J l a ha))).trans
    ((attained_link_images J marked hr hn F l a ha).trans
      (congrArg (Set.image _) (addressedAttained_eq J marked F _ (rightAddress J l a ha))).symm)

theorem attained_first (hr : 2 ≤ r) (hn : 0 < n) (F : RingSystem J marked (n := n))
    (e : E) (a : ProductImages.Instance.Address r) (ha : J.Allowed e a) :
    J.leftForm e '' realAttained J marked F (J.source e) a =
      scalarAttained J marked F e ⟨0,hn⟩ a ha := by
  have h := wire_images J marked hr hn F (e,⟨0,by omega⟩) a ha
  simp only [dite_eq_right (Ne.symm hn.ne'),matchOutput,ite_eq_right (Ne.symm hn.ne'),dite_true] at h
  exact (congrArg (Set.image (J.leftForm e)) (addressedAttained_eq J marked F _ (realAddress J (J.source e) a))).symm.trans
    (h.trans (congrArg (Set.image (fun v => v (0 : Fin 1)))
      (addressedAttained_eq J marked F _ (internalAddress J e ⟨0,hn⟩ a ha))))

theorem attained_last (hr : 2 ≤ r) (hn : 0 < n) (F : RingSystem J marked (n := n))
    (e : E) (a : ProductImages.Instance.Address r) (ha : J.Allowed e a) :
    scalarAttained J marked F e ⟨n-1,by omega⟩ a ha =
      J.rightForm e '' realAttained J marked F (J.target e) (J.mapAddress e a) := by
  have h := wire_images J marked hr hn F (e,⟨n,by omega⟩) a ha
  simp only [dite_eq_right hn.ne',matchOutput,dite_true,ite_true] at h
  exact (congrArg (Set.image (fun v => v (0 : Fin 1)))
    (addressedAttained_eq J marked F _ (internalAddress J e ⟨n-1,by omega⟩ a ha))).symm.trans
    (h.trans (congrArg (Set.image (J.rightForm e))
      (addressedAttained_eq J marked F _ (realAddress J (J.target e) (J.mapAddress e a)))))

theorem attained_internal (hr : 2 ≤ r) (hn : 0 < n) (F : RingSystem J marked (n := n))
    (e : E) (a : ProductImages.Instance.Address r) (ha : J.Allowed e a)
    (j : ℕ) (hj : j+1 < n) :
    scalarAttained J marked F e ⟨j,by omega⟩ a ha =
      scalarAttained J marked F e ⟨j+1,hj⟩ a ha := by
  have h := wire_images J marked hr hn F (e,⟨j+1,by omega⟩) a ha
  simp only [dite_eq_right (Nat.succ_ne_zero j),dite_eq_right hj.ne,matchOutput,ite_eq_right hj.ne] at h
  exact (congrArg (Set.image (fun v => v (0 : Fin 1)))
    (addressedAttained_eq J marked F _ (internalAddress J e ⟨j,by omega⟩ a ha))).symm.trans
    (h.trans (congrArg (Set.image (fun v => v (0 : Fin 1)))
      (addressedAttained_eq J marked F _ (internalAddress J e ⟨j+1,hj⟩ a ha))))

noncomputable def extractedWitness (hr : 2 ≤ r) (hn : 0 < n) (F : RingSystem J marked (n := n)) : J.Witness where
  values := realAttained J marked F
  nonempty p a := attained_nonempty J marked F _ _
  images e a ha := by
    calc
      _ = scalarAttained J marked F e ⟨0,hn⟩ a ha := attained_first J marked hr hn F e a ha
      _ = scalarAttained J marked F e ⟨n-1,by omega⟩ a ha := by
        have hs (j : ℕ) (hj : j < n) : scalarAttained J marked F e ⟨0,hn⟩ a ha =
            scalarAttained J marked F e ⟨j,hj⟩ a ha := by
          induction j with
          | zero => rfl
          | succ j ih => exact (ih (by omega)).trans (attained_internal J marked hr hn F e a ha j hj)
        exact hs _ (by omega)
      _ = _ := attained_last J marked hr hn F e a ha
end VariableWL.Blocks

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_PortGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9

namespace VariableWL.SubcubicRealization
attribute [local instance] Classical.propDecidable

structure PortGraph (V : Type uVariable1) where
  edge : (V × Fin 3) → (V × Fin 3) → Prop
  symm : ∀ {a b}, edge a b → edge b a
  unique : ∀ {a b c}, edge a b → edge a c → b = c
  different : ∀ {a b}, edge a b → a.1 ≠ b.1

def PortGraph.graph {V : Type uVariable2} (Y : PortGraph V) : SimpleGraph V where
  Adj v w := ∃ j k, Y.edge (v,j) (w,k)
  symm := ⟨fun _ _ ⟨j,k,h⟩ => ⟨k,j,Y.symm h⟩⟩
  loopless := ⟨fun _ ⟨_,_,h⟩ => Y.different h rfl⟩

@[ext] structure Vertex {V : Type uVariable3} (color : V → ℕ) where
  owner : V
  port : Fin 3
  level : ℕ
  bound : level < color owner + 2

namespace Vertex
variable {V : Type uVariable4} {color : V → ℕ}

def equivSigma : Vertex color ≃ (Σ v : V, Fin 3 × Fin (color v+2)) where
  toFun x := ⟨x.owner,x.port,⟨x.level,x.bound⟩⟩
  invFun x := ⟨x.1,x.2.1,x.2.2.val,x.2.2.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance instFintype [Fintype V] : Fintype (Vertex color) :=
  Fintype.ofEquiv _ equivSigma.symm

end Vertex

variable {V : Type uVariable5} (Y : PortGraph V) (color : V → ℕ)

def Internal (x y : Vertex color) : Prop :=
  x.owner = y.owner ∧
    ((x.level = 0 ∧ y.level = 0 ∧ x.port ≠ y.port) ∨
      (x.port = y.port ∧ (x.level+1 = y.level ∨ y.level+1 = x.level)))

def External (x y : Vertex color) : Prop :=
  x.level = 1 ∧ y.level = 1 ∧ Y.edge (x.owner,x.port) (y.owner,y.port)

def graph : SimpleGraph (Vertex color) where
  Adj x y := Internal color x y ∨ External Y color x y
  symm := ⟨by
    intro x y h
    rcases h with ⟨ho,(⟨hx,hy,hp⟩ | ⟨hp,hl⟩)⟩ | ⟨hx,hy,he⟩
    · exact Or.inl ⟨ho.symm,Or.inl ⟨hy,hx,hp.symm⟩⟩
    · exact Or.inl ⟨ho.symm,Or.inr ⟨hp.symm,hl.symm⟩⟩
    · exact Or.inr ⟨hy,hx,Y.symm he⟩⟩
  loopless := ⟨by
    intro x h
    rcases h with ⟨_,(⟨_,_,hp⟩ | ⟨_,hl⟩)⟩ | ⟨_,_,he⟩
    · exact hp rfl
    · omega
    · exact Y.different he rfl⟩

end VariableWL.SubcubicRealization

namespace VariableWL.SubcubicRealization
variable {V : Type uVariable8} {W : Type uVariable9} {color : V → ℕ} {color' : W → ℕ}

def vertexEquiv (f : V ≃ W) (ports : V → Equiv.Perm (Fin 3))
    (hc : ∀ v, color' (f v) = color v) : Vertex color ≃ Vertex color' where
  toFun x := ⟨f x.owner,ports x.owner x.port,x.level,by rw [hc]; exact x.bound⟩
  invFun y := ⟨f.symm y.owner,(ports (f.symm y.owner)).symm y.port,y.level,by
    rw [← hc,f.apply_symm_apply]; exact y.bound⟩
  left_inv x := by apply Vertex.ext <;> simp
  right_inv y := by apply Vertex.ext <;> simp

theorem vertexEquiv_internal (f : V ≃ W) (ports : V → Equiv.Perm (Fin 3))
    (hc : ∀ v, color' (f v) = color v) (x y : Vertex color) :
    Internal color' (vertexEquiv f ports hc x) (vertexEquiv f ports hc y) ↔ Internal color x y := by
  change (f x.owner = f y.owner ∧ _) ↔ _
  rw [f.injective.eq_iff]
  by_cases ho : x.owner = y.owner
  · simp only [Internal,vertexEquiv,Equiv.coe_fn_mk,ho,true_and]
    simp only [ne_eq,(ports y.owner).injective.eq_iff]
  · simp only [ho,false_and,Internal]

theorem vertexEquiv_adj (Y : PortGraph V) (Z : PortGraph W)
    (f : V ≃ W) (ports : V → Equiv.Perm (Fin 3))
    (hc : ∀ v, color' (f v) = color v) (x y : Vertex color)
    (he : Y.edge (x.owner,x.port) (y.owner,y.port) ↔
      Z.edge (f x.owner,ports x.owner x.port) (f y.owner,ports y.owner y.port)) :
    (graph Z color').Adj (vertexEquiv f ports hc x) (vertexEquiv f ports hc y) ↔
      (graph Y color).Adj x y := by
  change (Internal color' _ _ ∨ _) ↔ (Internal color x y ∨ _)
  rw [vertexEquiv_internal]
  change (Internal color x y ∨ x.level=1 ∧ y.level=1 ∧
    Z.edge (f x.owner,ports x.owner x.port) (f y.owner,ports y.owner y.port)) ↔ _
  rw [← he]
  rfl

end VariableWL.SubcubicRealization

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_TypedGame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9

namespace VariableWL.TypedGame
attribute [local instance] Classical.propDecidable
variable {V : Type uVariable1} {W : Type uVariable2} [Fintype V] [Fintype W]

noncomputable abbrev numbered (G : SimpleGraph V) : Graph :=
  ⟨Fintype.card V,G.comap (Fintype.equivFin V).symm⟩

noncomputable def numbering (G : SimpleGraph V) : G ≃g (numbered G).graph where
  toEquiv := Fintype.equivFin V
  map_rel_iff' := by intro x y; change G.Adj _ _ ↔ _; simp

end VariableWL.TypedGame

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_PrefixParts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.PrefixParts
open VariableWL.Affine
open scoped CharTwo
attribute [local instance] Classical.propDecidable

structure Data where
  dimension : ℕ
  channels : ℕ
  positive : 0 < channels
  root : Fin channels → ℕ
  root_le : ∀ c, root c ≤ dimension
  zero_root : root ⟨0,positive⟩ = 0
  order : Fin channels → Equiv.Perm (Fin dimension)
  legal : Bit → Set (Vec dimension)
  nonempty : ∀ ε, (legal ε).Nonempty
  coset : ∀ (ξ : Vec dimension), ξ ∈ legal 1 →
    ∀ z, z ∈ legal 0 ↔ z+ξ ∈ legal 1

namespace Data
@[simp] theorem vec_add_self {a : ℕ} (v : Vec a) : v+v=0 := by
  ext i; simp

variable (D : Data)
abbrev Valuation (ε : Bit) := {z : Vec D.dimension // z ∈ D.legal ε}

noncomputable def translate (ξ : D.Valuation 1) : D.Valuation 0 ≃ D.Valuation 1 where
  toFun z := ⟨z.val+ξ.val,(D.coset _ ξ.property _).mp z.property⟩
  invFun z := ⟨z.val+ξ.val,(D.coset _ ξ.property _).mpr (by rw [add_assoc,vec_add_self,add_zero]; exact z.property)⟩
  left_inv z := by ext i; simp
  right_inv z := by ext i; simp

def truncate {a : ℕ} (h : ℕ) (u : Vec a) : Vec a := fun i => if i.val<h then u i else 0

theorem truncate_add {a h : ℕ} (u v : Vec a) : truncate h (u+v)=truncate h u+truncate h v := by
  ext i; simp only [truncate,Pi.add_apply]; split_ifs <;> simp

theorem truncate_truncate {a h k : ℕ} (hk : h ≤ k) (u : Vec a) :
    truncate h (truncate k u)=truncate h u := by
  ext i; simp only [truncate]; split_ifs <;> (first | rfl | omega)

@[simp] theorem truncate_zero {a : ℕ} (u : Vec a) : truncate 0 u=0 := by
  ext i; simp [truncate]

@[simp] theorem truncate_full {a : ℕ} (u : Vec a) : truncate a u=u := by
  ext i; simp [truncate,i.isLt]

abbrev RawTree := Fin D.channels × Fin (D.dimension+1) × Vec D.dimension

def TreeLegal (ε : Bit) (t : D.RawTree) : Prop :=
  D.root t.1 ≤ t.2.1.val ∧ ∃ z : D.Valuation ε,
    truncate t.2.1.val (z.val ∘ D.order t.1)=t.2.2

abbrev Tree (ε : Bit) := {t : D.RawTree // D.TreeLegal ε t}
abbrev Vertex (ε : Bit) := Unit ⊕ ((Fin D.channels × D.Valuation ε) ⊕ D.Tree ε)

namespace Tree
variable {D} {ε : Bit}
abbrev channel (t : D.Tree ε) := t.val.1
abbrev height (t : D.Tree ε) := t.val.2.1.val
abbrev bits (t : D.Tree ε) := t.val.2.2

def ofValuation (c : Fin D.channels) (h : ℕ) (hqa : D.root c ≤ h) (ha : h ≤ D.dimension)
    (z : D.Valuation ε) : D.Tree ε :=
  ⟨(c,⟨h,by omega⟩,truncate h (z.val ∘ D.order c)),hqa,z,rfl⟩

@[ext] theorem ext {t u : D.Tree ε} (hc : t.channel=u.channel)
    (hh : t.height=u.height) (hb : t.bits=u.bits) : t=u := by
  apply Subtype.ext
  exact Prod.ext hc (Prod.ext (Fin.ext hh) hb)

theorem truncated (t : D.Tree ε) : truncate t.height t.bits=t.bits := by
  obtain ⟨_,z,hz⟩ := t.property
  change truncate t.height (z.val ∘ D.order t.channel)=t.bits at hz
  rw [← hz,truncate_truncate le_rfl]

theorem above_zero (t : D.Tree ε) (i : Fin D.dimension) (hi : t.height ≤ i.val) : t.bits i=0 := by
  have h := congrFun t.truncated i
  simpa [truncate,show ¬i.val<t.height by omega] using h.symm

theorem height_zero (t : D.Tree ε) (hh : t.height=0) : t.bits=0 := by
  rw [← t.truncated,hh,truncate_zero]

end Tree

variable {D}
def TreeStep {ε : Bit} (t u : D.Tree ε) : Prop :=
  t.channel=u.channel ∧ t.height+1=u.height ∧ truncate t.height u.bits=t.bits

def Forward {ε : Bit} : D.Vertex ε → D.Vertex ε → Prop
  | .inl _, .inr (.inr t) => t.channel.val=0 ∧ t.height=0
  | .inr (.inl (c,z)), .inr (.inl (d,w)) => c.val+1=d.val ∧ z=w
  | .inr (.inr t), .inr (.inr u) => TreeStep t u
  | .inr (.inr t), .inr (.inl (c,z)) =>
      t.channel=c ∧ t.height=D.dimension ∧ t.bits=z.val ∘ D.order c
  | _, _ => False

variable (D)
def graph (ε : Bit) : SimpleGraph (D.Vertex ε) where
  Adj x y := Forward x y ∨ Forward y x
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨by
    intro x
    cases x with
    | inl u => simp [Forward]
    | inr v =>
      cases v with
      | inl v => simp only [Forward,or_self]; omega
      | inr t => simp only [Forward,TreeStep,or_self]; omega⟩

noncomputable def treeTranslation (ξ : D.Valuation 1) : D.Tree 0 ≃ D.Tree 1 where
  toFun t := ⟨(t.channel,t.val.2.1,t.bits+truncate t.height (ξ.val ∘ D.order t.channel)),by
    refine ⟨t.property.1,?_⟩
    obtain ⟨z,hz⟩ := t.property.2
    refine ⟨D.translate ξ z,?_⟩
    change truncate t.height ((z.val+ξ.val) ∘ D.order t.channel)=_
    have he : (z.val+ξ.val) ∘ D.order t.channel = z.val ∘ D.order t.channel+ξ.val ∘ D.order t.channel := rfl
    rw [he,truncate_add,hz]⟩
  invFun t := ⟨(t.channel,t.val.2.1,t.bits+truncate t.height (ξ.val ∘ D.order t.channel)),by
    refine ⟨t.property.1,?_⟩
    obtain ⟨z,hz⟩ := t.property.2
    refine ⟨(D.translate ξ).symm z,?_⟩
    change truncate t.height ((z.val+ξ.val) ∘ D.order t.channel)=_
    have he : (z.val+ξ.val) ∘ D.order t.channel = z.val ∘ D.order t.channel+ξ.val ∘ D.order t.channel := rfl
    rw [he,truncate_add,hz]⟩
  left_inv t := by
    apply Tree.ext
    · rfl
    · rfl
    · change (t.bits+truncate t.height (ξ.val ∘ D.order t.channel))+truncate t.height (ξ.val ∘ D.order t.channel)=t.bits
      rw [add_assoc,vec_add_self,add_zero]
  right_inv t := by
    apply Tree.ext
    · rfl
    · rfl
    · change (t.bits+truncate t.height (ξ.val ∘ D.order t.channel))+truncate t.height (ξ.val ∘ D.order t.channel)=t.bits
      rw [add_assoc,vec_add_self,add_zero]

noncomputable def vertexTranslation (ξ : D.Valuation 1) : D.Vertex 0 ≃ D.Vertex 1 :=
  Equiv.sumCongr (Equiv.refl Unit) (Equiv.sumCongr
    (Equiv.prodCongr (Equiv.refl _) (D.translate ξ)) (D.treeTranslation ξ))

end Data
end VariableWL.PrefixParts

namespace VariableWL.PrefixParts.Data
open VariableWL.Affine
open scoped CharTwo
attribute [local instance] Classical.propDecidable
variable {D : Data} {ε : Bit}

theorem Tree.height_le (t : D.Tree ε) : t.height ≤ D.dimension := Nat.le_of_lt_succ t.val.2.1.isLt

theorem TreeStep.lower_lt {t u : D.Tree ε} (h : TreeStep t u) : t.height < D.dimension := by
  have hu := u.height_le
  have hh := h.2.1
  omega

theorem TreeStep.parent_unique {t u v : D.Tree ε} (h : TreeStep u t) (h' : TreeStep v t) : u=v := by
  have hh := h.2.1
  have hh' := h'.2.1
  apply Tree.ext (h.1.trans h'.1.symm)
  · omega
  · have hh : u.height=v.height := by omega
    rw [← h.2.2,hh,h'.2.2]

theorem TreeStep.child_unique {t u v : D.Tree ε} (h : TreeStep t u) (h' : TreeStep t v)
    (hb : u.bits ⟨t.height,h.lower_lt⟩=v.bits ⟨t.height,h'.lower_lt⟩) : u=v := by
  have hh := h.2.1
  have hh' := h'.2.1
  apply Tree.ext (h.1.symm.trans h'.1)
  · omega
  · ext i
    rcases lt_trichotomy i.val t.height with hi | hi | hi
    · have hu := congrFun h.2.2 i
      have hv := congrFun h'.2.2 i
      simpa [truncate,hi] using hu.trans hv.symm
    · have he : i=⟨t.height,h.lower_lt⟩ := Fin.ext hi
      simpa only [he] using hb
    · rw [u.above_zero i (by omega),v.above_zero i (by omega)]

theorem Tree.root_unique {t u : D.Tree ε} (hc : t.channel=u.channel)
    (ht : t.height=0) (hu : u.height=0) : t=u :=
  Tree.ext hc (ht.trans hu.symm) ((t.height_zero ht).trans (u.height_zero hu).symm)

def bitPort (b : Bit) : Fin 3 := ⟨b.val+1,by have := ZMod.val_lt b; omega⟩

theorem bitPort_ne_zero (b : Bit) : bitPort b ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp only [bitPort,Fin.val_zero] at this
  omega

theorem bitPort_injective : Function.Injective bitPort := by
  intro a b h
  apply ZMod.val_injective 2
  have he := congrArg Fin.val h
  change a.val+1=b.val+1 at he
  omega

noncomputable def slot {ε : Bit} : D.Vertex ε → D.Vertex ε → Fin 3
  | .inl _, _ => 0
  | .inr (.inl (c,_)), .inr (.inl (d,_)) => if d.val<c.val then 0 else 1
  | .inr (.inl _), _ => 2
  | .inr (.inr _), .inl _ => 0
  | .inr (.inr _), .inr (.inl _) => 1
  | .inr (.inr t), .inr (.inr u) =>
      if u.height<t.height then 0 else
        if ht : t.height<D.dimension then bitPort (u.bits ⟨t.height,ht⟩) else 1

theorem slot_parent {t u : D.Tree ε} (h : TreeStep t u) :
    slot (.inr (.inr u)) (.inr (.inr t))=0 := by
  have hh := h.2.1
  simp only [slot,ite_eq_left (show t.height<u.height by omega)]

theorem slot_child {t u : D.Tree ε} (h : TreeStep t u) :
    slot (.inr (.inr t)) (.inr (.inr u))=bitPort (u.bits ⟨t.height,h.lower_lt⟩) := by
  have hh := h.2.1
  simp only [slot,ite_eq_right (show ¬u.height<t.height by omega),dite_eq_left h.lower_lt]

theorem leaf_unique (t : D.Tree ε) {c d : Fin D.channels} {z w : D.Valuation ε}
    (h : t.channel=c ∧ t.height=D.dimension ∧ t.bits=z.val ∘ D.order c)
    (h' : t.channel=d ∧ t.height=D.dimension ∧ t.bits=w.val ∘ D.order d) : (c,z)=(d,w) := by
  have hc : c=d := h.1.symm.trans h'.1
  subst d
  apply Prod.ext
  · rfl
  apply Subtype.ext
  ext i
  have he := congrFun (h.2.2.symm.trans h'.2.2) ((D.order c).symm i)
  simpa only [Function.comp_apply,Equiv.apply_symm_apply] using he

theorem leaf_node_unique {t u : D.Tree ε} {c : Fin D.channels} {z : D.Valuation ε}
    (h : t.channel=c ∧ t.height=D.dimension ∧ t.bits=z.val ∘ D.order c)
    (h' : u.channel=c ∧ u.height=D.dimension ∧ u.bits=z.val ∘ D.order c) : t=u :=
  Tree.ext (h.1.trans h'.1.symm) (h.2.1.trans h'.2.1.symm) (h.2.2.trans h'.2.2.symm)

theorem slot_injective (x : D.Vertex ε) :
    Function.Injective (fun y : (D.graph ε).neighborSet x => slot x y.val) := by
  rintro ⟨y,hy⟩ ⟨z,hz⟩ he
  change slot x y=slot x z at he
  apply Subtype.ext
  change y=z
  have hy' : Forward x y ∨ Forward y x := hy
  have hz' : Forward x z ∨ Forward z x := hz
  rcases x with x | (⟨c,v⟩ | t)
  · rcases y with y | (y | u) <;> rcases z with z | (z | w) <;>
      simp only [Forward,or_false] at hy' hz'; try contradiction
    obtain ⟨huc,hu⟩ := hy'
    obtain ⟨hwc,hw⟩ := hz'
    exact congrArg (fun a => Sum.inr (Sum.inr a)) (Tree.root_unique (Fin.ext (huc.trans hwc.symm)) hu hw)
  · rcases y with y | (⟨d,w⟩ | u) <;> rcases z with z | (⟨e,v'⟩ | t') <;>
      simp only [Forward,false_or,or_false] at hy' hz' <;> try contradiction
    · have hd : w=v := by rcases hy' with h | h; exact h.2.symm; exact h.2
      have he' : v'=v := by rcases hz' with h | h; exact h.2.symm; exact h.2
      subst w; subst v'
      have hc : d=e := by
        apply Fin.ext
        simp only [slot] at he
        split_ifs at he <;> (rcases hy' with h | h) <;> (rcases hz' with h' | h') <;>
          omega
      subst e; rfl
    · simp only [slot] at he
      split_ifs at he <;> have := congrArg Fin.val he <;> norm_num at this
    · simp only [slot] at he
      split_ifs at he <;> have := congrArg Fin.val he <;> norm_num at this
    · exact congrArg (fun a => Sum.inr (Sum.inr a)) (leaf_node_unique hy' hz')
  · rcases y with y | (⟨d,w⟩ | u) <;> rcases z with z | (⟨e,v'⟩ | t') <;>
      simp only [Forward,false_or,or_false] at hy' hz'
    · cases y; cases z; rfl
    · have := congrArg Fin.val he; norm_num [slot] at this
    · rcases hz' with h | h
      · rw [slot_child h] at he
        exact (bitPort_ne_zero _ he.symm).elim
      · have ht := hy'.2
        have hh := h.2.1
        omega
    · have := congrArg Fin.val he; norm_num [slot] at this
    · exact congrArg (fun a => Sum.inr (Sum.inl a)) (leaf_unique t hy' hz')
    · rcases hz' with h | h
      · have hh := h.lower_lt; omega
      · rw [slot_parent h] at he
        have := congrArg Fin.val he; norm_num [slot] at this
    · rcases hy' with h | h
      · rw [slot_child h] at he
        exact (bitPort_ne_zero _ he).elim
      · have ht := hz'.2
        have hh := h.2.1
        omega
    · rcases hy' with h | h
      · have hh := h.lower_lt; omega
      · rw [slot_parent h] at he
        have := congrArg Fin.val he; norm_num [slot] at this
    · rcases hy' with h | h <;> rcases hz' with h' | h'
      · rw [slot_child h,slot_child h'] at he
        exact congrArg (fun a => Sum.inr (Sum.inr a)) (h.child_unique h' (bitPort_injective he))
      · rw [slot_child h,slot_parent h'] at he
        exact (bitPort_ne_zero _ he).elim
      · rw [slot_parent h,slot_child h'] at he
        exact (bitPort_ne_zero _ he.symm).elim
      · exact congrArg (fun a => Sum.inr (Sum.inr a)) (h.parent_unique h')

end VariableWL.PrefixParts.Data

namespace VariableWL.PrefixParts.Data
open VariableWL.Affine
attribute [local instance] Classical.propDecidable
variable {D : Data}

def portAlphabet : Fin 3 ≃ Option Bit := finSuccEquiv 2

@[simp] theorem portAlphabet_zero : portAlphabet 0=none := rfl

@[simp] theorem portAlphabet_bitPort (b : Bit) : portAlphabet (bitPort b)=some b := by
  exact finSuccEquiv_succ b

def shiftPorts (b : Bit) : Equiv.Perm (Fin 3) :=
  portAlphabet.trans ((Equiv.optionCongr (Equiv.addRight b)).trans portAlphabet.symm)

@[simp] theorem shiftPorts_zero (b : Bit) : shiftPorts b 0=0 := by
  apply portAlphabet.injective
  simp [shiftPorts]

@[simp] theorem shiftPorts_bitPort (a b : Bit) : shiftPorts b (bitPort a)=bitPort (a+b) := by
  apply portAlphabet.injective
  simp [shiftPorts]

noncomputable def localPorts (ξ : D.Valuation 1) : D.Vertex 0 → Equiv.Perm (Fin 3)
  | .inr (.inr t) => if h : t.height<D.dimension then
      shiftPorts (ξ.val (D.order t.channel ⟨t.height,h⟩)) else Equiv.refl _
  | _ => Equiv.refl _

@[simp] theorem localPorts_zero (ξ : D.Valuation 1) (x : D.Vertex 0) : localPorts ξ x 0=0 := by
  rcases x with x | (x | t) <;> simp only [localPorts,Equiv.refl_apply]
  split_ifs <;> simp

theorem proper_root_reserved {ε : Bit} (t : D.Tree ε)
    (hc : t.channel.val ≠ 0) (hh : t.height=D.root t.channel)
    {y : D.Vertex ε} (hy : (D.graph ε).Adj (.inr (.inr t)) y) :
    slot (.inr (.inr t)) y ≠ 0 := by
  have hy' : Forward (.inr (.inr t)) y ∨ Forward y (.inr (.inr t)) := hy
  rcases y with y | (⟨c,z⟩ | u)
  · simp only [Forward,false_or] at hy'
    exact (hc hy'.1).elim
  · change (1 : Fin 3) ≠ 0
    decide
  · rcases hy' with h | h
    · rw [slot_child h]
      exact bitPort_ne_zero _
    · have hroot := u.property.1
      change D.root u.channel ≤ u.height at hroot
      have hch := h.1
      have hht := h.2.1
      rw [hch] at hroot
      omega

end VariableWL.PrefixParts.Data

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_PrefixWiring
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9

namespace VariableWL.SubcubicRealization.PortGraph
attribute [local instance] Classical.propDecidable
variable {V : Type uVariable1}

def ofSlots (G : SimpleGraph V) (slot : V → V → Fin 3)
    (hinj : ∀ x, Function.Injective (fun y : G.neighborSet x => slot x y.val)) : PortGraph V where
  edge a b := G.Adj a.1 b.1 ∧ a.2=slot a.1 b.1 ∧ b.2=slot b.1 a.1
  symm := fun h => ⟨h.1.symm,h.2.2,h.2.1⟩
  unique := by
    rintro ⟨x,i⟩ ⟨y,j⟩ ⟨z,k⟩ h h'
    have he : (⟨y,h.1⟩ : G.neighborSet x)=⟨z,h'.1⟩ := hinj x (h.2.1.symm.trans h'.2.1)
    have hy : y=z := congrArg Subtype.val he
    subst z
    exact Prod.ext rfl (h.2.2.trans h'.2.2.symm)
  different := fun h => h.1.ne

@[simp] theorem ofSlots_graph (G : SimpleGraph V) (slot : V → V → Fin 3)
    (hinj : ∀ x, Function.Injective (fun y : G.neighborSet x => slot x y.val)) :
    (ofSlots G slot hinj).graph=G := by
  ext x y
  exact ⟨fun ⟨_,_,h⟩ => h.1,fun h => ⟨slot x y,slot y x,h,rfl,rfl⟩⟩

def sigma {B : Type uVariable2} {A : B → Type uVariable9} (Y : ∀ b, PortGraph (A b)) : PortGraph (Σ b,A b) where
  edge a b := ∃ h : a.1.1=b.1.1, (Y a.1.1).edge (a.1.2,a.2) (h.symm ▸ b.1.2,b.2)
  symm := by
    rintro ⟨⟨b,x⟩,i⟩ ⟨⟨c,y⟩,j⟩ ⟨h,he⟩
    dsimp at h
    subst c
    exact ⟨rfl,(Y b).symm he⟩
  unique := by
    rintro ⟨⟨b,x⟩,i⟩ ⟨⟨c,y⟩,j⟩ ⟨⟨d,z⟩,k⟩ ⟨h,he⟩ ⟨h',he'⟩
    dsimp at h h'
    subst c
    subst d
    have hh := (Y b).unique he he'
    change (y,j)=(z,k) at hh
    cases hh
    rfl
  different := by
    rintro ⟨⟨b,x⟩,i⟩ ⟨⟨c,y⟩,j⟩ ⟨h,he⟩ hxy
    dsimp at h
    subst c
    exact (Y b).different he (eq_of_heq (Sigma.mk.inj_iff.mp hxy).2)

def union (Y Z : PortGraph V)
    (hd : ∀ a b c, Y.edge a b → Z.edge a c → False) : PortGraph V where
  edge a b := Y.edge a b ∨ Z.edge a b
  symm := fun h => h.elim (fun h => Or.inl (Y.symm h)) (fun h => Or.inr (Z.symm h))
  unique := by
    intro a b c h h'
    rcases h with h | h <;> rcases h' with h' | h'
    · exact Y.unique h h'
    · exact (hd _ _ _ h h').elim
    · exact (hd _ _ _ h' h).elim
    · exact Z.unique h h'
  different := fun h => h.elim Y.different Z.different

end VariableWL.SubcubicRealization.PortGraph

namespace VariableWL.PrefixParts.Data
open VariableWL.SubcubicRealization
attribute [local instance] Classical.propDecidable

noncomputable def ports (D : Data) (ε : Affine.Bit) : PortGraph (D.Vertex ε) :=
  PortGraph.ofSlots (D.graph ε) slot slot_injective

@[simp] theorem ports_graph (D : Data) (ε : Affine.Bit) : (D.ports ε).graph=D.graph ε :=
  PortGraph.ofSlots_graph _ _ _

end VariableWL.PrefixParts.Data

namespace VariableWL.PrefixParts
open VariableWL.Affine VariableWL.SubcubicRealization
open scoped CharTwo
attribute [local instance] Classical.propDecidable

abbrev Channel {B : Type uVariable3} (D : B → Data) := Σ b, {c : Fin (D b).channels // c.val≠0}

structure Wiring {B : Type uVariable4} (D : B → Data) where
  mate : Channel D ≃ Channel D
  involutive : Function.Involutive mate
  different : ∀ c, (mate c).1≠c.1
  root_eq : ∀ c, (D (mate c).1).root (mate c).2.val=(D c.1).root c.2.val

namespace Wiring
variable {B : Type uVariable5} [Fintype B] [FiniteNumbering B] (D : B → Data) (W : Wiring D)
abbrev Vertex (ε : Bit) := Σ b, (D b).Vertex ε

abbrev Root (ε : Bit) (c : Channel D) :=
  {t : (D c.1).Tree ε // t.channel=c.2.val ∧ t.height=(D c.1).root c.2.val}
abbrev RootLabel (ε : Bit) := Σ c : Channel D, Root D ε c

def rootVertex {ε : Bit} (x : RootLabel D ε) : Vertex D ε :=
  ⟨x.1.1,.inr (.inr x.2.val)⟩

omit [Fintype B] in
theorem rootVertex_injective {ε : Bit} : Function.Injective (rootVertex (D := D) (ε := ε)) := by
  rintro ⟨⟨b,c⟩,t⟩ ⟨⟨d,e⟩,u⟩ h
  have hb : b=d := congrArg Sigma.fst h
  subst d
  have ht : t.val=u.val := Sum.inr_injective (Sum.inr_injective (eq_of_heq (Sigma.mk.inj_iff.mp h).2))
  have hc : c=e := Subtype.ext (t.property.1.symm.trans ((congrArg Data.Tree.channel ht).trans u.property.1))
  subst e
  have hu : t=u := Subtype.ext ht
  subst u
  rfl

def pad {a : ℕ} (v : Vec a) : ℕ → Bit := fun j => if h : j<a then v ⟨j,h⟩ else 0

theorem pad_injective {a : ℕ} : Function.Injective (@pad a) := by
  intro v w h
  ext i
  simpa only [pad,dite_eq_left i.isLt] using congrFun h i.val

@[simp] theorem pad_add {a : ℕ} (v w : Vec a) : pad (v+w)=pad v+pad w := by
  ext i
  simp only [pad,Pi.add_apply]
  split_ifs <;> simp

noncomputable def internal (ε : Bit) : PortGraph (Vertex D ε) :=
  PortGraph.sigma (fun b => (D b).ports ε)

def rootPorts (ε : Bit) : PortGraph (Vertex D ε) where
  edge a b := ∃ x y : RootLabel D ε, a=(rootVertex D x,0) ∧ b=(rootVertex D y,0) ∧
    W.mate x.1=y.1 ∧ pad x.2.val.bits=pad y.2.val.bits
  symm := by
    rintro a b ⟨x,y,rfl,rfl,hm,hv⟩
    refine ⟨y,x,rfl,rfl,?_,hv.symm⟩
    rw [← hm,W.involutive]
  unique := by
    rintro a b c ⟨x,y,rfl,rfl,hm,hv⟩ ⟨x',z,hx,rfl,hm',hv'⟩
    have hxx : x=x' := rootVertex_injective D (congrArg Prod.fst hx)
    subst x'
    have hc : y.1=z.1 := hm.symm.trans hm'
    have hyz : y=z := by
      rcases y with ⟨c,y⟩
      rcases z with ⟨d,z⟩
      dsimp at hc
      subst d
      have hb : y.val.bits=z.val.bits := pad_injective (hv.symm.trans hv')
      have ht : y.val=z.val := Data.Tree.ext (y.property.1.trans z.property.1.symm)
        (y.property.2.trans z.property.2.symm) hb
      exact congrArg (Sigma.mk c) (Subtype.ext ht)
    subst z
    rfl
  different := by
    rintro a b ⟨x,y,rfl,rfl,hm,_⟩ he
    have hblock : x.1.1=y.1.1 := congrArg (fun v : Vertex D ε => v.1) he
    exact W.different x.1 (by rw [hm]; exact hblock.symm)

omit [Fintype B] in

theorem internal_root_disjoint (ε : Bit) (a b c : Vertex D ε × Fin 3)
    (hi : (internal D ε).edge a b) (hr : (W.rootPorts D ε).edge a c) : False := by
  obtain ⟨x,y,rfl,rfl,_,_⟩ := hr
  rcases x with ⟨⟨d,e⟩,t⟩
  rcases b with ⟨⟨f,v⟩,j⟩
  obtain ⟨h,hint⟩ := hi
  dsimp [rootVertex] at h
  subst f
  have hh : ((D d).graph ε).Adj (.inr (.inr t.val)) v := hint.1
  have hs : Data.slot (.inr (.inr t.val)) v=0 := hint.2.1.symm
  exact Data.proper_root_reserved t.val
    (by rw [t.property.1]; exact e.property) (by rw [t.property.1]; exact t.property.2) hh hs

def anchor (ε : Bit) (b : B) : Vertex D ε := ⟨b,.inl ()⟩

def anchorPorts (ε : Bit) : PortGraph (Vertex D ε) where
  edge a b :=
    (∃ x y : B, a=(anchor D ε x,2) ∧ b=(anchor D ε y,1) ∧
      (enumeration B x).val+1=(enumeration B y).val) ∨
    (∃ x y : B, b=(anchor D ε x,2) ∧ a=(anchor D ε y,1) ∧
      (enumeration B x).val+1=(enumeration B y).val)
  symm := fun h => h.symm
  unique := by
    intro a b c h h'
    rcases h with ⟨x,y,rfl,rfl,hxy⟩ | ⟨x,y,rfl,rfl,hxy⟩
    · rcases h' with ⟨x',z,hx,rfl,hxz⟩ | ⟨z,x',rfl,hx,hzx⟩
      · have hxx : x=x' := congrArg (fun a => a.1.1) hx
        subst x'
        have hyz : y=z := (enumeration B).injective (Fin.ext (hxy.symm.trans hxz))
        subst z
        rfl
      · have hs : (2 : Fin 3)=1 := congrArg Prod.snd hx
        exact ((by decide : (2 : Fin 3)≠1) hs).elim
    · rcases h' with ⟨y',z,hy,rfl,hyz⟩ | ⟨z,y',rfl,hy,hzy⟩
      · have hs : (1 : Fin 3)=2 := congrArg Prod.snd hy
        exact ((by decide : (1 : Fin 3)≠2) hs).elim
      · have hyy : y=y' := congrArg (fun a => a.1.1) hy
        subst y'
        have hxz : x=z := (enumeration B).injective (Fin.ext (by omega))
        subst z
        rfl
  different := by
    intro a b he hab
    rcases he with ⟨x,y,rfl,rfl,hxy⟩ | ⟨x,y,rfl,rfl,hxy⟩
    · have h : x=y := congrArg Sigma.fst hab
      subst y
      omega
    · have h : y=x := congrArg Sigma.fst hab
      subst y
      omega

theorem internal_anchor_disjoint (ε : Bit) (a b c : Vertex D ε × Fin 3)
    (hi : (internal D ε).edge a b) (ha : (anchorPorts D ε).edge a c) : False := by
  rcases ha with ⟨x,y,rfl,rfl,_⟩ | ⟨y,x,rfl,rfl,_⟩
  all_goals
    rcases b with ⟨⟨d,v⟩,j⟩
    obtain ⟨h,hint⟩ := hi
    dsimp [anchor] at h
    subst d
    have hs := hint.2.1
    change (_ : Fin 3)=Data.slot (.inl ()) v at hs
    simp only [Data.slot] at hs
    omega

theorem root_anchor_disjoint (ε : Bit) (a b c : Vertex D ε × Fin 3)
    (hr : (W.rootPorts D ε).edge a b) (ha : (anchorPorts D ε).edge a c) : False := by
  obtain ⟨x,y,rfl,rfl,_,_⟩ := hr
  rcases ha with ⟨u,v,hu,_,_⟩ | ⟨u,v,_,hu,_⟩
  · have hs : (0 : Fin 3)=2 := congrArg Prod.snd hu
    exact (by decide : (0 : Fin 3)≠2) hs
  · have hs : (0 : Fin 3)=1 := congrArg Prod.snd hu
    exact (by decide : (0 : Fin 3)≠1) hs

noncomputable def ports (ε : Bit) : PortGraph (Vertex D ε) :=
  (internal D ε).union ((W.rootPorts D ε).union (anchorPorts D ε) (root_anchor_disjoint D W ε))
    (fun a b c hi he => he.elim (internal_root_disjoint D W ε a b c hi)
      (internal_anchor_disjoint D ε a b c hi))

end Wiring
end VariableWL.PrefixParts

namespace VariableWL.PrefixParts.Data
open VariableWL.Affine VariableWL.SubcubicRealization
attribute [local instance] Classical.propDecidable
variable {D : Data}

abbrev SortTag (D : Data) := Unit ⊕ (Fin D.channels ⊕ (Σ c : Fin D.channels,
  {h : Fin (D.dimension+1) // D.root c ≤ h.val}))

def sort {ε : Bit} : D.Vertex ε → D.SortTag
  | .inl _ => .inl ()
  | .inr (.inl (c,_)) => .inr (.inl c)
  | .inr (.inr t) => .inr (.inr ⟨t.channel,t.val.2.1,t.property.1⟩)

@[simp] theorem sort_translation (ξ : D.Valuation 1) (x : D.Vertex 0) :
    sort (D.vertexTranslation ξ x)=sort x := by
  rcases x with x | (x | x) <;> rfl

@[simp] theorem localPorts_anchor (ξ : D.Valuation 1) (i : Fin 3) :
    localPorts ξ (.inl ()) i=i := rfl

end VariableWL.PrefixParts.Data

namespace VariableWL.PrefixParts.Wiring
open VariableWL.Affine VariableWL.SubcubicRealization
attribute [local instance] Classical.propDecidable
variable {B : Type uVariable6} [Fintype B] (D : B → Data) (W : Wiring D)

abbrev SortTag := Σ b, (D b).SortTag
variable [FiniteNumbering B] [FiniteNumbering (SortTag D)]

def sort {ε : Bit} (x : Vertex D ε) : SortTag D := ⟨x.1,Data.sort x.2⟩

noncomputable def color {ε : Bit} (x : Vertex D ε) : ℕ :=
  (enumeration (SortTag D) (sort D x)).val+1

omit [FiniteNumbering B] in
theorem color_eq_iff {ε δ : Bit} (x : Vertex D ε) (y : Vertex D δ) :
    color D x=color D y ↔ sort D x=sort D y := by
  unfold color
  exact ⟨fun h => (enumeration (SortTag D)).injective (Fin.ext (by omega)),fun h => congrArg (fun t : SortTag D => (enumeration (SortTag D) t).val+1) h⟩

noncomputable def vertexTranslation (ξ : ∀ b, (D b).Valuation 1) : Vertex D 0 ≃ Vertex D 1 :=
  Equiv.sigmaCongrRight (fun b => (D b).vertexTranslation (ξ b))

omit [Fintype B] in
@[simp] theorem vertexTranslation_apply (ξ : ∀ b, (D b).Valuation 1) (b : B) (v : (D b).Vertex 0) :
    vertexTranslation D ξ ⟨b,v⟩=⟨b,(D b).vertexTranslation (ξ b) v⟩ := rfl

omit [FiniteNumbering B] in
@[simp] theorem color_translation (ξ : ∀ b, (D b).Valuation 1) (x : Vertex D 0) :
    color D (vertexTranslation D ξ x)=color D x := by
  apply (color_eq_iff D _ _).mpr
  exact congrArg (Sigma.mk x.1) (Data.sort_translation _ _)

noncomputable def localPorts (ξ : ∀ b, (D b).Valuation 1) (x : Vertex D 0) : Equiv.Perm (Fin 3) :=
  Data.localPorts (ξ x.1) x.2

noncomputable def incidenceTranslation (ξ : ∀ b, (D b).Valuation 1) :
    (Vertex D 0 × Fin 3) ≃ (Vertex D 1 × Fin 3) where
  toFun a := (vertexTranslation D ξ a.1,localPorts D ξ a.1 a.2)
  invFun a := ((vertexTranslation D ξ).symm a.1,
    (localPorts D ξ ((vertexTranslation D ξ).symm a.1)).symm a.2)
  left_inv a := by simp
  right_inv a := by simp

omit [Fintype B] in
@[simp] theorem root_truncated {ε : Bit} (x : RootLabel D ε) :
    Data.truncate ((D x.1.1).root x.1.2.val) x.2.val.bits=x.2.val.bits := by
  calc
    _ = Data.truncate x.2.val.height x.2.val.bits :=
      congrArg (fun h => Data.truncate h x.2.val.bits) x.2.property.2.symm
    _ = _ := x.2.val.truncated

noncomputable def rootTranslation (ξ : ∀ b, (D b).Valuation 1) : RootLabel D 0 ≃ RootLabel D 1 :=
  Equiv.sigmaCongrRight (fun c =>
    { toFun := fun t => ⟨(D c.1).treeTranslation (ξ c.1) t.val,t.property⟩
      invFun := fun t => ⟨((D c.1).treeTranslation (ξ c.1)).symm t.val,t.property⟩
      left_inv := fun t => Subtype.ext (((D c.1).treeTranslation (ξ c.1)).symm_apply_apply t.val)
      right_inv := fun t => Subtype.ext (((D c.1).treeTranslation (ξ c.1)).apply_symm_apply t.val) })

omit [Fintype B] in
@[simp] theorem translate_root_incidence (ξ : ∀ b, (D b).Valuation 1) (x : RootLabel D 0) :
    incidenceTranslation D ξ (rootVertex D x,0)=(rootVertex D (rootTranslation D ξ x),0) := by
  apply Prod.ext
  · rfl
  · exact Data.localPorts_zero _ _

noncomputable def rootShift (ξ : ∀ b, (D b).Valuation 1) (c : Channel D) : ℕ → Bit :=
  pad (Data.truncate ((D c.1).root c.2.val) ((ξ c.1).val ∘ (D c.1).order c.2.val))

omit [Fintype B] in
@[simp] theorem rootTranslation_bits (ξ : ∀ b, (D b).Valuation 1) (x : RootLabel D 0) :
    pad (rootTranslation D ξ x).2.val.bits=pad x.2.val.bits+rootShift D ξ x.1 := by
  change pad (x.2.val.bits+Data.truncate x.2.val.height ((ξ x.1.1).val ∘ (D x.1.1).order x.2.val.channel))=_
  rw [pad_add,x.2.property.1,x.2.property.2]
  rfl

end VariableWL.PrefixParts.Wiring

namespace VariableWL.PrefixParts.Wiring
open VariableWL.Affine VariableWL.SubcubicRealization
attribute [local instance] Classical.propDecidable
variable {B : Type uVariable7} [Fintype B] [FiniteNumbering B] (D : B → Data) [FiniteNumbering (SortTag D)] (W : Wiring D)

omit [Fintype B] in
@[simp] theorem translate_anchor_incidence (ξ : ∀ b, (D b).Valuation 1) (b : B) (i : Fin 3) :
    incidenceTranslation D ξ (anchor D 0 b,i)=(anchor D 1 b,i) := rfl

end VariableWL.PrefixParts.Wiring

namespace VariableWL.PrefixParts.Wiring
open VariableWL.Affine VariableWL.SubcubicRealization
attribute [local instance] Classical.propDecidable
variable {B : Type uVariable8} [Fintype B] [FiniteNumbering B] (D : B → Data) [FiniteNumbering (SortTag D)] (W : Wiring D)

abbrev UncoloredVertex (ε : Bit) := SubcubicRealization.Vertex (@color B _ D _ ε)

noncomputable def uncolored (ε : Bit) : SimpleGraph (UncoloredVertex D ε) :=
  SubcubicRealization.graph (W.ports D ε) (color D)

end VariableWL.PrefixParts.Wiring

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Coordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7

namespace VariableWL.BlockCoordinates
open VariableWL.Affine VariableWL.Blocks Subdivision
attribute [local instance] Classical.propDecidable
variable {r n : ℕ} {P : Type uVariable1} {E : Type uVariable2} (J : ProductImages.Instance r P E)

def Coordinate : RawBlock r n P E → Type
  | .inl h => Fin (dimension J h.type)
  | .inr s => (Fin (dimension J (left J.source s.link)) ⊕
      Fin (dimension J (right J.target s.link))) ⊕ Bool

instance coordinateFintype (b : RawBlock r n P E) : Fintype (Coordinate J b) := by
  cases b <;> dsimp only [Coordinate] <;> infer_instance

def coordinateEquiv (b : RawBlock r n P E) : RawValue J b ≃+ (Coordinate J b → Bit) := by
  cases b with
  | inl h => exact AddEquiv.refl _
  | inr s =>
    exact {
      toFun := fun z => Sum.elim (Sum.elim z.1.1 z.1.2) (fun t => if t then z.2.2 else z.2.1)
      invFun := fun f => ((fun i => f (.inl (.inl i)),fun i => f (.inl (.inr i))),
        (f (.inr false),f (.inr true)))
      left_inv := fun z => by cases z; rfl
      right_inv := fun f => by
        funext i
        rcases i with (i | i) | t
        · rfl
        · rfl
        · cases t <;> rfl
      map_add' := fun z w => by
        funext i
        rcases i with (i | i) | t
        · rfl
        · rfl
        · cases t <;> rfl }

noncomputable def numbering (b : RawBlock r n P E) : Coordinate J b ≃ Fin (Fintype.card (Coordinate J b)) :=
  Fintype.equivFin _

noncomputable def encode (b : RawBlock r n P E) : RawValue J b ≃+ Vec (Fintype.card (Coordinate J b)) where
  toFun z := coordinateEquiv J b z ∘ (numbering J b).symm
  invFun f := (coordinateEquiv J b).symm (f ∘ numbering J b)
  left_inv z := by simp only [Function.comp_def,Equiv.symm_apply_apply]; exact (coordinateEquiv J b).symm_apply_apply z
  right_inv f := by funext i; simp
  map_add' z w := by funext i; exact congrFun ((coordinateEquiv J b).map_add z w) _

def readoutDimension : Readout r n P E → ℕ
  | .inl h => dimension J h.type
  | .inr _ => 1

def readoutEquiv (a : Readout r n P E) : ReadoutValue J a ≃+ Vec (readoutDimension J a) := by
  cases a with
  | inl h => exact AddEquiv.refl _
  | inr v =>
    change Bit ≃+ Vec 1
    exact { toFun := fun z _ => z
            invFun := fun f => f 0
            left_inv := fun _ => rfl
            right_inv := fun f => by funext i; have : i=0 := Subsingleton.elim _ _; subst i; rfl
            map_add' := fun _ _ => rfl }

theorem coordinate_lift (hr : 2 ≤ r) (hn : 0 < n) {b : RawBlock r n P E}
    {a : Readout r n P E} (ha : HasReadout J b a) :
    ∃ e : Fin (readoutDimension J a) ↪ Coordinate J b,
      ∀ z i, coordinateEquiv J b z (e i)=readoutEquiv J a (readout J z ha) i := by
  cases b with
  | inl h =>
    cases ha
    refine ⟨Function.Embedding.refl _,?_⟩
    intro z i
    rw [readout_eq J hr hn (b := .inl h) (z := z) (a := .inl h) rfl ⟨rfl,HEq.rfl⟩]
    rfl
  | inr s =>
    rcases ha with rfl | rfl | rfl | rfl
    · refine ⟨⟨fun i => .inl (.inl i),fun i j h => Sum.inl.inj (Sum.inl.inj h)⟩,?_⟩
      intro z i
      rw [readout_eq J hr hn (b := .inr s) (z := z) (a := (.inl (squareLeft J s))) (Or.inl rfl) (Or.inl ⟨rfl,HEq.rfl⟩)]
      rfl
    · refine ⟨⟨fun i => .inl (.inr i),fun i j h => Sum.inr.inj (Sum.inl.inj h)⟩,?_⟩
      intro z i
      rw [readout_eq J hr hn (b := .inr s) (z := z) (a := (.inl (squareRight J s))) (Or.inr (Or.inl rfl)) (Or.inr (Or.inl ⟨rfl,HEq.rfl⟩))]
      rfl
    · refine ⟨⟨fun _ => .inr false,by intro i j _; apply Fin.ext; have hi : i.val<1 := i.isLt; have hj : j.val<1 := j.isLt; omega⟩,?_⟩
      intro z i
      rw [readout_eq J hr hn (b := .inr s) (z := z) (a := (.inr (squareBottom s))) (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inl ⟨rfl,HEq.rfl⟩)))]
      rfl
    · refine ⟨⟨fun _ => .inr true,by intro i j _; apply Fin.ext; have hi : i.val<1 := i.isLt; have hj : j.val<1 := j.isLt; omega⟩,?_⟩
      intro z i
      rw [readout_eq J hr hn (b := .inr s) (z := z) (a := (.inr (squareTop s))) (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (Or.inr (Or.inr ⟨rfl,HEq.rfl⟩)))]
      rfl

noncomputable def readoutEmbedding (hr : 2 ≤ r) (hn : 0 < n) {b : RawBlock r n P E}
    {a : Readout r n P E} (ha : HasReadout J b a) :
    Fin (readoutDimension J a) ↪ Fin (Fintype.card (Coordinate J b)) :=
  (coordinate_lift J hr hn ha).choose.trans (numbering J b).toEmbedding

theorem readoutEmbedding_spec (hr : 2 ≤ r) (hn : 0 < n) {b : RawBlock r n P E}
    {a : Readout r n P E} (ha : HasReadout J b a) (z : RawValue J b) (i : Fin (readoutDimension J a)) :
    encode J b z (readoutEmbedding J hr hn ha i)=readoutEquiv J a (readout J z ha) i := by
  simpa only [encode,AddEquiv.coe_mk,Equiv.coe_fn_mk,Function.comp_apply,readoutEmbedding,
    Function.Embedding.trans_apply,Equiv.toEmbedding_apply,Equiv.symm_apply_apply] using
    (coordinate_lift J hr hn ha).choose_spec z i

theorem readoutDimension_le (hr : 2 ≤ r) (hn : 0 < n) {b : RawBlock r n P E}
    {a : Readout r n P E} (ha : HasReadout J b a) :
    readoutDimension J a ≤ Fintype.card (Coordinate J b) := by
  simpa using Fintype.card_le_of_injective _ (readoutEmbedding J hr hn ha).injective

theorem exists_readout_order (hr : 2 ≤ r) (hn : 0 < n) {b : RawBlock r n P E}
    {a : Readout r n P E} (ha : HasReadout J b a) :
    ∃ e : Equiv.Perm (Fin (Fintype.card (Coordinate J b))),
      ∀ i : Fin (readoutDimension J a),
      e ⟨i.val,lt_of_lt_of_le i.isLt (readoutDimension_le J hr hn ha)⟩=readoutEmbedding J hr hn ha i := by
  exact Equiv.Perm.exists_extending_pair
    (fun i : Fin (readoutDimension J a) => (⟨i.val,lt_of_lt_of_le i.isLt (readoutDimension_le J hr hn ha)⟩ :
      Fin (Fintype.card (Coordinate J b)))) (readoutEmbedding J hr hn ha)
    (fun _ _ h => Fin.ext (congrArg (fun x : Fin (Fintype.card (Coordinate J b)) => x.val) h)) (readoutEmbedding J hr hn ha).injective

end VariableWL.BlockCoordinates

namespace VariableWL.BlockCoordinates
open VariableWL.Affine VariableWL.Blocks Subdivision VariableWL.PrefixParts
attribute [local instance] Classical.propDecidable
variable {r n : ℕ} {P : Type uVariable3} {E : Type uVariable4} [Fintype P] [Fintype E]
  (J : ProductImages.Instance r P E)

abbrev Proper (b : Block (n := n) J) :=
  Σ c : {c : Block (n := n) J // c≠b}, {a : Readout r n P E // HasReadout J b.val a ∧ HasReadout J c.val.val a}

noncomputable instance (priority := 10) defaultProperNumberings :
    (b : Block (n := n) J) → FiniteNumbering (Proper J b) :=
  fun b=>defaultFiniteNumbering (Proper J b)
variable [∀ b : Block (n := n) J, FiniteNumbering (Proper J b)]

noncomputable def properNumber (b : Block (n := n) J) :
    Proper J b ≃ {c : Fin (Fintype.card (Proper J b)+1) // c.val≠0} where
  toFun p := ⟨(enumeration (Proper J b) p).succ,by simp⟩
  invFun c := (enumeration (Proper J b)).symm ⟨c.val.val-1,by have := c.val.isLt; have := c.property; omega⟩
  left_inv p := by simp
  right_inv c := by apply Subtype.ext; apply Fin.ext; simp; have := c.property; omega

noncomputable def channelRoot (b : Block (n := n) J)
    (c : Fin (Fintype.card (Proper J b)+1)) : ℕ :=
  if h : c.val=0 then 0 else readoutDimension J ((properNumber J b).symm ⟨c,h⟩).2.val

noncomputable def channelOrder (hr : 2 ≤ r) (hn : 0 < n) (b : Block (n := n) J)
    (c : Fin (Fintype.card (Proper J b)+1)) : Equiv.Perm (Fin (Fintype.card (Coordinate J b.val))) :=
  if h : c.val=0 then Equiv.refl _ else
    (exists_readout_order J hr hn ((properNumber J b).symm ⟨c,h⟩).2.property.1).choose

noncomputable def data (hr : 2 ≤ r) (hn : 0 < n) (marked : Fin r) (b : Block (n := n) J) : Data where
  dimension := Fintype.card (Coordinate J b.val)
  channels := Fintype.card (Proper J b)+1
  positive := Nat.zero_lt_succ _
  root := channelRoot J b
  root_le c := by
    unfold channelRoot
    split_ifs with h
    · exact Nat.zero_le _
    · exact readoutDimension_le J hr hn ((properNumber J b).symm ⟨c,h⟩).2.property.1
  zero_root := by simp [channelRoot]
  order := channelOrder J hr hn b
  legal ε := {z | LegalValue J marked ε b.val ((encode J b.val).symm z)}
  nonempty ε := by
    obtain ⟨z,hz⟩ := legal_nonempty J marked ε b.val
    exact ⟨encode J b.val z,by simpa using hz⟩
  coset ξ hξ z := by
    change boundaryMap J b.val ((encode J b.val).symm z) = 0 * inhomogeneity J marked b.val ↔
      boundaryMap J b.val ((encode J b.val).symm (z+ξ)) = 1 * inhomogeneity J marked b.val
    change boundaryMap J b.val ((encode J b.val).symm ξ) = 1 * inhomogeneity J marked b.val at hξ
    rw [map_add,map_add,hξ,zero_mul]
    exact add_eq_right.symm

noncomputable def valuationEquiv (hr : 2 ≤ r) (hn : 0 < n) (marked : Fin r) (b : Block (n := n) J) (ε : Bit) :
    Valuation J marked ε b ≃ (data J hr hn marked b).Valuation ε where
  toFun z := ⟨encode J b.val z.val,by
    change LegalValue J marked ε b.val ((encode J b.val).symm (encode J b.val z.val))
    rw [AddEquiv.symm_apply_apply]
    exact z.property⟩
  invFun z := ⟨(encode J b.val).symm z.val,z.property⟩
  left_inv z := Subtype.ext ((encode J b.val).symm_apply_apply _)
  right_inv z := Subtype.ext ((encode J b.val).apply_symm_apply _)

def properSwap : (Σ b : Block (n := n) J, Proper J b) ≃ (Σ b : Block (n := n) J, Proper J b) where
  toFun x := ⟨x.2.1.val,⟨x.1,Ne.symm x.2.1.property⟩,x.2.2.val,x.2.2.property.symm⟩
  invFun x := ⟨x.2.1.val,⟨x.1,Ne.symm x.2.1.property⟩,x.2.2.val,x.2.2.property.symm⟩
  left_inv x := by rfl
  right_inv x := by rfl

noncomputable def channelEquiv (hr : 2 ≤ r) (hn : 0 < n) (marked : Fin r) :
    (Σ b : Block (n := n) J, Proper J b) ≃ Channel (data J hr hn marked) where
  toFun x := ⟨x.1,properNumber J x.1 x.2⟩
  invFun x := ⟨x.1,(properNumber J x.1).symm x.2⟩
  left_inv x := by simp
  right_inv x := by
    rcases x with ⟨b,c⟩
    change (⟨b,properNumber J b ((properNumber J b).symm c)⟩ : Channel (data J hr hn marked))=⟨b,c⟩
    exact congrArg (fun d : {c : Fin (Fintype.card (Proper J b)+1) // c.val ≠ 0} =>
      (⟨b,d⟩ : Channel (data J hr hn marked))) ((properNumber J b).apply_symm_apply c)

theorem channelRoot_number (b : Block (n := n) J) (p : Proper J b) :
    channelRoot J b (properNumber J b p).val=readoutDimension J p.2.val := by
  rw [channelRoot,dite_eq_right (properNumber J b p).property]
  change readoutDimension J ((properNumber J b).symm (properNumber J b p)).2.val=_
  rw [Equiv.symm_apply_apply]

noncomputable def wiring (hr : 2 ≤ r) (hn : 0 < n) (marked : Fin r) : Wiring (data J hr hn marked) where
  mate := (channelEquiv J hr hn marked).symm.trans ((properSwap J).trans (channelEquiv J hr hn marked))
  involutive c := by
    change (channelEquiv J hr hn marked) ((properSwap J) ((channelEquiv J hr hn marked).symm
      ((channelEquiv J hr hn marked) ((properSwap J) ((channelEquiv J hr hn marked).symm c)))))=c
    rw [Equiv.symm_apply_apply]
    change (channelEquiv J hr hn marked) ((channelEquiv J hr hn marked).symm c)=c
    exact Equiv.apply_symm_apply _ _
  different c := by
    obtain ⟨⟨b,p⟩,rfl⟩ := (channelEquiv J hr hn marked).surjective c
    change ((channelEquiv J hr hn marked) ((properSwap J) ((channelEquiv J hr hn marked).symm
      ((channelEquiv J hr hn marked) ⟨b,p⟩)))).1≠b
    rw [Equiv.symm_apply_apply]
    exact p.1.property
  root_eq c := by
    obtain ⟨⟨b,p⟩,rfl⟩ := (channelEquiv J hr hn marked).surjective c
    change (data J hr hn marked
      ((channelEquiv J hr hn marked) ((properSwap J) ((channelEquiv J hr hn marked).symm
        ((channelEquiv J hr hn marked) ⟨b,p⟩)))).1).root
      ((channelEquiv J hr hn marked) ((properSwap J) ((channelEquiv J hr hn marked).symm
        ((channelEquiv J hr hn marked) ⟨b,p⟩)))).2.val = _
    rw [Equiv.symm_apply_apply]
    change channelRoot J p.1.val
      (properNumber J p.1.val ⟨⟨b,Ne.symm p.1.property⟩,p.2.val,p.2.property.symm⟩).val =
      channelRoot J b (properNumber J b p).val
    rw [channelRoot_number,channelRoot_number]

end VariableWL.BlockCoordinates

namespace VariableWL.BlockCoordinates
open VariableWL.Affine VariableWL.Blocks Subdivision VariableWL.PrefixParts
open VariableWL.PrefixParts.Wiring
attribute [local instance] Classical.propDecidable
variable {r n : ℕ} {P : Type uVariable5} {E : Type uVariable6} (J : ProductImages.Instance r P E)

theorem readout_prefix (hr : 2 ≤ r) (hn : 0 < n) {b : RawBlock r n P E}
    {a : Readout r n P E} (ha : HasReadout J b a) (z : RawValue J b) :
    pad (Data.truncate (readoutDimension J a)
      (encode J b z ∘ (exists_readout_order J hr hn ha).choose)) =
    pad (readoutEquiv J a (readout J z ha)) := by
  funext j
  by_cases hj : j<readoutDimension J a
  · have hja : j<Fintype.card (Coordinate J b) := lt_of_lt_of_le hj (readoutDimension_le J hr hn ha)
    simp only [pad,dite_eq_left hja,dite_eq_left hj,Data.truncate,ite_eq_left hj,Function.comp_apply]
    rw [(exists_readout_order J hr hn ha).choose_spec ⟨j,hj⟩]
    exact readoutEmbedding_spec J hr hn ha z ⟨j,hj⟩
  · simp only [pad,dite_eq_right hj]
    split_ifs with hja
    · simp only [Data.truncate,ite_eq_right hj]
    · rfl

variable [Fintype P] [Fintype E] [∀ b : Block (n := n) J, FiniteNumbering (Proper J b)]

theorem channelOrder_number (hr : 2 ≤ r) (hn : 0 < n) (b : Block (n := n) J) (p : Proper J b) :
    channelOrder J hr hn b (properNumber J b p).val=
      (exists_readout_order J hr hn p.2.property.1).choose := by
  rw [channelOrder,dite_eq_right (properNumber J b p).property]
  change (exists_readout_order J hr hn
    ((properNumber J b).symm (properNumber J b p)).2.property.1).choose=_
  rw [Equiv.symm_apply_apply]

theorem data_prefix (hr : 2 ≤ r) (hn : 0 < n) (marked : Fin r) (b : Block (n := n) J)
    (p : Proper J b) {ε : Bit} (z : Valuation J marked ε b) :
    pad (Data.truncate ((data J hr hn marked b).root (properNumber J b p).val)
      (((valuationEquiv J hr hn marked b ε) z).val ∘
        (data J hr hn marked b).order (properNumber J b p).val)) =
    pad (readoutEquiv J p.2.val (readout J z.val p.2.property.1)) := by
  change pad (Data.truncate (channelRoot J b (properNumber J b p).val)
    (encode J b.val z.val ∘ channelOrder J hr hn b (properNumber J b p).val))=_
  rw [channelRoot_number,channelOrder_number]
  exact readout_prefix J hr hn p.2.property.1 z.val

@[simp] theorem mate_channel (hr : 2 ≤ r) (hn : 0 < n) (marked : Fin r)
    (x : Σ b : Block (n := n) J, Proper J b) :
    (wiring J hr hn marked).mate (channelEquiv J hr hn marked x)=
      channelEquiv J hr hn marked (properSwap J x) := by
  change (channelEquiv J hr hn marked) ((properSwap J)
    ((channelEquiv J hr hn marked).symm ((channelEquiv J hr hn marked) x)))=_
  rw [Equiv.symm_apply_apply]

noncomputable def encodeList (hr : 2 ≤ r) (hn : 0 < n) (marked : Fin r)
    (ξ : ∀ b : Block (n := n) J, Valuation J marked 1 b) :
    ∀ b, (data J hr hn marked b).Valuation 1 := fun b => valuationEquiv J hr hn marked b 1 (ξ b)

end VariableWL.BlockCoordinates

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_SubcubicGame
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

noncomputable abbrev graph (ε : Bit) := uncolored (data (n := n) J hr hn marked) (wiring J hr hn marked) ε
noncomputable abbrev finiteGraph (ε : Bit) := TypedGame.numbered (graph J hr hn marked ε)

end VariableWL.Subcubic

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Circuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10 uVariable11 uVariable12 uVariable13 uVariable14

namespace VariableWL.Circuit
attribute [local instance] Classical.propDecidable
open VariableWL.ScalarImages
variable (S : Type uVariable1) (A : Type uVariable2) (E : Type uVariable3)
abbrev Gate := S ⊕ A
abbrev Port := S ⊕ (A × Bool)

abbrev target : Port S A → Gate S A
  | .inl s => .inl s
  | .inr (a,_) => .inr a

abbrev Value : Gate S A → Type
  | .inl _ => Bit
  | .inr _ => Pair

def output : (g : Gate S A) → Value S A g → Bit
  | .inl _ => id
  | .inr _ => sum

def input : (p : Port S A) → Value S A (target S A p) → Bit
  | .inl _ => id
  | .inr (_,false) => Prod.fst
  | .inr (_,true) => Prod.snd

structure System where
  source : E → Gate S A
  destination : E → Port S A
  seeds : Set S
  tests : Set S
  terminal : ∀ s ∈ tests, ∀ e, source e ≠ .inl s

variable {S A E}
namespace System
variable (C : System S A E)

inductive TrueGate : Gate S A → Prop
  | seed (s : S) (hs : s ∈ C.seeds) : TrueGate (.inl s)
  | scalar (e : E) (s : S) (he : C.destination e=.inl s)
      (hs : TrueGate (C.source e)) : TrueGate (.inl s)
  | and (a : A) (e f : E) (he : C.destination e=.inr (a,false))
      (hf : C.destination f=.inr (a,true))
      (hs : TrueGate (C.source e)) (ht : TrueGate (C.source f)) : TrueGate (.inr a)

def TruePort (p : Port S A) : Prop := ∃ e, C.destination e=p ∧ C.TrueGate (C.source e)

theorem true_scalar_iff (s : S) : C.TrueGate (.inl s) ↔ s ∈ C.seeds ∨ C.TruePort (.inl s) := by
  constructor
  · intro h
    cases h with
    | seed s hs => exact Or.inl hs
    | scalar e s he hs => exact Or.inr ⟨e,he,hs⟩
  · rintro (hs | ⟨e,he,hs⟩)
    · exact .seed _ hs
    · exact .scalar e s he hs

theorem true_and_iff (a : A) : C.TrueGate (.inr a) ↔
    C.TruePort (.inr (a,false)) ∧ C.TruePort (.inr (a,true)) := by
  constructor
  · intro h
    cases h with
    | and a e f he hf hs ht => exact ⟨⟨e,he,hs⟩,⟨f,hf,ht⟩⟩
  · rintro ⟨⟨e,he,hs⟩,⟨f,hf,ht⟩⟩
    exact .and a e f he hf hs ht

structure Witness where
  gates : ∀ g : Gate S A, Set (Value S A g)
  buffers : E → Set Pair
  gates_nonempty : ∀ g, (gates g).Nonempty
  buffers_nonempty : ∀ e, (buffers e).Nonempty
  first : ∀ e, output S A (C.source e) '' gates (C.source e)=Prod.fst '' buffers e
  second : ∀ e, output S A (C.source e) '' gates (C.source e)=Prod.snd '' buffers e
  last : ∀ e, sum '' buffers e=input S A (C.destination e) '' gates (target S A (C.destination e))
  seed : ∀ s ∈ C.seeds, gates (.inl s)={0}
  test : ∀ s ∈ C.tests, gates (.inl s)={1}

variable (hfalse : ∀ s ∈ C.tests, ¬ C.TrueGate (.inl s))

noncomputable def gateSets : (g : Gate S A) → Set (Value S A g)
  | .inl s => if s ∈ C.tests then {1} else {x | C.TrueGate (.inl s) → x=0}
  | .inr a => andWitness (C.TruePort (.inr (a,false))) (C.TruePort (.inr (a,true)))

theorem gateSets_nonempty (g : Gate S A) : (C.gateSets g).Nonempty := by
  classical
  cases g with
  | inl s =>
    by_cases hs : s ∈ C.tests
    · exact ⟨1,by simp [gateSets,hs]⟩
    · exact ⟨0,by simp [gateSets,hs]⟩
  | inr a => exact andWitness_nonempty _ _

theorem gateSets_output_scalar {s : S} (hs : s ∉ C.tests) :
    output S A (.inl s) '' C.gateSets (.inl s)={x | C.TrueGate (.inl s) → x=0} := by
  simp [output,gateSets,hs]

theorem gateSets_output_and (a : A) :
    output S A (.inr a) '' C.gateSets (.inr a)={x | C.TrueGate (.inr a) → x=0} := by
  rw [output,gateSets,andWitness_sum]
  simp only [C.true_and_iff]

theorem gateSets_source (e : E) :
    output S A (C.source e) '' C.gateSets (C.source e)={x | C.TrueGate (C.source e) → x=0} := by
  cases h : C.source e with
  | inl s => exact C.gateSets_output_scalar (fun hs => C.terminal s hs e h)
  | inr a => exact C.gateSets_output_and a

include hfalse in
theorem gateSets_input_true {p : Port S A} (hp : C.TruePort p) :
    input S A p '' C.gateSets (target S A p)={0} := by
  classical
  rcases p with s | ⟨a,b⟩
  · have ht : C.TrueGate (.inl s) := (C.true_scalar_iff s).mpr (Or.inr hp)
    have hnt : s ∉ C.tests := fun hs => hfalse s hs ht
    simp [input,target,gateSets,hnt,ht]
  · cases b
    · change Prod.fst '' andWitness _ _={0}
      rw [andWitness_fst]
      ext x
      simp [hp]
    · change Prod.snd '' andWitness _ _={0}
      rw [andWitness_snd]
      ext x
      simp [hp]

noncomputable def bufferSets (e : E) : Set Pair :=
  if C.TrueGate (C.source e) then {(0,0)}
  else buffer (input S A (C.destination e) '' C.gateSets (target S A (C.destination e)))

theorem bufferSets_nonempty (e : E) : (C.bufferSets e).Nonempty := by
  classical
  by_cases hs : C.TrueGate (C.source e)
  · simp [bufferSets,hs]
  · simpa only [bufferSets,ite_eq_right hs] using
      buffer_nonempty ((C.gateSets_nonempty _).image _)

theorem bufferSets_first (e : E) :
    output S A (C.source e) '' C.gateSets (C.source e)=Prod.fst '' C.bufferSets e := by
  classical
  rw [C.gateSets_source]
  by_cases hs : C.TrueGate (C.source e)
  · simp [bufferSets,hs]
  · simp only [bufferSets,hs,false_implies,Set.ofPred_true]
    exact (buffer_image_fst ((C.gateSets_nonempty _).image _)).symm

theorem bufferSets_second (e : E) :
    output S A (C.source e) '' C.gateSets (C.source e)=Prod.snd '' C.bufferSets e := by
  classical
  rw [C.gateSets_source]
  by_cases hs : C.TrueGate (C.source e)
  · simp [bufferSets,hs]
  · simp only [bufferSets,hs,false_implies,Set.ofPred_true]
    exact (buffer_image_snd ((C.gateSets_nonempty _).image _)).symm

include hfalse in
theorem bufferSets_last (e : E) :
    sum '' C.bufferSets e=input S A (C.destination e) '' C.gateSets (target S A (C.destination e)) := by
  classical
  by_cases hs : C.TrueGate (C.source e)
  · rw [C.gateSets_input_true hfalse ⟨e,rfl,hs⟩]
    simp [bufferSets,hs,sum]
  · simpa only [bufferSets,ite_eq_right hs] using buffer_image_sum _

noncomputable def witness : C.Witness where
  gates := C.gateSets
  buffers := C.bufferSets
  gates_nonempty := C.gateSets_nonempty
  buffers_nonempty := C.bufferSets_nonempty
  first := C.bufferSets_first
  second := C.bufferSets_second
  last := C.bufferSets_last hfalse
  seed s hs := by
    have ht : C.TrueGate (.inl s) := .seed s hs
    have hnt : s ∉ C.tests := fun he => hfalse s he ht
    simp [gateSets,hnt,ht]
  test s hs := by simp [gateSets,hs]

end System
end VariableWL.Circuit

namespace VariableWL.Circuit
open VariableWL.Affine
attribute [local instance] Classical.propDecidable
variable {S : Type uVariable4} {A : Type uVariable5}

abbrev dimension : Gate S A → ℕ
  | .inl _ => 1
  | .inr _ => 2

def scalarVector (x : Bit) : Vec 1 := fun _ => x
def pairVector (x : ScalarImages.Pair) : Vec 2 := fun i => if i.val=0 then x.1 else x.2

def scalarValue (x : Vec 1) : Bit := x 0
def pairValue (x : Vec 2) : ScalarImages.Pair := (x 0,x 1)

@[simp] theorem scalarValue_vector (x : Bit) : scalarValue (scalarVector x)=x := rfl
@[simp] theorem pairValue_vector (x : ScalarImages.Pair) : pairValue (pairVector x)=x := by
  simp [pairValue,pairVector]
@[simp] theorem scalarVector_value (x : Vec 1) : scalarVector (scalarValue x)=x := by
  funext i
  exact congrArg x (Subsingleton.elim _ _)
@[simp] theorem pairVector_value (x : Vec 2) : pairVector (pairValue x)=x := by
  funext i
  fin_cases i <;> rfl

def outputLinear (g : Gate S A) : Vec (dimension g) →ₗ[Bit] Bit :=
  match g with
  | .inl _ => LinearMap.proj 0
  | .inr _ => (LinearMap.proj (0 : Fin 2) : Vec 2 →ₗ[Bit] Bit) + LinearMap.proj 1

def inputLinear (p : Port S A) : Vec (dimension (target S A p)) →ₗ[Bit] Bit :=
  match p with
  | .inl _ => LinearMap.proj 0
  | .inr (_,false) => LinearMap.proj 0
  | .inr (_,true) => LinearMap.proj 1

def gateAt {X : Type uVariable6} : Gate S A → X → Gate (S × X) (A × X)
  | .inl s,x => .inl (s,x)
  | .inr a,x => .inr (a,x)

def portAt {X : Type uVariable7} : Port S A → X → Port (S × X) (A × X)
  | .inl s,x => .inl (s,x)
  | .inr (a,b),x => .inr ((a,x),b)

@[simp] theorem target_portAt {X : Type uVariable8} (p : Port S A) (x : X) :
    target (S × X) (A × X) (portAt p x)=gateAt (target S A p) x := by
  cases p <;> rfl

structure Description (r : ℕ) (S : Type uVariable9) (A : Type uVariable10) (E : Type uVariable11) (R : Type uVariable12) where
  source : E → Gate S A
  destination : E → Port S A
  domain : E → Fin r → Finset Bool
  domain_nonempty : ∀ e i, (domain e i).Nonempty
  map : E → Fin r → Bool → Bool
  map_injective : ∀ e i, Set.InjOn (map e i) (domain e i)
  requestGate : R → S
  requestTest : R → Bool
  requestDomain : R → Fin r → Finset Bool
  request_nonempty : ∀ b i, (requestDomain b i).Nonempty

namespace Description
open ProductImages.Instance
variable {r : ℕ} {E : Type uVariable13} {R : Type uVariable14} (D : Description r S A E R)

def Allowed (e : E) (a : Address r) : Prop := ∀ i, a i ∈ D.domain e i
def RequestAllowed (b : R) (a : Address r) : Prop := ∀ i, a i ∈ D.requestDomain b i
def mapAddress (e : E) (a : Address r) : Address r := fun i => D.map e i (a i)

abbrev ExpandedEdges := Σ e, {a : Address r // D.Allowed e a}

def requests (v : Bool) : Set (S × Address r) :=
  {x | ∃ b, D.requestGate b=x.1 ∧ D.requestTest b=v ∧ D.RequestAllowed b x.2}

def Terminal : Prop := ∀ s a, (s,a) ∈ D.requests true →
  ∀ e z, D.Allowed e z → gateAt (D.source e) z ≠ .inl (s,a)

abbrev expanded (h : D.Terminal) : System (S × Address r) (A × Address r) D.ExpandedEdges where
  source x := gateAt (D.source x.1) x.2.val
  destination x := portAt (D.destination x.1) (D.mapAddress x.1 x.2.val)
  seeds := D.requests false
  tests := D.requests true
  terminal := fun ⟨s,a⟩ hs ⟨e,z⟩ => h s a hs e z.val z.property

abbrev Real := Gate S A ⊕ (E ⊕ Unit)
abbrev Comparison := (E ⊕ (E ⊕ E)) ⊕ R

abbrev realDimension : Real (S := S) (A := A) (E := E) → ℕ
  | .inl g => dimension g
  | .inr (.inl _) => 2
  | .inr (.inr _) => 1

abbrev comparisonSource : Comparison (E := E) (R := R) → Real (S := S) (A := A) (E := E)
  | .inl (.inl e) => .inl (D.source e)
  | .inl (.inr (.inl e)) => .inl (D.source e)
  | .inl (.inr (.inr e)) => .inr (.inl e)
  | .inr b => .inl (.inl (D.requestGate b))

abbrev comparisonTarget : Comparison (E := E) (R := R) → Real (S := S) (A := A) (E := E)
  | .inl (.inl e) => .inr (.inl e)
  | .inl (.inr (.inl e)) => .inr (.inl e)
  | .inl (.inr (.inr e)) => .inl (target S A (D.destination e))
  | .inr _ => .inr (.inr ())

abbrev consistency : ProductImages.Instance r
    (Real (S := S) (A := A) (E := E)) (Comparison (E := E) (R := R)) where
  dimension := realDimension
  dimension_one_or_two p := by
    rcases p with (s | a) | (e | u) <;> simp [realDimension,dimension]
  source := D.comparisonSource
  target := D.comparisonTarget
  domain c := match c with
    | .inl (.inl e) => D.domain e
    | .inl (.inr (.inl e)) => D.domain e
    | .inl (.inr (.inr e)) => D.domain e
    | .inr b => D.requestDomain b
  domain_nonempty c i := by
    rcases c with (e | (e | e)) | b
    · exact D.domain_nonempty e i
    · exact D.domain_nonempty e i
    · exact D.domain_nonempty e i
    · exact D.request_nonempty b i
  map c := match c with
    | .inl (.inl _) => fun _ => id
    | .inl (.inr (.inl _)) => fun _ => id
    | .inl (.inr (.inr e)) => D.map e
    | .inr _ => fun _ => id
  map_injective c i := by
    rcases c with (e | (e | e)) | b
    · exact Function.injective_id.injOn
    · exact Function.injective_id.injOn
    · exact D.map_injective e i
    · exact Function.injective_id.injOn
  linearLeft c := match c with
    | .inl (.inl e) => outputLinear (D.source e)
    | .inl (.inr (.inl e)) => outputLinear (D.source e)
    | .inl (.inr (.inr _)) => (LinearMap.proj (0 : Fin 2) : Vec 2 →ₗ[Bit] Bit) + LinearMap.proj 1
    | .inr _ => LinearMap.proj 0
  linearRight c := match c with
    | .inl (.inl _) => LinearMap.proj 0
    | .inl (.inr (.inl _)) => LinearMap.proj 1
    | .inl (.inr (.inr e)) => inputLinear (D.destination e)
    | .inr _ => 0
  constantLeft _ := 0
  constantRight c := match c with
    | .inl _ => 0
    | .inr b => if D.requestTest b then 1 else 0

end Description
end VariableWL.Circuit

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_CellularCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10

namespace VariableWL.Circuit
open VariableWL.Affine ProductImages.Instance
attribute [local instance] Classical.propDecidable
variable {S : Type uVariable1} {A : Type uVariable2} {r : ℕ}

noncomputable def decodeGates (Q : ∀ g : Gate S A, Address r → Set (Vec (dimension g))) :
    ∀ g : Gate (S × Address r) (A × Address r), Set (Value (S × Address r) (A × Address r) g)
  | .inl (s,a) => scalarValue '' Q (.inl s) a
  | .inr (b,a) => pairValue '' Q (.inr b) a

theorem decodeGates_nonempty (Q : ∀ g : Gate S A, Address r → Set (Vec (dimension g)))
    (h : ∀ g a, (Q g a).Nonempty) (g : Gate (S × Address r) (A × Address r)) :
    (decodeGates Q g).Nonempty := by
  rcases g with ⟨s,a⟩ | ⟨b,a⟩
  · exact (h (.inl s) a).image scalarValue
  · exact (h (.inr b) a).image pairValue

theorem output_decode (Q : ∀ g : Gate S A, Address r → Set (Vec (dimension g)))
    (g : Gate S A) (a : Address r) :
    output (S × Address r) (A × Address r) (gateAt g a) '' decodeGates Q (gateAt g a)=
      outputLinear g '' Q g a := by
  cases g <;> simp only [gateAt,decodeGates,Set.image_image] <;> rfl

theorem input_decode (Q : ∀ g : Gate S A, Address r → Set (Vec (dimension g)))
    (p : Port S A) (a : Address r) :
    input (S × Address r) (A × Address r) (portAt p a) ''
      decodeGates Q (target _ _ (portAt p a))=inputLinear p '' Q (target _ _ p) a := by
  rcases p with s | ⟨b,v⟩
  · simp only [portAt,target,decodeGates,Set.image_image]
    rfl
  · cases v <;> simp only [portAt,target,decodeGates,Set.image_image] <;> rfl

noncomputable def encodeGates
    (Q : ∀ g : Gate (S × Address r) (A × Address r), Set (Value (S × Address r) (A × Address r) g)) :
    ∀ g : Gate S A, Address r → Set (Vec (dimension g))
  | .inl s,a => scalarVector '' Q (.inl (s,a))
  | .inr b,a => pairVector '' Q (.inr (b,a))

theorem encodeGates_nonempty
    (Q : ∀ g : Gate (S × Address r) (A × Address r), Set (Value (S × Address r) (A × Address r) g))
    (h : ∀ g, (Q g).Nonempty) (g : Gate S A) (a : Address r) : (encodeGates Q g a).Nonempty := by
  cases g with
  | inl s => exact (h (.inl (s,a))).image scalarVector
  | inr b => exact (h (.inr (b,a))).image pairVector

theorem output_encode
    (Q : ∀ g : Gate (S × Address r) (A × Address r), Set (Value (S × Address r) (A × Address r) g))
    (g : Gate S A) (a : Address r) :
    outputLinear g '' encodeGates Q g a=
      output (S × Address r) (A × Address r) (gateAt g a) '' Q (gateAt g a) := by
  cases g <;> simp only [encodeGates,Set.image_image] <;> rfl

theorem input_encode
    (Q : ∀ g : Gate (S × Address r) (A × Address r), Set (Value (S × Address r) (A × Address r) g))
    (p : Port S A) (a : Address r) :
    inputLinear p '' encodeGates Q (target _ _ p) a=
      input (S × Address r) (A × Address r) (portAt p a) '' Q (target _ _ (portAt p a)) := by
  rcases p with s | ⟨b,v⟩
  · simp only [inputLinear,target,encodeGates,Set.image_image]
    rfl
  · cases v <;> simp only [inputLinear,target,encodeGates,Set.image_image] <;> rfl

theorem const_image {X : Type uVariable3} {Y : Type uVariable4} (Q : Set X) (hq : Q.Nonempty) (y : Y) :
    (fun _ : X => y) '' Q={y} := by
  ext z
  simp only [Set.mem_image,Set.mem_singleton_iff]
  exact ⟨fun ⟨_,_,he⟩ => he.symm,fun he => by subst z; obtain ⟨x,hx⟩ := hq; exact ⟨x,hx,rfl⟩⟩

namespace Description
variable {E : Type uVariable5} {R : Type uVariable6} (D : Description r S A E R)

noncomputable def decodeWitness (h : D.Terminal) (Q : D.consistency.Witness) :
    (D.expanded h).Witness where
  gates := decodeGates (fun g a => Q.values (.inl g) a)
  buffers x := pairValue '' Q.values (.inr (.inl x.1)) x.2.val
  gates_nonempty := decodeGates_nonempty _ (fun g a => Q.nonempty (.inl g) a)
  buffers_nonempty x := (Q.nonempty (.inr (.inl x.1)) x.2.val).image _
  first x := by
    change output _ _ (gateAt (D.source x.1) x.2.val) '' _ = _
    rw [output_decode]
    have hz := Q.images (.inl (.inl x.1)) x.2.val x.2.property
    change (fun v => outputLinear (D.source x.1) v+0) '' Q.values (.inl (D.source x.1)) x.2.val=
      (fun v : Vec 2 => v 0+0) '' Q.values (.inr (.inl x.1)) x.2.val at hz
    simpa only [add_zero,Set.image_image,Function.comp_def,pairValue] using hz
  second x := by
    change output _ _ (gateAt (D.source x.1) x.2.val) '' _ = _
    rw [output_decode]
    have hz := Q.images (.inl (.inr (.inl x.1))) x.2.val x.2.property
    change (fun v => outputLinear (D.source x.1) v+0) '' Q.values (.inl (D.source x.1)) x.2.val=
      (fun v : Vec 2 => v 1+0) '' Q.values (.inr (.inl x.1)) x.2.val at hz
    simpa only [add_zero,Set.image_image,Function.comp_def,pairValue] using hz
  last x := by
    change ScalarImages.sum '' _=input _ _ (portAt (D.destination x.1) (D.mapAddress x.1 x.2.val)) '' _
    rw [input_decode]
    have hz := Q.images (.inl (.inr (.inr x.1))) x.2.val x.2.property
    change (fun v : Vec 2 => (v 0+v 1)+0) '' Q.values (.inr (.inl x.1)) x.2.val=
      (fun v => inputLinear (D.destination x.1) v+0) ''
        Q.values (.inl (target _ _ (D.destination x.1))) (D.mapAddress x.1 x.2.val) at hz
    simpa only [add_zero,Set.image_image,Function.comp_def,pairValue,ScalarImages.sum] using hz
  seed s hs := by
    obtain ⟨b,hb,hv,ha⟩ := hs
    have hz := Q.images (.inr b) s.2 ha
    change (fun v : Vec 1 => v 0+0) '' Q.values (.inl (.inl (D.requestGate b))) s.2=
      (fun _ : Vec 1 => (0 : Bit)+(if D.requestTest b then (1 : Bit) else 0)) '' Q.values (.inr (.inr ())) s.2 at hz
    simp only [add_zero,hv,Bool.false_eq_true,ite_false] at hz
    have hc := const_image (Q.values (.inr (.inr ())) s.2) (Q.nonempty _ _) (0 : Bit)
    have heq := congrArg (fun t : S => scalarValue '' Q.values (.inl (.inl t)) s.2) hb
    exact heq.symm.trans (hz.trans hc)
  test s hs := by
    obtain ⟨b,hb,hv,ha⟩ := hs
    have hz := Q.images (.inr b) s.2 ha
    change (fun v : Vec 1 => v 0+0) '' Q.values (.inl (.inl (D.requestGate b))) s.2=
      (fun _ : Vec 1 => (0 : Bit)+(if D.requestTest b then (1 : Bit) else 0)) '' Q.values (.inr (.inr ())) s.2 at hz
    simp only [add_zero,zero_add,hv,ite_true] at hz
    have hc := const_image (Q.values (.inr (.inr ())) s.2) (Q.nonempty _ _) (1 : Bit)
    have heq := congrArg (fun t : S => scalarValue '' Q.values (.inl (.inl t)) s.2) hb
    exact heq.symm.trans (hz.trans hc)

noncomputable def encodedValues (h : D.Terminal) (Q : (D.expanded h).Witness) :
    ∀ p : (Real (S := S) (A := A) (E := E)), Address r → Set (Vec (realDimension p))
  | .inl g,a => encodeGates Q.gates g a
  | .inr (.inl e),a => if ha : D.Allowed e a then pairVector '' Q.buffers ⟨e,⟨a,ha⟩⟩ else Set.univ
  | .inr (.inr _),_ => Set.univ

theorem encodedValues_nonempty (h : D.Terminal) (Q : (D.expanded h).Witness)
    (p : (Real (S := S) (A := A) (E := E))) (a : Address r) : (D.encodedValues h Q p a).Nonempty := by
  rcases p with g | (e | u)
  · exact encodeGates_nonempty Q.gates Q.gates_nonempty g a
  · dsimp only [encodedValues]
    split_ifs with ha
    · exact (Q.buffers_nonempty _).image _
    · exact Set.univ_nonempty
  · exact Set.univ_nonempty

noncomputable def encodeWitness (h : D.Terminal) (Q : (D.expanded h).Witness) :
    D.consistency.Witness where
  values := D.encodedValues h Q
  nonempty := D.encodedValues_nonempty h Q
  images c a ha := by
    rcases c with (e | (e | e)) | b
    · change (fun v => outputLinear (D.source e) v+0) '' encodeGates Q.gates (D.source e) a=
        (fun v : Vec 2 => v 0+0) '' D.encodedValues h Q (.inr (.inl e)) a
      simp only [add_zero]
      have hea : D.Allowed e a := ha
      rw [encodedValues,dite_eq_left hea,output_encode,Set.image_image]
      exact Q.first ⟨e,⟨a,hea⟩⟩
    · change (fun v => outputLinear (D.source e) v+0) '' encodeGates Q.gates (D.source e) a=
        (fun v : Vec 2 => v 1+0) '' D.encodedValues h Q (.inr (.inl e)) a
      simp only [add_zero]
      have hea : D.Allowed e a := ha
      rw [encodedValues,dite_eq_left hea,output_encode,Set.image_image]
      exact Q.second ⟨e,⟨a,hea⟩⟩
    · change (fun v : Vec 2 => (v 0+v 1)+0) '' D.encodedValues h Q (.inr (.inl e)) a=
        (fun v => inputLinear (D.destination e) v+0) '' encodeGates Q.gates (target _ _ (D.destination e)) (D.mapAddress e a)
      simp only [add_zero]
      have hea : D.Allowed e a := ha
      rw [encodedValues,dite_eq_left hea,input_encode,Set.image_image]
      exact Q.last ⟨e,⟨a,hea⟩⟩
    · have hea : D.RequestAllowed b a := ha
      change (fun v : Vec 1 => v 0+0) '' (scalarVector '' Q.gates (.inl (D.requestGate b,a)))=
        (fun _ : Vec 1 => 0+(if D.requestTest b then (1 : Bit) else 0)) '' Set.univ
      simp only [add_zero,zero_add]
      rw [const_image _ Set.univ_nonempty,Set.image_image]
      change id '' Q.gates (.inl (D.requestGate b,a))={if D.requestTest b then (1 : Bit) else 0}
      rw [Set.image_id]
      cases hv : D.requestTest b
      · simpa only [hv,Bool.false_eq_true,ite_false] using
          Q.seed (D.requestGate b,a) ⟨b,rfl,hv,hea⟩
      · simpa only [hv,ite_true] using Q.test (D.requestGate b,a) ⟨b,rfl,hv,hea⟩

end Description
end VariableWL.Circuit

namespace VariableWL.Circuit.Cellular
attribute [local instance] Classical.propDecidable
variable (L : Type uVariable7) (J : Type uVariable8) (N : ℕ)
abbrev Triple := L × L × L
variable {L J N}

structure Data (L : Type uVariable9) (J : Type uVariable10) where
  rule : L → L → L → L
  previous : J → J
  next : J → J
  initial : J → L
  accepting : Set L

namespace Data
variable (D : Data L J)

def state : ℕ → J → L
  | 0 => D.initial
  | t+1 => fun j => D.rule (state t (D.previous j)) (state t j) (state t (D.next j))

end Data
end VariableWL.Circuit.Cellular

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Binary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6

namespace VariableWL.Binary
attribute [local instance] Classical.propDecidable
abbrev Digits (d : ℕ) := Fin d → Bool

def number : {d : ℕ} → Digits d → ℕ
  | 0,_ => 0
  | d+1,x => (x 0).toNat+2*number (fun i : Fin d => x i.succ)

theorem number_lt {d : ℕ} (x : Digits d) : number x<2^d := by
  induction d with
  | zero => simp [number]
  | succ d ih =>
    have ht := ih (fun i : Fin d => x i.succ)
    have hb : (x 0).toNat ≤ 1 := by cases x 0 <;> decide
    simp only [number,pow_succ]
    omega

theorem number_injective {d : ℕ} : Function.Injective (@number d) := by
  induction d with
  | zero => intro x y _; exact Subsingleton.elim _ _
  | succ d ih =>
    intro x y he
    have hb : x 0=y 0 := by
      dsimp only [number] at he
      cases hx : x 0 <;> cases hy : y 0 <;> simp_all only [Bool.toNat_false,Bool.toNat_true] <;> omega
    have ht : (fun i : Fin d => x i.succ)=(fun i : Fin d => y i.succ) := by
      apply ih
      dsimp only [number] at he
      rw [hb] at he
      omega
    funext i
    exact Fin.cases hb (fun j => congrFun ht j) i

@[simp] theorem number_false (d : ℕ) : number (fun _ : Fin d => false)=0 := by
  induction d with
  | zero => rfl
  | succ d ih => simp [number,ih]

@[simp] theorem number_true (d : ℕ) : number (fun _ : Fin d => true)+1=2^d := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [number,Bool.toNat_true,pow_succ]; omega

noncomputable def equivalence (d : ℕ) : Digits d ≃ Fin (2^d) :=
  Equiv.ofBijective (fun x => ⟨number x,number_lt x⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨fun x y h => number_injective (congrArg Fin.val h), by simp⟩)

@[simp] theorem equivalence_val {d : ℕ} (x : Digits d) : (equivalence d x).val=number x := rfl

def domain {d : ℕ} (bit : Bool) (h i : Fin d) : Finset Bool :=
  if i<h then {bit} else if i=h then {!bit} else Finset.univ

def table {d : ℕ} (h i : Fin d) (x : Bool) : Bool := if i≤h then !x else x

def Allowed {d : ℕ} (bit : Bool) (h : Fin d) (x : Digits d) : Prop := ∀ i, x i ∈ domain bit h i

def flip {d : ℕ} (h : Fin d) (x : Digits d) : Digits d := fun i => table h i (x i)

theorem domain_nonempty {d : ℕ} (bit : Bool) (h i : Fin d) : (domain bit h i).Nonempty := by
  unfold domain
  split_ifs <;> simp

theorem table_injective {d : ℕ} (h i : Fin d) : Function.Injective (table h i) := by
  intro x y he
  unfold table at he
  split_ifs at he with h
  · exact Bool.not_injective he
  · exact he

theorem allowed_iff {d : ℕ} (bit : Bool) (h : Fin d) (x : Digits d) :
    Allowed bit h x ↔ x h = !bit ∧ ∀ i, i<h → x i=bit := by
  constructor
  · intro hx
    exact ⟨by simpa [domain] using hx h,fun i hi => by simpa [domain,hi] using hx i⟩
  · rintro ⟨hh,hlt⟩ i
    by_cases hi : i<h
    · simp [domain,hi,hlt i hi]
    · by_cases he : i=h
      · subst i
        simp [domain,hh]
      · simp [domain,hi,he]

theorem number_flip {d : ℕ} (h : Fin d) (x : Digits d) (hx : Allowed true h x) :
    number (flip h x)=number x+1 := by
  induction d with
  | zero => exact Fin.elim0 h
  | succ d ih =>
    cases h using Fin.cases with
    | zero =>
      have hh : x 0=false := (allowed_iff true 0 x).mp hx |>.1
      have ht : (fun i : Fin d => flip 0 x i.succ)=(fun i : Fin d => x i.succ) := by
        funext i
        simp [flip,table]
      simp only [number]
      rw [ht]
      simp [flip,table,hh,Nat.add_comm]
    | succ h =>
      obtain ⟨hh,hlt⟩ := (allowed_iff true h.succ x).mp hx
      have hz : x 0=true := hlt 0 (Fin.succ_pos h)
      have htail : Allowed true h (fun i : Fin d => x i.succ) :=
        (allowed_iff true h _).mpr ⟨hh,fun i hi => hlt i.succ (Fin.succ_lt_succ_iff.mpr hi)⟩
      have ht : (fun i : Fin d => flip h.succ x i.succ)=flip h (fun i : Fin d => x i.succ) := by
        funext i
        simp [flip,table]
      have he := ih h (fun i : Fin d => x i.succ) htail
      simp only [number]
      rw [ht]
      simp only [flip,table,Fin.zero_le,ite_eq_left,hz,Bool.not_true,Bool.toNat_false,Bool.toNat_true,zero_add]
      omega

def cyclicDomain {d : ℕ} (bit : Bool) (h : Option (Fin d)) (i : Fin d) : Finset Bool :=
  match h with | none => {bit} | some h => domain bit h i

def cyclicTable {d : ℕ} (h : Option (Fin d)) (i : Fin d) (x : Bool) : Bool :=
  match h with | none => !x | some h => table h i x

def CyclicAllowed {d : ℕ} (bit : Bool) (h : Option (Fin d)) (x : Digits d) : Prop :=
  ∀ i, x i ∈ cyclicDomain bit h i

def cyclicFlip {d : ℕ} (h : Option (Fin d)) (x : Digits d) : Digits d := fun i => cyclicTable h i (x i)

theorem cyclicDomain_nonempty {d : ℕ} (bit : Bool) (h : Option (Fin d)) (i : Fin d) :
    (cyclicDomain bit h i).Nonempty := by
  cases h with
  | none => exact Finset.singleton_nonempty _
  | some h => exact domain_nonempty bit h i

theorem cyclicTable_injective {d : ℕ} (h : Option (Fin d)) (i : Fin d) :
    Function.Injective (cyclicTable h i) := by
  cases h with
  | none => exact Bool.not_injective
  | some h => exact table_injective h i

end VariableWL.Binary

namespace VariableWL.Binary
attribute [local instance] Classical.propDecidable

def GreaterAt {d : ℕ} (μ x : Digits d) (h : Fin d) : Prop :=
  μ h=false ∧ x h=true ∧ ∀ i, h < i → x i=μ i

def thresholdDomain {d : ℕ} (μ : Digits d) (h : Option {h : Fin d // μ h=false}) (i : Fin d) : Finset Bool :=
  match h with
  | none => {μ i}
  | some h => if h.val < i then {μ i} else if i=h.val then {true} else Finset.univ

def ThresholdAllowed {d : ℕ} (μ : Digits d) (h : Option {h : Fin d // μ h=false}) (x : Digits d) : Prop :=
  ∀ i, x i ∈ thresholdDomain μ h i

theorem thresholdDomain_nonempty {d : ℕ} (μ : Digits d) (h : Option {h : Fin d // μ h=false}) (i : Fin d) :
    (thresholdDomain μ h i).Nonempty := by
  cases h with
  | none => exact Finset.singleton_nonempty _
  | some h => simp only [thresholdDomain]; split_ifs <;> simp

end VariableWL.Binary

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_ProductCellular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9

namespace VariableWL.Circuit.ProductCellular
open Binary ProductImages.Instance
attribute [local instance] Classical.propDecidable
variable {L : Type uVariable1} {d m : ℕ}

abbrev Address (d : ℕ) := Fin (d+d) → Bool

def timeBits (x : Address d) : Digits d := fun i => x (i.castAdd d)
def positionBits (x : Address d) : Digits d := fun i => x (Fin.natAdd d i)
def join {α : Type uVariable2} (x y : Fin d → α) : Fin (d+d) → α := Fin.addCases x y

@[simp] theorem join_left {α : Type uVariable3} (x y : Fin d → α) (i : Fin d) : join x y (i.castAdd d)=x i :=
  Fin.addCases_left i
@[simp] theorem join_right {α : Type uVariable4} (x y : Fin d → α) (i : Fin d) : join x y (Fin.natAdd d i)=y i :=
  Fin.addCases_right i
@[simp] theorem join_addNat {α : Type uVariable5} (x y : Fin d → α) (i : Fin d) : join x y (i.addNat d)=y i := by
  rw [← Fin.natAdd_eq_addNat]
  exact join_right x y i
@[simp] theorem time_join (x y : Digits d) : timeBits (join x y)=x := by funext i; simp [timeBits]
@[simp] theorem position_join (x y : Digits d) : positionBits (join x y)=y := by funext i; simp [positionBits]
@[simp] theorem join_parts (x : Address d) : join (timeBits x) (positionBits x)=x := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [timeBits,positionBits]

theorem all_parts {P : Fin (d+d) → Prop} : (∀ i, P i) ↔
    (∀ i : Fin d, P (i.castAdd d)) ∧ (∀ i : Fin d, P (Fin.natAdd d i)) := Fin.forall_fin_add P

abbrev Kind (d : ℕ) := (Fin d × Option (Fin d)) ⊕ (Fin d ⊕ ((Fin d × Option (Fin d)) ⊕ Bool))
abbrev Edge (L : Type uVariable6) (d : ℕ) := Cellular.Triple L × Kind d

def left (h : Fin d) (j : Option (Fin d)) : Kind d := .inl (h,j)
def center (h : Fin d) : Kind d := .inr (.inl h)
def right (h : Fin d) (j : Option (Fin d)) : Kind d := .inr (.inr (.inl (h,j)))
def same (v : Bool) : Kind d := .inr (.inr (.inr v))

def timeDomain : Kind d → Fin d → Finset Bool
  | .inl (h,_) => Binary.domain true h
  | .inr (.inl h) => Binary.domain true h
  | .inr (.inr (.inl (h,_))) => Binary.domain true h
  | .inr (.inr (.inr _)) => fun _ => Finset.univ

def positionDomain : Kind d → Fin d → Finset Bool
  | .inl (_,j) => cyclicDomain true j
  | .inr (.inl _) => fun _ => Finset.univ
  | .inr (.inr (.inl (_,j))) => cyclicDomain false j
  | .inr (.inr (.inr _)) => fun _ => Finset.univ

def timeMap : Kind d → Fin d → Bool → Bool
  | .inl (h,_) => table h
  | .inr (.inl h) => table h
  | .inr (.inr (.inl (h,_))) => table h
  | .inr (.inr (.inr _)) => fun _ => id

def positionMap : Kind d → Fin d → Bool → Bool
  | .inl (_,j) => cyclicTable j
  | .inr (.inl _) => fun _ => id
  | .inr (.inr (.inl (_,j))) => cyclicTable j
  | .inr (.inr (.inr _)) => fun _ => id

def source : Edge L d → Gate L (Cellular.Triple L × Bool)
  | ((a,_,_),.inl _) => .inl a
  | ((_,b,_),.inr (.inl _)) => .inl b
  | ((_,_,c),.inr (.inr (.inl _))) => .inl c
  | (abc,.inr (.inr (.inr v))) => .inr (abc,v)

def destination (rule : L → L → L → L) : Edge L d → Port L (Cellular.Triple L × Bool)
  | (abc,.inl _) => .inr ((abc,false),false)
  | (abc,.inr (.inl _)) => .inr ((abc,false),true)
  | (abc,.inr (.inr (.inl _))) => .inr ((abc,true),true)
  | (abc,.inr (.inr (.inr false))) => .inr ((abc,true),false)
  | ((a,b,c),.inr (.inr (.inr true))) => .inl (rule a b c)

theorem timeDomain_nonempty (k : Kind d) (i : Fin d) : (timeDomain k i).Nonempty := by
  rcases k with ⟨h,j⟩ | h | ⟨h,j⟩ | v
  all_goals simp only [timeDomain]
  all_goals first | exact Binary.domain_nonempty _ _ _ | exact ⟨false,Finset.mem_univ _⟩

theorem positionDomain_nonempty (k : Kind d) (i : Fin d) : (positionDomain k i).Nonempty := by
  rcases k with ⟨h,j⟩ | h | ⟨h,j⟩ | v
  all_goals simp only [positionDomain]
  all_goals first | exact cyclicDomain_nonempty _ _ _ | exact ⟨false,Finset.mem_univ _⟩

theorem timeMap_injective (k : Kind d) (i : Fin d) : Function.Injective (timeMap k i) := by
  rcases k with ⟨h,j⟩ | h | ⟨h,j⟩ | v
  all_goals first | exact table_injective _ _ | exact Function.injective_id

theorem positionMap_injective (k : Kind d) (i : Fin d) : Function.Injective (positionMap k i) := by
  rcases k with ⟨h,j⟩ | h | ⟨h,j⟩ | v
  all_goals first | exact cyclicTable_injective _ _ | exact Function.injective_id

structure Data (L : Type uVariable7) (d m : ℕ) where
  rule : L → L → L → L
  input : Fin m → L
  blank : L
  accepting : Set L
  fits : m < 2^d

namespace Data
variable (D : Data L d m)
noncomputable def threshold : Digits d := (Binary.equivalence d).symm ⟨m,D.fits⟩
@[simp] theorem number_threshold : number D.threshold=m := by
  have h := congrArg Fin.val ((Binary.equivalence d).apply_symm_apply ⟨m,D.fits⟩)
  exact h

abbrev Request := (Fin m ⊕ Option {h : Fin d // D.threshold h=false}) ⊕ {f : L // f ∈ D.accepting}

def requestGate : D.Request → L
  | .inl (.inl j) => D.input j
  | .inl (.inr _) => D.blank
  | .inr f => f.val

def requestTest : D.Request → Bool
  | .inl _ => false
  | .inr _ => true

noncomputable def inputBits (j : Fin m) : Digits d := (Binary.equivalence d).symm ⟨j.val,j.isLt.trans D.fits⟩
@[simp] theorem number_inputBits (j : Fin m) : number (D.inputBits j)=j.val :=
  congrArg Fin.val ((Binary.equivalence d).apply_symm_apply ⟨j.val,j.isLt.trans D.fits⟩)

noncomputable def requestTimeDomain : D.Request → Fin d → Finset Bool
  | .inl _ => fun _ => {false}
  | .inr _ => fun _ => {true}
noncomputable def requestPositionDomain : D.Request → Fin d → Finset Bool
  | .inl (.inl j) => fun i => {D.inputBits j i}
  | .inl (.inr h) => thresholdDomain D.threshold h
  | .inr _ => fun _ => Finset.univ

noncomputable def description : Description (d+d) L (Cellular.Triple L × Bool) (Edge L d) D.Request where
  source := source
  destination := destination D.rule
  domain e := join (timeDomain e.2) (positionDomain e.2)
  domain_nonempty e i := Fin.addCases (fun j => by simpa using timeDomain_nonempty e.2 j)
    (fun j => by simpa using positionDomain_nonempty e.2 j) i
  map e := join (timeMap e.2) (positionMap e.2)
  map_injective e i := by
    apply Function.Injective.injOn
    exact Fin.addCases (fun j => by simpa using timeMap_injective e.2 j)
      (fun j => by simpa using positionMap_injective e.2 j) i
  requestGate := D.requestGate
  requestTest := D.requestTest
  requestDomain b := join (D.requestTimeDomain b) (D.requestPositionDomain b)
  request_nonempty b i := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rcases b with (j|h)|f <;> simp [requestTimeDomain]
    · rcases b with (j|h)|f
      · simp [requestPositionDomain]
      · simpa [requestPositionDomain] using thresholdDomain_nonempty D.threshold h _
      · simp [requestPositionDomain]

@[simp] theorem allowed_parts (abc : Cellular.Triple L) (k : Kind d) (x : Address d) :
    D.description.Allowed (abc,k) x ↔
    (∀ i, timeBits x i ∈ timeDomain k i) ∧ (∀ i, positionBits x i ∈ positionDomain k i) := by
  unfold Description.Allowed
  rw [all_parts]
  simp only [description,join_left,join_right,timeBits,positionBits]

@[simp] theorem time_mapAddress (e : Edge L d) (x : Address d) :
    timeBits (D.description.mapAddress e x)=fun i => timeMap e.2 i (timeBits x i) := by
  funext i
  simp [Description.mapAddress,description,timeBits]
@[simp] theorem position_mapAddress (e : Edge L d) (x : Address d) :
    positionBits (D.description.mapAddress e x)=fun i => positionMap e.2 i (positionBits x i) := by
  funext i
  simp [Description.mapAddress,description,positionBits]

@[simp] theorem request_parts (b : D.Request) (x : Address d) :
    D.description.RequestAllowed b x ↔
    (∀ i, timeBits x i ∈ D.requestTimeDomain b i) ∧
      (∀ i, positionBits x i ∈ D.requestPositionDomain b i) := by
  unfold Description.RequestAllowed
  rw [all_parts]
  simp only [description,join_left,join_right,timeBits,positionBits]

noncomputable def initial (j : Fin (2^d)) : L := if h : j.val < m then D.input ⟨j.val,h⟩ else D.blank

theorem tests_exact (f : L) (x : Address d) : (f,x) ∈ D.description.requests true ↔
    number (timeBits x)=2^d-1 ∧ f ∈ D.accepting := by
  classical
  have ht : (∀ i, timeBits x i=true) ↔ number (timeBits x)=2^d-1 := by
    have hb := number_true d
    constructor
    · intro h; rw [funext h]; omega
    · intro h
      have he := number_injective (a₁ := timeBits x) (a₂ := fun _ => true) (by omega)
      exact congrFun he
  constructor
  · rintro ⟨b,hg,hb,hreq⟩
    rcases b with (j|h)|f'
    · cases hb
    · cases hb
    · have hp := (D.request_parts _ _).mp hreq
      change f'.val=f at hg
      exact ⟨ht.mp (fun i => Finset.mem_singleton.mp (hp.1 i)),hg ▸ f'.property⟩
  · rintro ⟨hx,hf⟩
    refine ⟨.inr ⟨f,hf⟩,rfl,rfl,(D.request_parts _ _).mpr ⟨?_,?_⟩⟩
    · intro i; simpa [requestTimeDomain] using ht.mpr hx i
    · intro i; simp [requestPositionDomain]

theorem terminal : D.description.Terminal := by
  intro f x hx e z hz he
  obtain ⟨ht,_⟩ := (D.tests_exact f x).mp hx
  rcases e with ⟨⟨a,b,c⟩,(⟨h,j⟩|h|⟨h,j⟩|v)⟩
  all_goals try { cases he }
  all_goals
    have hxz : z=x := congrArg (fun g : Gate (L × Address d) ((Cellular.Triple L × Bool) × Address d) =>
      match g with | .inl s => s.2 | .inr s => s.2) he
    have hh := (D.allowed_parts _ _ _).mp hz |>.1
    have hi := number_flip h (timeBits z) hh
    have hb := number_lt (Binary.flip h (timeBits z))
    rw [hxz,ht] at hi
    rw [hxz] at hb
    have hpow : 0<2^d := pow_pos (by decide) _
    omega

end Data

end VariableWL.Circuit.ProductCellular

namespace VariableWL.Circuit.ProductCellular
open Binary
attribute [local instance] Classical.propDecidable
variable {L : Type uVariable8} {d m : ℕ}

instance powTwoNeZero (d : ℕ) : NeZero (2^d) := ⟨pow_ne_zero _ (by decide)⟩

noncomputable def position (x : Address d) : Fin (2^d) := Binary.equivalence d (positionBits x)

@[simp] theorem position_index_join (t p : Digits d) : position (join t p)=Binary.equivalence d p := by
  simp only [position,ProductCellular.position_join]

namespace Data
variable (D : Data L d m)

noncomputable abbrev system := D.description.expanded D.terminal

noncomputable def cellular : Cellular.Data L (Fin (2^d)) where
  rule := D.rule
  previous := fun j => j-1
  next := fun j => j+1
  initial := D.initial
  accepting := D.accepting

noncomputable abbrev state (t : ℕ) (j : Fin (2^d)) := D.cellular.state t j

@[simp] theorem same_allowed (abc : Cellular.Triple L) (v : Bool) (x : Address d) :
    D.description.Allowed (abc,same v) x := by
  simp [allowed_parts,timeDomain,positionDomain,same]

def gateMeaning : Gate (L × Address d) ((Cellular.Triple L × Bool) × Address d) → Prop
  | .inl (f,x) => D.state (number (timeBits x)) (position x)=f
  | .inr (((a,b,_),false),x) => 0 < number (timeBits x) ∧
      D.state (number (timeBits x)-1) (position x-1)=a ∧ D.state (number (timeBits x)-1) (position x)=b
  | .inr (((a,b,c),true),x) => 0 < number (timeBits x) ∧
      D.state (number (timeBits x)-1) (position x-1)=a ∧ D.state (number (timeBits x)-1) (position x)=b ∧
      D.state (number (timeBits x)-1) (position x+1)=c

def portMeaning : Port (L × Address d) ((Cellular.Triple L × Bool) × Address d) → Prop
  | .inl s => D.gateMeaning (.inl s)
  | .inr (((abc,false),x),false) => 0 < number (timeBits x) ∧
      D.state (number (timeBits x)-1) (position x-1)=abc.1
  | .inr (((abc,false),x),true) => 0 < number (timeBits x) ∧
      D.state (number (timeBits x)-1) (position x)=abc.2.1
  | .inr (((abc,true),x),false) => D.gateMeaning (.inr ((abc,false),x))
  | .inr (((abc,true),x),true) => 0 < number (timeBits x) ∧
      D.state (number (timeBits x)-1) (position x+1)=abc.2.2

end Data
end VariableWL.Circuit.ProductCellular

namespace VariableWL.Circuit.ProductCellular
open Binary
attribute [local instance] Classical.propDecidable
variable {L : Type uVariable9} {d m : ℕ}

noncomputable def previousTime (x : Address d) : Digits d :=
  (Binary.equivalence d).symm ⟨number (timeBits x)-1,Nat.lt_of_le_of_lt (Nat.sub_le _ _) (number_lt _)⟩
noncomputable def backAddress (x : Address d) (j : Fin (2^d)) : Address d :=
  join (previousTime x) ((Binary.equivalence d).symm j)

@[simp] theorem number_previousTime (x : Address d) : number (previousTime x)=number (timeBits x)-1 :=
  congrArg Fin.val ((Binary.equivalence d).apply_symm_apply _)
@[simp] theorem time_backAddress (x : Address d) (j : Fin (2^d)) :
    number (timeBits (backAddress x j))=number (timeBits x)-1 := by
  simp only [backAddress,time_join,number_previousTime]
@[simp] theorem position_backAddress (x : Address d) (j : Fin (2^d)) : position (backAddress x j)=j := by
  simp only [backAddress,position_index_join,Equiv.apply_symm_apply]

end VariableWL.Circuit.ProductCellular

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Program
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.Computation

variable {Γ : Type}

abbrev Symbol (Γ : Type) := Option (Bool ⊕ Γ)

def bitSymbol (b : Bool) : Symbol Γ := some (.inl b)

def typedWordCells (w : Word) (i : ℤ) : Symbol Γ :=
  if 0 ≤ i then w[i.toNat]?.map bitSymbol |>.join else none

structure Program (Q Γ : Type) (k : ℕ) where
  transition : Option Q → (Fin (k+1) → Symbol Γ) →
    Option (Option Q × (Fin (k+1) → Symbol Γ × Motion))

structure State (Q Γ : Type) (k : ℕ) where
  control : Option Q
  heads : Fin (k+1) → ℤ
  cells : Fin (k+1) → ℤ → Symbol Γ

namespace Program
variable {Q Γ : Type} {k : ℕ}

 def initial (w : Word) : State Q Γ k where
  control := none
  heads := fun _ => 0
  cells := fun j => if j=0 then typedWordCells w else fun _ => none

 def step (P : Program Q Γ k) (s : State Q Γ k) : Option (State Q Γ k) :=
  (P.transition s.control (fun j => s.cells j (s.heads j))).map fun data =>
    { control := data.1
      heads := fun j => s.heads j + (data.2 j).2.displacement
      cells := fun j i => if i=s.heads j then (data.2 j).1 else s.cells j i }

 def run (P : Program Q Γ k) (w : Word) : ℕ → State Q Γ k
  | 0 => initial w
  | n+1 => (P.step (P.run w n)).getD (P.run w n)

 def OutputsWithin (P : Program Q Γ k) (w out : Word) (bound : ℕ) : Prop :=
  ∃ t ≤ bound, P.step (P.run w t)=none ∧
    (P.run w t).cells 0 = typedWordCells out

noncomputable section
variable [Fintype Q] [Fintype Γ]

 def controlCode : Option Q → Fin (Fintype.card Q+1)
  | none => ⟨0, by omega⟩
  | some q => ⟨(Fintype.equivFin Q q).val+1, by omega⟩

 def symbolCode : Symbol Γ → Fin (Fintype.card Γ+3)
  | none => ⟨0, by omega⟩
  | some (.inl false) => ⟨1, by omega⟩
  | some (.inl true) => ⟨2, by omega⟩
  | some (.inr a) => ⟨(Fintype.equivFin Γ a).val+3, by omega⟩

 def controlDecode := Function.invFun (controlCode (Q:=Q))
 def symbolDecode := Function.invFun (symbolCode (Γ:=Γ))

 def compile (P : Program Q Γ k) : Machine where
  states := Fintype.card Q
  workSymbols := Fintype.card Γ
  extraTapes := k
  transition := fun q as =>
    (P.transition (controlDecode q) (fun j => symbolDecode (as j))).map fun d =>
      (controlCode d.1, fun j => (symbolCode (d.2 j).1, (d.2 j).2))

 def encodeState (P : Program Q Γ k) (s : State Q Γ k) : Configuration P.compile where
  control := controlCode s.control
  heads := s.heads
  cells := fun j i => symbolCode (s.cells j i)

end
end Program
end VariableWL.Computation

namespace VariableWL.Computation

variable {Γ : Type}

 def stackCells (w : Word) (i : ℤ) : Symbol Γ := typedWordCells w (i+w.length)
 def stackHead (w : Word) : ℤ := -(w.length:ℤ)

namespace Stack

inductive Action where
  | keep | pop | push (b : Bool)
  deriving DecidableEq,Fintype

 def Action.apply : Action → Word → Word
  | .keep,w => w
  | .pop,w => w.tail
  | .push b,w => b::w

 def Action.firstMove : Action → Option Bool → Motion
  | .push _,_ => .left
  | .pop,some _ => .right
  | _,_ => .stay

 def Action.firstWrite (a : Action) (top : Option Bool) : Symbol Γ :=
  if a=.pop then none else top.bind bitSymbol

 def Action.secondWrite (a : Action) (current : Symbol Γ) : Symbol Γ :=
  match a with
  | .push b => bitSymbol b
  | _ => current

structure Machine (Q : Type) (k : ℕ) where
  start : Q
  output : Fin (k+1)
  transition : Q → (Fin (k+1) → Option Bool) → Option (Q × (Fin (k+1) → Action))

structure State (Q : Type) (k : ℕ) where
  control : Q
  tapes : Fin (k+1) → Word

variable {Q : Type} {k : ℕ}

 def Machine.step (M : Machine Q k) (s : State Q k) : Option (State Q k) :=
  (M.transition s.control (fun j => (s.tapes j).head?)).map fun d =>
    {control := d.1,tapes := fun j => (d.2 j).apply (s.tapes j)}

 def Machine.initial (M : Machine Q k) (w : Word) : State Q k where
  control := M.start
  tapes := fun j => if j=0 then w.reverse else []

 def Machine.run (M : Machine Q k) (w : Word) : ℕ → State Q k
  | 0 => M.initial w
  | n+1 => (M.step (M.run w n)).getD (M.run w n)

 def Machine.OutputsWithin (M : Machine Q k) (w out : Word) (T : ℕ) : Prop :=
  ∃ t ≤ T, M.step (M.run w t)=none ∧ (M.run w t).tapes M.output=out

end Stack
end VariableWL.Computation

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Stack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.Computation

variable {Q Γ : Type} {k : ℕ}

namespace Program
variable {Q Γ : Type} {k : ℕ}

 def evolve (P : Program Q Γ k) (s : State Q Γ k) : ℕ → State Q Γ k
  | 0 => s
  | n+1 => (P.step (P.evolve s n)).getD (P.evolve s n)

end Program

namespace Stack

inductive Control (Q : Type) (k : ℕ) where
  | read
  | put (b : Bool)
  | back
  | execute (q : Q)
  | pending (q : Q) (acts : Fin (k+1) → Action)
  | output
  deriving Fintype

 def readBit : Symbol PUnit → Option Bool
  | some (.inl b) => some b
  | _ => none

 @[simp] theorem readBit_bit (b : Bool) : readBit (bitSymbol b)=some b := rfl
 @[simp] theorem readBit_none : readBit none=none := rfl
 @[simp] theorem readBit_bind (b : Option Bool) : readBit (b.bind bitSymbol)=b := by
  cases b <;> rfl

 def marker : Symbol PUnit := some (.inr PUnit.unit)

 def instruction (q : Control Q k) (io : Symbol PUnit × Motion)
    (work : Fin (k+1) → Symbol PUnit × Motion) :
    Option (Option (Control Q k) × (Fin (k+2) → Symbol PUnit × Motion)) :=
  some (some q, Fin.cases io work)

 def Machine.program (M : Machine Q k) : Program (Control Q k) PUnit (k+1) where
  transition q cells :=
    match q with
    | none =>
      match readBit (cells 0) with
      | none => instruction (.execute M.start) (none,.stay)
          (fun j => (cells j.succ,.stay))
      | some b => instruction (.put b) (marker,.right)
          (fun j => (cells j.succ,if j=0 then .left else .stay))
    | some .read =>
      match readBit (cells 0) with
      | none => instruction .back (none,.left) (fun j => (cells j.succ,.stay))
      | some b => instruction (.put b) (none,.right)
          (fun j => (cells j.succ,if j=0 then .left else .stay))
    | some (.put b) => instruction .read (cells 0,.stay)
        (fun j => (if j=0 then bitSymbol b else cells j.succ,.stay))
    | some .back =>
      match cells 0 with
      | some (.inr _) => instruction (.execute M.start) (none,.stay)
          (fun j => (cells j.succ,.stay))
      | _ => instruction .back (cells 0,.left) (fun j => (cells j.succ,.stay))
    | some (.execute q) =>
      match M.transition q (fun j => readBit (cells j.succ)) with
      | none => instruction .output (cells 0,.stay) (fun j => (cells j.succ,.stay))
      | some (q',acts) => instruction (.pending q' acts) (cells 0,.stay)
          (fun j => ((acts j).firstWrite (readBit (cells j.succ)),
            (acts j).firstMove (readBit (cells j.succ))))
    | some (.pending q acts) => instruction (.execute q) (cells 0,.stay)
        (fun j => ((acts j).secondWrite (cells j.succ),.stay))
    | some .output =>
      match readBit (cells M.output.succ) with
      | none => none
      | some b => instruction .output (bitSymbol b,.right)
          (fun j => (if j=M.output then none else cells j.succ,
            if j=M.output then .right else .stay))

 def Machine.execState (_M : Machine Q k) (s : State Q k) :
    Computation.State (Control Q k) PUnit (k+1) where
  control := some (.execute s.control)
  heads := Fin.cases 0 (fun j => stackHead (s.tapes j))
  cells := Fin.cases (fun _ => none) (fun j => stackCells (s.tapes j))

 def intermediate (s : Computation.State Q Γ k) (q : Option Q)
    (data : Fin (k+1) → Symbol Γ × Motion) : Computation.State Q Γ k where
  control := q
  heads := fun j => s.heads j + (data j).2.displacement
  cells := fun j i => if i=s.heads j then (data j).1 else s.cells j i

end Stack
end VariableWL.Computation

namespace VariableWL.Computation

variable {Q Γ : Type} {k : ℕ}

namespace Stack

 def tapeState (q : Option Q) (h : ℤ) (c : ℤ → Symbol Γ) (ws : Fin (k+1) → Word) :
    Computation.State Q Γ (k+1) where
  control := q
  heads := Fin.cases h (fun j => stackHead (ws j))
  cells := Fin.cases c (fun j => stackCells (ws j))

 def firstData (ws : Fin (k+1) → Word) (io : Symbol Γ × Motion)
    (acts : Fin (k+1) → Action) : Fin (k+2) → Symbol Γ × Motion :=
  Fin.cases io (fun j => ((acts j).firstWrite (ws j).head?,(acts j).firstMove (ws j).head?))

 def secondData (s : Computation.State Q Γ (k+1)) (acts : Fin (k+1) → Action) :
    Fin (k+2) → Symbol Γ × Motion :=
  Fin.cases (s.cells 0 (s.heads 0),.stay)
    (fun j => ((acts j).secondWrite (s.cells j.succ (s.heads j.succ)),.stay))

 def inputTapes (w : Word) : Fin (k+1) → Word := fun j => if j=0 then w.reverse else []
 def pushInput (b : Bool) : Fin (k+1) → Action := fun j => if j=0 then .push b else .keep

 def inputCells (p w : Word) (i : ℤ) : Symbol PUnit :=
  if i=0 then marker else typedWordCells w (i-p.length)

 def Machine.loading (_M : Machine Q k) (p w : Word) :
    Computation.State (Control Q k) PUnit (k+1) :=
  tapeState (some .read) p.length (inputCells p w) (inputTapes p)

end Stack
end VariableWL.Computation

namespace VariableWL.Computation.Stack

variable {Q : Type} {k : ℕ}

 def Machine.backState (_M : Machine Q k) (n : ℕ) (ws : Fin (k+1) → Word) :
    Computation.State (Control Q k) PUnit (k+1) :=
  tapeState (some .back) n (fun i => if i=0 then marker else none) ws

end VariableWL.Computation.Stack

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_OneHead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10

namespace VariableWL.Computation

variable {Q Γ : Type} {k : ℕ}

namespace Stack

 def Machine.outputState (M : Machine Q k) (p remaining : Word) (ws : Fin (k+1) → Word) :
    Computation.State (Control Q k) PUnit (k+1) :=
  tapeState (some .output) p.length (typedWordCells p) (Function.update ws M.output remaining)

noncomputable def Machine.compile [Fintype Q] (M : Machine Q k) : VariableWL.Machine :=
  M.program.compile

end Stack
end VariableWL.Computation

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

namespace VariableWL.BoundedSimulation

inductive Steps {S : Type uVariable9} (f : S → Option S) : ℕ → S → S → Prop where
  | zero (a) : Steps f 0 a a
  | succ {n a b c} : f a=some b → Steps f n b c → Steps f (n+1) a c

noncomputable def evolve {S : Type uVariable11} (f : S → Option S) (a : S) : ℕ → S
  | 0 => a
  | t+1 => (f (evolve f a t)).getD (evolve f a t)

def Within {S : Type uVariable14} (f : S → Option S) (a b : S) (N : ℕ) : Prop :=
  ∃ n ≤ N, Steps f n a b

end VariableWL.BoundedSimulation

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

namespace VariableWL.RealizationSize
open VariableWL.Affine Blocks Subdivision
attribute [local instance] Classical.propDecidable
variable {r n : ℕ} {P : Type uVariable1} {E : Type uVariable2} [Fintype P] [Fintype E]
variable (J : ProductImages.Instance r P E)

omit [Fintype P] [Fintype E] in
theorem dimension_le_two (t : Subdivision.Vertex P E n) : Blocks.dimension J t ≤ 2 := by
  cases t with
  | inl p => rcases J.dimension_one_or_two p with h|h <;> simp [Blocks.dimension,h]
  | inr q => simp [Blocks.dimension]

omit [Fintype P] [Fintype E] in
theorem coordinate_card (b : RawBlock r n P E) : Fintype.card (BlockCoordinates.Coordinate J b) ≤ 6 := by
  cases b with
  | inl h =>
    have hd : Blocks.dimension J h.type ≤ 6 := (dimension_le_two J h.type).trans (by omega)
    simpa [BlockCoordinates.Coordinate] using hd
  | inr s =>
    have hl := dimension_le_two J (left J.source s.link)
    have hr := dimension_le_two J (right J.target s.link)
    simpa only [BlockCoordinates.Coordinate,Fintype.card_sum,Fintype.card_fin,Fintype.card_bool] using
      (show Blocks.dimension J (left J.source s.link)+Blocks.dimension J (right J.target s.link)+2 ≤ 6 by omega)

end VariableWL.RealizationSize

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Encoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.Computation.Stack
open VariableWL.BoundedSimulation
abbrev Stores (k : ℕ) := Fin (k+1) → Word
abbrev Heads (k : ℕ) := Fin (k+1) → Option Bool
abbrev Actions (k : ℕ) := Fin (k+1) → Action

def heads {k : ℕ} (s : Stores k) : Heads k := fun j => (s j).head?
def execute {k : ℕ} (a : Actions k) (s : Stores k) : Stores k := fun j => (a j).apply (s j)
def nop {k : ℕ} : Actions k := fun _ => .keep
@[simp] theorem execute_nop {k : ℕ} (s : Stores k) : execute nop s=s := rfl

inductive Code (k : ℕ) where
  | skip
  | action (a : Heads k → Actions k)
  | seq (a b : Code k)
  | branch (p : Heads k → Bool) (a b : Code k)
  | loop (p : Heads k → Bool) (body : Code k)

namespace Code
variable {k : ℕ}
def Control : Code k → Type
  | .skip => Unit
  | .action _ => Bool
  | .seq a b => a.Control ⊕ b.Control
  | .branch _ a b => Unit ⊕ (a.Control ⊕ b.Control)
  | .loop _ a => Unit ⊕ a.Control

noncomputable instance controlFintype (C : Code k) : Fintype C.Control := by
  induction C with
  | skip => exact inferInstanceAs (Fintype Unit)
  | action => exact inferInstanceAs (Fintype Bool)
  | seq a b ha hb => exact inferInstanceAs (Fintype (a.Control ⊕ b.Control))
  | branch p a b ha hb => exact inferInstanceAs (Fintype (Unit ⊕ (a.Control ⊕ b.Control)))
  | loop p a ha => exact inferInstanceAs (Fintype (Unit ⊕ a.Control))

def start : (C : Code k) → C.Control
  | .skip => ()
  | .action _ => false
  | .seq a _ => .inl a.start
  | .branch _ _ _ => .inl ()
  | .loop _ _ => .inl ()

def transition : (C : Code k) → C.Control → Heads k → Option (C.Control × Actions k)
  | .skip,_,_ => none
  | .action a,false,h => some (true,a h)
  | .action _,true,_ => none
  | .seq a b,.inl q,h =>
      match a.transition q h with
      | some (q',u) => some (.inl q',u)
      | none => some (.inr b.start,nop)
  | .seq _ b,.inr q,h => (b.transition q h).map (fun (q',u) => (.inr q',u))
  | .branch p a b,.inl _,h => some (if p h then .inr (.inl a.start) else .inr (.inr b.start),nop)
  | .branch _ a _,.inr (.inl q),h => (a.transition q h).map (fun (q',u) => (.inr (.inl q'),u))
  | .branch _ _ b,.inr (.inr q),h => (b.transition q h).map (fun (q',u) => (.inr (.inr q'),u))
  | .loop p a,.inl _,h => if p h then some (.inr a.start,nop) else none
  | .loop _ a,.inr q,h =>
      match a.transition q h with
      | some (q',u) => some (.inr q',u)
      | none => some (.inl (),nop)

def machine (C : Code k) (output : Fin (k+1)) : Machine C.Control k where
  start := C.start
  output := output
  transition := C.transition

def step (C : Code k) (s : State C.Control k) : Option (State C.Control k) :=
  (C.transition s.control (heads s.tapes)).map fun (q,a) => ⟨q,execute a s.tapes⟩

def liftState {Q R : Type} (f : Q → R) (s : State Q k) : State R k := ⟨f s.control,s.tapes⟩

inductive Eval : Code k → Stores k → ℕ → Stores k → Prop where
  | skip (s) : Eval .skip s 0 s
  | action (a) (s) : Eval (.action a) s 1 (execute (a (heads s)) s)
  | seq {a b s t u n m} : Eval a s n t → Eval b t m u → Eval (.seq a b) s (n+1+m) u
  | branch_true {p a b s t n} : p (heads s)=true → Eval a s n t → Eval (.branch p a b) s (n+1) t
  | branch_false {p a b s t n} : p (heads s)=false → Eval b s n t → Eval (.branch p a b) s (n+1) t
  | loop_false {p a s} : p (heads s)=false → Eval (.loop p a) s 0 s
  | loop_true {p a s t u n m} : p (heads s)=true → Eval a s n t →
      Eval (.loop p a) t m u → Eval (.loop p a) s (n+2+m) u

end Code
end VariableWL.Computation.Stack

namespace VariableWL.Encoding
attribute [local instance] Classical.propDecidable

noncomputable def matrix (G : Graph) : Word := by
  classical
  exact List.ofFn fun p : Fin (G.order*G.order) => decide (G.graph.Adj p.divNat p.modNat)

@[simp] theorem matrix_length (G : Graph) : (matrix G).length=G.order*G.order := List.length_ofFn

end VariableWL.Encoding

namespace VariableWL.Computation.Stack
namespace Code
variable {k : ℕ}

def one (j : Fin (k+1)) (a : Action) : Actions k := fun i => if i=j then a else .keep

theorem execute_one (j : Fin (k+1)) (a : Action) (s : Stores k) :
    execute (one j a) s=Function.update s j (a.apply (s j)) := by
  funext i
  by_cases hi : i=j
  · subst i; simp [execute,one]
  · simp [execute,one,hi,Action.apply]

def push (j : Fin (k+1)) (b : Bool) : Code k := .action (fun _ => one j (.push b))
def pop (j : Fin (k+1)) : Code k := .action (fun _ => one j .pop)
def clear (j : Fin (k+1)) : Code k := .loop (fun h => (h j).isSome) (pop j)

theorem eval_push (j : Fin (k+1)) (b : Bool) (s : Stores k) :
    Eval (push j b) s 1 (Function.update s j (b::s j)) := by
  simpa only [push,execute_one,Action.apply] using Eval.action (fun _ => one j (.push b)) s

theorem eval_pop (j : Fin (k+1)) (s : Stores k) :
    Eval (pop j) s 1 (Function.update s j (s j).tail) := by
  simpa only [pop,execute_one,Action.apply] using Eval.action (fun _ => one j .pop) s

 theorem eval_clear_update (j : Fin (k+1)) (s : Stores k) (w : Word) :
    Eval (clear j) (Function.update s j w) (3*w.length) (Function.update s j []) := by
  induction w with
  | nil => exact Eval.loop_false (by simp [heads])
  | cons b w ih =>
    have hb := eval_pop j (Function.update s j (b::w))
    simp only [Function.update_self,List.tail_cons,Function.update_idem] at hb
    have he := Eval.loop_true (p := fun h => (h j).isSome) (by simp [heads]) hb ih
    convert he using 1 <;> simp [clear,List.length_cons]; omega

 theorem eval_clear (j : Fin (k+1)) (s : Stores k) :
    Eval (clear j) s (3*(s j).length) (Function.update s j []) := by
  simpa only [Function.update_eq_self] using eval_clear_update j s (s j)

def transfer (j t : Fin (k+1)) (f : Bool → Bool) : Code k :=
  .loop (fun h => (h j).isSome) (.action fun h i =>
    if i=j then .pop else if i=t then .push (f ((h j).getD false)) else .keep)

def pairStore (s : Stores k) (j t : Fin (k+1)) (w u : Word) : Stores k :=
  Function.update (Function.update s j w) t u

 theorem transfer_action (j t : Fin (k+1)) (hjt : j≠t) (f : Bool → Bool)
    (s : Stores k) (b : Bool) (w u : Word) :
    execute (fun i => if i=j then .pop else if i=t then
      .push (f (((heads (pairStore s j t (b::w) u)) j).getD false)) else .keep)
      (pairStore s j t (b::w) u) = pairStore s j t w (f b::u) := by
  funext i
  by_cases hi : i=j
  · subst i
    simp [execute,pairStore,hjt,Action.apply]
  · by_cases ht : i=t
    · subst i
      simp [execute,pairStore,heads,hjt,Ne.symm hjt,Action.apply]
    · simp [execute,pairStore,hi,ht,Action.apply]

 theorem eval_transfer_pair (j t : Fin (k+1)) (hjt : j≠t) (f : Bool → Bool)
    (s : Stores k) (w u : Word) :
    Eval (transfer j t f) (pairStore s j t w u) (3*w.length)
      (pairStore s j t [] (w.reverse.map f++u)) := by
  induction w generalizing u with
  | nil => exact Eval.loop_false (by simp [heads,pairStore,hjt])
  | cons b w ih =>
    have ha := Eval.action (fun h i => if i=j then .pop else if i=t then
      .push (f ((h j).getD false)) else .keep) (pairStore s j t (b::w) u)
    rw [transfer_action j t hjt f] at ha
    have he := Eval.loop_true (p := fun h => (h j).isSome) (by simp [heads,pairStore,hjt]) ha (ih (f b::u))
    convert he using 1 <;> simp only [transfer,List.length_cons,List.reverse_cons,List.map_append,List.map_cons,List.map_nil,
      List.append_assoc,List.singleton_append]; omega

 theorem eval_transfer (j t : Fin (k+1)) (hjt : j≠t) (f : Bool → Bool) (s : Stores k) :
    Eval (transfer j t f) s (3*(s j).length)
      (pairStore s j t [] ((s j).reverse.map f++s t)) := by
  have he := eval_transfer_pair j t hjt f s (s j) (s t)
  simpa only [pairStore,Function.update_eq_self] using he

end Code
end VariableWL.Computation.Stack

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

def entry (n : ℕ) (v : Word) (i j : Fin n) : Bool := v.getD (i.val*n+j.val) false

def MatrixValid (n : ℕ) (v : Word) : Prop :=
  v.length=n*n ∧ (∀ i j : Fin n, entry n v i j=entry n v j i) ∧
    (∀ i : Fin n, entry n v i i=false)

end VariableWL.Encoding

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_UnaryPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.Computation.Stack.Code
variable {k : ℕ}

def tripleStore (s : Stores k) (j t u : Fin (k+1)) (w a b : Word) : Stores k :=
  Function.update (pairStore s j t w a) u b

def distribute (j t u : Fin (k+1)) (f : Bool → Bool) : Code k :=
  .loop (fun h => (h j).isSome) (.action fun h i =>
    if i=j then .pop else if i=t then .push ((h j).getD false)
    else if i=u then .push (f ((h j).getD false)) else .keep)

 theorem distribute_action (j t u : Fin (k+1)) (hjt : j≠t) (hju : j≠u) (htu : t≠u)
    (f : Bool → Bool) (s : Stores k) (b : Bool) (w a v : Word) :
    execute (fun i => if i=j then .pop else if i=t then .push ((heads (tripleStore s j t u (b::w) a v) j).getD false)
      else if i=u then .push (f ((heads (tripleStore s j t u (b::w) a v) j).getD false)) else .keep)
      (tripleStore s j t u (b::w) a v)=tripleStore s j t u w (b::a) (f b::v) := by
  funext i
  by_cases hi : i=j
  · subst i; simp [execute,tripleStore,pairStore,hju,hjt,Action.apply]
  · by_cases hit : i=t
    · subst i; simp [execute,tripleStore,pairStore,htu,hjt,Ne.symm hjt,hju,heads,Action.apply]
    · by_cases hiu : i=u
      · subst i; simp [execute,tripleStore,pairStore,Ne.symm hju,Ne.symm htu,hju,hjt,heads,Action.apply]
      · simp [execute,tripleStore,pairStore,hi,hit,hiu,Action.apply]

 theorem eval_distribute (j t u : Fin (k+1)) (hjt : j≠t) (hju : j≠u) (htu : t≠u)
    (f : Bool → Bool) (s : Stores k) (w a b : Word) :
    Eval (distribute j t u f) (tripleStore s j t u w a b) (3*w.length)
      (tripleStore s j t u [] (w.reverse++a) (w.reverse.map f++b)) := by
  induction w generalizing a b with
  | nil => exact Eval.loop_false (by simp [heads,tripleStore,pairStore,hju,hjt])
  | cons c w ih =>
    have he := Eval.action (fun h i => if i=j then .pop else if i=t then .push ((h j).getD false)
      else if i=u then .push (f ((h j).getD false)) else .keep) (tripleStore s j t u (c::w) a b)
    rw [distribute_action j t u hjt hju htu f] at he
    have hh := Eval.loop_true (p := fun h => (h j).isSome)
      (by simp [heads,tripleStore,pairStore,hjt,hju]) he (ih (c::a) (f c::b))
    convert hh using 1 <;> simp only [distribute,List.length_cons,List.reverse_cons,
      List.map_append,List.map_cons,List.map_nil,List.append_assoc,List.singleton_append]; omega

def duplicate (j t u : Fin (k+1)) (f : Bool → Bool) : Code k :=
  .seq (distribute j t u f) (transfer t j id)

 theorem eval_duplicate (j t u : Fin (k+1)) (hjt : j≠t) (hju : j≠u) (htu : t≠u)
    (f : Bool → Bool) (s : Stores k) (ht : s t=[]) :
    Eval (duplicate j t u f) s (6*(s j).length+1)
      (Function.update s u ((s j).reverse.map f++s u)) := by
  have he := eval_distribute j t u hjt hju htu f s (s j) [] (s u)
  have hin : tripleStore s j t u (s j) [] (s u)=s := by
    simp only [tripleStore,pairStore,← ht,Function.update_eq_self]
  rw [hin] at he
  let s' := tripleStore s j t u [] ((s j).reverse++[]) ((s j).reverse.map f++s u)
  have htrans := eval_transfer t j (Ne.symm hjt) id s'
  have hs' : s' t=(s j).reverse := by simp [s',tripleStore,pairStore,htu]
  have hj' : s' j=[] := by simp [s',tripleStore,pairStore,hjt,hju]
  rw [hs',hj'] at htrans
  simp only [List.reverse_reverse,List.map_id_fun,id_eq,List.append_nil,List.length_reverse] at htrans
  have hout : pairStore s' t j [] (s j)=Function.update s u ((s j).reverse.map f++s u) := by
    funext i
    by_cases hi : i=j
    · subst i; simp [pairStore,hju]
    · by_cases hit : i=t
      · subst i; simp [pairStore,Ne.symm hjt,htu,ht]
      · by_cases hiu : i=u
        · subst i; simp [pairStore,s',tripleStore,Ne.symm hju,Ne.symm htu]
        · simp [pairStore,s',tripleStore,hi,hit,hiu]
  rw [hout] at htrans
  have hh := Eval.seq he htrans
  unfold duplicate
  have hn : 6*(s j).length+1=3*(s j).length+1+3*(s j).length := by omega
  rw [hn]
  exact hh

 theorem eval_length_add (j t u : Fin (k+1)) (hjt : j≠t) (hju : j≠u) (htu : t≠u)
    (s : Stores k) (ht : s t=[]) (m : ℕ) (hu : s u=List.replicate m true) :
    Eval (duplicate j t u (fun _ => true)) s (6*(s j).length+1)
      (Function.update s u (List.replicate ((s j).length+m) true)) := by
  have h := eval_duplicate j t u hjt hju htu (fun _ => true) s ht
  simpa only [List.map_const',List.length_reverse,hu,← List.replicate_add] using h

end VariableWL.Computation.Stack.Code

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_BinaryMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.Computation.Stack.BinaryMachine
open Code

def value : Word → ℕ → ℕ
  | [],q => q
  | b::w,q => value w (2*q+b.toNat)

end VariableWL.Computation.Stack.BinaryMachine

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_BoundedLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.Computation.Stack.Code
variable {k l : ℕ}

noncomputable def put (e : Fin (k+1) ↪ Fin (l+1)) (s : Stores k) (t : Stores l) : Stores l := by
  classical
  exact fun j => if h : ∃ i, e i=j then s h.choose else t j

 theorem put_apply (e : Fin (k+1) ↪ Fin (l+1)) (s : Stores k) (t : Stores l) (i : Fin (k+1)) :
    put e s t (e i)=s i := by
  classical
  unfold put
  rw [dite_eq_left ⟨i,rfl⟩]
  congr 1
  exact e.injective (Exists.choose_spec (show ∃ a, e a=e i from ⟨i,rfl⟩))

 theorem put_outside (e : Fin (k+1) ↪ Fin (l+1)) (s : Stores k) (t : Stores l) {j : Fin (l+1)}
    (h : ¬∃ i, e i=j) : put e s t j=t j := by
  classical
  exact dite_eq_right h

 theorem put_self (e : Fin (k+1) ↪ Fin (l+1)) (s : Stores l) : put e (s ∘ e) s=s := by
  funext j
  by_cases h : ∃ i, e i=j
  · obtain ⟨i,rfl⟩ := h
    exact put_apply e (s ∘ e) s i
  · exact put_outside e (s ∘ e) s h

 theorem put_put (e : Fin (k+1) ↪ Fin (l+1)) (s s' : Stores k) (t : Stores l) :
    put e s' (put e s t)=put e s' t := by
  funext j
  by_cases h : ∃ i, e i=j
  · obtain ⟨i,rfl⟩ := h
    rw [put_apply,put_apply]
  · rw [put_outside e s' _ h,put_outside e s _ h,put_outside e s' _ h]

noncomputable def liftAction (e : Fin (k+1) ↪ Fin (l+1)) (a : Actions k) : Actions l := by
  classical
  exact fun j => if h : ∃ i, e i=j then a h.choose else .keep

 theorem liftAction_apply (e : Fin (k+1) ↪ Fin (l+1)) (a : Actions k) (i : Fin (k+1)) :
    liftAction e a (e i)=a i := by
  classical
  unfold liftAction
  rw [dite_eq_left ⟨i,rfl⟩]
  congr 1
  exact e.injective (Exists.choose_spec (show ∃ b, e b=e i from ⟨i,rfl⟩))

 theorem liftAction_outside (e : Fin (k+1) ↪ Fin (l+1)) (a : Actions k) {j : Fin (l+1)}
    (h : ¬∃ i, e i=j) : liftAction e a j=.keep := by
  classical
  exact dite_eq_right h

 theorem execute_liftAction (e : Fin (k+1) ↪ Fin (l+1)) (a : Actions k) (s : Stores k) (t : Stores l) :
    execute (liftAction e a) (put e s t)=put e (execute a s) t := by
  funext j
  by_cases h : ∃ i, e i=j
  · obtain ⟨i,rfl⟩ := h
    simp only [execute,liftAction_apply,put_apply]
  · simp only [execute,liftAction_outside e a h,put_outside e s t h,
      put_outside e (execute a s) t h,Action.apply]

 theorem heads_put (e : Fin (k+1) ↪ Fin (l+1)) (s : Stores k) (t : Stores l) :
    heads (put e s t) ∘ e=heads s := by
  funext i
  simp only [Function.comp_apply,heads,put_apply]

noncomputable def rename (e : Fin (k+1) ↪ Fin (l+1)) : Code k → Code l
  | .skip => .skip
  | .action a => .action fun h => liftAction e (a (h ∘ e))
  | .seq a b => .seq (rename e a) (rename e b)
  | .branch p a b => .branch (fun h => p (h ∘ e)) (rename e a) (rename e b)
  | .loop p a => .loop (fun h => p (h ∘ e)) (rename e a)

 theorem eval_rename (e : Fin (k+1) ↪ Fin (l+1)) {C : Code k} {s s' : Stores k} {n : ℕ}
    (h : Eval C s n s') (t : Stores l) : Eval (rename e C) (put e s t) n (put e s' t) := by
  induction h with
  | skip s => exact Eval.skip _
  | action a s =>
    have hh := Eval.action (fun h : Heads l => liftAction e (a (h ∘ e))) (put e s t)
    rw [heads_put,execute_liftAction] at hh
    exact hh
  | seq _ _ ia ib => exact Eval.seq ia ib
  | @branch_true p a b s u n hp ha ih =>
    exact Eval.branch_true (by simpa only [heads_put] using hp) ih
  | @branch_false p a b s u n hp ha ih =>
    exact Eval.branch_false (by simpa only [heads_put] using hp) ih
  | loop_false hp => exact Eval.loop_false (by simpa only [heads_put] using hp)
  | @loop_true p a s u v n m hp ha hb ia ib =>
    exact Eval.loop_true (by simpa only [heads_put] using hp) ia ib

 theorem eval_rename_from (e : Fin (k+1) ↪ Fin (l+1)) {C : Code k} {s' : Stores k} {n : ℕ}
    (t : Stores l) (h : Eval C (t ∘ e) n s') : Eval (rename e C) t n (put e s' t) := by
  simpa only [put_self] using eval_rename e h t

end VariableWL.Computation.Stack.Code

namespace VariableWL.Computation.Stack.BoundedLoop
open Code
variable (k : ℕ)

def embed : Fin (k+1) ↪ Fin (k+3) := Fin.castAddEmb 2
def counter : Fin (k+3) := ⟨k+1,by omega⟩
def scratch : Fin (k+3) := ⟨k+2,by omega⟩

 theorem counter_ne (i : Fin (k+1)) : embed k i≠counter k := by
  intro h
  have := congrArg Fin.val h
  change i.val=k+1 at this
  omega

 theorem scratch_ne (i : Fin (k+1)) : embed k i≠scratch k := by
  intro h
  have := congrArg Fin.val h
  change i.val=k+2 at this
  omega

 theorem counter_scratch : counter k≠scratch k := by
  intro h
  have := congrArg Fin.val h
  simp only [counter,scratch] at this
  omega

noncomputable def state (s : Stores k) (n : ℕ) : Stores (k+2) :=
  put (embed k) s (fun j => if j=counter k then List.replicate n true else [])

@[simp] theorem state_embed (s : Stores k) (n : ℕ) (i : Fin (k+1)) :
    state k s n (embed k i)=s i := put_apply _ _ _ _

@[simp] theorem state_counter (s : Stores k) (n : ℕ) :
    state k s n (counter k)=List.replicate n true := by
  rw [state,put_outside]
  · simp only [ite_true]
  · rintro ⟨i,hi⟩
    exact counter_ne k i hi

@[simp] theorem state_scratch (s : Stores k) (n : ℕ) :
    state k s n (scratch k)=[] := by
  rw [state,put_outside]
  · simp only [Ne.symm (counter_scratch k),ite_false]
  · rintro ⟨i,hi⟩
    exact scratch_ne k i hi

 theorem cases_index (j : Fin (k+3)) :
    (∃ i : Fin (k+1), embed k i=j) ∨ j=counter k ∨ j=scratch k := by
  by_cases h : j.val<k+1
  · left
    exact ⟨⟨j.val,h⟩,Fin.ext rfl⟩
  · right
    have : j.val=k+1 ∨ j.val=k+2 := by omega
    rcases this with h|h
    · exact .inl (Fin.ext h)
    · exact .inr (Fin.ext h)

 theorem update_counter (s : Stores k) (n m : ℕ) :
    Function.update (state k s n) (counter k) (List.replicate m true)=state k s m := by
  funext j
  rcases cases_index k j with ⟨i,rfl⟩|rfl|rfl
  · simp only [Function.update_of_ne (counter_ne k i),state_embed]
  · simp only [Function.update_self,state_counter]
  · simp only [Function.update_of_ne (Ne.symm (counter_scratch k)),state_scratch]

 theorem put_state (s t : Stores k) (n : ℕ) : put (embed k) t (state k s n)=state k t n := by
  exact put_put _ _ _ _

noncomputable def loopBody (a : Code k) : Code (k+2) := .seq (pop (counter k)) (rename (embed k) a)
noncomputable def loop (a : Code k) : Code (k+2) := .loop (fun h => (h (counter k)).isSome) (loopBody k a)
noncomputable def program (i : Fin (k+1)) (a : Code k) : Code (k+2) :=
  .seq (duplicate (embed k i) (scratch k) (counter k) (fun _ => true)) (loop k a)

 theorem eval_body {a : Code k} {s t : Stores k} {c : ℕ} (h : Eval a s c t) (n : ℕ) :
    Eval (loopBody k a) (state k s (n+1)) (c+2) (state k t n) := by
  have hp := eval_pop (counter k) (state k s (n+1))
  rw [state_counter,List.replicate_succ,List.tail_cons,update_counter] at hp
  have hb := eval_rename (embed k) h (state k s n)
  rw [put_state,put_state] at hb
  have he := Eval.seq hp hb
  have hn : c+2=1+1+c := by omega
  rw [hn]
  exact he

def total : ℕ → (ℕ → ℕ) → ℕ
  | 0,_ => 0
  | n+1,T => T 0+4+total n (fun j => T (j+1))

 theorem eval_loop (a : Code k) (n : ℕ) (S : ℕ → Stores k) (T : ℕ → ℕ)
    (h : ∀ j<n, Eval a (S j) (T j) (S (j+1))) :
    Eval (loop k a) (state k (S 0) n) (total n T) (state k (S n) 0) := by
  induction n generalizing S T with
  | zero => exact Eval.loop_false (by simp only [heads,state_counter,List.replicate_zero,List.head?_nil,Option.isSome_none])
  | succ n ih =>
    have h0 := eval_body k (h 0 (by omega)) n
    have ht := ih (fun j => S (j+1)) (fun j => T (j+1)) (by intro j hj; exact h (j+1) (by omega))
    have he := Eval.loop_true (p := fun h => (h (counter k)).isSome)
      (by simp [heads,List.replicate_succ]) h0 ht
    have hn : total (n+1) T=(T 0+2)+2+total n (fun j => T (j+1)) := by simp only [total]
    rw [hn]
    exact he

 theorem eval_program (i : Fin (k+1)) (a : Code k) (S : ℕ → Stores k) (T : ℕ → ℕ)
    (h : ∀ j<(S 0 i).length, Eval a (S j) (T j) (S (j+1))) :
    Eval (program k i a) (state k (S 0) 0)
      (6*(S 0 i).length+2+total (S 0 i).length T) (state k (S (S 0 i).length) 0) := by
  have hd := eval_length_add (embed k i) (scratch k) (counter k) (scratch_ne k i)
    (counter_ne k i) (Ne.symm (counter_scratch k)) (state k (S 0) 0)
    (state_scratch k _ _) 0 (state_counter k _ _)
  simp only [state_embed,Nat.add_zero,update_counter] at hd
  have he := Eval.seq hd (eval_loop k a _ S T h)
  have hn : 6*(S 0 i).length+2+total (S 0 i).length T=
      (6*(S 0 i).length+1)+1+total (S 0 i).length T := by omega
  rw [hn]
  exact he

 theorem total_bound (n B : ℕ) (T : ℕ → ℕ) (h : ∀ j<n, T j≤B) : total n T≤(B+4)*n := by
  induction n generalizing T with
  | zero => simp [total]
  | succ n ih =>
    have hi := ih (fun j => T (j+1)) (by intro j hj; exact h (j+1) (by omega))
    have h0 := h 0 (by omega)
    simp only [total]
    nlinarith

 theorem program_bound (n B : ℕ) (T : ℕ → ℕ) (h : ∀ j<n, T j≤B) :
    6*n+2+total n T≤(B+10)*n+2 := by
  have := total_bound n B T h
  nlinarith

end VariableWL.Computation.Stack.BoundedLoop

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Procedure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.Computation.Stack.Procedure
open Code
variable {k : ℕ}

def extend (e : ℕ) (s : Stores k) : Stores (k+e) :=
  fun j => if h : j.val<k+1 then s ⟨j.val,h⟩ else []

@[simp] theorem extend_front (e : ℕ) (s : Stores k) (i : Fin (k+1)) :
    extend e s (⟨i.val,by omega⟩ : Fin (k+e+1))=s i := by
  simp only [extend, i.isLt, dite_true]

 theorem extend_back (e : ℕ) (s : Stores k) (j : Fin (k+e+1)) (h : k+1≤j.val) :
    extend e s j=[] := by simp only [extend,show ¬j.val<k+1 by omega,dite_false]

 theorem extend_zero (s : Stores k) : extend 0 s=s := by
  funext i
  exact extend_front 0 s i

def widen (k e f : ℕ) (h : e≤f) : Fin (k+e+1) ↪ Fin (k+f+1) :=
  Fin.castLEEmb (by omega)

 theorem extend_project (e f : ℕ) (h : e≤f) (s : Stores k) :
    extend f s ∘ widen k e f h=extend e s := by
  funext i
  simp only [extend,Function.comp_apply,widen,Fin.coe_castLEEmb,Fin.val_castLE]

 theorem extend_put (e f : ℕ) (h : e≤f) (s t : Stores k) :
    put (widen k e f h) (extend e t) (extend f s)=extend f t := by
  classical
  funext j
  by_cases hj : j.val<k+e+1
  · let i : Fin (k+e+1) := ⟨j.val,hj⟩
    have he : widen k e f h i=j := Fin.ext rfl
    rw [←he,put_apply]
    have hp := congrFun (extend_project e f h t) i
    exact hp.symm
  · have hout : ¬∃i, widen k e f h i=j := by
      rintro ⟨i,hi⟩
      have hv := congrArg Fin.val hi
      change i.val=j.val at hv
      omega
    rw [put_outside _ _ _ hout]
    rw [extend_back _ _ _ (by omega),extend_back _ _ _ (by omega)]

 theorem eval_widen {e f : ℕ} (h : e≤f) {C : Code (k+e)} {s t : Stores k} {n : ℕ}
    (hc : Eval C (extend e s) n (extend e t)) :
    Eval (rename (widen k e f h) C) (extend f s) n (extend f t) := by
  have he := eval_rename_from (widen k e f h) (t := extend f s)
    (by simpa only [extend_project] using hc)
  rw [extend_put] at he
  exact he

def Realizes (f : Stores k → Stores k) (T : Stores k → ℕ) : Prop :=
  ∃ e : ℕ, ∃ C : Code (k+e), ∀ s, ∃ n≤T s, Eval C (extend e s) n (extend e (f s))

 theorem monotone {f : Stores k → Stores k} {T U : Stores k → ℕ}
    (h : Realizes f T) (hTU : ∀ s, T s≤U s) : Realizes f U := by
  obtain ⟨e,C,hC⟩ := h
  refine ⟨e,C,fun s => ?_⟩
  obtain ⟨n,hn,he⟩ := hC s
  exact ⟨n,hn.trans (hTU s),he⟩

 theorem direct (C : Code k) (f : Stores k → Stores k) (T : Stores k → ℕ)
    (h : ∀s,∃n≤T s,Eval C s n (f s)) : Realizes f T := by
  refine ⟨0,C,fun s => ?_⟩
  simpa only [extend_zero] using h s

 theorem seq {f g : Stores k → Stores k} {T U : Stores k → ℕ}
    (hf : Realizes f T) (hg : Realizes g U) :
    Realizes (g ∘ f) (fun s => T s+1+U (f s)) := by
  obtain ⟨e,A,hA⟩ := hf
  obtain ⟨f',B,hB⟩ := hg
  let a := widen k e (max e f') (Nat.le_max_left _ _)
  let b := widen k f' (max e f') (Nat.le_max_right _ _)
  refine ⟨max e f',.seq (rename a A) (rename b B),fun s => ?_⟩
  obtain ⟨n,hn,heA⟩ := hA s
  obtain ⟨m,hm,heB⟩ := hB (f s)
  exact ⟨n+1+m,by dsimp only; omega, Eval.seq (eval_widen _ heA) (eval_widen _ heB)⟩

 theorem clear (i : Fin (k+1)) :
    Realizes (fun s : Stores k => Function.update s i []) (fun s => 3*(s i).length) :=
  direct (Code.clear i) _ _ (fun s => ⟨_,le_rfl,eval_clear i s⟩)

 theorem push (i : Fin (k+1)) (b : Bool) :
    Realizes (fun s : Stores k => Function.update s i (b::s i)) (fun _ => 1) :=
  direct (Code.push i b) _ _ (fun s => ⟨_,le_rfl,eval_push i b s⟩)

 theorem pop (i : Fin (k+1)) :
    Realizes (fun s : Stores k => Function.update s i (s i).tail) (fun _ => 1) :=
  direct (Code.pop i) _ _ (fun s => ⟨_,le_rfl,eval_pop i s⟩)

 theorem action (a : Heads k → Actions k) :
    Realizes (fun s => execute (a (heads s)) s) (fun _ => 1) :=
  direct (.action a) _ _ (fun s => ⟨_,le_rfl,Eval.action a s⟩)

end VariableWL.Computation.Stack.Procedure

namespace VariableWL.Computation.Stack.Procedure
open Code
variable {k : ℕ}

def front (k e : ℕ) : Fin (k+1) ↪ Fin (k+e+1) := Fin.castLEEmb (by omega)

 theorem heads_extend (e : ℕ) (s : Stores k) : heads (extend e s) ∘ front k e=heads s := by
  funext i
  change (extend e s (⟨i.val,_⟩ : Fin (k+e+1))).head?=(s i).head?
  rw [extend_front]

 theorem branch (p : Heads k → Bool) {f g : Stores k → Stores k} {T U : Stores k → ℕ}
    (hf : Realizes f T) (hg : Realizes g U) :
    Realizes (fun s => if p (heads s) then f s else g s)
      (fun s => (if p (heads s) then T s else U s)+1) := by
  obtain ⟨e,A,hA⟩ := hf
  obtain ⟨f',B,hB⟩ := hg
  let a := widen k e (max e f') (Nat.le_max_left _ _)
  let b := widen k f' (max e f') (Nat.le_max_right _ _)
  let p' : Heads (k+max e f') → Bool := fun h => p (h ∘ front k (max e f'))
  refine ⟨max e f',.branch p' (rename a A) (rename b B),fun s => ?_⟩
  have hps : p' (heads (extend (max e f') s))=p (heads s) := by change p (heads (extend (max e f') s) ∘ front k (max e f'))=p (heads s); rw [heads_extend]
  cases hp : p (heads s) with
  | false =>
    obtain ⟨n,hn,he⟩ := hB s
    simp only [hp,Bool.false_eq_true,ite_false]
    exact ⟨n+1,by omega,Eval.branch_false (hps.trans hp) (eval_widen _ he)⟩
  | true =>
    obtain ⟨n,hn,he⟩ := hA s
    simp only [hp,ite_true]
    exact ⟨n+1,by omega,Eval.branch_true (hps.trans hp) (eval_widen _ he)⟩

 theorem state_extend (e : ℕ) (s : Stores k) :
    BoundedLoop.state (k+e) (extend e s) 0=extend (e+2) s := by
  funext j
  rcases BoundedLoop.cases_index (k+e) j with ⟨i,rfl⟩|rfl|rfl
  · rw [BoundedLoop.state_embed]
    rfl
  · rw [BoundedLoop.state_counter, List.replicate_zero]
    exact (extend_back _ _ _ (by change k+1≤k+e+1; omega)).symm
  · rw [BoundedLoop.state_scratch]
    exact (extend_back _ _ _ (by change k+1≤k+e+2; omega)).symm

 theorem total_mono (n : ℕ) (A B : ℕ → ℕ) (h : ∀j<n,A j≤B j) :
    BoundedLoop.total n A≤BoundedLoop.total n B := by
  induction n generalizing A B with
  | zero => rfl
  | succ n ih =>
    have hi := ih (fun j=>A (j+1)) (fun j=>B (j+1)) (by intro j hj; exact h (j+1) (by omega))
    have h0 := h 0 (by omega)
    simp only [BoundedLoop.total]
    omega

 theorem countedLoop (i : Fin (k+1)) {f : Stores k → Stores k} {T : Stores k → ℕ}
    (hf : Realizes f T) :
    Realizes (fun s => (f^[(s i).length]) s)
      (fun s => 6*(s i).length+2+BoundedLoop.total (s i).length (fun j => T ((f^[j]) s))) := by
  classical
  obtain ⟨e,A,hA⟩ := hf
  let i' : Fin (k+e+1) := ⟨i.val,by omega⟩
  refine ⟨e+2,BoundedLoop.program (k+e) i' A,fun s => ?_⟩
  let S (j : ℕ) := extend e ((f^[j]) s)
  let τ (j : ℕ) := (hA ((f^[j]) s)).choose
  have ht (j : ℕ) : τ j≤T ((f^[j]) s) := (hA ((f^[j]) s)).choose_spec.1
  have hb (j : ℕ) : Eval A (S j) (τ j) (S (j+1)) := by
    have he := (hA ((f^[j]) s)).choose_spec.2
    simpa only [S,Function.iterate_succ_apply'] using he
  have he := BoundedLoop.eval_program (k+e) i' A S τ (fun j _ => hb j)
  have hs : S 0=extend e s := rfl
  have hl : (S 0 i').length=(s i).length := by rw [hs,extend_front]
  rw [hl,hs,state_extend,state_extend] at he
  have hn := total_mono (s i).length τ (fun j => T ((f^[j]) s)) (fun j _ => ht j)
  exact ⟨_,by dsimp only; omega,he⟩

 theorem countedLoop_bound (i : Fin (k+1)) {f : Stores k → Stores k} {T B : Stores k → ℕ}
    (hf : Realizes f T) (hB : ∀s j,j<(s i).length → T ((f^[j]) s)≤B s) :
    Realizes (fun s => (f^[(s i).length]) s) (fun s => (B s+10)*(s i).length+2) := by
  apply monotone (countedLoop i hf)
  intro s
  exact BoundedLoop.program_bound _ _ _ (hB s)

end VariableWL.Computation.Stack.Procedure

namespace VariableWL.Computation.Stack.Procedure
open Code
variable {k : ℕ}

@[simp] theorem extend_front' (e : ℕ) (s : Stores k) (i : Fin (k+1)) :
    extend e s (front k e i)=s i := extend_front e s i

 theorem state_base (s : Stores k) : BoundedLoop.state k s 0=extend 2 s := by
  simpa only [extend_zero,Nat.add_zero] using state_extend 0 s

attribute [local simp] BoundedLoop.counter_ne BoundedLoop.scratch_ne BoundedLoop.counter_scratch

 theorem extend_update (e : ℕ) (s : Stores k) (i : Fin (k+1)) (w : Word) :
    Function.update (extend e s) (front k e i) w=extend e (Function.update s i w) := by
  funext j
  by_cases hj : j.val<k+1
  · have he : j=front k e ⟨j.val,hj⟩ := Fin.ext rfl
    rw [he]
    by_cases hi : (⟨j.val,hj⟩ : Fin (k+1))=i
    · rw [hi,Function.update_self,extend_front',Function.update_self]
    · have hne : front k e ⟨j.val,hj⟩≠front k e i := fun h => hi ((front k e).injective h)
      rw [Function.update_of_ne hne,extend_front',extend_front',Function.update_of_ne hi]
  · have hi : j≠front k e i := by
      intro he
      have hv := congrArg Fin.val he
      change j.val=i.val at hv
      omega
    rw [Function.update_of_ne hi,extend_back _ _ _ (by omega),extend_back _ _ _ (by omega)]

 theorem reverseCopy (j u : Fin (k+1)) (hju : j≠u) (f : Bool → Bool) :
    Realizes (fun s : Stores k => Function.update s u ((s j).reverse.map f++s u))
      (fun s => 6*(s j).length+1) := by
  let j' := front k 1 j
  let u' := front k 1 u
  let tmp : Fin (k+1+1) := ⟨k+1,by omega⟩
  have hjt : j'≠tmp := by
    intro h; have hv := congrArg Fin.val h; change j.val=k+1 at hv; omega
  have hut : u'≠tmp := by
    intro h; have hv := congrArg Fin.val h; change u.val=k+1 at hv; omega
  have hju' : j'≠u' := fun h => hju ((front k 1).injective h)
  refine ⟨1,duplicate j' tmp u' f,fun s => ?_⟩
  have ht : extend 1 s tmp=[] := extend_back _ _ _ (by rfl)
  have he := eval_duplicate j' tmp u' hjt hju' (Ne.symm hut) f (extend 1 s) ht
  simp only [j',u',extend_front',extend_update] at he
  exact ⟨_,le_rfl,he⟩

def pushWord (i : Fin (k+1)) : Word → Code k
  | [] => .skip
  | b::w => .seq (pushWord i w) (Code.push i b)

 theorem eval_pushWord (i : Fin (k+1)) (w : Word) (s : Stores k) :
    Eval (pushWord i w) s (2*w.length) (Function.update s i (w++s i)) := by
  induction w with
  | nil => simpa only [pushWord,List.length_nil,List.nil_append,Function.update_eq_self,Nat.mul_zero] using Eval.skip s
  | cons b w ih =>
    have he := Eval.seq ih (eval_push i b (Function.update s i (w++s i)))
    simpa only [pushWord,List.length_cons,Function.update_self,Function.update_idem,
      List.cons_append,show 2*(w.length+1)=2*w.length+1+1 by omega] using he

 theorem prepend (i : Fin (k+1)) (w : Word) :
    Realizes (fun s : Stores k => Function.update s i (w++s i)) (fun _ => 2*w.length) :=
  direct (pushWord i w) _ _ (fun s => ⟨_,le_rfl,eval_pushWord i w s⟩)

 theorem constant (i : Fin (k+1)) (w : Word) :
    Realizes (fun s : Stores k => Function.update s i w) (fun s => 3*(s i).length+1+2*w.length) := by
  have h := seq (clear i) (prepend i w)
  simpa only [Function.comp_def,Function.update_self,Function.update_idem,List.append_nil] using h

 theorem lengthAdd (j u : Fin (k+1)) (hju : j≠u) :
    Realizes (fun s : Stores k => Function.update s u (List.replicate (s j).length true++s u))
      (fun s => 6*(s j).length+1) := by
  simpa only [List.map_const',List.length_reverse] using reverseCopy j u hju (fun _ => true)

 theorem copy (j u : Fin (k+1)) :
    Realizes (fun s : Stores k => Function.update s u (s j))
      (fun s => 9*(s j).length+3*(s u).length+3) := by
  let j' := BoundedLoop.embed k j
  let u' := BoundedLoop.embed k u
  let tmp := BoundedLoop.counter k
  let data := BoundedLoop.scratch k
  let C := Code.seq (duplicate j' tmp data id) (.seq (Code.clear u') (Code.transfer data u' id))
  refine ⟨2,C,fun s => ?_⟩
  let s₀ := BoundedLoop.state k s 0
  let s₁ := Function.update s₀ data (s j).reverse
  let s₂ := Function.update s₁ u' []
  have hd := eval_duplicate j' tmp data (BoundedLoop.counter_ne k j)
    (BoundedLoop.scratch_ne k j) (BoundedLoop.counter_scratch k) id s₀ (by simp [s₀,tmp])
  have hds : Eval (duplicate j' tmp data id) s₀ (6*(s j).length+1) s₁ := by
    simpa only [s₀,j',data,BoundedLoop.state_embed,BoundedLoop.state_scratch,List.map_id_fun,id_eq,List.append_nil] using hd
  have h₁ : s₁ u'=s u := by
    simp [s₁,s₀,u',data]
  have hc := eval_clear u' s₁
  rw [h₁] at hc
  have h₂ : s₂ data=(s j).reverse := by
    simp [s₂,s₁,u',data,Ne.symm (BoundedLoop.scratch_ne k u)]
  have hu₂ : s₂ u'=[] := Function.update_self ..
  have ht := eval_transfer data u' (Ne.symm (BoundedLoop.scratch_ne k u)) id s₂
  rw [h₂,hu₂] at ht
  simp only [List.length_reverse,List.reverse_reverse,List.map_id_fun,id_eq,List.append_nil] at ht
  have hout : pairStore s₂ data u' [] (s j)=BoundedLoop.state k (Function.update s u (s j)) 0 := by
    funext z
    rcases BoundedLoop.cases_index k z with ⟨i,rfl⟩|rfl|rfl
    · by_cases hi : i=u
      · subst i
        simp [pairStore,u']
      · have hne : BoundedLoop.embed k i≠u' := fun h => hi ((BoundedLoop.embed k).injective h)
        simp [pairStore,s₂,s₁,s₀,u',data,hi,show BoundedLoop.embed k i≠BoundedLoop.embed k u from hne]
    · simp [pairStore,s₂,s₁,s₀,u',data,Ne.symm (BoundedLoop.counter_ne k u)]
    · simp [pairStore,u',data,Ne.symm (BoundedLoop.scratch_ne k u)]
  rw [hout] at ht
  have he := Eval.seq hds (Eval.seq hc ht)
  rw [show C=Code.seq (duplicate j' tmp data id) (.seq (Code.clear u') (Code.transfer data u' id)) from rfl]
  refine ⟨(6*(s j).length+1)+1+(3*(s u).length+1+3*(s j).length),by dsimp only; omega,?_⟩
  simpa only [s₀,state_base] using he

end VariableWL.Computation.Stack.Procedure

namespace VariableWL.Computation.Stack.Procedure
open Code
variable {k : ℕ}

def join (k e w : ℕ) : Fin (k+e+w+1) ↪ Fin (k+(e+w)+1) := Fin.castLEEmb (by omega)

 theorem extend_nested (e w : ℕ) (s : Stores k) :
    extend (e+w) s ∘ join k e w=extend w (extend e s) := by
  funext i
  change (if h:i.val<k+1 then s ⟨i.val,h⟩ else []) =
    (if h:i.val<k+e+1 then (if h':i.val<k+1 then s ⟨i.val,h'⟩ else []) else [])
  split_ifs <;> first | rfl | omega

 theorem put_nested (e w : ℕ) (s t : Stores k) :
    put (join k e w) (extend w (extend e t)) (extend (e+w) s)=extend (e+w) t := by
  funext j
  let i : Fin (k+e+w+1) := ⟨j.val,by have := j.isLt; omega⟩
  have he : join k e w i=j := Fin.ext rfl
  rw [←he,put_apply]
  exact (congrFun (extend_nested e w t) i).symm

 theorem localRegisters (e : ℕ) {f : Stores (k+e) → Stores (k+e)} {T : Stores (k+e) → ℕ}
    {g : Stores k → Stores k} {U : Stores k → ℕ}
    (hf : Realizes f T) (hfg : ∀s,f (extend e s)=extend e (g s))
    (hT : ∀s,T (extend e s)≤U s) : Realizes g U := by
  obtain ⟨w,C,hC⟩ := hf
  refine ⟨e+w,rename (join k e w) C,fun s => ?_⟩
  obtain ⟨n,hn,he⟩ := hC (extend e s)
  rw [hfg] at he
  have hr := eval_rename_from (join k e w) (extend (e+w) s)
    (by simpa only [extend_nested] using he)
  rw [put_nested] at hr
  exact ⟨n,hn.trans (hT s),hr⟩

 theorem iterate_update {f : Word → Word} (i : Fin (k+1)) (s : Stores k) (n : ℕ) :
    ((fun t : Stores k=>Function.update t i (f (t i)))^[n]) s=
      Function.update s i ((f^[n]) (s i)) := by
  induction n with
  | zero => simp only [Function.iterate_zero, id_eq,Function.update_eq_self]
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih,Function.update_self,Function.update_idem,Function.iterate_succ_apply']

 theorem iterate_tail (w : Word) (n : ℕ) : (List.tail^[n]) w=w.drop n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply',ih,List.tail_drop]

 theorem countedPop (bound target : Fin (k+1)) :
    Realizes (fun s : Stores k=>Function.update s target ((s target).drop (s bound).length))
      (fun s=>11*(s bound).length+2) := by
  have h := countedLoop_bound bound (pop target) (B := fun _=>1) (by intros; exact le_rfl)
  simpa only [iterate_update,iterate_tail] using h

end VariableWL.Computation.Stack.Procedure

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

structure Data where
  leftOrder : ℕ
  rightOrder : ℕ
  dimension : ℕ
  leftMatrix : Word
  rightMatrix : Word

attribute [local instance] Classical.propDecidable

end VariableWL.NumericRefinement

namespace VariableWL.Computation.Stack.Procedure
open Code
variable {k : ℕ}

 def aux (k : ℕ) : Fin (k+1+1) := ⟨k+1,by omega⟩

 theorem front_ne_aux (i : Fin (k+1)) : front k 1 i≠aux k := by
  intro h
  have hv := congrArg Fin.val h
  change i.val=k+1 at hv
  omega

 theorem aux_ne_front (i : Fin (k+1)) : aux k≠front k 1 i := Ne.symm (front_ne_aux i)

 @[simp] theorem extend_aux (s : Stores k) : extend 1 s (aux k)=[] := extend_back _ _ _ (by rfl)

 theorem clear_aux (s : Stores k) : Function.update (extend 1 s) (aux k) []=extend 1 s := by
  rw [←extend_aux s,Function.update_eq_self]

 theorem pushHead (a o : Fin (k+1)) :
    Realizes (fun s : Stores k=>Function.update s o ((s a).head?.getD false::s o)) (fun _=>1) := by
  have h := action (fun h : Heads k=>one o (.push ((h a).getD false)))
  simpa only [execute_one,Action.apply,heads] using h

 theorem lookup (a ix o : Fin (k+1)) :
    Realizes (fun s : Stores k=>Function.update s o [(s a).getD (s ix).length false])
      (fun s=>12*(s a).length+11*(s ix).length+3*(s o).length+12) := by
  let a' := front k 1 a
  let i' := front k 1 ix
  let o' := front k 1 o
  let q := aux k
  have hf := seq (copy a' q) (seq (countedPop i' q)
    (seq (clear o') (seq (pushHead q o') (clear q))))
  apply localRegisters 1 hf
  · intro s
    dsimp only [Function.comp_def,a',i',o',q]
    simp only [Function.update_self,Function.update_of_ne (front_ne_aux ix),
      Function.update_of_ne (aux_ne_front o),Function.update_idem,extend_front',List.head?_drop]
    rw [Function.update_comm (front_ne_aux o),Function.update_idem,clear_aux,extend_update]
    rfl
  · intro s
    dsimp only [Function.comp_def,a',i',o',q]
    simp only [Function.update_self,Function.update_of_ne (front_ne_aux ix),
      Function.update_of_ne (front_ne_aux o),Function.update_of_ne (aux_ne_front o),
      extend_front',extend_aux,List.length_nil,List.length_drop]
    omega

end VariableWL.Computation.Stack.Procedure

namespace VariableWL.Computation.Stack.Procedure
open Code
variable {k : ℕ}

 theorem iterate_lengthAdd (a o : Fin (k+1)) (h : a≠o) (n : ℕ) (s : Stores k) :
    ((fun t : Stores k=>Function.update t o (List.replicate (t a).length true++t o))^[n]) s=
      Function.update s o (List.replicate (n*(s a).length) true++s o) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih,Function.update_of_ne h,Function.update_self,
      Function.update_idem,←List.append_assoc,←List.replicate_add]
    congr 3
    ring

 theorem multiplyAdd (a b o : Fin (k+1)) (hao : a≠o) :
    Realizes (fun s : Stores k=>Function.update s o
      (List.replicate ((s b).length*(s a).length) true++s o))
      (fun s=>(6*(s a).length+11)*(s b).length+2) := by
  have h := countedLoop_bound b (lengthAdd a o hao) (B := fun s=>6*(s a).length+1)
    (by intro s j _; rw [iterate_lengthAdd a o hao,Function.update_of_ne hao])
  simpa only [iterate_lengthAdd a o hao,Nat.add_assoc] using h

 theorem multiply (a b o : Fin (k+1)) :
    Realizes (fun s : Stores k=>Function.update s o (List.replicate ((s a).length*(s b).length) true))
      (fun s=>20*((s a).length+1)*((s b).length+1)+3*(s o).length+10) := by
  let a' := front k 1 a
  let b' := front k 1 b
  let o' := front k 1 o
  let q := aux k
  have hf := seq (multiplyAdd a' b' q (front_ne_aux a)) (seq (copy q o') (clear q))
  apply localRegisters 1 hf
  · intro s
    dsimp only [Function.comp_def,a',b',o',q]
    simp only [extend_front',extend_aux,List.append_nil,Function.update_self,Nat.mul_comm]
    rw [Function.update_comm (front_ne_aux o),Function.update_idem,clear_aux,extend_update]
  · intro s
    dsimp only [Function.comp_def,a',b',o',q]
    simp only [extend_front',extend_aux,List.append_nil,Function.update_self,
      Function.update_of_ne (front_ne_aux o),Function.update_of_ne (aux_ne_front o),List.length_replicate]
    nlinarith

end VariableWL.Computation.Stack.Procedure

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Recipe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.Computation.Stack.Procedure
open Code
variable {k : ℕ}
 theorem length_fast (a o : Fin (k+1)) :
    Realizes (fun s : Stores k=>Function.update s o (List.replicate (s a).length true))
      (fun s=>20*((s a).length+1)+3*(s o).length) := by
  let a' := front k 1 a
  let o' := front k 1 o
  let q := aux k
  have hf := seq (lengthAdd a' q (front_ne_aux a)) (seq (copy q o') (clear q))
  apply localRegisters 1 hf
  · intro s
    dsimp only [Function.comp_def,a',o',q]
    simp only [extend_front',extend_aux,List.append_nil,Function.update_self]
    rw [Function.update_comm (front_ne_aux o),Function.update_idem,clear_aux,extend_update]
  · intro s
    dsimp only [Function.comp_def,a',o',q]
    simp only [extend_front',extend_aux,List.append_nil,Function.update_self,
      Function.update_of_ne (front_ne_aux o),Function.update_of_ne (aux_ne_front o),List.length_replicate]
    omega

 theorem add_fast (a b o : Fin (k+1)) :
    Realizes (fun s : Stores k=>Function.update s o (List.replicate ((s a).length+(s b).length) true))
      (fun s=>20*((s a).length+(s b).length+1)+3*(s o).length) := by
  let a' := front k 1 a
  let b' := front k 1 b
  let o' := front k 1 o
  let q := aux k
  have hf := seq (lengthAdd b' q (front_ne_aux b))
    (seq (lengthAdd a' q (front_ne_aux a)) (seq (copy q o') (clear q)))
  apply localRegisters 1 hf
  · intro s
    dsimp only [Function.comp_def,a',b',o',q]
    simp only [extend_front',extend_aux,List.append_nil,Function.update_self,
      Function.update_of_ne (front_ne_aux a),Function.update_idem,←List.replicate_add]
    rw [Function.update_comm (front_ne_aux o),Function.update_idem,clear_aux,extend_update]
  · intro s
    dsimp only [Function.comp_def,a',b',o',q]
    simp only [extend_front',extend_aux,List.append_nil,Function.update_self,
      Function.update_of_ne (front_ne_aux a),Function.update_of_ne (front_ne_aux o),
      Function.update_of_ne (aux_ne_front o),List.length_append,List.length_replicate]
    omega

 theorem subtract_fast (a b o : Fin (k+1)) :
    Realizes (fun s : Stores k=>Function.update s o (List.replicate ((s a).length-(s b).length) true))
      (fun s=>20*((s a).length+(s b).length+1)+3*(s o).length) := by
  let a' := front k 1 a
  let b' := front k 1 b
  let o' := front k 1 o
  let q := aux k
  have hf := seq (lengthAdd a' q (front_ne_aux a))
    (seq (countedPop b' q) (seq (copy q o') (clear q)))
  apply localRegisters 1 hf
  · intro s
    dsimp only [Function.comp_def,a',b',o',q]
    simp only [extend_front',extend_aux,List.append_nil,Function.update_self,
      Function.update_of_ne (front_ne_aux b),Function.update_idem,List.drop_replicate]
    rw [Function.update_comm (front_ne_aux o),Function.update_idem,clear_aux,extend_update]
  · intro s
    dsimp only [Function.comp_def,a',b',o',q]
    simp only [extend_front',extend_aux,List.append_nil,Function.update_self,
      Function.update_of_ne (front_ne_aux b),Function.update_of_ne (front_ne_aux o),
      Function.update_of_ne (aux_ne_front o),List.length_drop,List.length_replicate]
    omega

 theorem reverse (a o : Fin (k+1)) :
    Realizes (fun s : Stores k=>Function.update s o (s a).reverse)
      (fun s=>20*((s a).length+1)+3*(s o).length) := by
  let a' := front k 1 a
  let o' := front k 1 o
  let q := aux k
  have hf := seq (reverseCopy a' q (front_ne_aux a) id) (seq (copy q o') (clear q))
  apply localRegisters 1 hf
  · intro s
    dsimp only [Function.comp_def,a',o',q]
    simp only [extend_front',extend_aux,List.append_nil,List.map_id_fun,id_eq,Function.update_self]
    rw [Function.update_comm (front_ne_aux o),Function.update_idem,clear_aux,extend_update]
  · intro s
    dsimp only [Function.comp_def,a',o',q]
    simp only [extend_front',extend_aux,List.append_nil,List.map_id_fun,id_eq,Function.update_self,
      Function.update_of_ne (front_ne_aux o),Function.update_of_ne (aux_ne_front o),List.length_reverse]
    omega

 theorem append (a b o : Fin (k+1)) :
    Realizes (fun s : Stores k=>Function.update s o (s a++s b))
      (fun s=>20*((s a).length+(s b).length+1)+3*(s o).length) := by
  let a' := front k 1 a
  let b' := front k 1 b
  let o' := front k 1 o
  let q := aux k
  have hf := seq (reverseCopy a' q (front_ne_aux a) id)
    (seq (copy b' o') (seq (reverseCopy q o' (aux_ne_front o) id) (clear q)))
  apply localRegisters 1 hf
  · intro s
    dsimp only [Function.comp_def,a',b',o',q]
    simp only [extend_front',extend_aux,List.append_nil,List.map_id_fun,id_eq,Function.update_self,
      Function.update_of_ne (front_ne_aux b),Function.update_of_ne (aux_ne_front o),List.reverse_reverse,
      Function.update_idem]
    rw [Function.update_comm (front_ne_aux o),Function.update_idem,clear_aux,extend_update]
  · intro s
    dsimp only [Function.comp_def,a',b',o',q]
    simp only [extend_front',extend_aux,List.append_nil,List.map_id_fun,id_eq,Function.update_self,
      Function.update_of_ne (front_ne_aux b),Function.update_of_ne (front_ne_aux o),
      Function.update_of_ne (aux_ne_front o),List.length_reverse]
    omega

 theorem drop (a ix o : Fin (k+1)) :
    Realizes (fun s : Stores k=>Function.update s o ((s a).drop (s ix).length))
      (fun s=>24*((s a).length+1)+11*(s ix).length+3*(s o).length) := by
  let a' := front k 1 a
  let i' := front k 1 ix
  let o' := front k 1 o
  let q := aux k
  have hf := seq (copy a' q) (seq (countedPop i' q) (seq (copy q o') (clear q)))
  apply localRegisters 1 hf
  · intro s
    dsimp only [Function.comp_def,a',i',o',q]
    simp only [extend_front',Function.update_self,Function.update_of_ne (front_ne_aux ix),
      Function.update_idem]
    rw [Function.update_comm (front_ne_aux o),Function.update_idem,clear_aux,extend_update]
  · intro s
    dsimp only [Function.comp_def,a',i',o',q]
    simp only [extend_front',extend_aux,Function.update_self,Function.update_of_ne (front_ne_aux ix),
      Function.update_of_ne (front_ne_aux o),Function.update_of_ne (aux_ne_front o),List.length_drop,List.length_nil]
    omega

end VariableWL.Computation.Stack.Procedure

namespace VariableWL.Computation.Stack.Recipe
open Procedure
abbrev Env (n : ℕ) := Fin n → Word

def cons {n : ℕ} (w : Word) (v : Env n) : Env (n+1) := Fin.cons w v

structure Certified (n : ℕ) where
  value : Env n → Word
  time : Env n → ℕ
  compiled : ∀ (k : ℕ) (ρ : Fin n → Fin (k+1)) (o : Fin (k+1)),
    Realizes (fun s : Stores k=>Function.update s o (value (s ∘ ρ)))
      (fun s=>time (s ∘ ρ)+3*(s o).length)

variable {n m : ℕ}

def reindex (P : Certified n) (φ : Fin n → Fin m) : Certified m where
  value := fun v=>P.value (v ∘ φ)
  time := fun v=>P.time (v ∘ φ)
  compiled k ρ o := P.compiled k (ρ ∘ φ) o

def input (i : Fin n) : Certified n where
  value := fun v=>v i
  time := fun v=>9*(v i).length+3
  compiled k ρ o := by
    simpa only [Function.comp_apply,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using copy (ρ i) o

def literal (w : Word) : Certified n where
  value := fun _=>w
  time := fun _=>1+2*w.length
  compiled k ρ o := by
    simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using constant o w

 theorem env_front (k : ℕ) (ρ : Fin n → Fin (k+1)) (s : Stores k) :
    extend 1 s ∘ (front k 1 ∘ ρ)=s ∘ ρ := by
  funext i
  exact extend_front' 1 s (ρ i)

 theorem env_cons (k : ℕ) (ρ : Fin n → Fin (k+1)) (s : Stores k) (w : Word) :
    Function.update (extend 1 s) (aux k) w ∘ Fin.cons (aux k) (front k 1 ∘ ρ)=cons w (s ∘ ρ) := by
  funext i
  refine Fin.cases ?_ (fun j=>?_) i
  · simp only [Function.comp_apply,Fin.cons_zero,Function.update_self,cons]
  · simp only [Function.comp_apply,Fin.cons_succ,Function.update_of_ne (front_ne_aux (ρ j)),
      extend_front',cons]

def bind (P : Certified n) (Q : Certified (n+1)) : Certified n where
  value := fun v=>Q.value (cons (P.value v) v)
  time := fun v=>P.time v+Q.time (cons (P.value v) v)+3*(P.value v).length+2
  compiled k ρ o := by
    let ρ' := front k 1 ∘ ρ
    let o' := front k 1 o
    let q := aux k
    have hf := seq (P.compiled (k+1) ρ' q)
      (seq (Q.compiled (k+1) (Fin.cons q ρ') o') (clear q))
    apply localRegisters 1 hf
    · intro s
      dsimp only [Function.comp_def,ρ',o',q]
      rw [show (fun x => extend 1 s (front k 1 (ρ x)))=s ∘ ρ by exact env_front k ρ s]
      have hc := env_cons k ρ s (P.value (s ∘ ρ))
      dsimp only [Function.comp_def] at hc
      dsimp only [Function.comp_def]
      rw [hc]
      rw [Function.update_comm (front_ne_aux o),Function.update_idem,clear_aux,extend_update]
    · intro s
      dsimp only [Function.comp_def,ρ',o',q]
      rw [show (fun x => extend 1 s (front k 1 (ρ x)))=s ∘ ρ by exact env_front k ρ s]
      have hc := env_cons k ρ s (P.value (s ∘ ρ))
      dsimp only [Function.comp_def] at hc
      dsimp only [Function.comp_def]
      rw [hc]
      simp only [extend_aux,List.length_nil,Nat.mul_zero,Nat.add_zero,
        Function.update_of_ne (front_ne_aux o),Function.update_of_ne (aux_ne_front o),
        Function.update_self,extend_front']
      omega

def headBranch (p : (Fin n → Option Bool) → Bool) (P Q : Certified n) : Certified n where
  value := fun v=>if p (fun i=>(v i).head?) then P.value v else Q.value v
  time := fun v=>(if p (fun i=>(v i).head?) then P.time v else Q.time v)+1
  compiled k ρ o := by
    have h := branch (fun h=>p (h ∘ ρ)) (P.compiled k ρ o) (Q.compiled k ρ o)
    have he : (fun s : Stores k => if p (heads s ∘ ρ) then Function.update s o (P.value (s ∘ ρ))
        else Function.update s o (Q.value (s ∘ ρ)))=
        (fun s : Stores k => Function.update s o (if p (fun i=>(s (ρ i)).head?) then P.value (s ∘ ρ) else Q.value (s ∘ ρ))) := by
      funext s
      change (if p (fun i=>(s (ρ i)).head?) then _ else _)=_
      split <;> rfl
    rw [he] at h
    apply monotone h
    intro s
    change (if p (fun i=>(s (ρ i)).head?) then P.time (s ∘ ρ)+3*(s o).length
      else Q.time (s ∘ ρ)+3*(s o).length)+1 ≤ _
    dsimp only [Function.comp_apply]
    split_ifs <;> omega

def test (p : (Fin n → Option Bool) → Bool) : Certified n :=
  headBranch p (literal [true]) (literal [false])

 theorem test_value (p : (Fin n → Option Bool) → Bool) (v : Env n) :
    (test p).value v=[p (fun i=>(v i).head?)] := by
  simp only [test,headBranch,literal]
  split <;> rename_i h <;> simp_all

def length (i : Fin n) : Certified n where
  value := fun v=>List.replicate (v i).length true
  time := fun v=>20*((v i).length+1)
  compiled k ρ o := by simpa only [Function.comp_apply] using length_fast (ρ i) o

def add (i j : Fin n) : Certified n where
  value := fun v=>List.replicate ((v i).length+(v j).length) true
  time := fun v=>20*((v i).length+(v j).length+1)
  compiled k ρ o := by simpa only [Function.comp_apply] using add_fast (ρ i) (ρ j) o

def subtract (i j : Fin n) : Certified n where
  value := fun v=>List.replicate ((v i).length-(v j).length) true
  time := fun v=>20*((v i).length+(v j).length+1)
  compiled k ρ o := by simpa only [Function.comp_apply] using subtract_fast (ρ i) (ρ j) o

def multiply (i j : Fin n) : Certified n where
  value := fun v=>List.replicate ((v i).length*(v j).length) true
  time := fun v=>20*((v i).length+1)*((v j).length+1)+10
  compiled k ρ o := by
    simpa only [Function.comp_apply,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using Procedure.multiply (ρ i) (ρ j) o

def reverse (i : Fin n) : Certified n where
  value := fun v=>(v i).reverse
  time := fun v=>20*((v i).length+1)
  compiled k ρ o := by simpa only [Function.comp_apply] using Procedure.reverse (ρ i) o

def append (i j : Fin n) : Certified n where
  value := fun v=>v i++v j
  time := fun v=>20*((v i).length+(v j).length+1)
  compiled k ρ o := by simpa only [Function.comp_apply] using Procedure.append (ρ i) (ρ j) o

def drop (i j : Fin n) : Certified n where
  value := fun v=>(v i).drop (v j).length
  time := fun v=>24*((v i).length+1)+11*(v j).length
  compiled k ρ o := by simpa only [Function.comp_apply] using Procedure.drop (ρ i) (ρ j) o

def lookup (i j : Fin n) : Certified n where
  value := fun v=>[(v i).getD (v j).length false]
  time := fun v=>12*(v i).length+11*(v j).length+12
  compiled k ρ o := by
    simpa only [Function.comp_apply,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using Procedure.lookup (ρ i) (ρ j) o

end VariableWL.Computation.Stack.Recipe

namespace VariableWL.Computation.Stack.Recipe
open Procedure
variable {n : ℕ}

 def foldValue (Q : Certified (n+2)) (v : Env n) (w : Word) : ℕ → Word
  | 0 => w
  | j+1 => Q.value (cons (foldValue Q v w j) (cons (List.replicate j true) v))

 def foldTime (Q : Certified (n+2)) (v : Env n) (w : Word) (j : ℕ) : ℕ :=
  Q.time (cons (foldValue Q v w j) (cons (List.replicate j true) v))+
    3*(foldValue Q v w j).length+2

noncomputable def frame {k : ℕ} (s : Stores k) (j : ℕ) (w : Word) : Stores (k+2) :=
  Function.update (BoundedLoop.state k s j) (BoundedLoop.scratch k) w

 @[simp] theorem frame_front {k : ℕ} (s : Stores k) (j : ℕ) (w : Word) (i : Fin (k+1)) :
    frame s j w (BoundedLoop.embed k i)=s i := by
  rw [frame,Function.update_of_ne (BoundedLoop.scratch_ne k i),BoundedLoop.state_embed]

 @[simp] theorem frame_index {k : ℕ} (s : Stores k) (j : ℕ) (w : Word) :
    frame s j w (BoundedLoop.counter k)=List.replicate j true := by
  rw [frame,Function.update_of_ne (BoundedLoop.counter_scratch k),BoundedLoop.state_counter]

 @[simp] theorem frame_acc {k : ℕ} (s : Stores k) (j : ℕ) (w : Word) :
    frame s j w (BoundedLoop.scratch k)=w := Function.update_self ..

 def foldInputs (k : ℕ) (ρ : Fin n → Fin (k+1)) : Fin (n+2) → Fin (k+2+1) :=
  Fin.cons (BoundedLoop.scratch k) (Fin.cons (BoundedLoop.counter k) (BoundedLoop.embed k ∘ ρ))

 theorem frame_env {k : ℕ} (ρ : Fin n → Fin (k+1)) (s : Stores k) (j : ℕ) (w : Word) :
    frame s j w ∘ foldInputs k ρ=cons w (cons (List.replicate j true) (s ∘ ρ)) := by
  funext i
  refine Fin.cases ?_ (fun i=>Fin.cases ?_ (fun i=>?_) i) i
  · simp only [foldInputs,Function.comp_apply,Fin.cons_zero,frame_acc,cons]
  · simp only [foldInputs,Function.comp_apply,Fin.cons_succ,Fin.cons_zero,frame_index,cons]
  · simp only [foldInputs,Function.comp_apply,Fin.cons_succ,frame_front,cons]

 theorem frame_initial {k : ℕ} (s : Stores k) (w : Word) :
    Function.update (extend 2 s) (BoundedLoop.scratch k) w=frame s 0 w := by
  rw [←state_base]
  rfl

 theorem frame_step {k : ℕ} (s : Stores k) (j : ℕ) (w v : Word) :
    Function.update (Function.update (frame s j w) (BoundedLoop.scratch k) v)
      (BoundedLoop.counter k)
      (true::Function.update (frame s j w) (BoundedLoop.scratch k) v (BoundedLoop.counter k))=
    frame s (j+1) v := by
  rw [Function.update_of_ne (BoundedLoop.counter_scratch k),frame_index,←List.replicate_succ]
  unfold frame
  rw [Function.update_idem,Function.update_comm (Ne.symm (BoundedLoop.counter_scratch k)),BoundedLoop.update_counter]

 theorem frame_finish {k : ℕ} (s : Stores k) (j : ℕ) (w : Word) (o : Fin (k+1)) :
    Function.update (Function.update (Function.update (frame s j w) (BoundedLoop.embed k o) w)
      (BoundedLoop.scratch k) []) (BoundedLoop.counter k) []=
      extend 2 (Function.update s o w) := by
  funext z
  rcases BoundedLoop.cases_index k z with ⟨i,rfl⟩|rfl|rfl
  · have ht : extend 2 (Function.update s o w) (BoundedLoop.embed k i)=Function.update s o w i :=
      extend_front 2 _ i
    rw [ht,Function.update_of_ne (BoundedLoop.counter_ne k i),
      Function.update_of_ne (BoundedLoop.scratch_ne k i)]
    by_cases hi : i=o
    · subst i; simp only [Function.update_self]
    · rw [Function.update_of_ne (fun h=>hi ((BoundedLoop.embed k).injective h)),
        Function.update_of_ne hi,frame_front]
  · rw [Function.update_self,extend_back _ _ _ (by rfl)]
  · rw [Function.update_of_ne (Ne.symm (BoundedLoop.counter_scratch k)),Function.update_self,
      extend_back _ _ _ (by change k+1≤k+2; omega)]

 def foldBody {k : ℕ} (Q : Certified (n+2)) (ρ : Fin n → Fin (k+1)) (s : Stores (k+2)) : Stores (k+2) :=
  let t := Function.update s (BoundedLoop.scratch k) (Q.value (s ∘ foldInputs k ρ))
  Function.update t (BoundedLoop.counter k) (true::t (BoundedLoop.counter k))

 theorem iterate_foldBody {k : ℕ} (Q : Certified (n+2)) (ρ : Fin n → Fin (k+1))
    (s : Stores k) (w : Word) (j : ℕ) :
    ((foldBody Q ρ)^[j]) (frame s 0 w)=frame s j (foldValue Q (s ∘ ρ) w j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply',ih]
    unfold foldBody
    rw [frame_env,frame_step]
    rfl

 def fold (b z : Fin n) (Q : Certified (n+2)) : Certified n where
  value := fun v=>foldValue Q v (v z) (v b).length
  time := fun v=>9*(v z).length+9*(v b).length+
    BoundedLoop.total (v b).length (foldTime Q v (v z))+
    12*(foldValue Q v (v z) (v b).length).length+20
  compiled k ρ o := by
    let q := BoundedLoop.counter k
    let a := BoundedLoop.scratch k
    let ρ' := BoundedLoop.embed k ∘ ρ
    let o' := BoundedLoop.embed k o
    have hb := seq (Q.compiled (k+2) (foldInputs k ρ) a) (push q true)
    have hf := seq (copy (ρ' z) a) (seq (countedLoop (ρ' b) hb)
      (seq (copy a o') (seq (clear a) (clear q))))
    apply localRegisters 2 hf
    · intro s
      dsimp only [Function.comp_def,ρ',o',a,q]
      rw [show extend 2 s (BoundedLoop.embed k (ρ z))=s (ρ z) from extend_front 2 s (ρ z)]
      rw [frame_initial]
      change Function.update (Function.update (Function.update
        (((foldBody Q ρ)^[(frame s 0 (s (ρ z)) (BoundedLoop.embed k (ρ b))).length])
          (frame s 0 (s (ρ z)))) (BoundedLoop.embed k o)
        ((((foldBody Q ρ)^[(frame s 0 (s (ρ z)) (BoundedLoop.embed k (ρ b))).length])
          (frame s 0 (s (ρ z)))) (BoundedLoop.scratch k)))
        (BoundedLoop.scratch k) []) (BoundedLoop.counter k) []=_
      rw [frame_front,iterate_foldBody,frame_acc,frame_finish]
      rfl
    · intro s
      dsimp only [Function.comp_def,ρ',o',a,q]
      rw [show extend 2 s (BoundedLoop.embed k (ρ z))=s (ρ z) from extend_front 2 s (ρ z)]
      rw [show extend 2 s (BoundedLoop.scratch k)=[] from extend_back 2 s _ (by change k+1≤k+2; omega)]
      rw [frame_initial,frame_front]
      have hj (j : ℕ) :
          ((fun t : Stores (k+2) => Function.update
            (Function.update t (BoundedLoop.scratch k) (Q.value (fun x=>t (foldInputs k ρ x))))
            (BoundedLoop.counter k) (true::t (BoundedLoop.counter k)))^[j]) (frame s 0 (s (ρ z)))=
          frame s j (foldValue Q (s ∘ ρ) (s (ρ z)) j) := by
        have heq : foldBody Q ρ=(fun t : Stores (k+2) => Function.update
            (Function.update t (BoundedLoop.scratch k) (Q.value (fun x=>t (foldInputs k ρ x))))
            (BoundedLoop.counter k) (true::t (BoundedLoop.counter k))) := by
          funext t
          unfold foldBody
          simp only [Function.comp_def,Function.update_of_ne (BoundedLoop.counter_scratch k)]
        rw [←heq]
        exact iterate_foldBody Q ρ s (s (ρ z)) j
      have henv (j : ℕ) : (fun x=>frame s j (foldValue Q (s ∘ ρ) (s (ρ z)) j) (foldInputs k ρ x))=
          cons (foldValue Q (s ∘ ρ) (s (ρ z)) j) (cons (List.replicate j true) (s ∘ ρ)) :=
        frame_env ρ s j _
      simp only [hj,henv,frame_acc,frame_front,List.length_nil,Nat.mul_zero,Nat.add_zero,
        Function.update_of_ne (Ne.symm (BoundedLoop.scratch_ne k o)),
        Function.update_of_ne (Ne.symm (BoundedLoop.counter_ne k o)),
        Function.update_of_ne (BoundedLoop.counter_scratch k),frame_index,List.length_replicate]
      have he : (fun j=>Q.time (cons (foldValue Q (s ∘ ρ) (s (ρ z)) j)
        (cons (List.replicate j true) (s ∘ ρ)))+3*(foldValue Q (s ∘ ρ) (s (ρ z)) j).length+1+1)=
        foldTime Q (s ∘ ρ) (s (ρ z)) := by funext j; simp only [foldTime]
      rw [he]
      simp only [Function.comp_def]
      omega

end VariableWL.Computation.Stack.Recipe

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_CertifiedRecipe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.Computation.Stack.Recipe
variable {n m : ℕ}

namespace Certified
abbrev reindex (P : Certified n) (φ : Fin n → Fin m) : Certified m := Recipe.reindex P φ
abbrev bind (P : Certified n) (Q : Certified (n+1)) : Certified n := Recipe.bind P Q
end Certified

@[simp] theorem cons_zero (w : Word) (v : Env n) : cons w v 0=w := rfl
@[simp] theorem cons_succ (w : Word) (v : Env n) (i : Fin n) : cons w v i.succ=v i := rfl
@[simp] theorem reindex_value (P : Certified n) (φ : Fin n → Fin m) (v : Env m) :
    (P.reindex φ).value v=P.value (v ∘ φ) := rfl
@[simp] theorem bind_value (P : Certified n) (Q : Certified (n+1)) (v : Env n) :
    (P.bind Q).value v=Q.value (cons (P.value v) v) := rfl
@[simp] theorem input_value (i : Fin n) (v : Env n) : (input i).value v=v i := rfl
@[simp] theorem literal_value (w : Word) (v : Env n) : (literal w).value v=w := rfl
@[simp] theorem cons_comp_succ (w : Word) (v : Env n) : cons w v ∘ Fin.succ=v := rfl

 def unary (P : Certified n) (op : Fin (n+1) → Certified (n+1)) : Certified n := P.bind (op 0)
 def binary (P Q : Certified n) (op : Fin (n+2) → Fin (n+2) → Certified (n+2)) : Certified n :=
  P.bind ((Q.reindex Fin.succ).bind (op 1 0))

 def len (P : Certified n) : Certified n := unary P length
 def plus (P Q : Certified n) : Certified n := binary P Q add
 def minus (P Q : Certified n) : Certified n := binary P Q subtract
 def times (P Q : Certified n) : Certified n := binary P Q multiply
 def cat (P Q : Certified n) : Certified n := binary P Q append
 def rev (P : Certified n) : Certified n := unary P reverse
 def atIndex (P Q : Certified n) : Certified n := binary P Q lookup
 def tailAt (P Q : Certified n) : Certified n := binary P Q drop

@[simp] theorem len_value (P : Certified n) (v : Env n) :
    (len P).value v=List.replicate (P.value v).length true := rfl
@[simp] theorem plus_value (P Q : Certified n) (v : Env n) :
    (plus P Q).value v=List.replicate ((P.value v).length+(Q.value v).length) true := rfl
@[simp] theorem minus_value (P Q : Certified n) (v : Env n) :
    (minus P Q).value v=List.replicate ((P.value v).length-(Q.value v).length) true := rfl
@[simp] theorem times_value (P Q : Certified n) (v : Env n) :
    (times P Q).value v=List.replicate ((P.value v).length*(Q.value v).length) true := rfl
@[simp] theorem cat_value (P Q : Certified n) (v : Env n) :
    (cat P Q).value v=P.value v++Q.value v := rfl
@[simp] theorem rev_value (P : Certified n) (v : Env n) : (rev P).value v=(P.value v).reverse := rfl
@[simp] theorem atIndex_value (P Q : Certified n) (v : Env n) :
    (atIndex P Q).value v=[(P.value v).getD (Q.value v).length false] := rfl
@[simp] theorem tailAt_value (P Q : Certified n) (v : Env n) :
    (tailAt P Q).value v=(P.value v).drop (Q.value v).length := rfl

 def asBool (P : Certified n) : Certified n := P.bind (test (fun h=>h 0==some true))
 def isZero (P : Certified n) : Certified n := P.bind (test (fun h=>h 0==none))
 def choose (B P Q : Certified n) : Certified n :=
  B.bind (headBranch (fun h=>h 0==some true) (P.reindex Fin.succ) (Q.reindex Fin.succ))
 def lessEq (P Q : Certified n) : Certified n := isZero (minus P Q)
 def equal (P Q : Certified n) : Certified n := isZero (plus (minus P Q) (minus Q P))
 def conj (P Q : Certified n) : Certified n :=
  choose P (asBool Q) (literal [false])

@[simp] theorem asBool_value (P : Certified n) (v : Env n) :
    (asBool P).value v=[decide ((P.value v).head?=some true)] := by
  simp only [asBool,bind_value,test_value,cons_zero]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq,decide_eq_true_eq]
@[simp] theorem isZero_value (P : Certified n) (v : Env n) :
    (isZero P).value v=[decide ((P.value v).length=0)] := by
  simp only [isZero,bind_value,test_value,cons_zero]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq,decide_eq_true_eq,List.head?_eq_none_iff,List.length_eq_zero_iff]
@[simp] theorem choose_value (B P Q : Certified n) (v : Env n) :
    (choose B P Q).value v=if (B.value v).head?=some true then P.value v else Q.value v := by
  simp only [choose,bind_value,headBranch,cons_zero,beq_iff_eq,reindex_value,cons_comp_succ]
  split_ifs <;> simp_all
@[simp] theorem lessEq_value (P Q : Certified n) (v : Env n) :
    (lessEq P Q).value v=[decide ((P.value v).length≤(Q.value v).length)] := by
  simp only [lessEq,isZero_value,minus_value,List.length_replicate,Nat.sub_eq_zero_iff_le]
@[simp] theorem equal_value (P Q : Certified n) (v : Env n) :
    (equal P Q).value v=[decide ((P.value v).length=(Q.value v).length)] := by
  simp only [equal,isZero_value,plus_value,minus_value,List.length_replicate]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  omega

@[simp] theorem conj_value (P Q : Certified n) (v : Env n) :
    (conj P Q).value v=[decide ((P.value v).head?=some true) && decide ((Q.value v).head?=some true)] := by
  rw [conj,choose_value]
  split_ifs <;> rename_i h <;> simp [h,asBool_value]

 def liftIndices (φ : Fin n → Fin m) : Fin (n+2) → Fin (m+2) :=
  Fin.cons 0 (Fin.cons 1 (fun i=>(φ i).succ.succ))

 theorem lift_env (φ : Fin n → Fin m) (v : Env m) (a b : Word) :
    cons a (cons b v) ∘ liftIndices φ=cons a (cons b (v ∘ φ)) := by
  funext i
  refine Fin.cases ?_ (fun i=>Fin.cases ?_ (fun i=>?_) i) i <;> rfl

 theorem foldValue_reindex (Q : Certified (n+2)) (φ : Fin n → Fin m) (v : Env m) (w : Word) (j : ℕ) :
    foldValue (Q.reindex (liftIndices φ)) v w j=foldValue Q (v ∘ φ) w j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [foldValue,reindex_value,ih,lift_env]

 def iterate (B Z : Certified n) (Q : Certified (n+2)) : Certified n :=
  B.bind ((Z.reindex Fin.succ).bind (fold 1 0 (Q.reindex (liftIndices (fun i=>i.succ.succ)))))

 theorem iterate_value (B Z : Certified n) (Q : Certified (n+2)) (v : Env n) :
    (iterate B Z Q).value v=foldValue Q v (Z.value v) (B.value v).length := by
  simp only [iterate,bind_value,reindex_value,cons_comp_succ,fold,cons_zero]
  change foldValue _ (cons (Z.value v) (cons (B.value v) v)) (Z.value v) (B.value v).length=_
  rw [foldValue_reindex]
  rfl

 def collect (B : Certified n) (Q : Certified (n+1)) : Certified n :=
  iterate B (literal []) (cat (input 0) (asBool (Q.reindex Fin.succ)))

 theorem collect_value (B : Certified n) (Q : Certified (n+1)) (v : Env n) :
    (collect B Q).value v=(List.range (B.value v).length).map
      (fun i=>decide ((Q.value (cons (List.replicate i true) v)).head?=some true)) := by
  rw [collect,iterate_value]
  generalize (B.value v).length=j
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [foldValue,cat_value,input_value,cons_zero,ih,asBool_value,reindex_value,cons_comp_succ]
    rw [List.range_succ,List.map_append]
    rfl

@[simp] theorem decide_bool (b : Bool) : decide (b=true)=b := by cases b <;> rfl

 def all (B : Certified n) (Q : Certified (n+1)) : Certified n :=
  iterate B (literal [true]) (conj (input 0) (Q.reindex Fin.succ))

 theorem all_value (B : Certified n) (Q : Certified (n+1)) (v : Env n) :
    (all B Q).value v=[(List.range (B.value v).length).all
      (fun i=>decide ((Q.value (cons (List.replicate i true) v)).head?=some true))] := by
  rw [all,iterate_value]
  generalize (B.value v).length=j
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [foldValue,conj_value,input_value,cons_zero,ih,List.head?_cons,
      reindex_value,cons_comp_succ,List.range_succ,List.all_append,
      List.all_cons,List.all_nil,Bool.and_true,Option.some.injEq,decide_bool]
    rfl

 def countTrue (B : Certified n) (Q : Certified (n+1)) : Certified n :=
  iterate B (literal []) (choose (Q.reindex Fin.succ) (cat (literal [true]) (input 0)) (input 0))

 theorem countTrue_value (B : Certified n) (Q : Certified (n+1)) (v : Env n) :
    (countTrue B Q).value v=List.replicate ((List.range (B.value v).length).countP
      (fun i=>decide ((Q.value (cons (List.replicate i true) v)).head?=some true))) true := by
  rw [countTrue,iterate_value]
  generalize (B.value v).length=j
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [foldValue,choose_value,reindex_value,cons_comp_succ,cat_value,literal_value,
      input_value,cons_zero,List.range_succ,List.countP_append,List.countP_cons,List.countP_nil,
      Nat.zero_add]
    split_ifs <;> rename_i h <;> simp_all [List.replicate_succ]

 def power (B E : Certified n) : Certified n :=
  iterate E (literal [true]) (times (input 0) (B.reindex (fun i=>i.succ.succ)))

end VariableWL.Computation.Stack.Recipe

namespace VariableWL.Computation.Stack.Recipe
variable {n : ℕ}

 theorem count_range_lt (a b : ℕ) :
    (List.range a).countP (fun i=>decide (i<b))=min a b := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [List.range_succ,List.countP_append,ih]
    simp only [List.countP_cons,List.countP_nil,Nat.zero_add]
    split_ifs <;> rename_i h <;> simp only [decide_eq_true_eq] at h <;> omega

 theorem count_range_multiples (a b : ℕ) (hb : 0<b) :
    (List.range a).countP (fun i=>decide ((i+1)*b≤a))=a/b := by
  have he : (List.range a).countP (fun i=>decide ((i+1)*b≤a))=
      (List.range a).countP (fun i=>decide (i<a/b)) := by
    apply List.countP_congr
    intro i _
    simp only [decide_eq_true_eq,←Nat.le_div_iff_mul_le hb]
    omega
  rw [he,count_range_lt,min_eq_right (Nat.div_le_self a b)]

 def divide (i j : Fin n) : Certified n :=
  choose (isZero (input j)) (literal [])
    (countTrue (input i) (lessEq (times (plus (input 0) (literal [true])) (input j.succ)) (input i.succ)))

 theorem divide_value (i j : Fin n) (v : Env n) :
    (divide i j).value v=List.replicate ((v i).length/(v j).length) true := by
  rw [divide,choose_value]
  by_cases h : (v j).length=0
  · have hz : ((isZero (input j)).value v).head?=some true := by
      rw [isZero_value,input_value]
      simp only [h,decide_true,List.head?_cons]
    rw [ite_eq_left hz,literal_value,h,Nat.div_zero,List.replicate_zero]
  · have hz : ((isZero (input j)).value v).head?≠some true := by
      rw [isZero_value,input_value]
      simp only [h,decide_false,List.head?_cons,ne_eq,Option.some.injEq,Bool.false_eq_true,not_false_eq_true]
    rw [ite_eq_right hz,countTrue_value]
    simp only [lessEq_value,times_value,plus_value,input_value,cons_zero,cons_succ,
      literal_value,List.length_replicate,List.length_cons,List.length_nil,Nat.zero_add,
      List.head?_cons,Option.some.injEq,decide_bool]
    rw [count_range_multiples _ _ (by omega)]

 def quotient (A B : Certified n) : Certified n := binary A B divide
 def remainder (A B : Certified n) : Certified n := minus A (times (quotient A B) B)

 theorem quotient_value (A B : Certified n) (v : Env n) :
    (quotient A B).value v=List.replicate ((A.value v).length/(B.value v).length) true := by
  simp only [quotient,binary,bind_value,reindex_value,cons_comp_succ,divide_value]
  rfl

 theorem remainder_value (A B : Certified n) (v : Env n) :
    (remainder A B).value v=List.replicate ((A.value v).length%(B.value v).length) true := by
  simp only [remainder,minus_value,times_value,quotient_value,List.length_replicate,Nat.mod_eq_sub_div_mul]

 def minimum (A B : Certified n) : Certified n := choose (lessEq A B) (len A) (len B)
 theorem minimum_value (A B : Certified n) (v : Env n) :
    (minimum A B).value v=List.replicate (min (A.value v).length (B.value v).length) true := by
  simp only [minimum,choose_value,lessEq_value,List.head?_cons,Option.some.injEq,decide_eq_true_eq,len_value,Nat.min_def]
  split_ifs <;> rfl

 theorem min_mul_cap (x c b : ℕ) : min (min x c*b) c=min (x*b) c := by
  by_cases hb : b=0
  · simp [hb]
  · have h : c≤c*b := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left c (show 1≤b by omega)
    rw [←Nat.mul_min_mul_right,min_assoc,min_eq_right h]

 def boundedPower (B E C : Certified n) : Certified n :=
  iterate E (minimum (literal [true]) C)
    (minimum (times (input 0) (B.reindex (fun i=>i.succ.succ))) (C.reindex (fun i=>i.succ.succ)))

 theorem boundedPower_value (B E C : Certified n) (v : Env n) :
    (boundedPower B E C).value v=List.replicate (min ((B.value v).length^(E.value v).length) (C.value v).length) true := by
  rw [boundedPower,iterate_value]
  generalize (E.value v).length=j
  induction j with
  | zero => rw [foldValue,minimum_value,literal_value]; rfl
  | succ j ih =>
    rw [foldValue,minimum_value,times_value,input_value,cons_zero,ih,List.length_replicate]
    simp only [List.length_replicate,reindex_value]
    change List.replicate (min (min ((B.value v).length^j) (C.value v).length*(B.value v).length)
      (C.value v).length) true=_
    rw [min_mul_cap,pow_succ]

end VariableWL.Computation.Stack.Recipe

namespace VariableWL.Computation.Stack.Recipe
variable {n m : ℕ}

def Growth (f : ℕ → ℕ) : Prop := ∃ c d : ℕ, ∀N, f N≤c*(N+1)^d

namespace Growth
 theorem constant (a : ℕ) : Growth (fun _=>a) := ⟨a,0,by intro N; simp⟩
 theorem ident : Growth id := ⟨1,1,by intro N; simp⟩
 theorem add {f g : ℕ → ℕ} (hf : Growth f) (hg : Growth g) : Growth (fun N=>f N+g N) := by
  obtain ⟨a,b,ha⟩ := hf
  obtain ⟨c,d,hc⟩ := hg
  refine ⟨a+c,b+d,fun N=>?_⟩
  have h1 := (ha N).trans (Nat.mul_le_mul_left a (Nat.pow_le_pow_right (by omega : 0<N+1) (by omega : b≤b+d)))
  have h2 := (hc N).trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_right (by omega : 0<N+1) (by omega : d≤b+d)))
  nlinarith
 theorem mul {f g : ℕ → ℕ} (hf : Growth f) (hg : Growth g) : Growth (fun N=>f N*g N) := by
  obtain ⟨a,b,ha⟩ := hf
  obtain ⟨c,d,hc⟩ := hg
  refine ⟨a*c,b+d,fun N=>?_⟩
  exact (Nat.mul_le_mul (ha N) (hc N)).trans_eq (by rw [pow_add]; ring)
 theorem comp {f g : ℕ → ℕ} (hf : Growth f) (hg : Growth g) : Growth (f ∘ g) := by
  obtain ⟨a,b,ha⟩ := hf
  obtain ⟨c,d,hc⟩ := hg
  refine ⟨a*(c+1)^b,d*b,fun N=>?_⟩
  have hpos : 1≤(N+1)^d := Nat.succ_le_of_lt (pow_pos (by omega) _)
  have hh : g N+1≤(c+1)*(N+1)^d := by have := hc N; nlinarith
  refine (ha (g N)).trans ((Nat.mul_le_mul_left a (Nat.pow_le_pow_left hh b)).trans_eq ?_)
  rw [mul_pow,←pow_mul]
  ring
 theorem pow {f : ℕ → ℕ} (hf : Growth f) (d : ℕ) : Growth (fun N=>(f N)^d) := by
  induction d with
  | zero => simpa only [pow_zero] using constant 1
  | succ d ih => simpa only [pow_succ] using mul ih hf
end Growth

def EnvBound (C : ℕ) (v : Env n) : Prop := ∀i,(v i).length≤C

def Poly (P : Certified n) : Prop := ∃f : ℕ → ℕ, Growth f ∧
  ∀C v, EnvBound C v → P.time v+(P.value v).length≤f C

 theorem envBound_cons {C : ℕ} {v : Env n} {w : Word} (hv : EnvBound C v) (hw : w.length≤C) :
    EnvBound C (cons w v) := by
  intro i
  exact Fin.cases hw (fun j=>hv j) i

 theorem poly_of_bound (P : Certified n) (c d : ℕ)
    (h : ∀C v,EnvBound C v → P.time v+(P.value v).length≤c*(C+1)^d) : Poly P :=
  ⟨fun C=>c*(C+1)^d,⟨c,d,fun _=>le_rfl⟩,h⟩

 theorem poly_reindex {P : Certified n} (h : Poly P) (φ : Fin n → Fin m) : Poly (P.reindex φ) := by
  obtain ⟨f,hf,hP⟩ := h
  refine ⟨f,hf,fun C v hv=>hP C (v ∘ φ) (fun i=>hv (φ i))⟩

 theorem poly_input (i : Fin n) : Poly (input i) := by
  apply poly_of_bound _ 13 1
  intro C v hv
  have := hv i
  change 9*(v i).length+3+(v i).length≤13*(C+1)^1
  simp only [pow_one]
  omega

 theorem poly_literal (w : Word) : Poly (literal (n := n) w) := by
  exact ⟨fun _=>1+3*w.length,Growth.constant _,by intro C v hv; change 1+2*w.length+w.length≤1+3*w.length; omega⟩

 theorem poly_bind {P : Certified n} {Q : Certified (n+1)} (hP : Poly P) (hQ : Poly Q) : Poly (P.bind Q) := by
  obtain ⟨f,hf,hP⟩ := hP
  obtain ⟨g,hg,hQ⟩ := hQ
  refine ⟨fun C=>4*f C+g (f C+C)+2,?_,?_⟩
  · exact ((Growth.constant 4 |>.mul hf).add (hg.comp (hf.add Growth.ident))).add (Growth.constant 2)
  · intro C v hv
    have h1 := hP C v hv
    have hev : EnvBound (f C+C) (cons (P.value v) v) :=
      envBound_cons (fun i=>(hv i).trans (by omega)) (by omega)
    have h2 := hQ (f C+C) (cons (P.value v) v) hev
    change P.time v+Q.time (cons (P.value v) v)+3*(P.value v).length+2+
      (Q.value (cons (P.value v) v)).length≤4*f C+g (f C+C)+2
    omega

 theorem poly_headBranch (p : (Fin n → Option Bool) → Bool) {P Q : Certified n}
    (hP : Poly P) (hQ : Poly Q) : Poly (headBranch p P Q) := by
  obtain ⟨f,hf,hP⟩ := hP
  obtain ⟨g,hg,hQ⟩ := hQ
  refine ⟨fun C=>f C+g C+1,(hf.add hg).add (Growth.constant 1),?_⟩
  intro C v hv
  have h1 := hP C v hv
  have h2 := hQ C v hv
  change (if p (fun i=>(v i).head?) then P.time v else Q.time v)+1+
    (if p (fun i=>(v i).head?) then P.value v else Q.value v).length≤f C+g C+1
  split <;> omega

 theorem poly_test (p : (Fin n → Option Bool) → Bool) : Poly (test p) :=
  poly_headBranch p (poly_literal _) (poly_literal _)

 theorem poly_length (i : Fin n) : Poly (length i) := by
  apply poly_of_bound _ 21 1
  intro C v hv
  have := hv i
  change 20*((v i).length+1)+(List.replicate (v i).length true).length≤_
  simp only [List.length_replicate,pow_one]
  omega

 theorem poly_add (i j : Fin n) : Poly (add i j) := by
  apply poly_of_bound _ 42 1
  intro C v hv
  have := hv i
  have := hv j
  change 20*((v i).length+(v j).length+1)+(List.replicate ((v i).length+(v j).length) true).length≤_
  simp only [List.length_replicate,pow_one]
  omega

 theorem poly_subtract (i j : Fin n) : Poly (subtract i j) := by
  apply poly_of_bound _ 42 1
  intro C v hv
  have := hv i
  have := hv j
  change 20*((v i).length+(v j).length+1)+(List.replicate ((v i).length-(v j).length) true).length≤_
  simp only [List.length_replicate,pow_one]
  omega

 theorem poly_multiply (i j : Fin n) : Poly (multiply i j) := by
  apply poly_of_bound _ 31 2
  intro C v hv
  have h1 := hv i
  have h2 := hv j
  have hh := Nat.mul_le_mul h1 h2
  change 20*((v i).length+1)*((v j).length+1)+10+
    (List.replicate ((v i).length*(v j).length) true).length≤_
  simp only [List.length_replicate,pow_two]
  nlinarith

 theorem poly_reverse (i : Fin n) : Poly (reverse i) := by
  apply poly_of_bound _ 21 1
  intro C v hv
  have := hv i
  change 20*((v i).length+1)+(v i).reverse.length≤_
  simp only [List.length_reverse,pow_one]
  omega

 theorem poly_append (i j : Fin n) : Poly (append i j) := by
  apply poly_of_bound _ 42 1
  intro C v hv
  have := hv i
  have := hv j
  change 20*((v i).length+(v j).length+1)+((v i)++(v j)).length≤_
  simp only [List.length_append,pow_one]
  omega

 theorem poly_drop (i j : Fin n) : Poly (drop i j) := by
  apply poly_of_bound _ 36 1
  intro C v hv
  have := hv i
  have := hv j
  change 24*((v i).length+1)+11*(v j).length+((v i).drop (v j).length).length≤_
  simp only [List.length_drop,pow_one]
  omega

 theorem poly_lookup (i j : Fin n) : Poly (lookup i j) := by
  apply poly_of_bound _ 24 1
  intro C v hv
  have := hv i
  have := hv j
  change 12*(v i).length+11*(v j).length+12+[_].length≤_
  simp only [List.length_cons,List.length_nil,pow_one]
  omega

 theorem poly_unary {P : Certified n} (o : Fin (n+1) → Certified (n+1))
    (hP : Poly P) (ho : ∀i,Poly (o i)) : Poly (unary P o) := poly_bind hP (ho _)

 theorem poly_binary {P Q : Certified n} (o : Fin (n+2) → Fin (n+2) → Certified (n+2))
    (hP : Poly P) (hQ : Poly Q) (ho : ∀i j,Poly (o i j)) : Poly (binary P Q o) :=
  poly_bind hP (poly_bind (poly_reindex hQ Fin.succ) (ho _ _))

 theorem poly_len {P : Certified n} (hP : Poly P) : Poly (len P) := poly_unary length hP poly_length
 theorem poly_plus {P Q : Certified n} (hP : Poly P) (hQ : Poly Q) : Poly (plus P Q) := poly_binary add hP hQ poly_add
 theorem poly_minus {P Q : Certified n} (hP : Poly P) (hQ : Poly Q) : Poly (minus P Q) := poly_binary subtract hP hQ poly_subtract
 theorem poly_times {P Q : Certified n} (hP : Poly P) (hQ : Poly Q) : Poly (times P Q) := poly_binary multiply hP hQ poly_multiply
 theorem poly_cat {P Q : Certified n} (hP : Poly P) (hQ : Poly Q) : Poly (cat P Q) := poly_binary append hP hQ poly_append
 theorem poly_rev {P : Certified n} (hP : Poly P) : Poly (rev P) := poly_unary reverse hP poly_reverse
 theorem poly_atIndex {P Q : Certified n} (hP : Poly P) (hQ : Poly Q) : Poly (atIndex P Q) := poly_binary lookup hP hQ poly_lookup
 theorem poly_tailAt {P Q : Certified n} (hP : Poly P) (hQ : Poly Q) : Poly (tailAt P Q) := poly_binary drop hP hQ poly_drop
 theorem poly_asBool {P : Certified n} (hP : Poly P) : Poly (asBool P) := poly_bind hP (poly_test _)
 theorem poly_isZero {P : Certified n} (hP : Poly P) : Poly (isZero P) := poly_bind hP (poly_test _)
 theorem poly_choose {B P Q : Certified n} (hB : Poly B) (hP : Poly P) (hQ : Poly Q) : Poly (choose B P Q) :=
  poly_bind hB (poly_headBranch _ (poly_reindex hP _) (poly_reindex hQ _))
 theorem poly_lessEq {P Q : Certified n} (hP : Poly P) (hQ : Poly Q) : Poly (lessEq P Q) := poly_isZero (poly_minus hP hQ)
 theorem poly_equal {P Q : Certified n} (hP : Poly P) (hQ : Poly Q) : Poly (equal P Q) :=
  poly_isZero (poly_plus (poly_minus hP hQ) (poly_minus hQ hP))
 theorem poly_conj {P Q : Certified n} (hP : Poly P) (hQ : Poly Q) : Poly (conj P Q) :=
  poly_choose hP (poly_asBool hQ) (poly_literal _)
 theorem poly_minimum {P Q : Certified n} (hP : Poly P) (hQ : Poly Q) : Poly (minimum P Q) :=
  poly_choose (poly_lessEq hP hQ) (poly_len hP) (poly_len hQ)

end VariableWL.Computation.Stack.Recipe

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_PolyRecipe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.Computation.Stack.Recipe
variable {n m : ℕ}

@[simp] theorem reindex_time (P : Certified n) (φ : Fin n → Fin m) (v : Env m) :
    (P.reindex φ).time v=P.time (v ∘ φ) := rfl
@[simp] theorem bind_time (P : Certified n) (Q : Certified (n+1)) (v : Env n) :
    (P.bind Q).time v=P.time v+Q.time (cons (P.value v) v)+3*(P.value v).length+2 := rfl
 theorem fold_time (b z : Fin n) (Q : Certified (n+2)) (v : Env n) :
    (fold b z Q).time v=9*(v z).length+9*(v b).length+
      BoundedLoop.total (v b).length (foldTime Q v (v z))+
      12*(foldValue Q v (v z) (v b).length).length+20 := rfl

 theorem foldTime_reindex (Q : Certified (n+2)) (φ : Fin n → Fin m) (v : Env m) (w : Word) (j : ℕ) :
    foldTime (Q.reindex (liftIndices φ)) v w j=foldTime Q (v ∘ φ) w j := by
  simp only [foldTime,reindex_time,foldValue_reindex,lift_env]

 theorem iterate_time (B Z : Certified n) (Q : Certified (n+2)) (v : Env n) :
    (iterate B Z Q).time v=B.time v+Z.time v+12*(B.value v).length+12*(Z.value v).length+
      BoundedLoop.total (B.value v).length (foldTime Q v (Z.value v))+
      12*(foldValue Q v (Z.value v) (B.value v).length).length+24 := by
  simp only [iterate,bind_time,reindex_time,cons_comp_succ,fold_time]
  change B.time v+(Z.time v+(9*(Z.value v).length+9*(B.value v).length+
    BoundedLoop.total (B.value v).length (foldTime (Q.reindex (liftIndices (fun i=>i.succ.succ)))
      (cons (Z.value v) (cons (B.value v) v)) (Z.value v))+
    12*(foldValue (Q.reindex (liftIndices (fun i=>i.succ.succ)))
      (cons (Z.value v) (cons (B.value v) v)) (Z.value v) (B.value v).length).length+20)+
    3*(Z.value v).length+2)+3*(B.value v).length+2=_
  have he : foldTime (Q.reindex (liftIndices (fun i=>i.succ.succ)))
      (cons (Z.value v) (cons (B.value v) v)) (Z.value v)=foldTime Q v (Z.value v) := by
    funext j
    rw [foldTime_reindex]
    rfl
  rw [he,foldValue_reindex]
  change B.time v+(Z.time v+(9*(Z.value v).length+9*(B.value v).length+
    BoundedLoop.total (B.value v).length (foldTime Q v (Z.value v))+
    12*(foldValue Q v (Z.value v) (B.value v).length).length+20)+
    3*(Z.value v).length+2)+3*(B.value v).length+2=_
  omega

 theorem poly_iterate {B Z : Certified n} {Q : Certified (n+2)}
    (hB : Poly B) (hZ : Poly Z) (hQ : Poly Q)
    (f : ℕ → ℕ) (hf : Growth f)
    (hacc : ∀C v,EnvBound C v → ∀j≤(B.value v).length,(foldValue Q v (Z.value v) j).length≤f C) :
    Poly (iterate B Z Q) := by
  obtain ⟨b,hb,hB⟩ := hB
  obtain ⟨z,hz,hZ⟩ := hZ
  obtain ⟨q,hq,hQ⟩ := hQ
  let D : ℕ → ℕ := fun C=>b C+f C+C
  have hD : Growth D := (hb.add hf).add Growth.ident
  refine ⟨fun C=>13*(b C+z C+f C)+(q (D C)+3*f C+6)*b C+24,?_,?_⟩
  · exact (((Growth.constant 13).mul ((hb.add hz).add hf)).add
      ((((hq.comp hD).add ((Growth.constant 3).mul hf)).add (Growth.constant 6)).mul hb)).add (Growth.constant 24)
  · intro C v hv
    have h1 := hB C v hv
    have h2 := hZ C v hv
    have h3 := hacc C v hv (B.value v).length le_rfl
    have hcost (j : ℕ) (hj : j<(B.value v).length) : foldTime Q v (Z.value v) j≤q (D C)+3*f C+2 := by
      have h4 := hacc C v hv j (by omega)
      have hev : EnvBound (D C) (cons (foldValue Q v (Z.value v) j) (cons (List.replicate j true) v)) := by
        apply envBound_cons
        · apply envBound_cons
          · intro i; have := hv i; dsimp only [D]; omega
          · simp only [List.length_replicate]; dsimp only [D]; omega
        · dsimp only [D]; omega
      have h5 := hQ (D C) _ hev
      unfold foldTime
      omega
    have htot := BoundedLoop.total_bound (B.value v).length (q (D C)+3*f C+2) _ hcost
    have htot' : BoundedLoop.total (B.value v).length (foldTime Q v (Z.value v))≤
        (q (D C)+3*f C+6)*b C := by
      apply htot.trans
      have hm := Nat.mul_le_mul_left (q (D C)+3*f C+6) (show (B.value v).length≤b C by omega)
      simpa only [Nat.add_assoc] using hm
    rw [iterate_time,iterate_value]
    change B.time v+Z.time v+12*(B.value v).length+12*(Z.value v).length+
      BoundedLoop.total (B.value v).length (foldTime Q v (Z.value v))+
      12*(foldValue Q v (Z.value v) (B.value v).length).length+24+
      (foldValue Q v (Z.value v) (B.value v).length).length≤
      13*(b C+z C+f C)+(q (D C)+3*f C+6)*b C+24
    omega

 theorem collect_prefix (Q : Certified (n+1)) (v : Env n) (j : ℕ) :
    (foldValue (cat (input 0) (asBool (Q.reindex Fin.succ))) v [] j).length=j := by
  have h := collect_value (literal (List.replicate j true)) Q v
  rw [collect,iterate_value] at h
  simp only [literal_value,List.length_replicate] at h
  rw [h,List.length_map,List.length_range]

 theorem all_prefix (Q : Certified (n+1)) (v : Env n) (j : ℕ) :
    (foldValue (conj (input 0) (Q.reindex Fin.succ)) v [true] j).length=1 := by
  have h := all_value (literal (List.replicate j true)) Q v
  rw [all,iterate_value] at h
  simp only [literal_value,List.length_replicate] at h
  rw [h]
  rfl

 theorem countTrue_prefix (Q : Certified (n+1)) (v : Env n) (j : ℕ) :
    (foldValue (choose (Q.reindex Fin.succ) (cat (literal [true]) (input 0)) (input 0)) v [] j).length≤j := by
  have h := countTrue_value (literal (List.replicate j true)) Q v
  rw [countTrue,iterate_value] at h
  simp only [literal_value,List.length_replicate] at h
  rw [h,List.length_replicate]
  exact (List.countP_le_length).trans_eq (List.length_range (n := j))

 theorem poly_collect {B : Certified n} {Q : Certified (n+1)} (hB : Poly B) (hQ : Poly Q) : Poly (collect B Q) := by
  obtain ⟨b,hb,h⟩ := hB
  apply poly_iterate ⟨b,hb,h⟩ (poly_literal _) (poly_cat (poly_input _) (poly_asBool (poly_reindex hQ _))) b hb
  intro C v hv j hj
  rw [literal_value,collect_prefix]
  have hh := h C v hv
  omega

 theorem poly_all {B : Certified n} {Q : Certified (n+1)} (hB : Poly B) (hQ : Poly Q) : Poly (all B Q) := by
  apply poly_iterate hB (poly_literal _) (poly_conj (poly_input _) (poly_reindex hQ _)) (fun _=>1) (Growth.constant 1)
  intro C v hv j hj
  rw [literal_value,all_prefix]

 theorem poly_countTrue {B : Certified n} {Q : Certified (n+1)} (hB : Poly B) (hQ : Poly Q) : Poly (countTrue B Q) := by
  obtain ⟨b,hb,h⟩ := hB
  apply poly_iterate ⟨b,hb,h⟩ (poly_literal _)
    (poly_choose (poly_reindex hQ _) (poly_cat (poly_literal _) (poly_input _)) (poly_input _)) b hb
  intro C v hv j hj
  rw [literal_value]
  have hh := h C v hv
  exact (countTrue_prefix Q v j).trans (by omega)

 theorem poly_divide (i j : Fin n) : Poly (divide i j) :=
  poly_choose (poly_isZero (poly_input _)) (poly_literal _)
    (poly_countTrue (poly_input _) (poly_lessEq (poly_times (poly_plus (poly_input _) (poly_literal _)) (poly_input _)) (poly_input _)))

 theorem poly_quotient {A B : Certified n} (hA : Poly A) (hB : Poly B) : Poly (quotient A B) :=
  poly_binary divide hA hB poly_divide
 theorem poly_remainder {A B : Certified n} (hA : Poly A) (hB : Poly B) : Poly (remainder A B) :=
  poly_minus hA (poly_times (poly_quotient hA hB) hB)

 theorem boundedPower_prefix (B C : Certified n) (v : Env n) (j : ℕ) :
    (foldValue (minimum (times (input 0) (B.reindex (fun i=>i.succ.succ))) (C.reindex (fun i=>i.succ.succ)))
      v ((minimum (literal [true]) C).value v) j).length≤(C.value v).length := by
  have h := boundedPower_value B (literal (List.replicate j true)) C v
  rw [boundedPower,iterate_value] at h
  simp only [literal_value,List.length_replicate] at h
  rw [h,List.length_replicate]
  exact min_le_right _ _

 theorem poly_boundedPower {B E C : Certified n} (hB : Poly B) (hE : Poly E) (hC : Poly C) :
    Poly (boundedPower B E C) := by
  obtain ⟨c,hc,h⟩ := hC
  apply poly_iterate hE (poly_minimum (poly_literal _) ⟨c,hc,h⟩)
    (poly_minimum (poly_times (poly_input _) (poly_reindex hB _)) (poly_reindex ⟨c,hc,h⟩ _)) c hc
  intro N v hv j hj
  have hh := h N v hv
  exact (boundedPower_prefix B C v j).trans (by omega)

end VariableWL.Computation.Stack.Recipe

namespace VariableWL.Computation.Stack
namespace PolyRecipe
open Recipe

structure Expr (n : ℕ) where
  program : Certified n
  polynomial : Poly program

variable {n m : ℕ}
def Expr.value (P : Expr n) := P.program.value
def Expr.number (P : Expr n) (v : Env n) := (P.value v).length
def Expr.bit (P : Expr n) (v : Env n) := decide ((P.value v).head?=some true)
def Expr.reindex (P : Expr n) (φ : Fin n → Fin m) : Expr m :=
  ⟨P.program.reindex φ,poly_reindex P.polynomial φ⟩
def Expr.up (P : Expr n) : Expr (n+1) := P.reindex Fin.succ
def Expr.up₂ (P : Expr n) : Expr (n+2) := P.reindex (fun i=>i.succ.succ)
def input (i : Fin n) : Expr n := ⟨Recipe.input i,poly_input i⟩
def literal (w : Word) : Expr n := ⟨Recipe.literal w,poly_literal w⟩
def numeral (a : ℕ) : Expr n := literal (List.replicate a true)
def add (P Q : Expr n) : Expr n := ⟨plus P.program Q.program,poly_plus P.polynomial Q.polynomial⟩
def sub (P Q : Expr n) : Expr n := ⟨minus P.program Q.program,poly_minus P.polynomial Q.polynomial⟩
def mul (P Q : Expr n) : Expr n := ⟨times P.program Q.program,poly_times P.polynomial Q.polynomial⟩
def div (P Q : Expr n) : Expr n := ⟨quotient P.program Q.program,poly_quotient P.polynomial Q.polynomial⟩
def mod (P Q : Expr n) : Expr n := ⟨remainder P.program Q.program,poly_remainder P.polynomial Q.polynomial⟩
def capPow (P Q C : Expr n) : Expr n :=
  ⟨boundedPower P.program Q.program C.program,poly_boundedPower P.polynomial Q.polynomial C.polynomial⟩
def eq (P Q : Expr n) : Expr n := ⟨equal P.program Q.program,poly_equal P.polynomial Q.polynomial⟩
def le (P Q : Expr n) : Expr n := ⟨lessEq P.program Q.program,poly_lessEq P.polynomial Q.polynomial⟩
def choose (B P Q : Expr n) : Expr n :=
  ⟨Recipe.choose B.program P.program Q.program,poly_choose B.polynomial P.polynomial Q.polynomial⟩
def neg (P : Expr n) : Expr n := choose P (literal [false]) (literal [true])
def lt (P Q : Expr n) : Expr n := neg (le Q P)
def conj (P Q : Expr n) : Expr n := ⟨Recipe.conj P.program Q.program,poly_conj P.polynomial Q.polynomial⟩
def bitEq (P Q : Expr n) : Expr n := choose P Q (neg Q)
def lookup (P Q : Expr n) : Expr n := ⟨atIndex P.program Q.program,poly_atIndex P.polynomial Q.polynomial⟩
def all (B : Expr n) (Q : Expr (n+1)) : Expr n := ⟨Recipe.all B.program Q.program,poly_all B.polynomial Q.polynomial⟩
def collect (B : Expr n) (Q : Expr (n+1)) : Expr n :=
  ⟨Recipe.collect B.program Q.program,poly_collect B.polynomial Q.polynomial⟩
def count (B : Expr n) (Q : Expr (n+1)) : Expr n :=
  ⟨countTrue B.program Q.program,poly_countTrue B.polynomial Q.polynomial⟩

@[simp] theorem reindex_value (P : Expr n) (φ : Fin n → Fin m) (v : Env m) :
    (P.reindex φ).value v=P.value (v ∘ φ) := rfl
@[simp] theorem up_value (P : Expr n) (v : Env n) (w : Word) : P.up.value (cons w v)=P.value v := rfl
@[simp] theorem up₂_value (P : Expr n) (v : Env n) (w z : Word) : P.up₂.value (cons z (cons w v))=P.value v := rfl
@[simp] theorem input_value (i : Fin n) (v : Env n) : (input i).value v=v i := rfl
@[simp] theorem literal_value (w : Word) (v : Env n) : (literal w).value v=w := rfl
@[simp] theorem numeral_number (a : ℕ) (v : Env n) : (numeral a).number v=a := List.length_replicate ..
@[simp] theorem reindex_number (P : Expr n) (φ : Fin n → Fin m) (v : Env m) :
    (P.reindex φ).number v=P.number (v ∘ φ) := rfl
@[simp] theorem up_number (P : Expr n) (v : Env n) (w : Word) : P.up.number (cons w v)=P.number v := rfl
@[simp] theorem up₂_number (P : Expr n) (v : Env n) (w z : Word) : P.up₂.number (cons z (cons w v))=P.number v := rfl
@[simp] theorem input_number (i : Fin n) (v : Env n) : (input i).number v=(v i).length := rfl
@[simp] theorem add_number (P Q : Expr n) (v : Env n) : (add P Q).number v=P.number v+Q.number v := by
  simp only [Expr.number,Expr.value,add,plus_value,List.length_replicate]
@[simp] theorem sub_number (P Q : Expr n) (v : Env n) : (sub P Q).number v=P.number v-Q.number v := by
  simp only [Expr.number,Expr.value,sub,minus_value,List.length_replicate]
@[simp] theorem mul_number (P Q : Expr n) (v : Env n) : (mul P Q).number v=P.number v*Q.number v := by
  simp only [Expr.number,Expr.value,mul,times_value,List.length_replicate]
@[simp] theorem div_number (P Q : Expr n) (v : Env n) : (div P Q).number v=P.number v/Q.number v := by
  simp only [Expr.number,Expr.value,div,quotient_value,List.length_replicate]
@[simp] theorem mod_number (P Q : Expr n) (v : Env n) : (mod P Q).number v=P.number v%Q.number v := by
  simp only [Expr.number,Expr.value,mod,remainder_value,List.length_replicate]
@[simp] theorem capPow_number (P Q C : Expr n) (v : Env n) :
    (capPow P Q C).number v=min (P.number v^Q.number v) (C.number v) := by
  simp only [Expr.number,Expr.value,capPow,boundedPower_value,List.length_replicate]
@[simp] theorem eq_value (P Q : Expr n) (v : Env n) : (eq P Q).value v=[decide (P.number v=Q.number v)] :=
  equal_value ..
@[simp] theorem le_value (P Q : Expr n) (v : Env n) : (le P Q).value v=[decide (P.number v≤Q.number v)] :=
  lessEq_value ..
@[simp] theorem choose_value (B P Q : Expr n) (v : Env n) :
    (choose B P Q).value v=if B.bit v then P.value v else Q.value v := by
  simp only [Expr.value,Expr.bit,choose,Recipe.choose_value]
  by_cases h : (B.program.value v).head?=some true <;> simp [h]
@[simp] theorem neg_value (P : Expr n) (v : Env n) : (neg P).value v=[!(P.bit v)] := by
  rw [neg,choose_value,literal_value,literal_value]
  cases P.bit v <;> rfl
@[simp] theorem lt_value (P Q : Expr n) (v : Env n) : (lt P Q).value v=[decide (P.number v<Q.number v)] := by
  simp only [lt,neg_value,Expr.bit,le_value,List.head?_cons,Option.some.injEq,decide_bool]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp
 theorem bit_singleton (P : Expr n) (v : Env n) (b : Bool) (h : P.value v=[b]) : P.bit v=b := by
  unfold Expr.bit
  simp only [h,List.head?_cons,Option.some.injEq,decide_bool]

@[simp] theorem eq_bit (P Q : Expr n) (v : Env n) : (eq P Q).bit v=decide (P.number v=Q.number v) := bit_singleton _ _ _ (eq_value P Q v)
@[simp] theorem le_bit (P Q : Expr n) (v : Env n) : (le P Q).bit v=decide (P.number v≤Q.number v) := bit_singleton _ _ _ (le_value P Q v)
@[simp] theorem lt_bit (P Q : Expr n) (v : Env n) : (lt P Q).bit v=decide (P.number v<Q.number v) := bit_singleton _ _ _ (lt_value P Q v)
@[simp] theorem neg_bit (P : Expr n) (v : Env n) : (neg P).bit v=!(P.bit v) := bit_singleton _ _ _ (neg_value P v)
@[simp] theorem conj_value (P Q : Expr n) (v : Env n) : (conj P Q).value v=[P.bit v && Q.bit v] := Recipe.conj_value ..
@[simp] theorem conj_bit (P Q : Expr n) (v : Env n) : (conj P Q).bit v=(P.bit v && Q.bit v) := bit_singleton _ _ _ (conj_value P Q v)
@[simp] theorem choose_bit (B P Q : Expr n) (v : Env n) :
    (choose B P Q).bit v=if B.bit v then P.bit v else Q.bit v := by
  change decide (((choose B P Q).value v).head?=some true)=_
  rw [choose_value]
  split <;> rfl
@[simp] theorem bitEq_bit (P Q : Expr n) (v : Env n) : (bitEq P Q).bit v=decide (P.bit v=Q.bit v) := by
  rw [bitEq,choose_bit,neg_bit]
  cases P.bit v <;> cases Q.bit v <;> rfl
@[simp] theorem lookup_value (P Q : Expr n) (v : Env n) : (lookup P Q).value v=[(P.value v).getD (Q.number v) false] :=
  atIndex_value ..
@[simp] theorem lookup_bit (P Q : Expr n) (v : Env n) : (lookup P Q).bit v=(P.value v).getD (Q.number v) false := bit_singleton _ _ _ (lookup_value P Q v)
@[simp] theorem all_value (B : Expr n) (Q : Expr (n+1)) (v : Env n) :
    (all B Q).value v=[(List.range (B.number v)).all (fun i=>Q.bit (cons (List.replicate i true) v))] := Recipe.all_value ..
@[simp] theorem all_bit (B : Expr n) (Q : Expr (n+1)) (v : Env n) :
    (all B Q).bit v=(List.range (B.number v)).all (fun i=>Q.bit (cons (List.replicate i true) v)) := bit_singleton _ _ _ (all_value B Q v)
@[simp] theorem collect_value (B : Expr n) (Q : Expr (n+1)) (v : Env n) :
    (collect B Q).value v=(List.range (B.number v)).map (fun i=>Q.bit (cons (List.replicate i true) v)) := Recipe.collect_value ..
@[simp] theorem count_number (B : Expr n) (Q : Expr (n+1)) (v : Env n) :
    (count B Q).number v=(List.range (B.number v)).countP (fun i=>Q.bit (cons (List.replicate i true) v)) := by
  simp only [Expr.number,Expr.value,count,countTrue_value,List.length_replicate]
  rfl

end PolyRecipe
end VariableWL.Computation.Stack

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

@[simp] theorem cons_one (w z : Word) (v : Env n) : cons z (cons w v) (1 : Fin (n+2))=w := rfl

structure Data (n : ℕ) where
  leftOrder : Expr n
  rightOrder : Expr n
  dimension : Expr n
  leftMatrix : Expr n
  rightMatrix : Expr n
  capacity : Expr n

def Data.reindex (D : Data n) (φ : Fin n → Fin m) : Data m :=
  ⟨D.leftOrder.reindex φ,D.rightOrder.reindex φ,D.dimension.reindex φ,
    D.leftMatrix.reindex φ,D.rightMatrix.reindex φ,D.capacity.reindex φ⟩
def Data.up (D : Data n) : Data (n+1) := D.reindex Fin.succ
def Data.up₂ (D : Data n) : Data (n+2) := D.reindex (fun i=>i.succ.succ)
def Data.eval (D : Data n) (v : Env n) : NumericRefinement.Data :=
  ⟨D.leftOrder.number v,D.rightOrder.number v,D.dimension.number v,D.leftMatrix.value v,D.rightMatrix.value v⟩
@[simp] theorem eval_reindex (D : Data n) (φ : Fin n → Fin m) (v : Env m) :
    (D.reindex φ).eval v=D.eval (v ∘ φ) := rfl
@[simp] theorem eval_up (D : Data n) (v : Env n) (w : Word) : D.up.eval (cons w v)=D.eval v := rfl
@[simp] theorem eval_up₂ (D : Data n) (v : Env n) (w z : Word) : D.up₂.eval (cons z (cons w v))=D.eval v := rfl

@[simp] theorem choose_number (B P Q : Expr n) (v : Env n) :
    (PolyRecipe.choose B P Q).number v=if B.bit v then P.number v else Q.number v := by
  unfold Expr.number
  rw [PolyRecipe.choose_value]
  split <;> rfl
@[simp] theorem up_bit (P : Expr n) (v : Env n) (w : Word) : P.up.bit (cons w v)=P.bit v := rfl
@[simp] theorem up₂_bit (P : Expr n) (v : Env n) (w z : Word) : P.up₂.bit (cons z (cons w v))=P.bit v := rfl

def Data.leftCount (D : Data n) : Expr n := capPow D.leftOrder D.dimension D.capacity
def Data.rightCount (D : Data n) : Expr n := capPow D.rightOrder D.dimension D.capacity
def Data.count (D : Data n) : Expr n := add D.leftCount D.rightCount
def Data.isLeft (D : Data n) (a : Expr n) : Expr n := lt a D.leftCount
def Data.order (D : Data n) (a : Expr n) : Expr n := PolyRecipe.choose (D.isLeft a) D.leftOrder D.rightOrder
def Data.offset (D : Data n) (a : Expr n) : Expr n := PolyRecipe.choose (D.isLeft a) (numeral 0) D.leftCount
def Data.power (D : Data n) (a i : Expr n) : Expr n := capPow (D.order a) i D.capacity
def Data.coordinate (D : Data n) (a i : Expr n) : Expr n := mod (div (sub a (D.offset a)) (D.power a i)) (D.order a)
def Data.replacement (D : Data n) (a z i : Expr n) : Expr n :=
  add (D.offset a) (add (sub (sub a (D.offset a)) (mul (D.coordinate a i) (D.power a i))) (mul z (D.power a i)))
def Data.edge (D : Data n) (a i j : Expr n) : Expr n :=
  PolyRecipe.lookup (PolyRecipe.choose (D.isLeft a) D.leftMatrix D.rightMatrix)
    (add (mul (D.coordinate a i) (D.order a)) (D.coordinate a j))

def Data.initial (D : Data n) (a b : Expr n) : Expr n :=
  PolyRecipe.all D.dimension (PolyRecipe.all D.up.dimension
    (PolyRecipe.conj (bitEq (PolyRecipe.eq (D.up₂.coordinate a.up₂ (PolyRecipe.input 1)) (D.up₂.coordinate a.up₂ (PolyRecipe.input 0)))
      (PolyRecipe.eq (D.up₂.coordinate b.up₂ (PolyRecipe.input 1)) (D.up₂.coordinate b.up₂ (PolyRecipe.input 0))))
      (bitEq (D.up₂.edge a.up₂ (PolyRecipe.input 1) (PolyRecipe.input 0))
        (D.up₂.edge b.up₂ (PolyRecipe.input 1) (PolyRecipe.input 0)))))

end VariableWL.NumericProgram

namespace VariableWL.NumericProgram
open Computation.Stack Computation.Stack.Recipe Computation.Stack.PolyRecipe
variable {n : ℕ}

def sameRanges (A B : Expr n) (AA AB BA BB : Expr (n+2)) : Expr n :=
  PolyRecipe.conj
    (PolyRecipe.all A (PolyRecipe.eq (PolyRecipe.count A.up AA) (PolyRecipe.count B.up AB)))
    (PolyRecipe.all B (PolyRecipe.eq (PolyRecipe.count A.up BA) (PolyRecipe.count B.up BB)))

def Data.get (D : Data n) (R a b : Expr n) : Expr n := PolyRecipe.lookup R (add (mul a D.count) b)
def Data.profile (D : Data n) (R a z b w : Expr n) : Expr n :=
  PolyRecipe.all D.dimension (D.up.get R.up (D.up.replacement a.up z.up (PolyRecipe.input 0))
    (D.up.replacement b.up w.up (PolyRecipe.input 0)))
def Data.comparison (D : Data n) (R a b : Expr n) : Expr n :=
  sameRanges (D.order a) (D.order b)
    (D.up₂.profile R.up₂ a.up₂ (PolyRecipe.input 1) a.up₂ (PolyRecipe.input 0))
    (D.up₂.profile R.up₂ a.up₂ (PolyRecipe.input 1) b.up₂ (PolyRecipe.input 0))
    (D.up₂.profile R.up₂ b.up₂ (PolyRecipe.input 1) a.up₂ (PolyRecipe.input 0))
    (D.up₂.profile R.up₂ b.up₂ (PolyRecipe.input 1) b.up₂ (PolyRecipe.input 0))
def Data.update (D : Data n) (R a b : Expr n) : Expr n := PolyRecipe.conj (D.get R a b) (D.comparison R a b)

def Data.initialArray (D : Data n) : Expr n :=
  PolyRecipe.collect (mul D.count D.count)
    (D.up.initial (div (PolyRecipe.input 0) D.up.count) (mod (PolyRecipe.input 0) D.up.count))
def Data.nextArray (D : Data n) (R : Expr n) : Expr n :=
  PolyRecipe.collect (mul D.count D.count)
    (D.up.update R.up (div (PolyRecipe.input 0) D.up.count) (mod (PolyRecipe.input 0) D.up.count))

end VariableWL.NumericProgram

namespace VariableWL.NumericProgram
open Computation.Stack Computation.Stack.Recipe Computation.Stack.PolyRecipe
variable {n : ℕ}

theorem count_up₂ (D : Data n) (v : Env n) (w z : Word) :
    D.up₂.count.number (cons z (cons w v))=D.count.number v := by
  simp only [Data.count,add_number,Data.leftCount,Data.rightCount,capPow_number]
  rfl

theorem initialArray_length (D : Data n) (v : Env n) :
    (D.initialArray.value v).length=D.count.number v^2 := by
  rw [Data.initialArray,PolyRecipe.collect_value,List.length_map,List.length_range,mul_number,pow_two]

theorem nextArray_length (D : Data n) (R : Expr n) (v : Env n) :
    ((D.nextArray R).value v).length=D.count.number v^2 := by
  rw [Data.nextArray,PolyRecipe.collect_value,List.length_map,List.length_range,mul_number,pow_two]

def Data.arrayBody (D : Data n) : Expr (n+2) := D.up₂.nextArray (PolyRecipe.input 0)
def Data.arrayProgram (D : Data n) : Certified n :=
  Recipe.iterate (mul D.count D.count).program D.initialArray.program D.arrayBody.program

theorem arrayPrefix_length (D : Data n) (v : Env n) (j : ℕ) :
    (Recipe.foldValue D.arrayBody.program v (D.initialArray.value v) j).length=D.count.number v^2 := by
  cases j with
  | zero => exact initialArray_length D v
  | succ j =>
    change ((D.up₂.nextArray (PolyRecipe.input 0)).value _).length=_
    rw [nextArray_length,count_up₂]

theorem arrayProgram_poly (D : Data n) : Poly D.arrayProgram := by
  obtain ⟨f,hf,h⟩ := D.count.polynomial
  apply Recipe.poly_iterate (mul D.count D.count).polynomial D.initialArray.polynomial D.arrayBody.polynomial
    (fun C=>(f C)^2) (hf.pow 2)
  intro C v hv j hj
  change (Recipe.foldValue D.arrayBody.program v (D.initialArray.value v) j).length≤(f C)^2
  rw [arrayPrefix_length]
  have hb := h C v hv
  exact Nat.pow_le_pow_left (show D.count.number v≤f C by exact (Nat.le_add_left _ _).trans hb) 2

def Data.array (D : Data n) : Expr n := ⟨D.arrayProgram,arrayProgram_poly D⟩

def Data.histogram (D : Data n) (R : Expr n) : Expr n :=
  sameRanges D.leftCount D.rightCount
    (D.up₂.get R.up₂ (PolyRecipe.input 1) (PolyRecipe.input 0))
    (D.up₂.get R.up₂ (PolyRecipe.input 1) (add D.up₂.leftCount (PolyRecipe.input 0)))
    (D.up₂.get R.up₂ (add D.up₂.leftCount (PolyRecipe.input 1)) (PolyRecipe.input 0))
    (D.up₂.get R.up₂ (add D.up₂.leftCount (PolyRecipe.input 1)) (add D.up₂.leftCount (PolyRecipe.input 0)))

def Data.accepts (D : Data n) : Expr n := D.histogram D.array

end VariableWL.NumericProgram

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

def Expr.bind (P : Expr n) (Q : Expr (n+1)) : Expr n :=
  ⟨P.program.bind Q.program,poly_bind P.polynomial Q.polynomial⟩
@[simp] theorem bind_value (P : Expr n) (Q : Expr (n+1)) (v : Env n) :
    (P.bind Q).value v=Q.value (cons (P.value v) v) := rfl

def length (P : Expr n) : Expr n := ⟨Recipe.len P.program,poly_len P.polynomial⟩
def reverse (P : Expr n) : Expr n := ⟨Recipe.rev P.program,poly_rev P.polynomial⟩
def drop (P Q : Expr n) : Expr n := ⟨tailAt P.program Q.program,poly_tailAt P.polynomial Q.polynomial⟩
def minimum (P Q : Expr n) : Expr n := ⟨Recipe.minimum P.program Q.program,poly_minimum P.polynomial Q.polynomial⟩
def append (P Q : Expr n) : Expr n := ⟨cat P.program Q.program,poly_cat P.polynomial Q.polynomial⟩
@[simp] theorem length_number (P : Expr n) (v : Env n) : (length P).number v=(P.value v).length := by
  simp only [Expr.number,Expr.value,length,len_value,List.length_replicate]
@[simp] theorem reverse_value (P : Expr n) (v : Env n) : (reverse P).value v=(P.value v).reverse := Recipe.rev_value ..
@[simp] theorem drop_value (P Q : Expr n) (v : Env n) : (drop P Q).value v=(P.value v).drop (Q.number v) := tailAt_value ..
@[simp] theorem minimum_value (P Q : Expr n) (v : Env n) :
    (minimum P Q).value v=List.replicate (min (P.number v) (Q.number v)) true := Recipe.minimum_value ..
@[simp] theorem minimum_number (P Q : Expr n) (v : Env n) : (minimum P Q).number v=min (P.number v) (Q.number v) := by
  unfold Expr.number
  rw [minimum_value,List.length_replicate]
  rfl
@[simp] theorem append_value (P Q : Expr n) (v : Env n) : (append P Q).value v=P.value v++Q.value v := cat_value ..

def foldWordIndices (n : ℕ) : Fin (n+2) → Fin (n+3) :=
  Fin.cons 1 (Fin.cons 0 (fun i=>i.succ.succ.succ))

theorem foldWord_env (v : Env n) (acc bit index : Word) :
    cons bit (cons acc (cons index v)) ∘ foldWordIndices n=cons acc (cons bit v) := by
  funext i
  refine Fin.cases ?_ (fun i=>Fin.cases ?_ (fun i=>?_) i) i <;> rfl

def foldWordBody (W : Expr n) (Q : Expr (n+2)) : Expr (n+2) :=
  (lookup W.up₂ (input 1)).bind (Q.reindex (foldWordIndices n))

theorem foldWordBody_value (W : Expr n) (Q : Expr (n+2)) (v : Env n) (acc : Word) (i : ℕ) :
    (foldWordBody W Q).value (cons acc (cons (List.replicate i true) v))=
      Q.value (cons acc (cons [(W.value v).getD i false] v)) := by
  rw [foldWordBody,bind_value,reindex_value,lookup_value,up₂_value,input_number]
  change Q.value (cons [(W.value v).getD (List.replicate i true).length false]
    (cons acc (cons (List.replicate i true) v)) ∘ foldWordIndices n)=_
  rw [List.length_replicate,foldWord_env]

def foldWordStep (Q : Expr (n+2)) (v : Env n) (a : Word) (b : Bool) : Word := Q.value (cons a (cons [b] v))

theorem foldWord_prefix (W Z : Expr n) (Q : Expr (n+2)) (v : Env n) (j : ℕ) (hj : j≤(W.value v).length) :
    foldValue (foldWordBody W Q).program v (Z.value v) j=
      ((W.value v).take j).foldl (foldWordStep Q v) (Z.value v) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hj' : j<(W.value v).length := by omega
    change (foldWordBody W Q).value (cons (foldValue (foldWordBody W Q).program v (Z.value v) j)
      (cons (List.replicate j true) v))=_
    rw [foldWordBody_value,ih (by omega),List.take_succ_eq_append_getElem hj',List.foldl_append,List.foldl_cons,List.foldl_nil]
    unfold foldWordStep
    rw [List.getD_eq_getElem _ _ hj']

def foldWordProgram (W Z : Expr n) (Q : Expr (n+2)) : Certified n :=
  Recipe.iterate (length W).program Z.program (foldWordBody W Q).program

theorem foldWordProgram_poly (W Z : Expr n) (Q : Expr (n+2)) (F : ℕ → ℕ) (hF : Growth F)
    (hacc : ∀C v,EnvBound C v → ∀j≤(W.value v).length,
      (((W.value v).take j).foldl (foldWordStep Q v) (Z.value v)).length≤F C) :
    Poly (foldWordProgram W Z Q) := by
  apply poly_iterate (length W).polynomial Z.polynomial (foldWordBody W Q).polynomial F hF
  intro C v hv j hj
  change j≤(length W).number v at hj
  rw [length_number] at hj
  change (foldValue (foldWordBody W Q).program v (Z.value v) j).length≤F C
  rw [foldWord_prefix _ _ _ _ _ hj]
  exact hacc C v hv j hj

end VariableWL.Computation.Stack.PolyRecipe

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_MatrixOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

@[simp] theorem input_one_bit (a : Word) (b : Bool) (v : Env n) :
    (input (1 : Fin (n+2))).bit (cons a (cons [b] v))=b := by cases b <;> rfl

def binaryStep (C : Expr n) : Expr (n+2) :=
  minimum (add (mul (numeral 2) (input 0)) (choose (input 1) (numeral 1) (numeral 0))) C.up₂

theorem binaryStep_value (C : Expr n) (v : Env n) (a : Word) (b : Bool) :
    (binaryStep C).value (cons a (cons [b] v))=List.replicate (min (2*a.length+b.toNat) (C.number v)) true := by
  rw [binaryStep,minimum_value,add_number,mul_number,numeral_number,input_number,cons_zero,
    NumericProgram.choose_number,input_one_bit,numeral_number,numeral_number,up₂_number]
  cases b <;> rfl

theorem min_double (q C b : ℕ) : min (2*min q C+b) C=min (2*q+b) C := by
  by_cases h : q≤C
  · rw [min_eq_left h]
  · have hq : C≤q := by omega
    rw [min_eq_right hq,min_eq_right (by omega),min_eq_right (by omega)]

theorem binary_fold (C : Expr n) (v : Env n) (w : Word) (q : ℕ) :
    w.foldl (foldWordStep (binaryStep C) v) (List.replicate (min q (C.number v)) true)=
      List.replicate (min (BinaryMachine.value w q) (C.number v)) true := by
  induction w generalizing q with
  | nil => rfl
  | cons b w ih =>
    rw [List.foldl_cons]
    unfold foldWordStep
    rw [binaryStep_value,List.length_replicate,min_double]
    exact ih (2*q+b.toNat)

theorem binary_poly (W C : Expr n) : Poly (foldWordProgram (reverse W) (numeral 0) (binaryStep C)) := by
  obtain ⟨f,hf,h⟩ := C.polynomial
  apply foldWordProgram_poly _ _ _ f hf
  intro N v hv j hj
  have h0 : (numeral (0 : ℕ) : Expr n).value v=List.replicate (min 0 (C.number v)) true := by simp [numeral]
  rw [h0,binary_fold,List.length_replicate]
  have hc := h N v hv
  exact (min_le_right _ _).trans (by exact (Nat.le_add_left _ _).trans hc)

def binary (W C : Expr n) : Expr n := ⟨foldWordProgram (reverse W) (numeral 0) (binaryStep C),binary_poly W C⟩

def prefixStep : Expr (n+2) := choose (input 1) (add (input 0) (numeral 1)) (numeral 0)

def prefixValue : Word → ℕ → ℕ
  | [],q => q
  | false::w,_q => prefixValue w 0
  | true::w,q => prefixValue w (q+1)

def headCount : Word → ℕ
  | [] => 0
  | false::_ => 0
  | true::w => headCount w+1

theorem prefixValue_bound (w : Word) (q : ℕ) : prefixValue w q≤w.length+q := by
  induction w generalizing q with
  | nil => simp [prefixValue]
  | cons b w ih => cases b <;> simp only [prefixValue,List.length_cons] <;> have h := ih (q+1) <;> have h' := ih 0 <;> omega

theorem prefixStep_value (v : Env n) (q : ℕ) (b : Bool) :
    (prefixStep : Expr (n+2)).value (cons (List.replicate q true) (cons [b] v))=
      List.replicate (if b then q+1 else 0) true := by
  rw [prefixStep,choose_value,input_one_bit]
  cases b with
  | false => rfl
  | true =>
    change (Recipe.plus (Recipe.input 0) (Recipe.literal [true])).value (cons (List.replicate q true) (cons [true] v))=_
    rw [Recipe.plus_value]
    simp only [Recipe.input_value,cons_zero,Recipe.literal_value,List.length_replicate,List.length_cons,List.length_nil,Nat.zero_add,ite_true]

theorem prefix_fold (v : Env n) (w : Word) (q : ℕ) :
    w.foldl (foldWordStep (prefixStep : Expr (n+2)) v) (List.replicate q true)=List.replicate (prefixValue w q) true := by
  induction w generalizing q with
  | nil => rfl
  | cons b w ih =>
    rw [List.foldl_cons]
    unfold foldWordStep
    rw [prefixStep_value]
    cases b <;> exact ih _

theorem prefix_poly (W : Expr n) : Poly (foldWordProgram (reverse W) (numeral 0) prefixStep) := by
  obtain ⟨f,hf,h⟩ := W.polynomial
  apply foldWordProgram_poly _ _ _ f hf
  intro N v hv j hj
  change ((((reverse W).value v).take j).foldl (foldWordStep prefixStep v) (List.replicate 0 true)).length≤f N
  rw [prefix_fold,List.length_replicate]
  have hh := prefixValue_bound (((reverse W).value v).take j) 0
  have hw := h N v hv
  rw [Nat.add_zero,List.length_take,reverse_value,List.length_reverse] at hh
  exact hh.trans ((min_le_right _ _).trans ((Nat.le_add_left _ _).trans hw))

def prefixLength (W : Expr n) : Expr n := ⟨foldWordProgram (reverse W) (numeral 0) prefixStep,prefix_poly W⟩

end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

def take (W C : Expr n) : Expr n := reverse (drop (reverse W) (sub (length W) C))
@[simp] theorem take_value (W C : Expr n) (v : Env n) : (take W C).value v=(W.value v).take (C.number v) := by
  rw [take,reverse_value,drop_value,reverse_value,sub_number,length_number,← List.reverse_take,List.reverse_reverse]

def disj (P Q : Expr n) : Expr n := choose P (literal [true]) Q
@[simp] theorem disj_bit (P Q : Expr n) (v : Env n) : (disj P Q).bit v=(P.bit v || Q.bit v) := by
  rw [disj,choose_bit]
  have ht : (literal [true] : Expr n).bit v=true := rfl
  rw [ht]
  cases P.bit v <;> rfl

def canonical (W : Expr n) : Expr n := disj (eq (length W) (numeral 0)) (reverse W)

def afterHeader (W : Expr n) : Expr n := drop W (add (prefixLength W) (numeral 1))
def integerBits (W : Expr n) : Expr n := take (afterHeader W) (prefixLength W)
def afterInteger (W : Expr n) : Expr n := drop (afterHeader W) (prefixLength W)
def integerNumber (W C : Expr n) : Expr n := binary (integerBits W) C

def integerValid (W : Expr n) : Expr n := conj (lt (prefixLength W) (length W))
  (conj (le (prefixLength W) (length (afterHeader W))) (canonical (integerBits W)))

end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

def matrixEntry (A N I J : Expr n) : Expr n := lookup A (add (mul I N) J)
def matrixValid (A N : Expr n) : Expr n :=
  conj (eq (length A) (mul N N))
    (conj (all N (all N.up (bitEq (matrixEntry A.up₂ N.up₂ (input 1) (input 0))
      (matrixEntry A.up₂ N.up₂ (input 0) (input 1)))))
      (all N (neg (matrixEntry A.up N.up (input 0) (input 0)))))

@[simp] theorem matrixEntry_bit (A N I J : Expr n) (v : Env n) :
    (matrixEntry A N I J).bit v=(A.value v).getD (I.number v*N.number v+J.number v) false := by
  rw [matrixEntry,lookup_bit,add_number,mul_number]

def graphMatrix (W C : Expr n) : Expr n := take (afterInteger W) (mul (integerNumber W C) (integerNumber W C))
def afterGraph (W C : Expr n) : Expr n := drop (afterInteger W) (mul (integerNumber W C) (integerNumber W C))
def graphValid (W C : Expr n) : Expr n := conj (integerValid W) (matrixValid (graphMatrix W C) (integerNumber W C))

@[simp] theorem graphMatrix_value (W C : Expr n) (v : Env n) :
    (graphMatrix W C).value v=((afterInteger W).value v).take ((integerNumber W C).number v*(integerNumber W C).number v) := by
  rw [graphMatrix,take_value,mul_number]
@[simp] theorem afterGraph_value (W C : Expr n) (v : Env n) :
    (afterGraph W C).value v=((afterInteger W).value v).drop ((integerNumber W C).number v*(integerNumber W C).number v) := by
  rw [afterGraph,drop_value,mul_number]

end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

def Enough (W C : Expr n) (v : Env n) : Prop := 2^(W.value v).length≤C.number v

def secondWord (W C : Expr n) : Expr n := afterGraph W C
def dimensionWord (W C : Expr n) : Expr n := afterGraph (secondWord W C) C

def pairValid (W C : Expr n) : Expr n :=
  conj (graphValid W C) (conj (graphValid (secondWord W C) C)
    (conj (integerValid (dimensionWord W C)) (eq (length (afterInteger (dimensionWord W C))) (numeral 0))))

end VariableWL.Computation.Stack.PolyRecipe

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_ExponentialRecipe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

def maximum (P Q : Expr n) : Expr n := choose (le P Q) Q P
@[simp] theorem maximum_number (P Q : Expr n) (v : Env n) : (maximum P Q).number v=max (P.number v) (Q.number v) := by
  rw [maximum,NumericProgram.choose_number,le_bit]
  by_cases h : P.number v≤Q.number v
  · simp only [decide_eq_true h,ite_true,max_eq_right h]
  · simp only [decide_eq_false h,Bool.false_eq_true,ite_false,max_eq_left (Nat.le_of_not_ge h)]

def rawDimension (W C : Expr n) : Expr n := integerNumber (dimensionWord W C) C
def parsedData (W C : Expr n) : NumericProgram.Data n := {
  leftOrder := integerNumber W C
  rightOrder := integerNumber (secondWord W C) C
  dimension := minimum (rawDimension W C) (maximum (numeral 2) (integerNumber W C))
  leftMatrix := graphMatrix W C
  rightMatrix := graphMatrix (secondWord W C) C
  capacity := C }

def StrongEnough (W C : Expr n) (v : Env n) : Prop := 2^(((W.value v).length+2)^2+1)≤C.number v

def generalProgram (W C : Expr n) : Expr n :=
  conj (pairValid W C) (conj (le (numeral 2) (rawDimension W C)) (parsedData W C).accepts)

end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.Computation.Stack.ExponentialRecipe
open Recipe PolyRecipe

def exponent : Expr 1 :=
  add (mul (add (length (PolyRecipe.input 0)) (numeral 2)) (add (length (PolyRecipe.input 0)) (numeral 2))) (numeral 1)
def size (v : Env 1) : ℕ := 2^(((v 0).length+2)^2+1)
def capacity : Certified 1 := Recipe.power (Recipe.literal [true,true]) exponent.program

def full (Q : Expr 2) : Certified 1 := capacity.bind Q.program

def environment (w : Word) : Env 2 := cons (List.replicate (2^((w.length+2)^2+1)) true) (fun _=>w.reverse)

end VariableWL.Computation.Stack.ExponentialRecipe

namespace VariableWL.Computation.Stack.ExponentialRecipe
open Recipe PolyRecipe

def general : Expr 2 := generalProgram (PolyRecipe.reverse (PolyRecipe.input 1)) (PolyRecipe.input 0)

end VariableWL.Computation.Stack.ExponentialRecipe

namespace VariableWL.NumericPromise
attribute [local instance] Classical.propDecidable

def get (n : ℕ) (R : Word) (a b : ℕ) : Bool := R.getD (a*n+b) false
def pack (n : ℕ) (f : ℕ → ℕ → Bool) : Word :=
  (List.range (n*n)).map fun p=>f (p/n) (p%n)
def update (n : ℕ) (A R : Word) (a b : ℕ) : Bool :=
  get n R a b || (List.range n).any fun z=>get n A a z && get n R z b
def array (n : ℕ) (A : Word) : ℕ → Word
  | 0 => pack n (fun a b=>decide (a=b))
  | j+1 => pack n (update n A (array n A j))

end VariableWL.NumericPromise

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Descriptor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

def any (N : Expr n) (B : Expr (n+1)) : Expr n := neg (all N (neg B))
@[simp] theorem any_bit (N : Expr n) (B : Expr (n+1)) (v : Env n) :
    (any N B).bit v=(List.range (N.number v)).any fun j=>B.bit (cons (List.replicate j true) v) := by
  simp only [any,neg_bit,all_bit,List.any_eq_not_all_not]

def reachInitial (N : Expr n) : Expr n :=
  collect (mul N N) (eq (div (input 0) N.up) (mod (input 0) N.up))
def reachUpdate (N A R I J : Expr n) : Expr n :=
  disj (matrixEntry R N I J) (any N (conj (matrixEntry A.up N.up I.up (input 0))
    (matrixEntry R.up N.up (input 0) J.up)))
def reachNext (N A R : Expr n) : Expr n :=
  collect (mul N N) (reachUpdate N.up A.up R.up (div (input 0) N.up) (mod (input 0) N.up))

theorem reachInitial_value (N : Expr n) (v : Env n) :
    (reachInitial N).value v=NumericPromise.array (N.number v) [] 0 := by
  simp only [reachInitial,collect_value,mul_number,eq_bit,div_number,mod_number,input_number,
    cons_zero,List.length_replicate,up_number]
  rfl

theorem reachUpdate_bit (N A R I J : Expr n) (v : Env n) :
    (reachUpdate N A R I J).bit v=NumericPromise.update (N.number v) (A.value v) (R.value v) (I.number v) (J.number v) := by
  simp only [reachUpdate,disj_bit,matrixEntry_bit,any_bit,conj_bit,up_value,up_number,input_number,cons_zero,List.length_replicate]
  rfl

theorem reachNext_value (N A R : Expr n) (v : Env n) :
    (reachNext N A R).value v=NumericPromise.pack (N.number v)
      (NumericPromise.update (N.number v) (A.value v) (R.value v)) := by
  simp only [reachNext,collect_value,mul_number,reachUpdate_bit,up_number,up_value,div_number,mod_number,
    input_number,cons_zero,List.length_replicate]
  rfl

theorem reachInitial_length (N : Expr n) (v : Env n) : ((reachInitial N).value v).length=N.number v^2 := by
  rw [reachInitial_value]
  simp only [NumericPromise.array,NumericPromise.pack,List.length_map,List.length_range,pow_two]

theorem reachNext_length (N A R : Expr n) (v : Env n) : ((reachNext N A R).value v).length=N.number v^2 := by
  rw [reachNext_value]
  simp only [NumericPromise.pack,List.length_map,List.length_range,pow_two]

def reachBody (N A : Expr n) : Expr (n+2) := reachNext N.up₂ A.up₂ (input 0)
def reachProgram (N A : Expr n) : Certified n :=
  Recipe.iterate N.program (reachInitial N).program (reachBody N A).program

theorem reachPrefix_length (N A : Expr n) (v : Env n) (j : ℕ) :
    (Recipe.foldValue (reachBody N A).program v ((reachInitial N).value v) j).length=N.number v^2 := by
  cases j with
  | zero => exact reachInitial_length N v
  | succ j =>
    change ((reachNext N.up₂ A.up₂ (input 0)).value _).length=_
    rw [reachNext_length,up₂_number]

theorem reachProgram_poly (N A : Expr n) : Poly (reachProgram N A) := by
  obtain ⟨f,hf,h⟩ := N.polynomial
  apply Recipe.poly_iterate N.polynomial (reachInitial N).polynomial (reachBody N A).polynomial
    (fun C=>(f C)^2) (hf.pow 2)
  intro C v hv j hj
  change (Recipe.foldValue (reachBody N A).program v ((reachInitial N).value v) j).length≤(f C)^2
  rw [reachPrefix_length]
  have hb := h C v hv
  exact Nat.pow_le_pow_left (show N.number v≤f C by exact (Nat.le_add_left _ _).trans hb) 2

def reachArray (N A : Expr n) : Expr n := ⟨reachProgram N A,reachProgram_poly N A⟩

def connectedProgram (N A : Expr n) : Expr n :=
  conj (lt (numeral 0) N) (all N (all N.up (matrixEntry (reachArray N A).up₂ N.up₂ (input 1) (input 0))))
def subcubicProgram (N A : Expr n) : Expr n :=
  all N (le (count N.up (matrixEntry A.up₂ N.up₂ (input 1) (input 0))) (numeral 3))

end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

def promiseProgram (N M A B : Expr n) : Expr n :=
  conj (lt (numeral 0) N) (conj (eq N M) (conj (connectedProgram N A)
    (conj (connectedProgram M B) (conj (subcubicProgram N A) (subcubicProgram M B)))))

def subProgram (W C : Expr n) : Expr n :=
  conj (generalProgram W C) (promiseProgram (integerNumber W C) (integerNumber (secondWord W C) C)
    (graphMatrix W C) (graphMatrix (secondWord W C) C))

end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.Computation.Stack.ExponentialRecipe
open Recipe PolyRecipe

def subcubic : Expr 2 := subProgram (PolyRecipe.reverse (PolyRecipe.input 1)) (PolyRecipe.input 0)

end VariableWL.Computation.Stack.ExponentialRecipe

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

def binaryLength (N : Expr n) : Expr n :=
  count N (le (capPow (numeral 2) (input 0) (add N.up (numeral 1))) N.up)

def binaryDigit (N I : Expr n) : Expr n :=
  eq (mod (div N (capPow (numeral 2) I (add N (numeral 1)))) (numeral 2)) (numeral 1)

def binaryEncode (N : Expr n) : Expr n := collect (binaryLength N) (binaryDigit N.up (input 0))

def integerEncode (N : Expr n) : Expr n :=
  append (length (binaryEncode N)) (append (literal [false]) (binaryEncode N))

def graphEncode (N A : Expr n) : Expr n := append (integerEncode N) A

end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.Descriptor

def rank (P : ℕ → Bool) (a : ℕ) : ℕ := (List.range a).countP P

theorem rank_succ (P : ℕ → Bool) (a : ℕ) :
    rank P (a+1)=rank P a+(if P a then 1 else 0) := by
  simp only [rank,List.range_succ,List.countP_append,List.countP_cons,List.countP_nil,Nat.zero_add]

theorem rank_mono (P : ℕ → Bool) : Monotone (rank P) := by
  intro a b h
  exact List.Sublist.countP_le (List.range_sublist.mpr h)

theorem rank_lt (P : ℕ → Bool) {a b : ℕ} (h : a<b) (ha : P a=true) : rank P a<rank P b := by
  have hm := rank_mono P (Nat.succ_le_of_lt h)
  simp only [rank_succ,ha,ite_true] at hm
  omega

theorem rank_exists (P : ℕ → Bool) (N i : ℕ) (hi : i<rank P N) :
    ∃a,a<N ∧ P a=true ∧ rank P a=i := by
  induction N with
  | zero => simp [rank] at hi
  | succ N ih =>
    by_cases h : i<rank P N
    · obtain ⟨a,ha,hp,hr⟩ := ih h
      exact ⟨a,by omega,hp,hr⟩
    · rw [rank_succ] at hi
      cases hp : P N <;> simp only [hp,Bool.false_eq_true,ite_false,ite_true,Nat.add_zero] at hi
      · omega
      · exact ⟨N,by omega,hp,by omega⟩

def pick (N : ℕ) (P : ℕ → Bool) (i : ℕ) : ℕ :=
  (List.range N).countP fun j=>decide (rank P (j+1)≤ i)

theorem pick_rank (N : ℕ) (P : ℕ → Bool) (a : ℕ) (ha : a<N) (hp : P a=true) :
    pick N P (rank P a)=a := by
  have he (j : ℕ) : decide (rank P (j+1)≤rank P a)=decide (j<a) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro h
      by_contra hj
      have hm := rank_lt P (show a<j+1 by omega) hp
      omega
    · exact fun h=>rank_mono P (Nat.succ_le_of_lt h)
  simp only [pick,he]
  rw [Computation.Stack.Recipe.count_range_lt,Nat.min_eq_right (Nat.le_of_lt ha)]

theorem pick_spec (N : ℕ) (P : ℕ → Bool) (i : ℕ) (hi : i<rank P N) :
    pick N P i<N ∧ P (pick N P i)=true ∧ rank P (pick N P i)=i := by
  obtain ⟨a,ha,hp,hr⟩ := rank_exists P N i hi
  rw [←hr,pick_rank N P a ha hp]
  exact ⟨ha,hp,rfl⟩

abbrev Valid (N : ℕ) (P : ℕ → Bool) := {a : Fin N // P a.val=true}

def rankEquiv (N : ℕ) (P : ℕ → Bool) : Valid N P ≃ Fin (rank P N) where
  toFun a := ⟨rank P a.val.val,rank_lt P a.val.isLt a.property⟩
  invFun i := ⟨⟨pick N P i.val,(pick_spec N P i.val i.isLt).1⟩,(pick_spec N P i.val i.isLt).2.1⟩
  left_inv a := by apply Subtype.ext; apply Fin.ext; exact pick_rank N P a.val.val a.val.isLt a.property
  right_inv i := by apply Fin.ext; exact (pick_spec N P i.val i.isLt).2.2

end VariableWL.Descriptor

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

def underOne (P : Expr (n+1)) : Expr (n+2) := P.reindex (Fin.cons 0 (fun i=>i.succ.succ))

def select (N : Expr n) (P : Expr (n+1)) (I : Expr n) : Expr n :=
  count N (le (count (add (input 0) (numeral 1)) (underOne P)) I.up)

def apply₂ (F : Expr (n+2)) (A B : Expr n) : Expr n := B.bind (A.up.bind F)

end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.Descriptor
attribute [local instance] Classical.propDecidable

structure Data where
  bound : ℕ
  valid : ℕ → Bool
  edge : ℕ → ℕ → Bool

def Data.Sound (D : Data) : Prop :=
  (∀a b,a<D.bound → b<D.bound → D.valid a=true → D.valid b=true → D.edge a b=D.edge b a) ∧
  (∀a,a<D.bound → D.valid a=true → D.edge a a=false)

noncomputable def Data.graph (D : Data) (h : D.Sound) : Graph where
  order := rank D.valid D.bound
  graph := {
    Adj := fun i j=>D.edge (pick D.bound D.valid i.val) (pick D.bound D.valid j.val)=true
    symm := ⟨by
      intro i j hij
      have hi := pick_spec D.bound D.valid i.val i.isLt
      have hj := pick_spec D.bound D.valid j.val j.isLt
      rw [h.1 _ _ hj.1 hi.1 hj.2.1 hi.2.1]
      exact hij⟩
    loopless := ⟨by
      intro i he
      have hi := pick_spec D.bound D.valid i.val i.isLt
      rw [h.2 _ hi.1 hi.2.1] at he
      contradiction⟩ }

end VariableWL.Descriptor

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_PortListing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

def underTwo (P : Expr (n+2)) : Expr (n+3) :=
  P.reindex (Fin.cons 0 (Fin.cons 1 (fun i=>i.succ.succ.succ)))

structure GraphListing (n : ℕ) where
  bound : Expr n
  valid : Expr (n+1)
  edge : Expr (n+2)

def GraphListing.eval (D : GraphListing n) (v : Env n) : Descriptor.Data where
  bound := D.bound.number v
  valid := fun j=>D.valid.bit (cons (List.replicate j true) v)
  edge := fun i j=>D.edge.bit (cons (List.replicate i true) (cons (List.replicate j true) v))

def GraphListing.order (D : GraphListing n) : Expr n := count D.bound D.valid

def GraphListing.matrix (D : GraphListing n) : Expr n :=
  collect (mul D.order D.order) (apply₂ (underTwo D.edge)
    (select D.bound.up (underOne D.valid) (div (input 0) D.order.up))
    (select D.bound.up (underOne D.valid) (mod (input 0) D.order.up)))

def GraphListing.code (D : GraphListing n) : Expr n := graphEncode D.order D.matrix

end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.Descriptor
open SubcubicRealization
attribute [local instance] Classical.propDecidable

structure Presentation (A : Type uVariable1) where
  bound : ℕ
  valid : ℕ → Bool
  equiv : Valid bound valid ≃ A

namespace Presentation
variable {A : Type uVariable2} (D : Presentation A)
def encode (a : A) : ℕ := (D.equiv.symm a).val.val

theorem encode_lt (a : A) : D.encode a<D.bound := (D.equiv.symm a).val.isLt
theorem encode_valid (a : A) : D.valid (D.encode a)=true := (D.equiv.symm a).property

theorem encode_injective : Function.Injective D.encode := by
  intro a b h
  apply D.equiv.symm.injective
  apply Subtype.ext
  exact Fin.ext h

@[instance_reducible] noncomputable def numbering [Fintype A] : FiniteNumbering A :=
  ⟨D.equiv.symm.trans ((rankEquiv D.bound D.valid).trans (finCongr (by
    simpa only [Fintype.card_fin] using (Fintype.card_congr (rankEquiv D.bound D.valid)).symm.trans
      (Fintype.card_congr D.equiv))))⟩

end Presentation

@[ext] structure PortData where
  bound : ℕ
  valid : ℕ → Bool
  color : ℕ → ℕ
  colorBound : ℕ
  incidence : ℕ → ℕ → Bool

namespace PortData
abbrev Owners (D : PortData) := Valid D.bound D.valid

def Sound (D : PortData) : Prop :=
  (∀a : D.Owners,D.color a.val.val≤D.colorBound) ∧
  (∀a b : D.Owners,∀i j : Fin 3,
    D.incidence (3*a.val.val+i.val) (3*b.val.val+j.val)=
      D.incidence (3*b.val.val+j.val) (3*a.val.val+i.val)) ∧
  (∀a b c : D.Owners,∀i j k : Fin 3,
    D.incidence (3*a.val.val+i.val) (3*b.val.val+j.val)=true →
    D.incidence (3*a.val.val+i.val) (3*c.val.val+k.val)=true → b=c ∧ j=k) ∧
  (∀a b : D.Owners,∀i j : Fin 3,
    D.incidence (3*a.val.val+i.val) (3*b.val.val+j.val)=true → a≠b)

noncomputable def ports (D : PortData) (h : D.Sound) : PortGraph D.Owners where
  edge x y := D.incidence (3*x.1.val.val+x.2.val) (3*y.1.val.val+y.2.val)=true
  symm := by intro x y he; rw [h.2.1]; exact he
  unique := by intro x y z hy hz; obtain ⟨ha,hb⟩ := h.2.2.1 _ _ _ _ _ _ hy hz; exact Prod.ext ha hb
  different := by intro x y he; exact h.2.2.2 _ _ _ _ he

abbrev Vertices (D : PortData) := Vertex (fun a : D.Owners=>D.color a.val.val)

def stride (D : PortData) : ℕ := D.colorBound+2
def owner (D : PortData) (i : ℕ) : ℕ := i/D.stride/3
def port (D : PortData) (i : ℕ) : ℕ := i/D.stride%3
def level (D : PortData) (i : ℕ) : ℕ := i%D.stride
def code (D : PortData) (x : D.Vertices) : ℕ := (3*x.owner.val.val+x.port.val)*D.stride+x.level

def expanded (D : PortData) : Data where
  bound := (3*D.bound)*D.stride
  valid i := D.valid (D.owner i) && decide (D.level i<D.color (D.owner i)+2)
  edge i j :=
    (decide (D.owner i=D.owner j) &&
      ((decide (D.level i=0) && decide (D.level j=0) && decide (D.port i≠D.port j)) ||
        (decide (D.port i=D.port j) &&
          (decide (D.level i+1=D.level j) || decide (D.level j+1=D.level i))))) ||
    (decide (D.level i=1) && decide (D.level j=1) &&
      D.incidence (3*D.owner i+D.port i) (3*D.owner j+D.port j))

theorem stride_pos (D : PortData) : 0<D.stride := by unfold stride; omega

theorem owner_lt (D : PortData) {i : ℕ} (hi : i<D.expanded.bound) : D.owner i<D.bound := by
  have h : i/D.stride<3*D.bound := (Nat.div_lt_iff_lt_mul D.stride_pos).mpr hi
  unfold owner
  apply (Nat.div_lt_iff_lt_mul (by omega : 0<3)).mpr
  simpa only [Nat.mul_comm] using h

theorem code_parts (D : PortData) (h : D.Sound) (x : D.Vertices) :
    D.owner (D.code x)=x.owner.val.val ∧ D.port (D.code x)=x.port.val ∧ D.level (D.code x)=x.level := by
  have hx : x.level<D.stride := lt_of_lt_of_le x.bound (Nat.add_le_add_right (h.1 x.owner) 2)
  have hp : x.port.val<3 := x.port.isLt
  have hd : D.code x/D.stride=3*x.owner.val.val+x.port.val := by
    rw [code,Nat.mul_comm _ D.stride,Nat.mul_add_div D.stride_pos,Nat.div_eq_of_lt hx,Nat.add_zero]
  constructor
  · change (D.code x/D.stride)/3=_
    rw [hd,Nat.mul_add_div (by omega : 0<3),Nat.div_eq_of_lt hp,Nat.add_zero]
  constructor
  · change (D.code x/D.stride)%3=_
    rw [hd,Nat.mul_add_mod,Nat.mod_eq_of_lt hp]
  · change D.code x%D.stride=_
    rw [code,Nat.mul_comm _ D.stride,Nat.mul_add_mod,Nat.mod_eq_of_lt hx]

theorem code_lt (D : PortData) (h : D.Sound) (x : D.Vertices) : D.code x<D.expanded.bound := by
  have hx : x.level<D.stride := lt_of_lt_of_le x.bound (Nat.add_le_add_right (h.1 x.owner) 2)
  have hp : 3*x.owner.val.val+x.port.val<3*D.bound := by
    have := x.owner.val.isLt
    have := x.port.isLt
    omega
  exact (Nat.add_lt_add_left hx _).trans_le (by
    change (3*x.owner.val.val+x.port.val)*D.stride+D.stride≤(3*D.bound)*D.stride
    rw [←Nat.succ_mul]
    exact Nat.mul_le_mul_right _ hp)

noncomputable def presentation (D : PortData) (h : D.Sound) : Presentation D.Vertices where
  bound := D.expanded.bound
  valid := D.expanded.valid
  equiv := {
    toFun a := ⟨⟨⟨D.owner a.val.val,D.owner_lt a.val.isLt⟩,(Bool.and_eq_true_iff.mp a.property).1⟩,
      ⟨D.port a.val.val,Nat.mod_lt _ (by omega)⟩,D.level a.val.val,
      of_decide_eq_true (Bool.and_eq_true_iff.mp a.property).2⟩
    invFun x := ⟨⟨D.code x,D.code_lt h x⟩,by
      simp only [expanded,code_parts D h x |>.1,code_parts D h x |>.2.2,x.owner.property,
        x.bound,decide_true,Bool.and_self]⟩
    left_inv a := by
      apply Subtype.ext
      apply Fin.ext
      change (3*(a.val.val/D.stride/3)+(a.val.val/D.stride%3))*D.stride+a.val.val%D.stride=a.val.val
      rw [Nat.div_add_mod,Nat.mul_comm,Nat.div_add_mod]
    right_inv x := by
      apply Vertex.ext
      · apply Subtype.ext; apply Fin.ext; exact (code_parts D h x).1
      · apply Fin.ext; exact (code_parts D h x).2.1
      · exact (code_parts D h x).2.2 }

end PortData
end VariableWL.Descriptor

namespace VariableWL.Descriptor
@[ext] theorem data_ext {D E : Data} (hb : D.bound=E.bound) (hv : D.valid=E.valid)
    (he : D.edge=E.edge) : D=E := by cases D; cases E; cases hb; cases hv; cases he; rfl
end VariableWL.Descriptor

namespace VariableWL.Descriptor.PortData
open SubcubicRealization
attribute [local instance] Classical.propDecidable

 theorem edge_correct (D : PortData) (h : D.Sound) (a b : Valid D.expanded.bound D.expanded.valid) :
    D.expanded.edge a.val.val b.val.val=true ↔
      (graph (D.ports h) (fun x=>D.color x.val.val)).Adj
        ((D.presentation h).equiv a) ((D.presentation h).equiv b) := by
  change D.expanded.edge a.val.val b.val.val=true ↔
    ((⟨⟨D.owner a.val.val,D.owner_lt a.val.isLt⟩,
        (Bool.and_eq_true_iff.mp a.property).1⟩ : D.Owners)=
      ⟨⟨D.owner b.val.val,D.owner_lt b.val.isLt⟩,(Bool.and_eq_true_iff.mp b.property).1⟩ ∧
      ((D.level a.val.val=0 ∧ D.level b.val.val=0 ∧
        (⟨D.port a.val.val,Nat.mod_lt _ (by omega)⟩ : Fin 3)≠⟨D.port b.val.val,Nat.mod_lt _ (by omega)⟩) ∨
        ((⟨D.port a.val.val,Nat.mod_lt _ (by omega)⟩ : Fin 3)=⟨D.port b.val.val,Nat.mod_lt _ (by omega)⟩ ∧
          (D.level a.val.val+1=D.level b.val.val ∨ D.level b.val.val+1=D.level a.val.val)))) ∨
    (D.level a.val.val=1 ∧ D.level b.val.val=1 ∧
      D.incidence (3*D.owner a.val.val+D.port a.val.val) (3*D.owner b.val.val+D.port b.val.val)=true)
  simp only [expanded,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,
    Subtype.mk.injEq,ne_eq,Fin.ext_iff,and_assoc]

 theorem sound_expanded (D : PortData) (h : D.Sound) : D.expanded.Sound := by
  constructor
  · intro a b ha hb hva hvb
    let x : Valid D.expanded.bound D.expanded.valid := ⟨⟨a,ha⟩,hva⟩
    let y : Valid D.expanded.bound D.expanded.valid := ⟨⟨b,hb⟩,hvb⟩
    apply Bool.eq_iff_iff.mpr
    exact (D.edge_correct h x y).trans ((graph (D.ports h) (fun x=>D.color x.val.val)).adj_comm _ _ |>.trans
      (D.edge_correct h y x).symm)
  · intro a ha hva
    apply Bool.eq_false_iff.mpr
    intro he
    exact (graph (D.ports h) (fun x=>D.color x.val.val)).loopless.irrefl _
      ((D.edge_correct h ⟨⟨a,ha⟩,hva⟩ ⟨⟨a,ha⟩,hva⟩).mp he)

noncomputable def graphIso (D : PortData) (h : D.Sound) :
    (D.expanded.graph (D.sound_expanded h)).graph ≃g
      graph (D.ports h) (fun x=>D.color x.val.val) where
  toEquiv := (rankEquiv D.expanded.bound D.expanded.valid).symm.trans (D.presentation h).equiv
  map_rel_iff' := by
    intro x y
    exact (D.edge_correct h ((rankEquiv D.expanded.bound D.expanded.valid).symm x)
      ((rankEquiv D.expanded.bound D.expanded.valid).symm y)).symm

end VariableWL.Descriptor.PortData

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n m : ℕ}

def applyNat (P : Expr (n+1)) (I : Expr n) : Expr n := (length I).bind P

def applyNat₂ (P : Expr (n+2)) (I J : Expr n) : Expr n := applyNat (applyNat P I.up) J

structure PortListing (n : ℕ) where
  bound : Expr n
  valid : Expr (n+1)
  color : Expr (n+1)
  colorBound : Expr n
  incidence : Expr (n+2)

namespace PortListing

def eval (D : PortListing n) (v : Env n) : Descriptor.PortData where
  bound := D.bound.number v
  valid i := D.valid.bit (cons (List.replicate i true) v)
  color i := D.color.number (cons (List.replicate i true) v)
  colorBound := D.colorBound.number v
  incidence i j := D.incidence.bit (cons (List.replicate i true) (cons (List.replicate j true) v))

def up (D : PortListing n) : PortListing (n+1) where
  bound := D.bound.up
  valid := underOne D.valid
  color := underOne D.color
  colorBound := D.colorBound.up
  incidence := underTwo D.incidence

def stride (D : PortListing n) : Expr n := add D.colorBound (numeral 2)
def owner (D : PortListing n) (I : Expr n) : Expr n := div (div I D.stride) (numeral 3)
def port (D : PortListing n) (I : Expr n) : Expr n := mod (div I D.stride) (numeral 3)
def level (D : PortListing n) (I : Expr n) : Expr n := mod I D.stride

def expandedValid (D : PortListing n) (I : Expr n) : Expr n :=
  conj (applyNat D.valid (D.owner I))
    (lt (D.level I) (add (applyNat D.color (D.owner I)) (numeral 2)))

def expandedEdge (D : PortListing n) (I J : Expr n) : Expr n :=
  disj (conj (eq (D.owner I) (D.owner J))
    (disj (conj (conj (eq (D.level I) (numeral 0)) (eq (D.level J) (numeral 0)))
        (neg (eq (D.port I) (D.port J))))
      (conj (eq (D.port I) (D.port J))
        (disj (eq (add (D.level I) (numeral 1)) (D.level J))
          (eq (add (D.level J) (numeral 1)) (D.level I))))))
    (conj (conj (eq (D.level I) (numeral 1)) (eq (D.level J) (numeral 1)))
      (applyNat₂ D.incidence (add (mul (numeral 3) (D.owner I)) (D.port I))
        (add (mul (numeral 3) (D.owner J)) (D.port J))))

def expanded (D : PortListing n) : GraphListing n where
  bound := mul (mul (numeral 3) D.bound) D.stride
  valid := D.up.expandedValid (input 0)
  edge := D.up.up.expandedEdge (input 0) (input 1)

end PortListing
end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

def fixedNat : (N : ℕ) → (Fin N → ℕ) → Expr n → Expr n
  | 0,_,_ => numeral 0
  | N+1,f,I => choose (eq I (numeral 0)) (numeral (f 0))
      (fixedNat N (fun i=>f i.succ) (sub I (numeral 1)))

def fixedBool (N : ℕ) (f : Fin N → Bool) (I : Expr n) : Expr n :=
  eq (fixedNat N (fun i=>if f i then 1 else 0) I) (numeral 1)

end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.Computation.Stack.Recipe
@[simp] theorem cons_two {n : ℕ} (a b c : Word) (v : Env n) : cons a (cons b (cons c v)) (2 : Fin (n+3))=c := rfl
end VariableWL.Computation.Stack.Recipe

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_PrefixAlphabet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

def applyNat₃ (P : Expr (n+3)) (I J K : Expr n) : Expr n :=
  applyNat (applyNat₂ P I.up J.up) K

def tableLookup {N : ℕ} (f : Fin N → ℕ) (i : ℕ) : ℕ := if h : i<N then f ⟨i,h⟩ else 0

end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.Descriptor.Presentation
variable {A : Type uVariable1}

noncomputable def ofEncoding (N : ℕ) (P : ℕ → Bool) (f : A → ℕ)
    (hf : ∀a,f a<N) (hp : ∀a,P (f a)=true) (hi : Function.Injective f)
    (hs : ∀i,i<N → P i=true → ∃a,f a=i) : Presentation A where
  bound := N
  valid := P
  equiv := (Equiv.ofBijective (fun a=> (⟨⟨f a,hf a⟩,hp a⟩ : Valid N P)) (by
    constructor
    · intro a b he; exact hi (congrArg (fun a : Valid N P=>a.val.val) he)
    · intro i; obtain ⟨a,ha⟩ := hs i.val.val i.val.isLt i.property
      exact ⟨a,Subtype.ext (Fin.ext ha)⟩)).symm

end VariableWL.Descriptor.Presentation

namespace VariableWL.Descriptor.PortData
open SubcubicRealization
variable {A : Type uVariable3}
theorem sound_of_encoding (D : PortData) (f : A → D.Owners) (hf : Function.Bijective f) (Y : PortGraph A)
    (hc : ∀a,D.color (f a).val.val≤D.colorBound)
    (he : ∀a b i j,D.incidence (3*(f a).val.val+i.val) (3*(f b).val.val+j.val)=true ↔
      Y.edge (a,i) (b,j)) : D.Sound := by
  refine ⟨?_,?_,?_,?_⟩
  · intro x; obtain ⟨a,rfl⟩ := hf.2 x; exact hc a
  · intro x y i j
    obtain ⟨a,rfl⟩ := hf.2 x
    obtain ⟨b,rfl⟩ := hf.2 y
    apply Bool.eq_iff_iff.mpr
    exact (he a b i j).trans ⟨fun h=>(he b a j i).mpr (Y.symm h),fun h=>Y.symm ((he b a j i).mp h)⟩
  · intro x y z i j k hxy hxz
    obtain ⟨a,rfl⟩ := hf.2 x
    obtain ⟨b,rfl⟩ := hf.2 y
    obtain ⟨c,rfl⟩ := hf.2 z
    have ht := Y.unique ((he a b i j).mp hxy) ((he a c i k).mp hxz)
    exact ⟨congrArg f (congrArg Prod.fst ht),congrArg Prod.snd ht⟩
  · intro x y i j hxy hx
    obtain ⟨a,rfl⟩ := hf.2 x
    obtain ⟨b,rfl⟩ := hf.2 y
    exact Y.different ((he a b i j).mp hxy) (hf.1 hx)
end VariableWL.Descriptor.PortData

namespace VariableWL.PrefixAlphabet
open VariableWL.Affine
attribute [local instance] Classical.propDecidable

abbrev Vector := Σa : Fin 7, Vec a.val
abbrev Order := Σa : Fin 7, Equiv.Perm (Fin a.val)
noncomputable instance vectorFintype : Fintype Vector := inferInstance
noncomputable instance orderFintype : Fintype Order := Fintype.ofFinite _
noncomputable def vectorNumber : Vector ≃ Fin (Fintype.card Vector) := Fintype.equivFin _
noncomputable def orderNumber : Order ≃ Fin (Fintype.card Order) := Fintype.equivFin _
noncomputable def vectorCount : ℕ := Fintype.card Vector
noncomputable def orderCount : ℕ := Fintype.card Order

noncomputable def encode {a : ℕ} (h : a≤6) (z : Vec a) : ℕ :=
  (vectorNumber ⟨⟨a,by omega⟩,z⟩).val
noncomputable def encodeOrder {a : ℕ} (h : a≤6) (p : Equiv.Perm (Fin a)) : ℕ :=
  (orderNumber ⟨⟨a,by omega⟩,p⟩).val

theorem encode_lt {a : ℕ} (h : a≤6) (z : Vec a) : encode h z<vectorCount :=
  (vectorNumber ⟨⟨a,by omega⟩,z⟩).isLt
 theorem order_lt {a : ℕ} (h : a≤6) (p : Equiv.Perm (Fin a)) : encodeOrder h p<orderCount :=
  (orderNumber ⟨⟨a,by omega⟩,p⟩).isLt
 theorem encode_injective {a : ℕ} (h : a≤6) : Function.Injective (@encode a h) := by
  intro z w he
  have hv := vectorNumber.injective (Fin.ext he)
  exact eq_of_heq (Sigma.mk.inj_iff.mp hv).2

noncomputable def truncated (h : ℕ) (v : Vector) : Vector :=
  ⟨v.1,PrefixParts.Data.truncate h v.2⟩

noncomputable def permuted (p : Order) (v : Vector) : Vector :=
  if h : p.1=v.1 then ⟨v.1,v.2 ∘ (h ▸ p.2)⟩ else v

noncomputable def prefixCode (p h i : ℕ) : ℕ :=
  if hp : p<orderCount then if hi : i<vectorCount then
    (vectorNumber (truncated h (permuted (orderNumber.symm ⟨p,hp⟩) (vectorNumber.symm ⟨i,hi⟩)))).val
  else 0 else 0

noncomputable def bit (i h : ℕ) : ℕ :=
  if hi : i<vectorCount then
    let v := vectorNumber.symm ⟨i,hi⟩
    if hh : h<v.1.val then (v.2 ⟨h,hh⟩).val else 0
  else 0

noncomputable def paddedEqual (i j : ℕ) : Bool :=
  if hi : i<vectorCount then if hj : j<vectorCount then
    decide (PrefixParts.Wiring.pad (vectorNumber.symm ⟨i,hi⟩).2=
      PrefixParts.Wiring.pad (vectorNumber.symm ⟨j,hj⟩).2)
  else false else false

@[simp] theorem prefix_encode {a : ℕ} (ha : a≤6) (p : Equiv.Perm (Fin a)) (h : ℕ) (z : Vec a) :
    prefixCode (encodeOrder ha p) h (encode ha z)=encode ha (PrefixParts.Data.truncate h (z ∘ p)) := by
  simp only [prefixCode,dite_eq_left (order_lt ha p),dite_eq_left (encode_lt ha z)]
  change (vectorNumber (truncated h (permuted (orderNumber.symm (orderNumber ⟨⟨a,by omega⟩,p⟩))
    (vectorNumber.symm (vectorNumber ⟨⟨a,by omega⟩,z⟩))))).val=_
  rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  unfold permuted
  rw [dite_eq_left rfl]
  rfl

@[simp] theorem bit_encode {a : ℕ} (ha : a≤6) (z : Vec a) (i : Fin a) :
    bit (encode ha z) i.val=(z i).val := by
  simp only [bit,dite_eq_left (encode_lt ha z)]
  change (if h : i.val<(vectorNumber.symm (vectorNumber ⟨⟨a,by omega⟩,z⟩)).1.val then
    ((vectorNumber.symm (vectorNumber ⟨⟨a,by omega⟩,z⟩)).2 ⟨i.val,h⟩).val else 0)=_
  rw [Equiv.symm_apply_apply]
  exact dite_eq_left i.isLt

@[simp] theorem paddedEqual_encode {a b : ℕ} (ha : a≤6) (hb : b≤6) (z : Vec a) (w : Vec b) :
    paddedEqual (encode ha z) (encode hb w)=decide (PrefixParts.Wiring.pad z=PrefixParts.Wiring.pad w) := by
  simp only [paddedEqual,dite_eq_left (encode_lt ha z),dite_eq_left (encode_lt hb w)]
  change decide (PrefixParts.Wiring.pad (vectorNumber.symm (vectorNumber ⟨⟨a,by omega⟩,z⟩)).2=
    PrefixParts.Wiring.pad (vectorNumber.symm (vectorNumber ⟨⟨b,by omega⟩,w⟩)).2)=_
  rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]

end VariableWL.PrefixAlphabet

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

def fixedNat₂ (N M : ℕ) (f : ℕ → ℕ → ℕ) (I J : Expr n) : Expr n :=
  fixedNat (N*M) (fun q=>f (q.val/M) (q.val%M)) (add (mul I (numeral M)) J)

def fixedNat₃ (N M K : ℕ) (f : ℕ → ℕ → ℕ → ℕ) (I J L : Expr n) : Expr n :=
  fixedNat₂ N (M*K) (fun i q=>f i (q/K) (q%K)) I (add (mul J (numeral K)) L)

def fixedBool₂ (N M : ℕ) (f : ℕ → ℕ → Bool) (I J : Expr n) : Expr n :=
  eq (fixedNat₂ N M (fun i j=>if f i j then 1 else 0) I J) (numeral 1)

end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.PrefixAlphabet.Program
open Computation.Stack.PolyRecipe Computation.Stack.Recipe
variable {n : ℕ}

noncomputable def paddedEqual (I J : Expr n) : Expr n :=
  fixedBool₂ vectorCount vectorCount PrefixAlphabet.paddedEqual I J

end VariableWL.PrefixAlphabet.Program

namespace VariableWL.PrefixAlphabet
 theorem vectorCount_pos : 0<vectorCount := by
  let : Nonempty Vector := ⟨⟨0,0⟩⟩
  exact Fintype.card_pos
end VariableWL.PrefixAlphabet

namespace VariableWL.PrefixDescriptor
open VariableWL.Affine Descriptor PrefixParts
attribute [local instance] Classical.propDecidable

@[ext] structure Raw where
  block : ℕ
  kind : ℕ
  channel : ℕ
  height : ℕ
  vector : ℕ
  deriving DecidableEq

structure Data where
  blocks : ℕ
  validBlock : ℕ → Bool
  channelBound : ℕ
  dimension : ℕ → ℕ
  channels : ℕ → ℕ
  root : ℕ → ℕ → ℕ
  order : ℕ → ℕ → ℕ
  legal : ℕ → ℕ → Bool
  matching : ℕ → ℕ → Bool

namespace Data
variable (D : Data)

def sortBound : ℕ := D.blocks*3*D.channelBound*7
noncomputable def bound : ℕ := D.sortBound*PrefixAlphabet.vectorCount

def tag (x : Raw) : ℕ := ((x.block*3+x.kind)*D.channelBound+x.channel)*7+x.height
noncomputable def pack (x : Raw) : ℕ := D.tag x*PrefixAlphabet.vectorCount+x.vector
noncomputable def unpack (i : ℕ) : Raw :=
  ⟨i/PrefixAlphabet.vectorCount/7/D.channelBound/3,
    i/PrefixAlphabet.vectorCount/7/D.channelBound%3,
    i/PrefixAlphabet.vectorCount/7%D.channelBound,
    i/PrefixAlphabet.vectorCount%7,i%PrefixAlphabet.vectorCount⟩

theorem join_div (x y m : ℕ) (hm : 0 < m) (hy : y < m) : (x*m+y)/m=x := by
  rw [Nat.mul_comm x m,Nat.mul_add_div hm,Nat.div_eq_of_lt hy,Nat.add_zero]
theorem join_mod (x y m : ℕ) (hy : y < m) : (x*m+y)%m=y := by
  rw [Nat.mul_comm x m,Nat.mul_add_mod,Nat.mod_eq_of_lt hy]

theorem unpack_pack (x : Raw) (hk : x.kind<3) (hc : x.channel<D.channelBound)
    (hh : x.height<7) (hu : x.vector<PrefixAlphabet.vectorCount) : D.unpack (D.pack x)=x := by
  have hC : 0<D.channelBound := by omega
  simp only [unpack,pack,tag,join_div _ _ _ PrefixAlphabet.vectorCount_pos hu,
    join_mod _ _ _ hu,join_div _ _ _ (by omega : 0<7) hh,join_mod _ _ _ hh,
    join_div _ _ _ hC hc,join_mod _ _ _ hc,join_div _ _ _ (by omega : 0<3) hk,join_mod _ _ _ hk]

theorem pack_unpack (i : ℕ) : D.pack (D.unpack i)=i := by
  simp only [pack,tag,unpack]
  rw [Nat.mul_comm (i/PrefixAlphabet.vectorCount/7/D.channelBound/3) 3,Nat.div_add_mod,
    Nat.mul_comm (i/PrefixAlphabet.vectorCount/7/D.channelBound) D.channelBound,Nat.div_add_mod,
    Nat.mul_comm (i/PrefixAlphabet.vectorCount/7) 7,Nat.div_add_mod,
    Nat.mul_comm (i/PrefixAlphabet.vectorCount) PrefixAlphabet.vectorCount,Nat.div_add_mod]

theorem tag_lt (x : Raw) (hb : x.block<D.blocks) (hk : x.kind<3)
    (hc : x.channel<D.channelBound) (hh : x.height<7) : D.tag x<D.sortBound := by
  have h1 : x.block*3+x.kind<D.blocks*3 := by omega
  have h2 : (x.block*3+x.kind)*D.channelBound+x.channel<(D.blocks*3)*D.channelBound :=
    (Nat.add_lt_add_left hc _).trans_le (by rw [←Nat.succ_mul]; exact Nat.mul_le_mul_right _ h1)
  exact (Nat.add_lt_add_left hh _).trans_le (by rw [←Nat.succ_mul]; exact Nat.mul_le_mul_right _ h2)

theorem pack_lt (x : Raw) (hb : x.block<D.blocks) (hk : x.kind<3)
    (hc : x.channel<D.channelBound) (hh : x.height<7) (hu : x.vector<PrefixAlphabet.vectorCount) :
    D.pack x<D.bound :=
  (Nat.add_lt_add_left hu _).trans_le (by
    change D.tag x*PrefixAlphabet.vectorCount+PrefixAlphabet.vectorCount≤D.sortBound*PrefixAlphabet.vectorCount
    rw [←Nat.succ_mul]
    exact Nat.mul_le_mul_right _ (D.tag_lt x hb hk hc hh))

theorem unpack_bounds (hC : 0<D.channelBound) {i : ℕ} (hi : i<D.bound) :
    (D.unpack i).block<D.blocks ∧ (D.unpack i).kind<3 ∧
      (D.unpack i).channel<D.channelBound ∧ (D.unpack i).height<7 ∧
      (D.unpack i).vector<PrefixAlphabet.vectorCount := by
  refine ⟨?_,Nat.mod_lt _ (by omega),Nat.mod_lt _ hC,Nat.mod_lt _ (by omega),
    Nat.mod_lt _ PrefixAlphabet.vectorCount_pos⟩
  have h1 : i/PrefixAlphabet.vectorCount<D.sortBound :=
    (Nat.div_lt_iff_lt_mul PrefixAlphabet.vectorCount_pos).mpr hi
  have h2 : i/PrefixAlphabet.vectorCount/7<D.blocks*3*D.channelBound :=
    (Nat.div_lt_iff_lt_mul (by omega : 0<7)).mpr h1
  have h3 : i/PrefixAlphabet.vectorCount/7/D.channelBound<D.blocks*3 :=
    (Nat.div_lt_iff_lt_mul hC).mpr h2
  exact (Nat.div_lt_iff_lt_mul (by omega : 0<3)).mpr h3

noncomputable def treeValid (x : Raw) : Bool :=
  decide (D.root x.block x.channel≤x.height ∧ x.height≤D.dimension x.block) &&
    (List.range PrefixAlphabet.vectorCount).any (fun j=>D.legal x.block j &&
      decide (PrefixAlphabet.prefixCode (D.order x.block x.channel) x.height j=x.vector))

noncomputable def validRaw (x : Raw) : Bool := D.validBlock x.block &&
  ((decide (x.kind=0 ∧ x.channel=0 ∧ x.height=0 ∧ x.vector=0)) ||
    (decide (x.kind=1 ∧ x.channel<D.channels x.block ∧ x.height=0) && D.legal x.block x.vector) ||
    (decide (x.kind=2 ∧ x.channel<D.channels x.block) && D.treeValid x))
noncomputable def valid (i : ℕ) : Bool := D.validRaw (D.unpack i)

def sortValid (x : Raw) : Bool := D.validBlock x.block &&
  decide ((x.kind=0 ∧ x.channel=0 ∧ x.height=0) ∨
    (x.kind=1 ∧ x.channel<D.channels x.block ∧ x.height=0) ∨
    (x.kind=2 ∧ x.channel<D.channels x.block ∧ D.root x.block x.channel≤x.height ∧
      x.height≤D.dimension x.block))

end Data

variable {B : Type uVariable4} (P : Presentation B) (F : B → PrefixParts.Data)
variable (hDim : ∀b,(F b).dimension≤6) (ε : Bit)

structure Good (D : Data) : Prop where
  blocks : D.blocks=P.bound
  validBlock : D.validBlock=P.valid
  positive : 0<D.channelBound
  channelBound : ∀b,(F b).channels≤D.channelBound
  dimension : ∀b,D.dimension (P.encode b)=(F b).dimension
  channels : ∀b,D.channels (P.encode b)=(F b).channels
  root : ∀b (c : Fin (F b).channels),D.root (P.encode b) c.val=(F b).root c
  order : ∀b (c : Fin (F b).channels),D.order (P.encode b) c.val=PrefixAlphabet.encodeOrder (hDim b) ((F b).order c)
  legal : ∀b i,D.legal (P.encode b) i=true ↔
    ∃z : (F b).Valuation ε,PrefixAlphabet.encode (hDim b) z.val=i

noncomputable def raw (x : PrefixParts.Wiring.Vertex F ε) : Raw :=
  match x.2 with
  | .inl _ => ⟨P.encode x.1,0,0,0,0⟩
  | .inr (.inl (c,z)) => ⟨P.encode x.1,1,c.val,0,PrefixAlphabet.encode (hDim x.1) z.val⟩
  | .inr (.inr t) => ⟨P.encode x.1,2,t.channel.val,t.height,PrefixAlphabet.encode (hDim x.1) t.bits⟩

@[simp] theorem raw_block (x : PrefixParts.Wiring.Vertex F ε) : (raw P F hDim ε x).block=P.encode x.1 := by
  rcases x with ⟨b,x | (x | x)⟩ <;> rfl

theorem raw_bounds {D : Data} (h : Good P F hDim ε D) (x : PrefixParts.Wiring.Vertex F ε) :
    (raw P F hDim ε x).block<D.blocks ∧ (raw P F hDim ε x).kind<3 ∧
      (raw P F hDim ε x).channel<D.channelBound ∧ (raw P F hDim ε x).height<7 ∧
      (raw P F hDim ε x).vector<PrefixAlphabet.vectorCount := by
  have hb := P.encode_lt x.1
  rw [←h.blocks] at hb
  rcases x with ⟨b,x | (⟨c,z⟩ | t)⟩
  · exact ⟨hb,by change 0<3; omega,h.positive,by change 0<7; omega,PrefixAlphabet.vectorCount_pos⟩
  · exact ⟨hb,by change 1<3; omega,c.isLt.trans_le (h.channelBound b),by change 0<7; omega,PrefixAlphabet.encode_lt (hDim b) z.val⟩
  · have ht := t.val.2.1.isLt
    have hd := hDim b
    exact ⟨hb,by change 2<3; omega,t.channel.isLt.trans_le (h.channelBound b),by dsimp [raw,PrefixParts.Data.Tree.height]; omega,
      PrefixAlphabet.encode_lt (hDim b) t.bits⟩

 theorem raw_valid {D : Data} (h : Good P F hDim ε D) (x : PrefixParts.Wiring.Vertex F ε) :
    D.validRaw (raw P F hDim ε x)=true := by
  have hb : D.validBlock (P.encode x.1)=true := h.validBlock ▸ P.encode_valid x.1
  rcases x with ⟨b,x | (⟨c,z⟩ | t)⟩
  · simp only [raw,Data.validRaw,hb,Bool.true_and,and_self,decide_true,Bool.true_or]
  · have hz := (h.legal b (PrefixAlphabet.encode (hDim b) z.val)).mpr ⟨z,rfl⟩
    simp only [raw,Data.validRaw,hb,Bool.true_and,h.channels,one_ne_zero,false_and,
      decide_false,Bool.false_or,true_and,c.isLt,and_true,decide_true,Bool.true_and,hz,Bool.true_or]
  · apply Bool.and_eq_true_iff.mpr ⟨hb,?_⟩
    apply Bool.or_eq_true_iff.mpr
    right
    apply Bool.and_eq_true_iff.mpr
    refine ⟨by simp only [raw,h.channels,t.channel.isLt,and_self,decide_true],?_⟩
    change D.treeValid ⟨P.encode b,2,t.channel.val,t.height,PrefixAlphabet.encode (hDim b) t.bits⟩=true
    apply Bool.and_eq_true_iff.mpr
    refine ⟨by exact decide_eq_true (show D.root (P.encode b) t.channel.val≤t.height ∧
      t.height≤D.dimension (P.encode b) from ⟨(h.root b t.channel) ▸ t.property.1,
        (h.dimension b) ▸ Nat.le_of_lt_succ t.val.2.1.isLt⟩),?_⟩
    obtain ⟨z,hz⟩ := t.property.2
    apply List.any_eq_true.mpr
    refine ⟨PrefixAlphabet.encode (hDim b) z.val,List.mem_range.mpr (PrefixAlphabet.encode_lt _ _),?_⟩
    apply Bool.and_eq_true_iff.mpr
    refine ⟨(h.legal b _).mpr ⟨z,rfl⟩,?_⟩
    rw [h.order,PrefixAlphabet.prefix_encode,hz]
    exact decide_eq_true rfl

end VariableWL.PrefixDescriptor

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_PrefixDescriptor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4

namespace VariableWL.PrefixDescriptor
open VariableWL.Affine Descriptor PrefixParts
attribute [local instance] Classical.propDecidable
variable {B : Type uVariable1} (P : Presentation B) (F : B → PrefixParts.Data)
variable (hDim : ∀b,(F b).dimension≤6) (ε : Bit)

 theorem raw_injective : Function.Injective (raw P F hDim ε) := by
  rintro ⟨b,x⟩ ⟨d,y⟩ he
  have hb : b=d := P.encode_injective (by simpa only [raw_block] using congrArg Raw.block he)
  subst d
  apply congrArg (Sigma.mk b)
  cases x with
  | inl x =>
    cases y with
    | inl y => congr
    | inr y => cases y <;> have hk := congrArg Raw.kind he <;> cases hk
  | inr x =>
    cases y with
    | inl y => cases x <;> have hk := congrArg Raw.kind he <;> cases hk
    | inr y =>
      congr 1
      cases x with
      | inl x =>
        cases y with
        | inr y => have hk := congrArg Raw.kind he; cases hk
        | inl y =>
          congr 1
          apply Prod.ext
          · exact Fin.ext (congrArg Raw.channel he)
          · exact Subtype.ext (PrefixAlphabet.encode_injective (hDim b) (congrArg Raw.vector he))
      | inr x =>
        cases y with
        | inl y => have hk := congrArg Raw.kind he; cases hk
        | inr y =>
          congr 1
          exact Data.Tree.ext (Fin.ext (congrArg Raw.channel he)) (congrArg Raw.height he)
            (PrefixAlphabet.encode_injective (hDim b) (congrArg Raw.vector he))

 theorem raw_surjective {D : Data} (h : Good P F hDim ε D) (x : Raw)
    (hb : x.block<D.blocks) (hv : D.validRaw x=true) :
    ∃v : Wiring.Vertex F ε,raw P F hDim ε v=x := by
  obtain ⟨hbv,hv⟩ := Bool.and_eq_true_iff.mp hv
  let u : Valid P.bound P.valid := ⟨⟨x.block,h.blocks ▸ hb⟩,h.validBlock ▸ hbv⟩
  let b := P.equiv u
  have eb : P.encode b=x.block := by
    change (P.equiv.symm (P.equiv u)).val.val=_
    rw [Equiv.symm_apply_apply]
  rcases Bool.or_eq_true_iff.mp hv with hv | hv
  · rcases Bool.or_eq_true_iff.mp hv with hv | hv
    · obtain ⟨hk,hc,hh,hu⟩ := of_decide_eq_true hv
      refine ⟨⟨b,.inl ()⟩,?_⟩
      apply Raw.ext <;> simp only [raw,eb,hk,hc,hh,hu]
    · obtain ⟨hv,hl⟩ := Bool.and_eq_true_iff.mp hv
      obtain ⟨hk,hc,hh⟩ := of_decide_eq_true hv
      rw [←eb,h.channels] at hc
      rw [←eb] at hl
      obtain ⟨z,hz⟩ := (h.legal b x.vector).mp hl
      refine ⟨⟨b,.inr (.inl (⟨x.channel,hc⟩,z))⟩,?_⟩
      apply Raw.ext <;> simp only [raw,eb,hk,hh,hz]
  · obtain ⟨hv,ht⟩ := Bool.and_eq_true_iff.mp hv
    obtain ⟨hk,hc⟩ := of_decide_eq_true hv
    rw [←eb,h.channels] at hc
    let c : Fin (F b).channels := ⟨x.channel,hc⟩
    obtain ⟨ht,hz⟩ := Bool.and_eq_true_iff.mp ht
    obtain ⟨hr,hd⟩ := of_decide_eq_true ht
    rw [←eb,h.dimension] at hd
    have hr' : (F b).root c≤x.height := by
      rw [←eb] at hr
      change D.root (P.encode b) c.val≤x.height at hr
      rwa [h.root] at hr
    obtain ⟨j,_,hj⟩ := List.any_eq_true.mp hz
    obtain ⟨hl,hp⟩ := Bool.and_eq_true_iff.mp hj
    rw [←eb] at hl
    obtain ⟨z,ez⟩ := (h.legal b j).mp hl
    have hp' : PrefixAlphabet.encode (hDim b) (PrefixParts.Data.truncate x.height (z.val ∘ (F b).order c))=x.vector := by
      have hop := h.order b c
      rw [←ez,←eb,hop,PrefixAlphabet.prefix_encode] at hp
      exact of_decide_eq_true hp
    refine ⟨⟨b,.inr (.inr (PrefixParts.Data.Tree.ofValuation c x.height hr' hd z))⟩,?_⟩
    apply Raw.ext <;> simp only [raw,PrefixParts.Data.Tree.ofValuation,eb,hk,hp',c]

noncomputable def presentation {D : Data} (h : Good P F hDim ε D) : Presentation (Wiring.Vertex F ε) :=
  Presentation.ofEncoding D.bound D.valid (fun x=>D.pack (raw P F hDim ε x))
    (fun x=>D.pack_lt _ (raw_bounds P F hDim ε h x).1 (raw_bounds P F hDim ε h x).2.1
      (raw_bounds P F hDim ε h x).2.2.1 (raw_bounds P F hDim ε h x).2.2.2.1
      (raw_bounds P F hDim ε h x).2.2.2.2)
    (fun x=>by
      rw [Data.valid,D.unpack_pack _ (raw_bounds P F hDim ε h x).2.1
        (raw_bounds P F hDim ε h x).2.2.1 (raw_bounds P F hDim ε h x).2.2.2.1
        (raw_bounds P F hDim ε h x).2.2.2.2]
      exact raw_valid P F hDim ε h x)
    (by
      intro x y he
      have hb := raw_bounds P F hDim ε h x
      have hc := raw_bounds P F hDim ε h y
      have he' := congrArg D.unpack he
      rw [D.unpack_pack _ hb.2.1 hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2,
        D.unpack_pack _ hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2] at he'
      exact raw_injective P F hDim ε he')
    (by
      intro i hi hv
      obtain ⟨x,hx⟩ := raw_surjective P F hDim ε h (D.unpack i) (D.unpack_bounds h.positive hi).1 hv
      exact ⟨x,by rw [hx,D.pack_unpack]⟩)

@[simp] theorem presentation_encode {D : Data} (h : Good P F hDim ε D) (x : Wiring.Vertex F ε) :
    (presentation P F hDim ε h).encode x=D.pack (raw P F hDim ε x) := rfl

end VariableWL.PrefixDescriptor

namespace VariableWL.PrefixAlphabet
open VariableWL.Affine
noncomputable def trim (h i : ℕ) : ℕ :=
  if hi : i<vectorCount then (vectorNumber (truncated h (vectorNumber.symm ⟨i,hi⟩))).val else 0
@[simp] theorem trim_encode {a : ℕ} (ha : a≤6) (z : Vec a) (h : ℕ) :
    trim h (encode ha z)=encode ha (PrefixParts.Data.truncate h z) := by
  simp only [trim,dite_eq_left (encode_lt ha z)]
  change (vectorNumber (truncated h (vectorNumber.symm (vectorNumber ⟨⟨a,by omega⟩,z⟩)))).val=_
  rw [Equiv.symm_apply_apply]
  rfl
end VariableWL.PrefixAlphabet

namespace VariableWL.PrefixDescriptor
open VariableWL.Affine Descriptor PrefixParts
attribute [local instance] Classical.propDecidable
namespace Data
variable (D : Data)
noncomputable def forward (x y : Raw) : Bool :=
  (decide (x.kind=0 ∧ y.kind=2 ∧ y.channel=0 ∧ y.height=0)) ||
  (decide (x.kind=1 ∧ y.kind=1 ∧ x.channel+1=y.channel ∧ x.vector=y.vector)) ||
  (decide (x.kind=2 ∧ y.kind=2 ∧ x.channel=y.channel ∧ x.height+1=y.height ∧
    PrefixAlphabet.trim x.height y.vector=x.vector)) ||
  (decide (x.kind=2 ∧ y.kind=1 ∧ x.channel=y.channel ∧ x.height=D.dimension x.block ∧
    x.vector=PrefixAlphabet.prefixCode (D.order x.block y.channel) (D.dimension x.block) y.vector))
noncomputable def slot (x y : Raw) : ℕ :=
  if x.kind=0 then 0 else if x.kind=1 then
    if y.kind=1 then if y.channel<x.channel then 0 else 1 else 2
  else if y.kind=0 then 0 else if y.kind=1 then 1 else
    if y.height<x.height then 0 else
      if x.height<D.dimension x.block then PrefixAlphabet.bit y.vector x.height+1 else 1
noncomputable def internal (x y : Raw) (i j : ℕ) : Bool :=
  decide (x.block=y.block) && (D.forward x y || D.forward y x) &&
    decide (i=D.slot x y ∧ j=D.slot y x)
end Data

variable {B : Type uVariable2} (P : Presentation B) (F : B → PrefixParts.Data)
variable (hDim : ∀b,(F b).dimension≤6) (ε : Bit)

 theorem raw_forward {D : Data} (h : Good P F hDim ε D) (b : B) (x y : (F b).Vertex ε) :
    D.forward (raw P F hDim ε ⟨b,x⟩) (raw P F hDim ε ⟨b,y⟩)=true ↔ PrefixParts.Data.Forward x y := by
  have hinj (z w : Vec (F b).dimension) : PrefixAlphabet.encode (hDim b) z=PrefixAlphabet.encode (hDim b) w ↔ z=w :=
    (PrefixAlphabet.encode_injective (hDim b)).eq_iff
  rcases x with x | (⟨c,z⟩ | t) <;> rcases y with y | (⟨d,w⟩ | u) <;>
    simp only [raw,Data.forward,PrefixParts.Data.Forward,PrefixParts.Data.TreeStep,
      h.dimension,h.order,PrefixAlphabet.prefix_encode,PrefixAlphabet.trim_encode,
      PrefixParts.Data.truncate_full,Bool.or_eq_true,decide_eq_true_eq,hinj,
      Fin.ext_iff,Subtype.ext_iff]
  all_goals norm_num only
  all_goals simp only [true_and,false_and,and_true,and_false,false_or,or_false,decide_false,Bool.false_eq_true]

 theorem fin_val_ite (p : Prop) [Decidable p] (a b : Fin 3) :
    (if p then a else b).val=if p then a.val else b.val := by split_ifs <;> rfl
 theorem fin_val_dite (p : Prop) [Decidable p] (a : p → Fin 3) (b : ¬p → Fin 3) :
    (dite p a b).val=dite p (fun h => (a h).val) (fun h => (b h).val) := by split_ifs <;> rfl
 theorem raw_slot {D : Data} (h : Good P F hDim ε D) (b : B) (x y : (F b).Vertex ε) :
    D.slot (raw P F hDim ε ⟨b,x⟩) (raw P F hDim ε ⟨b,y⟩)=(PrefixParts.Data.slot x y).val := by
  rcases x with x | (⟨c,z⟩ | t) <;> rcases y with y | (⟨d,w⟩ | u) <;>
    simp only [Data.slot,raw,PrefixParts.Data.slot,h.dimension,one_ne_zero,show (2:ℕ)≠0 by omega,show (2:ℕ)≠1 by omega,
      ite_true,ite_false,show (0:ℕ)≠1 by omega,Fin.val_zero,Fin.val_one,fin_val_ite,fin_val_dite,PrefixParts.Data.bitPort]
  · rfl
  · rfl
  · rfl
  · split_ifs with h1 h2
    · rfl
    · rw [PrefixAlphabet.bit_encode (hDim b) u.bits ⟨t.height,h2⟩]
    · rfl

 theorem raw_internal [Fintype B] {D : Data} (h : Good P F hDim ε D)
    (x y : Wiring.Vertex F ε) (i j : Fin 3) :
    D.internal (raw P F hDim ε x) (raw P F hDim ε y) i.val j.val=true ↔
      (Wiring.internal F ε).edge (x,i) (y,j) := by
  rcases x with ⟨b,x⟩
  rcases y with ⟨d,y⟩
  by_cases hbd : b=d
  · subst d
    simp only [Data.internal,raw_block,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,
      true_and,raw_forward P F hDim ε h,raw_slot P F hDim ε h]
    simp only [Wiring.internal,SubcubicRealization.PortGraph.sigma,PrefixParts.Data.ports,
      PrefixParts.Data.graph,SubcubicRealization.PortGraph.ofSlots,exists_true_left,Fin.ext_iff]
  · have he : P.encode b≠P.encode d := P.encode_injective.ne hbd
    simp only [Data.internal,raw_block,he,decide_false,Bool.false_and,Bool.false_eq_true,
      Wiring.internal,SubcubicRealization.PortGraph.sigma,hbd]
    exact ⟨False.elim,fun ⟨h,_⟩=>h⟩

end VariableWL.PrefixDescriptor

namespace VariableWL.PrefixDescriptor
open VariableWL.Affine Descriptor PrefixParts
attribute [local instance] Classical.propDecidable
variable {B : Type uVariable3} (P : Presentation B) (F : B → PrefixParts.Data)

noncomputable def sortRaw (s : Wiring.SortTag F) : Raw := match s.2 with
  | .inl _ => ⟨P.encode s.1,0,0,0,0⟩
  | .inr (.inl c) => ⟨P.encode s.1,1,c.val,0,0⟩
  | .inr (.inr ⟨c,h⟩) => ⟨P.encode s.1,2,c.val,h.val.val,0⟩

@[simp] theorem sortRaw_block (s : Wiring.SortTag F) : (sortRaw P F s).block=P.encode s.1 := by
  rcases s with ⟨b,x| (x|x)⟩ <;> rfl

 theorem sortRaw_injective : Function.Injective (sortRaw P F) := by
  rintro ⟨b,x⟩ ⟨d,y⟩ he
  have hb := P.encode_injective (by simpa only [sortRaw_block] using congrArg Raw.block he)
  subst d
  apply congrArg (Sigma.mk b)
  cases x with
  | inl x =>
    cases y with
    | inl y => congr
    | inr y => cases y <;> have hk := congrArg Raw.kind he <;> cases hk
  | inr x =>
    cases y with
    | inl y => cases x <;> have hk := congrArg Raw.kind he <;> cases hk
    | inr y =>
      congr 1
      cases x with
      | inl x =>
        cases y with
        | inr y => have hk := congrArg Raw.kind he; cases hk
        | inl y => exact congrArg Sum.inl (Fin.ext (congrArg Raw.channel he))
      | inr x =>
        cases y with
        | inl y => have hk := congrArg Raw.kind he; cases hk
        | inr y =>
          congr 1
          rcases x with ⟨c,u⟩
          rcases y with ⟨d,v⟩
          have hc : c=d := Fin.ext (congrArg Raw.channel he)
          subst d
          apply congrArg (Sigma.mk c)
          exact Subtype.ext (Fin.ext (congrArg Raw.height he))

variable (hDim : ∀b,(F b).dimension≤6) (ε : Bit)
 theorem sortRaw_bounds {D : Data} (h : Good P F hDim ε D) (x : Wiring.SortTag F) :
    (sortRaw P F x).block<D.blocks ∧ (sortRaw P F x).kind<3 ∧
      (sortRaw P F x).channel<D.channelBound ∧ (sortRaw P F x).height<7 ∧
      (sortRaw P F x).vector<PrefixAlphabet.vectorCount := by
  have hb := P.encode_lt x.1
  rw [←h.blocks] at hb
  rcases x with ⟨b,x | (c | ⟨c,t⟩)⟩
  · exact ⟨hb,by change 0<3; omega,h.positive,by change 0<7; omega,PrefixAlphabet.vectorCount_pos⟩
  · exact ⟨hb,by change 1<3; omega,c.isLt.trans_le (h.channelBound b),by change 0<7; omega,PrefixAlphabet.vectorCount_pos⟩
  · have ht := t.val.isLt
    have hd := hDim b
    exact ⟨hb,by change 2<3; omega,c.isLt.trans_le (h.channelBound b),by dsimp [sortRaw]; omega,
      PrefixAlphabet.vectorCount_pos⟩

 theorem sortRaw_valid {D : Data} (h : Good P F hDim ε D) (x : Wiring.SortTag F) :
    D.sortValid (sortRaw P F x)=true := by
  have hb : D.validBlock (P.encode x.1)=true := h.validBlock ▸ P.encode_valid x.1
  rcases x with ⟨b,x | (c | ⟨c,t⟩)⟩
  · simp only [sortRaw,Data.sortValid,hb,Bool.true_and,and_self,true_or,decide_true]
  · have hc := c.isLt
    simp only [sortRaw,Data.sortValid,hb,Bool.true_and,h.channels,decide_eq_true_eq]
    exact Or.inr (Or.inl ⟨True.intro,hc,True.intro⟩)
  · simp only [sortRaw,Data.sortValid,hb,Bool.true_and,h.channels,h.root,h.dimension,decide_eq_true_eq]
    exact Or.inr (Or.inr ⟨True.intro,c.isLt,t.property,Nat.le_of_lt_succ t.val.isLt⟩)

namespace Data
variable (D : Data)
noncomputable def sortPredicate (i : ℕ) : Bool := D.sortValid (D.unpack (i*PrefixAlphabet.vectorCount))
noncomputable def color (i : ℕ) : ℕ := 1+Descriptor.rank D.sortPredicate (D.tag (D.unpack i))
noncomputable def colorBound : ℕ := 1+Descriptor.rank D.sortPredicate D.sortBound
end Data

 theorem sortPresentation {D : Data} (h : Good P F hDim ε D) :
    ∃Q : Presentation (Wiring.SortTag F),Q.bound=D.sortBound ∧ Q.valid=D.sortPredicate ∧
      ∀s,Q.encode s=D.tag (sortRaw P F s) := by
  let f := fun s : Wiring.SortTag F=>D.tag (sortRaw P F s)
  have hf (s) : f s<D.sortBound := by
    have hb := sortRaw_bounds P F hDim ε h s
    exact D.tag_lt _ hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.1
  have helper (s) : D.unpack (f s*PrefixAlphabet.vectorCount)=sortRaw P F s := by
    have hb := sortRaw_bounds P F hDim ε h s
    have hv : (sortRaw P F s).vector=0 := by rcases s with ⟨b,x | (x|x)⟩ <;> rfl
    have he : f s*PrefixAlphabet.vectorCount=D.pack (sortRaw P F s) := by simp only [Data.pack,hv,Nat.add_zero]; rfl
    rw [he,D.unpack_pack _ hb.2.1 hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2]
  have hp (s) : D.sortPredicate (f s)=true := by
    rw [Data.sortPredicate,helper]
    exact sortRaw_valid P F hDim ε h s
  have hi : Function.Injective f := by
    intro s t he
    apply sortRaw_injective P F
    rw [←helper s,←helper t,he]
  have hs (i : ℕ) (hi : i<D.sortBound) (hv : D.sortPredicate i=true) : ∃s,f s=i := by
    let x := D.unpack (i*PrefixAlphabet.vectorCount)
    have hx : i*PrefixAlphabet.vectorCount<D.bound := Nat.mul_lt_mul_of_pos_right hi PrefixAlphabet.vectorCount_pos
    have hb := (D.unpack_bounds h.positive hx).1
    obtain ⟨hbv,hv⟩ := Bool.and_eq_true_iff.mp hv
    let u : Valid P.bound P.valid := ⟨⟨x.block,h.blocks ▸ hb⟩,h.validBlock ▸ hbv⟩
    let b := P.equiv u
    have eb : P.encode b=x.block := by
      change (P.equiv.symm (P.equiv u)).val.val=_
      rw [Equiv.symm_apply_apply]
    have hxv : x.vector=0 := by simp [x,Data.unpack]
    have target (s : Wiring.SortTag F) (hh : sortRaw P F s=x) : f s=i := by
      have he := congrArg D.pack hh
      rw [D.pack_unpack] at he
      have hv : (sortRaw P F s).vector=0 := by rcases s with ⟨b,x | (x|x)⟩ <;> rfl
      simp only [Data.pack,hv,Nat.add_zero] at he
      exact Nat.eq_of_mul_eq_mul_right PrefixAlphabet.vectorCount_pos he
    change decide ((x.kind=0 ∧ x.channel=0 ∧ x.height=0) ∨
      (x.kind=1 ∧ x.channel<D.channels x.block ∧ x.height=0) ∨
      (x.kind=2 ∧ x.channel<D.channels x.block ∧ D.root x.block x.channel≤x.height ∧
        x.height≤D.dimension x.block))=true at hv
    rcases of_decide_eq_true hv with hh | hh | hh
    · obtain ⟨hk,hc,hh⟩ := hh
      exact ⟨⟨b,.inl ()⟩,target _ (by apply Raw.ext <;> simp only [sortRaw,eb,hk,hc,hh,hxv])⟩
    · obtain ⟨hk,hc,hh⟩ := hh
      rw [←eb,h.channels] at hc
      exact ⟨⟨b,.inr (.inl ⟨x.channel,hc⟩)⟩,target _ (by apply Raw.ext <;> simp only [sortRaw,eb,hk,hh,hxv])⟩
    · obtain ⟨hk,hc,hr,hd⟩ := hh
      rw [←eb,h.channels] at hc
      rw [←eb,h.dimension] at hd
      let c : Fin (F b).channels := ⟨x.channel,hc⟩
      have hr' : (F b).root c≤x.height := by
        rw [←eb] at hr
        change D.root (P.encode b) c.val≤x.height at hr
        rwa [h.root] at hr
      exact ⟨⟨b,.inr (.inr ⟨c,⟨x.height,by omega⟩,hr'⟩)⟩,
        target _ (by apply Raw.ext <;> simp only [sortRaw,eb,hk,hxv,c])⟩
  exact ⟨Presentation.ofEncoding _ _ f hf hp hi hs,rfl,rfl,fun s=>rfl⟩

end VariableWL.PrefixDescriptor

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}
def table₂ (N M : ℕ) (f : ℕ → ℕ → ℕ) (I J : Expr n) : Expr n :=
  choose (conj (lt I (numeral N)) (lt J (numeral M))) (fixedNat₂ N M f I J) (numeral 0)

def table₃ (N M K : ℕ) (f : ℕ → ℕ → ℕ → ℕ) (I J L : Expr n) : Expr n :=
  choose (conj (conj (lt I (numeral N)) (lt J (numeral M))) (lt L (numeral K)))
    (fixedNat₃ N M K f I J L) (numeral 0)

end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.PrefixAlphabet
open VariableWL.Affine

namespace TotalProgram
open Computation.Stack.PolyRecipe Computation.Stack.Recipe
variable {n : ℕ}
noncomputable def prefixCode (P H I : Expr n) : Expr n :=
  table₃ orderCount 8 vectorCount PrefixAlphabet.prefixCode P (minimum H (numeral 7)) I
noncomputable def trim (H I : Expr n) : Expr n :=
  table₂ 8 vectorCount PrefixAlphabet.trim (minimum H (numeral 7)) I
noncomputable def bit (I H : Expr n) : Expr n :=
  table₂ vectorCount 7 PrefixAlphabet.bit I H
end TotalProgram
end VariableWL.PrefixAlphabet

namespace VariableWL.PrefixDescriptor
open VariableWL.Affine Descriptor PrefixParts
attribute [local instance] Classical.propDecidable
namespace Data
variable (D : Data)
noncomputable def roots (x y : Raw) (i j : ℕ) : Bool :=
  decide (x.kind=2 ∧ y.kind=2 ∧ i=0 ∧ j=0 ∧ x.channel≠0 ∧ y.channel≠0 ∧
    x.height=D.root x.block x.channel ∧ y.height=D.root y.block y.channel) &&
  D.matching (x.block*D.channelBound+x.channel) (y.block*D.channelBound+y.channel) &&
  PrefixAlphabet.paddedEqual x.vector y.vector
noncomputable def anchors (x y : Raw) (i j : ℕ) : Bool :=
  decide (x.kind=0 ∧ y.kind=0 ∧
    ((i=2 ∧ j=1 ∧ Descriptor.rank D.validBlock x.block+1=Descriptor.rank D.validBlock y.block) ∨
      (i=1 ∧ j=2 ∧ Descriptor.rank D.validBlock y.block+1=Descriptor.rank D.validBlock x.block)))
noncomputable def incidence (a b : ℕ) : Bool :=
  let x := D.unpack (a/3)
  let y := D.unpack (b/3)
  D.internal x y (a%3) (b%3) || D.roots x y (a%3) (b%3) || D.anchors x y (a%3) (b%3)
noncomputable def portData : Descriptor.PortData where
  bound := D.bound
  valid := D.valid
  color := D.color
  colorBound := D.colorBound
  incidence := D.incidence
end Data

variable {B : Type uVariable4} (P : Presentation B) (F : B → PrefixParts.Data)
variable (hDim : ∀b,(F b).dimension≤6) (ε : Bit)

def MatchingGood (D : Data) (W : Wiring F) : Prop :=
  ∀c d : Channel F,D.matching (P.encode c.1*D.channelBound+c.2.val.val)
    (P.encode d.1*D.channelBound+d.2.val.val)=true ↔ W.mate c=d

 theorem rootPorts_tree [Fintype B] (W : Wiring F) (b d : B) (t : (F b).Tree ε) (u : (F d).Tree ε)
    (i j : Fin 3) :
    (W.rootPorts F ε).edge ((⟨b,.inr (.inr t)⟩ : Wiring.Vertex F ε),i) (⟨d,.inr (.inr u)⟩,j) ↔
    i=0 ∧ j=0 ∧ ∃hc : t.channel.val≠0,∃hd : u.channel.val≠0,
      t.height=(F b).root t.channel ∧ u.height=(F d).root u.channel ∧
      W.mate ⟨b,t.channel,hc⟩=⟨d,u.channel,hd⟩ ∧ Wiring.pad t.bits=Wiring.pad u.bits := by
  constructor
  · rintro ⟨⟨⟨b',c⟩,t'⟩,⟨⟨d',e⟩,u'⟩,hx,hy,hm,hp⟩
    have hi := congrArg Prod.snd hx
    have hj := congrArg Prod.snd hy
    have hb := congrArg (fun a : Wiring.Vertex F ε × Fin 3=>a.1.1) hx
    have hd := congrArg (fun a : Wiring.Vertex F ε × Fin 3=>a.1.1) hy
    dsimp only [Wiring.rootVertex] at hb hd
    subst b'; subst d'
    have ht : t=t'.val := Sum.inr_injective (Sum.inr_injective
      (eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Prod.fst hx)).2))
    have hu : u=u'.val := Sum.inr_injective (Sum.inr_injective
      (eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Prod.fst hy)).2))
    subst t; subst u
    have hc := t'.property.1
    have he := u'.property.1
    refine ⟨hi,hj,by rw [hc]; exact c.property,by rw [he]; exact e.property,?_,?_,?_,hp⟩
    · rw [hc]; exact t'.property.2
    · rw [he]; exact u'.property.2
    · simpa only [hc,he] using hm
  · rintro ⟨rfl,rfl,hc,hd,ht,hu,hm,hp⟩
    exact ⟨⟨⟨b,t.channel,hc⟩,t,rfl,ht⟩,⟨⟨d,u.channel,hd⟩,u,rfl,hu⟩,rfl,rfl,hm,hp⟩

 theorem raw_roots [Fintype B] {D : Data} (h : Good P F hDim ε D) (W : Wiring F)
    (hm : MatchingGood P F D W) (x y : Wiring.Vertex F ε) (i j : Fin 3) :
    D.roots (raw P F hDim ε x) (raw P F hDim ε y) i.val j.val=true ↔
      (W.rootPorts F ε).edge (x,i) (y,j) := by
  rcases x with ⟨b,x | (x | t)⟩ <;> rcases y with ⟨d,y | (y | u)⟩
  all_goals try {
    simp only [Data.roots,raw,show (0:ℕ)≠2 by omega,show (1:ℕ)≠2 by omega,false_and,and_false,
      decide_false,Bool.false_and,Bool.false_eq_true]
    constructor
    · exact False.elim
    · rintro ⟨a,b,ha,hb,_,_⟩
      first
      | have hx := congrArg (fun z : Wiring.Vertex F ε => (raw P F hDim ε z).kind) (congrArg Prod.fst ha)
        simp only [Wiring.rootVertex,raw] at hx
        omega
      | have hy := congrArg (fun z : Wiring.Vertex F ε => (raw P F hDim ε z).kind) (congrArg Prod.fst hb)
        simp only [Wiring.rootVertex,raw] at hy
        omega }
  rw [rootPorts_tree F ε W]
  simp only [Data.roots,raw,h.root,Bool.and_eq_true,decide_eq_true_eq,
    PrefixAlphabet.paddedEqual_encode,true_and]
  constructor
  · rintro ⟨⟨⟨hi,hj,hc,hd,ht,hu⟩,hmatch⟩,hp⟩
    exact ⟨Fin.ext hi,Fin.ext hj,hc,hd,ht,hu,(hm ⟨b,t.channel,hc⟩ ⟨d,u.channel,hd⟩).mp hmatch,hp⟩
  · rintro ⟨hi,hj,hc,hd,ht,hu,hmatch,hp⟩
    exact ⟨⟨⟨congrArg Fin.val hi,congrArg Fin.val hj,hc,hd,ht,hu⟩,
      (hm ⟨b,t.channel,hc⟩ ⟨d,u.channel,hd⟩).mpr hmatch⟩,hp⟩

end VariableWL.PrefixDescriptor

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

namespace VariableWL.PrefixAlphabet.TotalProgram
open Computation.Stack.PolyRecipe Computation.Stack.Recipe
variable {n : ℕ}
noncomputable def paddedEqual (I J : Expr n) : Expr n :=
  choose (conj (lt I (numeral vectorCount)) (lt J (numeral vectorCount)))
    (Program.paddedEqual I J) (literal [false])
end VariableWL.PrefixAlphabet.TotalProgram

namespace VariableWL.PrefixDescriptor.Program
attribute [local instance] Classical.propDecidable
open Computation.Stack.PolyRecipe Computation.Stack.Recipe
variable {n : ℕ}

structure RawExpr (n : ℕ) where
  block : Expr n
  kind : Expr n
  channel : Expr n
  height : Expr n
  vector : Expr n

def RawExpr.up (x : RawExpr n) : RawExpr (n+1) :=
  ⟨x.block.up,x.kind.up,x.channel.up,x.height.up,x.vector.up⟩

structure Listing (n : ℕ) where
  blocks : Expr n
  validBlock : Expr (n+1)
  channelBound : Expr n
  dimension : Expr (n+1)
  channels : Expr (n+1)
  root : Expr (n+2)
  order : Expr (n+2)
  legal : Expr (n+2)
  matching : Expr (n+2)

namespace Listing
variable (D : Listing n)
def up : Listing (n+1) where
  blocks := D.blocks.up
  validBlock := underOne D.validBlock
  channelBound := D.channelBound.up
  dimension := underOne D.dimension
  channels := underOne D.channels
  root := underTwo D.root
  order := underTwo D.order
  legal := underTwo D.legal
  matching := underTwo D.matching

noncomputable def sortBound : Expr n := mul (mul (mul D.blocks (numeral 3)) D.channelBound) (numeral 7)
noncomputable def bound : Expr n := mul D.sortBound (numeral PrefixAlphabet.vectorCount)
noncomputable def tag (x : RawExpr n) : Expr n :=
  add (mul (add (mul (add (mul x.block (numeral 3)) x.kind) D.channelBound) x.channel) (numeral 7)) x.height
noncomputable def unpack (I : Expr n) : RawExpr n :=
  let a := div I (numeral PrefixAlphabet.vectorCount)
  let b := div a (numeral 7)
  let c := div b D.channelBound
  ⟨div c (numeral 3),mod c (numeral 3),mod b D.channelBound,mod a (numeral 7),
    mod I (numeral PrefixAlphabet.vectorCount)⟩

noncomputable def treePossible (x : RawExpr n) (J : Expr n) : Expr n :=
  conj (applyNat₂ D.legal x.block J)
    (eq (PrefixAlphabet.TotalProgram.prefixCode (applyNat₂ D.order x.block x.channel) x.height J) x.vector)
noncomputable def treeValid (x : RawExpr n) : Expr n :=
  conj (conj (le (applyNat₂ D.root x.block x.channel) x.height) (le x.height (applyNat D.dimension x.block)))
    (any (numeral PrefixAlphabet.vectorCount) (D.up.treePossible x.up (input 0)))
noncomputable def validRaw (x : RawExpr n) : Expr n :=
  conj (applyNat D.validBlock x.block)
    (disj (conj (conj (eq x.kind (numeral 0)) (eq x.channel (numeral 0)))
      (conj (eq x.height (numeral 0)) (eq x.vector (numeral 0))))
    (disj (conj (conj (conj (eq x.kind (numeral 1)) (lt x.channel (applyNat D.channels x.block)))
        (eq x.height (numeral 0))) (applyNat₂ D.legal x.block x.vector))
      (conj (conj (eq x.kind (numeral 2)) (lt x.channel (applyNat D.channels x.block))) (D.treeValid x))))
noncomputable def valid (I : Expr n) : Expr n := D.validRaw (D.unpack I)

noncomputable def sortValid (x : RawExpr n) : Expr n :=
  conj (applyNat D.validBlock x.block)
    (disj (conj (eq x.kind (numeral 0)) (conj (eq x.channel (numeral 0)) (eq x.height (numeral 0))))
      (disj (conj (eq x.kind (numeral 1)) (conj (lt x.channel (applyNat D.channels x.block)) (eq x.height (numeral 0))))
        (conj (eq x.kind (numeral 2)) (conj (lt x.channel (applyNat D.channels x.block))
          (conj (le (applyNat₂ D.root x.block x.channel) x.height) (le x.height (applyNat D.dimension x.block)))))))
noncomputable def sortPredicate (I : Expr n) : Expr n := D.sortValid (D.unpack (mul I (numeral PrefixAlphabet.vectorCount)))
noncomputable def color (I : Expr n) : Expr n := add (numeral 1)
  (count (D.tag (D.unpack I)) (D.up.sortPredicate (input 0)))
noncomputable def colorBound : Expr n := add (numeral 1) (count D.sortBound (D.up.sortPredicate (input 0)))

noncomputable def forward (x y : RawExpr n) : Expr n :=
  disj (disj (disj
    (conj (conj (eq x.kind (numeral 0)) (eq y.kind (numeral 2)))
      (conj (eq y.channel (numeral 0)) (eq y.height (numeral 0))))
    (conj (conj (eq x.kind (numeral 1)) (eq y.kind (numeral 1)))
      (conj (eq (add x.channel (numeral 1)) y.channel) (eq x.vector y.vector))))
    (conj (conj (eq x.kind (numeral 2)) (eq y.kind (numeral 2)))
      (conj (eq x.channel y.channel) (conj (eq (add x.height (numeral 1)) y.height)
        (eq (PrefixAlphabet.TotalProgram.trim x.height y.vector) x.vector)))))
    (conj (conj (eq x.kind (numeral 2)) (eq y.kind (numeral 1)))
      (conj (eq x.channel y.channel) (conj (eq x.height (applyNat D.dimension x.block))
        (eq x.vector (PrefixAlphabet.TotalProgram.prefixCode (applyNat₂ D.order x.block y.channel)
          (applyNat D.dimension x.block) y.vector)))))
noncomputable def slot (x y : RawExpr n) : Expr n :=
  choose (eq x.kind (numeral 0)) (numeral 0)
    (choose (eq x.kind (numeral 1))
      (choose (eq y.kind (numeral 1)) (choose (lt y.channel x.channel) (numeral 0) (numeral 1)) (numeral 2))
      (choose (eq y.kind (numeral 0)) (numeral 0)
        (choose (eq y.kind (numeral 1)) (numeral 1)
          (choose (lt y.height x.height) (numeral 0)
            (choose (lt x.height (applyNat D.dimension x.block))
              (add (PrefixAlphabet.TotalProgram.bit y.vector x.height) (numeral 1)) (numeral 1))))))
noncomputable def internal (x y : RawExpr n) (I J : Expr n) : Expr n :=
  conj (conj (eq x.block y.block) (disj (D.forward x y) (D.forward y x)))
    (conj (eq I (D.slot x y)) (eq J (D.slot y x)))

noncomputable def roots (x y : RawExpr n) (I J : Expr n) : Expr n :=
  conj (conj (conj (conj (eq x.kind (numeral 2)) (eq y.kind (numeral 2)))
    (conj (conj (eq I (numeral 0)) (eq J (numeral 0)))
      (conj (conj (neg (eq x.channel (numeral 0))) (neg (eq y.channel (numeral 0))))
        (conj (eq x.height (applyNat₂ D.root x.block x.channel)) (eq y.height (applyNat₂ D.root y.block y.channel))))))
    (applyNat₂ D.matching (add (mul x.block D.channelBound) x.channel) (add (mul y.block D.channelBound) y.channel)))
    (PrefixAlphabet.TotalProgram.paddedEqual x.vector y.vector)
noncomputable def anchors (x y : RawExpr n) (I J : Expr n) : Expr n :=
  conj (conj (eq x.kind (numeral 0)) (eq y.kind (numeral 0)))
    (disj (conj (conj (eq I (numeral 2)) (eq J (numeral 1)))
      (eq (add (count x.block D.validBlock) (numeral 1)) (count y.block D.validBlock)))
      (conj (conj (eq I (numeral 1)) (eq J (numeral 2)))
        (eq (add (count y.block D.validBlock) (numeral 1)) (count x.block D.validBlock))))
noncomputable def incidence (I J : Expr n) : Expr n :=
  let x := D.unpack (div I (numeral 3))
  let y := D.unpack (div J (numeral 3))
  let i := mod I (numeral 3)
  let j := mod J (numeral 3)
  disj (disj (D.internal x y i j) (D.roots x y i j)) (D.anchors x y i j)

noncomputable def portListing : PortListing n where
  bound := D.bound
  valid := D.up.valid (input 0)
  color := D.up.color (input 0)
  colorBound := D.colorBound
  incidence := D.up.up.incidence (input 0) (input 1)
end Listing
end VariableWL.PrefixDescriptor.Program

namespace VariableWL.Descriptor.Presentation
variable {A : Type uVariable1} [Fintype A] (P : Presentation A)
 theorem enumeration_val (x : A) :
    ((@VariableWL.enumeration A _ P.numbering) x).val=Descriptor.rank P.valid (P.encode x) := rfl
end VariableWL.Descriptor.Presentation

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_BlockDescriptor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8

namespace VariableWL.PrefixDescriptor
open VariableWL.Affine Descriptor PrefixParts
attribute [local instance] Classical.propDecidable
variable {B : Type uVariable1} [Fintype B] (P : Presentation B) (F : B → PrefixParts.Data)
variable (hDim : ∀b,(F b).dimension≤6) (ε : Bit)

 theorem raw_anchors {D : Data} (h : Good P F hDim ε D) (x y : Wiring.Vertex F ε) (i j : Fin 3) :
    let _ : FiniteNumbering B := P.numbering
    D.anchors (raw P F hDim ε x) (raw P F hDim ε y) i.val j.val=true ↔
      (Wiring.anchorPorts F ε).edge (x,i) (y,j) := by
  let _ : FiniteNumbering B := P.numbering
  rcases x with ⟨b,x | (x | t)⟩ <;> rcases y with ⟨d,y | (y | u)⟩
  all_goals try {
    simp only [Data.anchors,raw,one_ne_zero,show (2:ℕ)≠0 by omega,false_and,and_false,decide_false,Bool.false_eq_true]
    constructor
    · exact False.elim
    · rintro (⟨a,b,ha,hb,_⟩ | ⟨a,b,hb,ha,_⟩)
      all_goals first
      | have hx := congrArg (fun z : Wiring.Vertex F ε => (raw P F hDim ε z).kind) (congrArg Prod.fst ha)
        simp only [Wiring.anchor,raw] at hx
        omega
      | have hy := congrArg (fun z : Wiring.Vertex F ε => (raw P F hDim ε z).kind) (congrArg Prod.fst hb)
        simp only [Wiring.anchor,raw] at hy
        omega }
  cases x; cases y
  simp only [Data.anchors,raw,h.validBlock,true_and,decide_eq_true_eq]
  constructor
  · rintro (⟨hi,hj,he⟩ | ⟨hi,hj,he⟩)
    · left; exact ⟨b,d,by congr; exact Fin.ext hi,by congr; exact Fin.ext hj,by simpa only [Presentation.enumeration_val] using he⟩
    · right; exact ⟨d,b,by congr; exact Fin.ext hj,by congr; exact Fin.ext hi,by simpa only [Presentation.enumeration_val] using he⟩
  · rintro (⟨a,c,ha,hc,he⟩ | ⟨a,c,hc,ha,he⟩)
    · have hb : b=a := congrArg (fun z : Wiring.Vertex F ε × Fin 3=>z.1.1) ha
      have hd : d=c := congrArg (fun z : Wiring.Vertex F ε × Fin 3=>z.1.1) hc
      subst a; subst c
      exact Or.inl ⟨congrArg (fun z : Wiring.Vertex F ε × Fin 3=>z.2.val) ha,
        congrArg (fun z : Wiring.Vertex F ε × Fin 3=>z.2.val) hc,by simpa only [Presentation.enumeration_val] using he⟩
    · have hb : b=c := congrArg (fun z : Wiring.Vertex F ε × Fin 3=>z.1.1) ha
      have hd : d=a := congrArg (fun z : Wiring.Vertex F ε × Fin 3=>z.1.1) hc
      subst a; subst c
      exact Or.inr ⟨congrArg (fun z : Wiring.Vertex F ε × Fin 3=>z.2.val) ha,
        congrArg (fun z : Wiring.Vertex F ε × Fin 3=>z.2.val) hc,by simpa only [Presentation.enumeration_val] using he⟩

 theorem raw_incidence {D : Data} (h : Good P F hDim ε D) (W : Wiring F) (hm : MatchingGood P F D W)
    (x y : Wiring.Vertex F ε) (i j : Fin 3) :
    let _ : FiniteNumbering B := P.numbering
    D.incidence (3*D.pack (raw P F hDim ε x)+i.val) (3*D.pack (raw P F hDim ε y)+j.val)=true ↔
      (W.ports F ε).edge (x,i) (y,j) := by
  let _ : FiniteNumbering B := P.numbering
  have hi : i.val<3 := i.isLt
  have hj : j.val<3 := j.isLt
  have hx := raw_bounds P F hDim ε h x
  have hy := raw_bounds P F hDim ε h y
  simp only [Data.incidence,Nat.mul_add_div (by omega : 0<3),Nat.mul_add_mod,Nat.mod_eq_of_lt hi,
    Nat.mod_eq_of_lt hj,Nat.div_eq_of_lt hi,Nat.div_eq_of_lt hj,Nat.add_zero,
    D.unpack_pack _ hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2,
    D.unpack_pack _ hy.2.1 hy.2.2.1 hy.2.2.2.1 hy.2.2.2.2,
    Bool.or_eq_true,raw_internal P F hDim ε h,raw_roots P F hDim ε h W hm,raw_anchors P F hDim ε h,
    Wiring.ports,SubcubicRealization.PortGraph.union,or_assoc]

 omit [Fintype B] in
 theorem tag_sort {D : Data} (x : Wiring.Vertex F ε) :
    D.tag (raw P F hDim ε x)=D.tag (sortRaw P F (Wiring.sort F x)) := by
  rcases x with ⟨b,x | (x | x)⟩ <;> rfl

 theorem raw_color {D : Data} (h : Good P F hDim ε D) (Q : Presentation (Wiring.SortTag F))
    (hq : Q.valid=D.sortPredicate) (he : ∀s,Q.encode s=D.tag (sortRaw P F s))
    (x : Wiring.Vertex F ε) :
    let _ : FiniteNumbering (Wiring.SortTag F) := Q.numbering
    D.color (D.pack (raw P F hDim ε x))=Wiring.color F x := by
  let _ : FiniteNumbering (Wiring.SortTag F) := Q.numbering
  have hx := raw_bounds P F hDim ε h x
  rw [Data.color,D.unpack_pack _ hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2,tag_sort P F hDim ε]
  simp only [Wiring.color,Presentation.enumeration_val,hq,he,Nat.add_comm]

 omit [Fintype B] in
 theorem color_le {D : Data} (h : Good P F hDim ε D) (x : Wiring.Vertex F ε) :
    D.color (D.pack (raw P F hDim ε x))≤D.colorBound := by
  have hx := raw_bounds P F hDim ε h x
  rw [Data.color,D.unpack_pack _ hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2,Data.colorBound]
  apply Nat.add_le_add_left
  exact Descriptor.rank_mono D.sortPredicate (D.tag_lt _ hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1).le

end VariableWL.PrefixDescriptor

namespace VariableWL.Descriptor.Presentation
attribute [local instance] Classical.propDecidable
variable {A : Type uVariable2} {B : Type uVariable3}

noncomputable def product (P : Presentation A) (Q : Presentation B) : Presentation (A × B) :=
  ofEncoding (P.bound*Q.bound) (fun i=>P.valid (i/Q.bound) && Q.valid (i%Q.bound))
    (fun x=>P.encode x.1*Q.bound+Q.encode x.2)
    (fun x=>by have hp := P.encode_lt x.1; have hq := Q.encode_lt x.2; nlinarith)
    (fun x=>by
      have hq := Q.encode_lt x.2
      simp only [PrefixDescriptor.Data.join_div _ _ _ (by omega : 0<Q.bound) hq,
        PrefixDescriptor.Data.join_mod _ _ _ hq,P.encode_valid,Q.encode_valid,Bool.and_self])
    (by
      intro x y he
      have hx := Q.encode_lt x.2
      have hy := Q.encode_lt y.2
      have hm := congrArg (fun i=>i%Q.bound) he
      have hd := congrArg (fun i=>i/Q.bound) he
      dsimp only at hm hd
      rw [PrefixDescriptor.Data.join_mod _ _ _ hx,PrefixDescriptor.Data.join_mod _ _ _ hy] at hm
      rw [PrefixDescriptor.Data.join_div _ _ _ (by omega : 0<Q.bound) hx,
        PrefixDescriptor.Data.join_div _ _ _ (by omega : 0<Q.bound) hy] at hd
      exact Prod.ext (P.encode_injective hd) (Q.encode_injective hm))
    (by
      intro i hi hv
      have hq : 0<Q.bound := by nlinarith
      obtain ⟨hpv,hqv⟩ := Bool.and_eq_true_iff.mp hv
      let a : Valid P.bound P.valid := ⟨⟨i/Q.bound,(Nat.div_lt_iff_lt_mul hq).mpr hi⟩,hpv⟩
      let b : Valid Q.bound Q.valid := ⟨⟨i%Q.bound,Nat.mod_lt _ hq⟩,hqv⟩
      refine ⟨(P.equiv a,Q.equiv b),?_⟩
      simp only [encode,Equiv.symm_apply_apply]
      change (i/Q.bound)*Q.bound+i%Q.bound=i
      rw [Nat.mul_comm,Nat.div_add_mod])

@[simp] theorem product_encode (P : Presentation A) (Q : Presentation B) (x : A × B) :
    (P.product Q).encode x=P.encode x.1*Q.bound+Q.encode x.2 := rfl

noncomputable def sum (P : Presentation A) (Q : Presentation B) : Presentation (A ⊕ B) :=
  ofEncoding (P.bound+Q.bound) (fun i=>if i<P.bound then P.valid i else Q.valid (i-P.bound))
    (Sum.elim P.encode (fun b=>P.bound+Q.encode b))
    (fun x=>by cases x with
      | inl a => exact (P.encode_lt a).trans_le (Nat.le_add_right _ _)
      | inr b => have := Q.encode_lt b; dsimp; omega)
    (fun x=>by cases x with
      | inl a => exact (ite_eq_left (P.encode_lt a)).trans (P.encode_valid a)
      | inr b => simpa only [Sum.elim_inr,not_lt.mpr (Nat.le_add_right _ _),ite_false,Nat.add_sub_cancel_left] using Q.encode_valid b)
    (by
      rintro (a|a) (b|b) he
      · exact congrArg Sum.inl (P.encode_injective he)
      · have := P.encode_lt a; dsimp at he; omega
      · have := P.encode_lt b; dsimp at he; omega
      · exact congrArg Sum.inr (Q.encode_injective (Nat.add_left_cancel he)))
    (by
      intro i hi hv
      by_cases h : i<P.bound
      · rw [ite_eq_left h] at hv
        let a : Valid P.bound P.valid := ⟨⟨i,h⟩,hv⟩
        exact ⟨.inl (P.equiv a),by simp only [Sum.elim_inl,encode,Equiv.symm_apply_apply]; rfl⟩
      · rw [ite_eq_right h] at hv
        let b : Valid Q.bound Q.valid := ⟨⟨i-P.bound,by omega⟩,hv⟩
        exact ⟨.inr (Q.equiv b),by simp only [Sum.elim_inr,encode,Equiv.symm_apply_apply]; change P.bound+(i-P.bound)=i; omega⟩)

@[simp] theorem sum_inl (P : Presentation A) (Q : Presentation B) (a : A) :
    (P.sum Q).encode (.inl a)=P.encode a := rfl
@[simp] theorem sum_inr (P : Presentation A) (Q : Presentation B) (b : B) :
    (P.sum Q).encode (.inr b)=P.bound+Q.encode b := rfl

noncomputable def filter (P : Presentation A) (Q : ℕ → Bool) (T : A → Prop)
    (h : ∀a,Q (P.encode a)=true ↔ T a) : Presentation {a // T a} :=
  ofEncoding P.bound (fun i=>P.valid i && Q i) (fun a=>P.encode a.val)
    (fun a=>P.encode_lt a.val)
    (fun a=>Bool.and_eq_true_iff.mpr ⟨P.encode_valid a.val,(h a.val).mpr a.property⟩)
    (by intro a b he; exact Subtype.ext (P.encode_injective he))
    (by
      intro i hi hv
      obtain ⟨hp,hq⟩ := Bool.and_eq_true_iff.mp hv
      let a : Valid P.bound P.valid := ⟨⟨i,hi⟩,hp⟩
      have ha : P.encode (P.equiv a)=i := by simp only [encode,Equiv.symm_apply_apply]; rfl
      exact ⟨⟨P.equiv a,(h _).mp (ha ▸ hq)⟩,ha⟩)

@[simp] theorem filter_encode (P : Presentation A) (Q : ℕ → Bool) (T : A → Prop) (h) (a : {a // T a}) :
    (P.filter Q T h).encode a=P.encode a.val := rfl

end VariableWL.Descriptor.Presentation

namespace VariableWL.PrefixDescriptor
open VariableWL.Affine Descriptor PrefixParts SubcubicRealization
attribute [local instance] Classical.propDecidable
variable {B : Type uVariable4} [Fintype B] (P : Presentation B) (F : B → PrefixParts.Data)
variable (hDim : ∀b,(F b).dimension≤6) (ε : Bit)

 omit [Fintype B] in
 theorem presentation_inverse_val {D : Data} (h : Good P F hDim ε D) (x : Wiring.Vertex F ε) :
    ((presentation P F hDim ε h).equiv.symm x).val.val=D.pack (raw P F hDim ε x) := rfl

 theorem port_sound {D : Data} (h : Good P F hDim ε D) (W : Wiring F) (hm : MatchingGood P F D W) :
    D.portData.Sound := by
  let _ : FiniteNumbering B := P.numbering
  let Q := presentation P F hDim ε h
  apply PortData.sound_of_encoding D.portData Q.equiv.symm Q.equiv.symm.bijective (W.ports F ε)
  · intro x
    exact color_le P F hDim ε h x
  · intro x y i j
    exact raw_incidence P F hDim ε h W hm x y i j

noncomputable def uncoloredIso {D : Data} (h : Good P F hDim ε D) (W : Wiring F)
    (hm : MatchingGood P F D W) (S : Presentation (Wiring.SortTag F))
    (hs : S.valid=D.sortPredicate) (he : ∀s,S.encode s=D.tag (sortRaw P F s)) :
    let _ : FiniteNumbering B := P.numbering
    let _ : FiniteNumbering (Wiring.SortTag F) := S.numbering
    (D.portData.expanded.graph (D.portData.sound_expanded (port_sound P F hDim ε h W hm))).graph ≃g
      Wiring.uncolored F W ε := by
  let _ : FiniteNumbering B := P.numbering
  let _ : FiniteNumbering (Wiring.SortTag F) := S.numbering
  let Q := presentation P F hDim ε h
  have hc (a : D.portData.Owners) : Wiring.color F (Q.equiv a)=D.color a.val.val := by
    obtain ⟨x,rfl⟩ := Q.equiv.symm.surjective a
    simpa only [Equiv.apply_symm_apply,Q,presentation_inverse_val] using (raw_color P F hDim ε h S hs he x).symm
  let E := vertexEquiv Q.equiv (fun _=>Equiv.refl (Fin 3)) hc
  let T : SubcubicRealization.graph (D.portData.ports (port_sound P F hDim ε h W hm))
      (fun a=>D.color a.val.val) ≃g Wiring.uncolored F W ε := {
    toEquiv := E
    map_rel_iff' := by
      intro x y
      apply vertexEquiv_adj
      obtain ⟨a,ha⟩ := Q.equiv.symm.surjective x.owner
      obtain ⟨b,hb⟩ := Q.equiv.symm.surjective y.owner
      change D.incidence (3*x.owner.val.val+x.port.val) (3*y.owner.val.val+y.port.val)=true ↔ _
      rw [←ha,←hb]
      simpa only [Equiv.apply_symm_apply,Equiv.refl_apply,Q,presentation_inverse_val] using raw_incidence P F hDim ε h W hm a b x.port y.port }
  exact (D.portData.graphIso (port_sound P F hDim ε h W hm)).trans T
end VariableWL.PrefixDescriptor

namespace VariableWL.Descriptor.Presentation
variable {A : Type uVariable5} {B : Type uVariable6}
def transport (P : Presentation A) (e : A ≃ B) : Presentation B := ⟨P.bound,P.valid,P.equiv.trans e⟩
@[simp] theorem transport_encode (P : Presentation A) (e : A ≃ B) (a : A) :
    (P.transport e).encode (e a)=P.encode a := by
  change ((P.equiv.symm (e.symm (e a))).val.val)=_
  rw [Equiv.symm_apply_apply]
  rfl

def fin (n : ℕ) : Presentation (Fin n) where
  bound := n
  valid _ := true
  equiv := { toFun a:=a.val, invFun a:=⟨a,rfl⟩,left_inv _:=rfl,right_inv _:=rfl }
@[simp] theorem fin_encode (n : ℕ) (a : Fin n) : (fin n).encode a=a.val := rfl

theorem count_eq_card [Fintype A] (P : Presentation A) : Descriptor.rank P.valid P.bound=Fintype.card A := by
  simpa only [Fintype.card_fin] using (Fintype.card_congr (Descriptor.rankEquiv P.bound P.valid)).symm.trans
    (Fintype.card_congr P.equiv)

end VariableWL.Descriptor.Presentation

namespace VariableWL.BlockDescriptor
open Blocks BlockCoordinates Descriptor
attribute [local instance] Classical.propDecidable
variable {r n : ℕ} {P : Type uVariable7} {E : Type uVariable8} [Fintype P] [Fintype E]
variable (J : ProductImages.Instance r P E)
variable (PB : Presentation (Block (n := n) J)) (PR : Presentation (Readout r n P E))
variable (H : ℕ → ℕ → Bool)
variable (hH : ∀b : Block (n := n) J,∀a,H (PB.encode b) (PR.encode a)=true ↔ HasReadout J b.val a)

noncomputable def properEquiv (b : Block (n := n) J) : Proper J b ≃
    {x : Block (n := n) J × Readout r n P E // x.1≠b ∧ HasReadout J b.val x.2 ∧ HasReadout J x.1.val x.2} where
  toFun p := ⟨(p.1.val,p.2.val),p.1.property,p.2.property⟩
  invFun x := ⟨⟨x.val.1,x.property.1⟩,x.val.2,x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def ProperPredicate (b i : ℕ) : Bool :=
  decide (i/PR.bound≠b) && (H b (i%PR.bound) && H (i/PR.bound) (i%PR.bound))

 omit [Fintype P] [Fintype E] in
 include hH in
 theorem properPredicate_code (b c : Block (n := n) J) (a : Readout r n P E) :
    ProperPredicate PR H (PB.encode b) (PB.encode c*PR.bound+PR.encode a)=true ↔
      c≠b ∧ HasReadout J b.val a ∧ HasReadout J c.val a := by
  have ha := PR.encode_lt a
  simp only [ProperPredicate,PrefixDescriptor.Data.join_div _ _ _ (by omega : 0<PR.bound) ha,
    PrefixDescriptor.Data.join_mod _ _ _ ha,Bool.and_eq_true,decide_eq_true_eq,
    hH]
  exact and_congr_left (fun _=>not_congr PB.encode_injective.eq_iff)

noncomputable def properPresentation (b : Block (n := n) J) : Presentation (Proper J b) :=
  ((PB.product PR).filter (ProperPredicate PR H (PB.encode b))
    (fun x=>x.1≠b ∧ HasReadout J b.val x.2 ∧ HasReadout J x.1.val x.2)
    (fun x=>properPredicate_code J PB PR H hH b x.1 x.2)).transport (properEquiv J b).symm

 omit [Fintype P] [Fintype E] in
 theorem properPresentation_valid (b : Block (n := n) J) (i : ℕ) :
    (properPresentation J PB PR H hH b).valid i=
      ((PB.valid (i/PR.bound) && PR.valid (i%PR.bound)) && ProperPredicate PR H (PB.encode b) i) := rfl

 theorem properNumber_pick (b : Block (n := n) J) (p : Proper J b) :
    let _ : ∀b : Block (n := n) J, FiniteNumbering (Proper J b) := fun b=>(properPresentation J PB PR H hH b).numbering
    Descriptor.pick (PB.bound*PR.bound) (properPresentation J PB PR H hH b).valid
      ((properNumber J b p).val.val-1)=PB.encode p.1.val*PR.bound+PR.encode p.2.val := by
  let _ : ∀b : Block (n := n) J, FiniteNumbering (Proper J b) := fun b=>(properPresentation J PB PR H hH b).numbering
  dsimp only
  change Descriptor.pick _ _ (Descriptor.rank _ _ + 1 - 1)=_
  rw [Nat.add_sub_cancel]
  exact Descriptor.pick_rank _ _ _ ((properPresentation J PB PR H hH b).encode_lt p)
    ((properPresentation J PB PR H hH b).encode_valid p)
end VariableWL.BlockDescriptor

namespace VariableWL.BlockDescriptor
structure Core where
  blocks : ℕ
  validBlock : ℕ → Bool
  reads : ℕ
  validRead : ℕ → Bool
  has : ℕ → ℕ → Bool
  dimension : ℕ → ℕ
  readDimension : ℕ → ℕ
  zeroOrder : ℕ → ℕ
  readOrder : ℕ → ℕ → ℕ
  legal : ℕ → ℕ → Bool
namespace Core
variable (D : Core)
def properBound : ℕ := D.blocks*D.reads
def channelBound : ℕ := D.properBound+1
def proper (b i : ℕ) : Bool :=
  (D.validBlock (i/D.reads) && D.validRead (i%D.reads)) &&
    (decide (i/D.reads≠b) && (D.has b (i%D.reads) && D.has (i/D.reads) (i%D.reads)))
def channels (b : ℕ) : ℕ := Descriptor.rank (D.proper b) D.properBound+1
def select (b c : ℕ) : ℕ := Descriptor.pick D.properBound (D.proper b) (c-1)
def other (b c : ℕ) : ℕ := D.select b c/D.reads
def readout (b c : ℕ) : ℕ := D.select b c%D.reads
def root (b c : ℕ) : ℕ := if c=0 then 0 else D.readDimension (D.readout b c)
def order (b c : ℕ) : ℕ := if c=0 then D.zeroOrder b else D.readOrder b (D.readout b c)
def matching (i j : ℕ) : Bool :=
  decide (D.other (i/D.channelBound) (i%D.channelBound)=j/D.channelBound ∧
    D.other (j/D.channelBound) (j%D.channelBound)=i/D.channelBound ∧
    D.readout (i/D.channelBound) (i%D.channelBound)=D.readout (j/D.channelBound) (j%D.channelBound))
def toPrefix : PrefixDescriptor.Data where
  blocks := D.blocks
  validBlock := D.validBlock
  channelBound := D.channelBound
  dimension := D.dimension
  channels := D.channels
  root := D.root
  order := D.order
  legal := D.legal
  matching := D.matching
 theorem channelBound_pos : 0<D.channelBound := Nat.zero_lt_succ _
 theorem channels_le (b : ℕ) : D.channels b≤D.channelBound := by
  apply Nat.add_le_add_right
  exact List.countP_le_length.trans_eq List.length_range
end Core
end VariableWL.BlockDescriptor

namespace VariableWL.BlockDescriptor.Program
open Computation.Stack.PolyRecipe Computation.Stack.Recipe
variable {n : ℕ}
structure Listing (n : ℕ) where
  blocks : Expr n
  validBlock : Expr (n+1)
  reads : Expr n
  validRead : Expr (n+1)
  has : Expr (n+2)
  dimension : Expr (n+1)
  readDimension : Expr (n+1)
  zeroOrder : Expr (n+1)
  readOrder : Expr (n+2)
  legal : Expr (n+2)
namespace Listing
variable (D : Listing n)
def eval (v : Env n) : Core where
  blocks := D.blocks.number v
  validBlock i := D.validBlock.bit (cons (List.replicate i true) v)
  reads := D.reads.number v
  validRead i := D.validRead.bit (cons (List.replicate i true) v)
  has i j := D.has.bit (cons (List.replicate i true) (cons (List.replicate j true) v))
  dimension i := D.dimension.number (cons (List.replicate i true) v)
  readDimension i := D.readDimension.number (cons (List.replicate i true) v)
  zeroOrder i := D.zeroOrder.number (cons (List.replicate i true) v)
  readOrder i j := D.readOrder.number (cons (List.replicate i true) (cons (List.replicate j true) v))
  legal i j := D.legal.bit (cons (List.replicate i true) (cons (List.replicate j true) v))
def up : Listing (n+1) where
  blocks := D.blocks.up
  validBlock := underOne D.validBlock
  reads := D.reads.up
  validRead := underOne D.validRead
  has := underTwo D.has
  dimension := underOne D.dimension
  readDimension := underOne D.readDimension
  zeroOrder := underOne D.zeroOrder
  readOrder := underTwo D.readOrder
  legal := underTwo D.legal

def properBound : Expr n := mul D.blocks D.reads
def channelBound : Expr n := add D.properBound (numeral 1)
def proper (B I : Expr n) : Expr n :=
  conj (conj (applyNat D.validBlock (div I D.reads)) (applyNat D.validRead (mod I D.reads)))
    (conj (neg (eq (div I D.reads) B))
      (conj (applyNat₂ D.has B (mod I D.reads)) (applyNat₂ D.has (div I D.reads) (mod I D.reads))))
def channels (B : Expr n) : Expr n := add (count D.properBound (D.up.proper B.up (input 0))) (numeral 1)
def select (B C : Expr n) : Expr n := Computation.Stack.PolyRecipe.select D.properBound (D.up.proper B.up (input 0)) (sub C (numeral 1))
def other (B C : Expr n) : Expr n := div (D.select B C) D.reads
def readout (B C : Expr n) : Expr n := mod (D.select B C) D.reads
def root (B C : Expr n) : Expr n := choose (eq C (numeral 0)) (numeral 0) (applyNat D.readDimension (D.readout B C))
def order (B C : Expr n) : Expr n := choose (eq C (numeral 0)) (applyNat D.zeroOrder B) (applyNat₂ D.readOrder B (D.readout B C))
def matching (I J : Expr n) : Expr n :=
  conj (eq (D.other (div I D.channelBound) (mod I D.channelBound)) (div J D.channelBound))
    (conj (eq (D.other (div J D.channelBound) (mod J D.channelBound)) (div I D.channelBound))
      (eq (D.readout (div I D.channelBound) (mod I D.channelBound)) (D.readout (div J D.channelBound) (mod J D.channelBound))))

def toPrefix : PrefixDescriptor.Program.Listing n where
  blocks := D.blocks
  validBlock := D.validBlock
  channelBound := D.channelBound
  dimension := D.dimension
  channels := D.up.channels (input 0)
  root := D.up.up.root (input 0) (input 1)
  order := D.up.up.order (input 0) (input 1)
  legal := D.legal
  matching := D.up.up.matching (input 0) (input 1)
end Listing
end VariableWL.BlockDescriptor.Program

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_BlockCatalog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6

namespace VariableWL.BlockDescriptor
open Blocks BlockCoordinates Descriptor VariableWL.Affine
attribute [local instance] Classical.propDecidable
variable {r n : ℕ} {P : Type uVariable1} {E : Type uVariable2} [Fintype P] [Fintype E]
variable (J : ProductImages.Instance r P E) (hr : 2≤r) (hn : 0<n) (marked : Fin r)
variable (PB : Presentation (Block (n := n) J)) (PR : Presentation (Readout r n P E))
variable (hDim : ∀b : Block (n := n) J,Fintype.card (Coordinate J b.val)≤6) (ε : Bit)

structure Good (D : Core) : Prop where
  blocks : D.blocks=PB.bound
  reads : D.reads=PR.bound
  validBlock : D.validBlock=PB.valid
  validRead : D.validRead=PR.valid
  has : ∀b a,D.has (PB.encode b) (PR.encode a)=true ↔ HasReadout J b.val a
  dimension : ∀b,D.dimension (PB.encode b)=Fintype.card (Coordinate J b.val)
  readDimension : ∀a,D.readDimension (PR.encode a)=readoutDimension J a
  zeroOrder : ∀b,D.zeroOrder (PB.encode b)=PrefixAlphabet.encodeOrder (hDim b) (Equiv.refl _)
  readOrder : ∀b a (ha : HasReadout J b.val a),D.readOrder (PB.encode b) (PR.encode a)=
    PrefixAlphabet.encodeOrder (hDim b) (exists_readout_order J hr hn ha).choose
  legal : ∀b i,D.legal (PB.encode b) i=true ↔ ∃z : Valuation J marked ε b,
    PrefixAlphabet.encode (hDim b) (BlockCoordinates.encode J b.val z.val)=i

variable {D : Core} (h : Good J hr hn marked PB PR hDim ε D)
@[instance_reducible] noncomputable def properNumberings : (b : Block (n := n) J) → FiniteNumbering (Proper J b) :=
  fun b=>(properPresentation J PB PR D.has h.has b).numbering

 omit [Fintype P] [Fintype E] in
 theorem proper_eq (b : Block (n := n) J) :
    D.proper (PB.encode b)=(properPresentation J PB PR D.has h.has b).valid := by
  funext i
  simp only [Core.proper,h.reads,h.validBlock,h.validRead,properPresentation_valid,ProperPredicate]
 include h in
 theorem channels_eq (b : Block (n := n) J) : D.channels (PB.encode b)=Fintype.card (Proper J b)+1 := by
  rw [Core.channels,proper_eq J hr hn marked PB PR hDim ε h]
  have he : D.properBound=(properPresentation J PB PR D.has h.has b).bound := by
    change D.blocks*D.reads=PB.bound*PR.bound
    rw [h.blocks,h.reads]
  rw [he,Presentation.count_eq_card]

 theorem select_number (b : Block (n := n) J) (p : Proper J b) :
    let _ : (b : Block (n := n) J) → FiniteNumbering (Proper J b) := properNumberings J hr hn marked PB PR hDim ε h
    D.select (PB.encode b) (properNumber J b p).val.val=PB.encode p.1.val*PR.bound+PR.encode p.2.val := by
  let _ : (b : Block (n := n) J) → FiniteNumbering (Proper J b) := properNumberings J hr hn marked PB PR hDim ε h
  dsimp only
  rw [Core.select,proper_eq J hr hn marked PB PR hDim ε h]
  change Descriptor.pick (D.blocks*D.reads) _ _=_
  rw [h.blocks,h.reads]
  exact properNumber_pick J PB PR D.has h.has b p

 theorem other_number (b : Block (n := n) J) (p : Proper J b) :
    let _ : (b : Block (n := n) J) → FiniteNumbering (Proper J b) := properNumberings J hr hn marked PB PR hDim ε h
    D.other (PB.encode b) (properNumber J b p).val.val=PB.encode p.1.val := by
  let _ : (b : Block (n := n) J) → FiniteNumbering (Proper J b) := properNumberings J hr hn marked PB PR hDim ε h
  dsimp only
  rw [Core.other,select_number J hr hn marked PB PR hDim ε h,h.reads]
  have ha := PR.encode_lt p.2.val
  exact PrefixDescriptor.Data.join_div _ _ _ (by omega) ha

 theorem readout_number (b : Block (n := n) J) (p : Proper J b) :
    let _ : (b : Block (n := n) J) → FiniteNumbering (Proper J b) := properNumberings J hr hn marked PB PR hDim ε h
    D.readout (PB.encode b) (properNumber J b p).val.val=PR.encode p.2.val := by
  let _ : (b : Block (n := n) J) → FiniteNumbering (Proper J b) := properNumberings J hr hn marked PB PR hDim ε h
  dsimp only
  rw [Core.readout,select_number J hr hn marked PB PR hDim ε h,h.reads]
  exact PrefixDescriptor.Data.join_mod _ _ _ (PR.encode_lt p.2.val)

 theorem prefix_good :
    let _ : (b : Block (n := n) J) → FiniteNumbering (Proper J b) := properNumberings J hr hn marked PB PR hDim ε h
    PrefixDescriptor.Good PB (data J hr hn marked) hDim ε D.toPrefix := by
  let _ : (b : Block (n := n) J) → FiniteNumbering (Proper J b) := properNumberings J hr hn marked PB PR hDim ε h
  dsimp only
  refine ⟨h.blocks,h.validBlock,D.channelBound_pos,?_,h.dimension,channels_eq J hr hn marked PB PR hDim ε h,?_,?_,?_⟩
  · intro b
    change Fintype.card (Proper J b)+1≤D.channelBound
    rw [←channels_eq J hr hn marked PB PR hDim ε h]
    exact D.channels_le _
  · intro b c
    change D.root (PB.encode b) c.val=channelRoot J b c
    by_cases hc : c.val=0
    · simp only [Core.root,ite_eq_left hc,channelRoot,dite_eq_left hc]
    · obtain ⟨p,hp⟩ := (properNumber J b).surjective ⟨c,hc⟩
      have hc' : (properNumber J b p).val=c := congrArg Subtype.val hp
      rw [←hc']
      change D.root (PB.encode b) (properNumber J b p).val.val=channelRoot J b (properNumber J b p).val
      rw [channelRoot_number,Core.root,ite_eq_right (properNumber J b p).property,
        readout_number J hr hn marked PB PR hDim ε h,h.readDimension]
  · intro b c
    change D.order (PB.encode b) c.val=PrefixAlphabet.encodeOrder (hDim b) (channelOrder J hr hn b c)
    by_cases hc : c.val=0
    · simp only [Core.order,ite_eq_left hc,channelOrder,dite_eq_left hc,h.zeroOrder]
    · obtain ⟨p,hp⟩ := (properNumber J b).surjective ⟨c,hc⟩
      have hc' : (properNumber J b p).val=c := congrArg Subtype.val hp
      rw [←hc']
      change D.order (PB.encode b) (properNumber J b p).val.val=
        PrefixAlphabet.encodeOrder (hDim b) (channelOrder J hr hn b (properNumber J b p).val)
      rw [channelOrder_number,Core.order,ite_eq_right (properNumber J b p).property,
        readout_number J hr hn marked PB PR hDim ε h,h.readOrder b p.2.val p.2.property.1]
  · intro b i
    constructor
    · intro hi
      obtain ⟨z,hz⟩ := (h.legal b i).mp hi
      exact ⟨valuationEquiv J hr hn marked b ε z,hz⟩
    · rintro ⟨z,hz⟩
      obtain ⟨y,rfl⟩ := (valuationEquiv J hr hn marked b ε).surjective z
      exact (h.legal b i).mpr ⟨y,hz⟩

 theorem matching_good :
    let _ : (b : Block (n := n) J) → FiniteNumbering (Proper J b) := properNumberings J hr hn marked PB PR hDim ε h
    PrefixDescriptor.MatchingGood PB (data J hr hn marked) D.toPrefix (wiring J hr hn marked) := by
  let _ : (b : Block (n := n) J) → FiniteNumbering (Proper J b) := properNumberings J hr hn marked PB PR hDim ε h
  dsimp only
  intro c d
  obtain ⟨⟨b,p⟩,rfl⟩ := (channelEquiv J hr hn marked).surjective c
  obtain ⟨⟨e,q⟩,rfl⟩ := (channelEquiv J hr hn marked).surjective d
  rw [mate_channel]
  have hp : (properNumber J b p).val.val<D.channelBound :=
    (properNumber J b p).val.isLt.trans_le (by rw [←channels_eq J hr hn marked PB PR hDim ε h]; exact D.channels_le _)
  have hq : (properNumber J e q).val.val<D.channelBound :=
    (properNumber J e q).val.isLt.trans_le (by rw [←channels_eq J hr hn marked PB PR hDim ε h]; exact D.channels_le _)
  change D.matching (PB.encode b*D.channelBound+(properNumber J b p).val.val)
    (PB.encode e*D.channelBound+(properNumber J e q).val.val)=true ↔ _
  simp only [Core.matching,PrefixDescriptor.Data.join_div _ _ _ D.channelBound_pos hp,
    PrefixDescriptor.Data.join_div _ _ _ D.channelBound_pos hq,
    PrefixDescriptor.Data.join_mod _ _ _ hp,PrefixDescriptor.Data.join_mod _ _ _ hq,
    other_number J hr hn marked PB PR hDim ε h,readout_number J hr hn marked PB PR hDim ε h,decide_eq_true_eq]
  rw [PB.encode_injective.eq_iff,PB.encode_injective.eq_iff,PR.encode_injective.eq_iff]
  rw [(channelEquiv J hr hn marked).injective.eq_iff]
  constructor
  · rintro ⟨he,hb,ha⟩
    subst e
    rcases q with ⟨⟨c,hc⟩,⟨a,haq⟩⟩
    dsimp only at hb ha
    subst c
    subst a
    rfl
  · intro he
    have he' := congrArg Sigma.fst he
    have hb' := congrArg (fun x : Σ b : Block (n := n) J,Proper J b=>x.2.1.val) he
    have ha' := congrArg (fun x : Σ b : Block (n := n) J,Proper J b=>x.2.2.val) he
    exact ⟨he',hb'.symm,ha'⟩
end VariableWL.BlockDescriptor

namespace VariableWL.Descriptor.Presentation
attribute [local instance] Classical.propDecidable
noncomputable def boolean : Presentation Bool :=
  ofEncoding 2 (fun _=>true) Bool.toNat (by intro b; cases b <;> decide) (fun _=>rfl)
    (by intro a b h; cases a <;> cases b <;> simp_all)
    (by intro i hi _; interval_cases i; exact ⟨false,rfl⟩; exact ⟨true,rfl⟩)
@[simp] theorem boolean_encode (b : Bool) : boolean.encode b=b.toNat := rfl
end VariableWL.Descriptor.Presentation

namespace VariableWL.BlockCatalog
open Blocks Subdivision Descriptor
attribute [local instance] Classical.propDecidable
variable {r n : ℕ} {P : Type uVariable3} {E : Type uVariable4}
variable (PP : Presentation P) (PE : Presentation E)
noncomputable def vertex : Presentation (Vertex P E n) := PP.sum (PE.product (Presentation.fin n))
noncomputable def link : Presentation (Link E n) := PE.product (Presentation.fin (n+1))

def horizontalEquiv : ((Fin r × Vertex P E n) × (Bool × Bool)) ≃ Horizontal r n P E where
  toFun a := ⟨a.1.1,a.1.2,a.2.1,a.2.2⟩
  invFun h := ((h.row,h.type),(h.first,h.last))
  left_inv _ := rfl
  right_inv _ := rfl

def squareEquiv : ((Fin r × Link E n) × (Bool × Bool)) ≃ Square r n E where
  toFun a := ⟨a.1.1,a.1.2,a.2.1,a.2.2⟩
  invFun h := ((h.row,h.link),(h.first,h.last))
  left_inv _ := rfl
  right_inv _ := rfl

def verticalEquiv : ((Fin r × Link E n) × Bool) ≃ Vertical r n E where
  toFun a := ⟨a.1.1,a.1.2,a.2⟩
  invFun h := ((h.row,h.link),h.label)
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def horizontal : Presentation (Horizontal r n P E) :=
  (((Presentation.fin r).product (vertex (n := n) PP PE)).product
    (Presentation.boolean.product Presentation.boolean)).transport horizontalEquiv
noncomputable def square : Presentation (Square r n E) :=
  (((Presentation.fin r).product (link (n := n) PE)).product
    (Presentation.boolean.product Presentation.boolean)).transport squareEquiv
noncomputable def vertical : Presentation (Vertical r n E) :=
  (((Presentation.fin r).product (link (n := n) PE)).product Presentation.boolean).transport verticalEquiv
noncomputable def raw : Presentation (RawBlock r n P E) := (horizontal PP PE).sum (square PE)
noncomputable def readout : Presentation (Readout r n P E) := (horizontal PP PE).sum (vertical PE)

 theorem horizontal_encode (h : Horizontal r n P E) :
    (horizontal PP PE).encode h=(h.row.val*(PP.bound+PE.bound*n)+(vertex PP PE).encode h.type)*4+
      h.first.toNat*2+h.last.toNat := by
  change (h.row.val*(PP.bound+PE.bound*n)+(vertex PP PE).encode h.type)*(2*2)+
    (h.first.toNat*2+h.last.toNat)=_
  omega
 theorem square_encode (s : Square r n E) :
    (square PE).encode s=(s.row.val*(PE.bound*(n+1))+(link PE).encode s.link)*4+
      s.first.toNat*2+s.last.toNat := by
  change (s.row.val*(PE.bound*(n+1))+(link PE).encode s.link)*(2*2)+
    (s.first.toNat*2+s.last.toNat)=_
  omega
 theorem vertex_inl (p : P) : (vertex (n := n) PP PE).encode (.inl p)=PP.encode p := rfl
 theorem vertex_inr (e : E) (j : Fin n) :
    (vertex PP PE).encode (.inr (e,j))=PP.bound+PE.encode e*n+j.val := by
  change PP.bound+(PE.encode e*n+j.val)=_; omega
 theorem link_encode (e : E) (j : Fin (n+1)) : (link PE).encode (e,j)=PE.encode e*(n+1)+j.val := rfl

structure Data where
  rows : ℕ
  internal : ℕ
  reals : ℕ
  comparisons : ℕ
  validReal : ℕ → Bool
  validComparison : ℕ → Bool
  source : ℕ → ℕ
  target : ℕ → ℕ
  domain : ℕ → ℕ → ℕ → Bool
  map : ℕ → ℕ → ℕ → ℕ

namespace Data
variable (D : Data)
def vertices : ℕ := D.reals+D.comparisons*D.internal
def links : ℕ := D.comparisons*(D.internal+1)
def horizontals : ℕ := D.rows*D.vertices*4
def squares : ℕ := D.rows*D.links*4
def verticals : ℕ := D.rows*D.links*2
def blocks : ℕ := D.horizontals+D.squares
def reads : ℕ := D.horizontals+D.verticals
def validVertex (i : ℕ) : Bool := if i<D.reals then D.validReal i else D.validComparison ((i-D.reals)/D.internal)
def validLink (i : ℕ) : Bool := D.validComparison (i/(D.internal+1))
def validH (i : ℕ) : Bool := D.validVertex (i/4%D.vertices)
def validS (i : ℕ) : Bool := D.validLink (i/4%D.links)
def validV (i : ℕ) : Bool := D.validLink (i/2%D.links)
def rawValid (i : ℕ) : Bool := if i<D.horizontals then D.validH i else D.validS (i-D.horizontals)
def readValid (i : ℕ) : Bool := if i<D.horizontals then D.validH i else D.validV (i-D.horizontals)
def hrow (i : ℕ) : ℕ := i/4/D.vertices
def htype (i : ℕ) : ℕ := i/4%D.vertices
def srow (i : ℕ) : ℕ := i/4/D.links
def slink (i : ℕ) : ℕ := i/4%D.links
def first (i : ℕ) : ℕ := i%4/2
def last (i : ℕ) : ℕ := i%2
def next (i : ℕ) : ℕ := (i+1)%D.rows
def labels (t i a : ℕ) : Bool := if t<D.reals then true else D.domain ((t-D.reals)/D.internal) i a
def horizontalValid (i : ℕ) : Bool := D.labels (D.htype i) (D.hrow i) (first i) && D.labels (D.htype i) (D.next (D.hrow i)) (last i)
def squareValid (i : ℕ) : Bool := D.domain (D.slink i/(D.internal+1)) (D.srow i) (first i) &&
  D.domain (D.slink i/(D.internal+1)) (D.next (D.srow i)) (last i)
def validBlock (i : ℕ) : Bool := D.rawValid i &&
  (if i<D.horizontals then D.horizontalValid i else D.squareValid (i-D.horizontals))
def left (l : ℕ) : ℕ := if l%(D.internal+1)=0 then D.source (l/(D.internal+1)) else
  D.reals+(l/(D.internal+1))*D.internal+(l%(D.internal+1)-1)
def right (l : ℕ) : ℕ := if l%(D.internal+1)=D.internal then D.target (l/(D.internal+1)) else
  D.reals+(l/(D.internal+1))*D.internal+l%(D.internal+1)
def output (l i a : ℕ) : ℕ := if l%(D.internal+1)=D.internal then D.map (l/(D.internal+1)) i a else a
def horizontalCode (i t a b : ℕ) : ℕ := (i*D.vertices+t)*4+a*2+b
def verticalCode (i l a : ℕ) : ℕ := D.horizontals+(i*D.links+l)*2+a
def squareLeft (s : ℕ) : ℕ := D.horizontalCode (D.srow s) (D.left (D.slink s)) (first s) (last s)
def squareRight (s : ℕ) : ℕ := D.horizontalCode (D.srow s) (D.right (D.slink s))
  (D.output (D.slink s) (D.srow s) (first s)) (D.output (D.slink s) (D.next (D.srow s)) (last s))
def squareBottom (s : ℕ) : ℕ := D.verticalCode (D.srow s) (D.slink s) (first s)
def squareTop (s : ℕ) : ℕ := D.verticalCode (D.next (D.srow s)) (D.slink s) (last s)
def has (b a : ℕ) : Bool := if b<D.horizontals then decide (a=b) else
  let s:=b-D.horizontals
  decide (a=D.squareLeft s ∨ a=D.squareRight s ∨ a=D.squareBottom s ∨ a=D.squareTop s)
end Data

structure Good (J : ProductImages.Instance r P E) (D : Data) : Prop where
  rows : D.rows=r
  internal : D.internal=n
  reals : D.reals=PP.bound
  comparisons : D.comparisons=PE.bound
  validReal : D.validReal=PP.valid
  validComparison : D.validComparison=PE.valid
  source : ∀e,D.source (PE.encode e)=PP.encode (J.source e)
  target : ∀e,D.target (PE.encode e)=PP.encode (J.target e)
  domain : ∀e i a,D.domain (PE.encode e) i.val a.toNat=true ↔ a ∈ J.domain e i
  map : ∀e i a,D.map (PE.encode e) i.val a.toNat=(J.map e i a).toNat
end VariableWL.BlockCatalog

namespace VariableWL.BlockCatalog
open Blocks Subdivision Descriptor
attribute [local instance] Classical.propDecidable
variable {r n : ℕ} {P : Type uVariable5} {E : Type uVariable6}
variable (PP : Presentation P) (PE : Presentation E) (J : ProductImages.Instance r P E)
variable {D : Data} (h : Good (n := n) PP PE J D)
include h

 theorem vertices_eq : D.vertices=(vertex (n := n) PP PE).bound := by
  change D.reals+D.comparisons*D.internal=PP.bound+PE.bound*n
  rw [h.reals,h.comparisons,h.internal]
 theorem links_eq : D.links=(link (n := n) PE).bound := by
  change D.comparisons*(D.internal+1)=PE.bound*(n+1)
  rw [h.comparisons,h.internal]
 theorem horizontals_eq : D.horizontals=(horizontal (r := r) (n := n) PP PE).bound := by
  change D.rows*D.vertices*4=r*(PP.bound+PE.bound*n)*(2*2)
  rw [h.rows,vertices_eq PP PE J h]
  rfl
 theorem squares_eq : D.squares=(square (r := r) (n := n) PE).bound := by
  change D.rows*D.links*4=r*(PE.bound*(n+1))*(2*2)
  rw [h.rows,links_eq PP PE J h]
  rfl
 theorem verticals_eq : D.verticals=(vertical (r := r) (n := n) PE).bound := by
  change D.rows*D.links*2=r*(PE.bound*(n+1))*2
  rw [h.rows,links_eq PP PE J h]
  rfl
 theorem blocks_eq : D.blocks=(raw (r := r) (n := n) PP PE).bound := by
  change D.horizontals+D.squares=_
  rw [horizontals_eq PP PE J h,squares_eq PP PE J h]
  rfl
 theorem reads_eq : D.reads=(readout (r := r) (n := n) PP PE).bound := by
  change D.horizontals+D.verticals=_
  rw [horizontals_eq PP PE J h,verticals_eq PP PE J h]
  rfl

 theorem validVertex_eq : D.validVertex=(vertex (n := n) PP PE).valid := by
  funext i
  change (if i<D.reals then D.validReal i else D.validComparison ((i-D.reals)/D.internal))=
    (if i<PP.bound then PP.valid i else (PE.valid ((i-PP.bound)/n) && true))
  simp only [h.reals,h.validReal,h.validComparison,h.internal,Bool.and_true]
 theorem validLink_eq : D.validLink=(link (n := n) PE).valid := by
  funext i
  change D.validComparison (i/(D.internal+1))= (PE.valid (i/(n+1)) && true)
  simp only [h.validComparison,h.internal,Bool.and_true]
 theorem validH_eq : D.validH=(horizontal (r := r) (n := n) PP PE).valid := by
  funext i
  change D.validVertex (i/4%D.vertices)=
    ((true && (vertex PP PE).valid (i/4%(vertex (n := n) PP PE).bound)) && (true && true))
  simp only [validVertex_eq PP PE J h,vertices_eq PP PE J h,Bool.true_and,Bool.and_true]
 theorem validS_eq : D.validS=(square (r := r) (n := n) PE).valid := by
  funext i
  change D.validLink (i/4%D.links)=
    ((true && (link PE).valid (i/4%(link (n := n) PE).bound)) && (true && true))
  simp only [validLink_eq PP PE J h,links_eq PP PE J h,Bool.true_and,Bool.and_true]
 theorem validV_eq : D.validV=(vertical (r := r) (n := n) PE).valid := by
  funext i
  change D.validLink (i/2%D.links)=
    ((true && (link PE).valid (i/2%(link (n := n) PE).bound)) && true)
  simp only [validLink_eq PP PE J h,links_eq PP PE J h,Bool.true_and,Bool.and_true]
 theorem rawValid_eq : D.rawValid=(raw (r := r) (n := n) PP PE).valid := by
  funext i
  change (if i<D.horizontals then D.validH i else D.validS (i-D.horizontals))=_
  simp only [horizontals_eq PP PE J h,validH_eq PP PE J h,validS_eq PP PE J h]
  rfl
 theorem readValid_eq : D.readValid=(readout (r := r) (n := n) PP PE).valid := by
  funext i
  change (if i<D.horizontals then D.validH i else D.validV (i-D.horizontals))=_
  simp only [horizontals_eq PP PE J h,validH_eq PP PE J h,validV_eq PP PE J h]
  rfl

 omit h in
 theorem boolPair_lt (a b : Bool) : a.toNat*2+b.toNat<4 := by cases a <;> cases b <;> decide
 omit h in
 theorem boolPair_first (a b : Bool) : (a.toNat*2+b.toNat)/2=a.toNat := by cases a <;> cases b <;> decide
 omit h in
 theorem packed_div (q : ℕ) (a b : Bool) : (q*4+a.toNat*2+b.toNat)/4=q := by
  rw [Nat.add_assoc]
  exact PrefixDescriptor.Data.join_div _ _ _ (by decide) (boolPair_lt a b)
 omit h in
 theorem packed_first (q : ℕ) (a b : Bool) : Data.first (q*4+a.toNat*2+b.toNat)=a.toNat := by
  unfold Data.first
  rw [Nat.add_assoc,PrefixDescriptor.Data.join_mod _ _ _ (boolPair_lt a b),boolPair_first]
 omit h in
 theorem packed_last (q : ℕ) (a b : Bool) : Data.last (q*4+a.toNat*2+b.toNat)=b.toNat := by
  unfold Data.last
  cases a <;> cases b <;> simp only [Bool.toNat_false,Bool.toNat_true] <;> omega

 theorem horizontal_parts (x : Horizontal r n P E) :
    D.hrow ((horizontal PP PE).encode x)=x.row.val ∧
    D.htype ((horizontal PP PE).encode x)=(vertex PP PE).encode x.type ∧
    Data.first ((horizontal PP PE).encode x)=x.first.toNat ∧
    Data.last ((horizontal PP PE).encode x)=x.last.toNat := by
  have hx := (vertex (n := n) PP PE).encode_lt x.type
  have hv := vertices_eq PP PE J h
  have hp : 0<(vertex (n := n) PP PE).bound := by omega
  simp only [horizontal_encode,Data.hrow,Data.htype,packed_div,packed_first,packed_last,hv]
  change (x.row.val*(vertex (n := n) PP PE).bound+(vertex PP PE).encode x.type)/(vertex PP PE).bound=x.row.val ∧
    (x.row.val*(vertex (n := n) PP PE).bound+(vertex PP PE).encode x.type)%(vertex PP PE).bound=_ ∧ _
  simp only [PrefixDescriptor.Data.join_div _ _ _ hp hx,PrefixDescriptor.Data.join_mod _ _ _ hx,and_self]

 theorem square_parts (x : Square r n E) :
    D.srow ((square PE).encode x)=x.row.val ∧ D.slink ((square PE).encode x)=(link PE).encode x.link ∧
    Data.first ((square PE).encode x)=x.first.toNat ∧ Data.last ((square PE).encode x)=x.last.toNat := by
  have hx := (link (n := n) PE).encode_lt x.link
  have hv := links_eq PP PE J h
  have hp : 0<(link (n := n) PE).bound := by omega
  simp only [square_encode,Data.srow,Data.slink,packed_div,packed_first,packed_last,hv]
  change (x.row.val*(link (n := n) PE).bound+(link PE).encode x.link)/(link PE).bound=x.row.val ∧
    (x.row.val*(link (n := n) PE).bound+(link PE).encode x.link)%(link PE).bound=_ ∧ _
  simp only [PrefixDescriptor.Data.join_div _ _ _ hp hx,PrefixDescriptor.Data.join_mod _ _ _ hx,and_self]

 theorem next_eq (i : Fin r) : D.next i.val=(finRotate r i).val := by
  have : NeZero r := i.neZero
  rw [Data.next,h.rows,finRotate_apply,Fin.val_add]
  simp only [Fin.val_one',Nat.add_mod_mod]

 theorem labels_code (t : Vertex P E n) (i : Fin r) (a : Bool) :
    D.labels ((vertex PP PE).encode t) i.val a.toNat=true ↔ a ∈ J.labels t i := by
  cases t with
  | inl p => simp only [Data.labels,vertex_inl,h.reals,ite_eq_left (PP.encode_lt p),ProductImages.Instance.labels,Finset.mem_univ]
  | inr q =>
    rcases q with ⟨e,j⟩
    simp only [Data.labels,vertex_inr,h.reals,not_lt.mpr (by omega : PP.bound≤PP.bound+PE.encode e*n+j.val),ite_false]
    have he : PP.bound+PE.encode e*n+j.val-PP.bound=PE.encode e*n+j.val := by omega
    rw [he,h.internal,PrefixDescriptor.Data.join_div _ _ _ (by omega : 0<n) j.isLt]
    exact h.domain e i a

 theorem horizontal_valid (x : Horizontal r n P E) :
    D.horizontalValid ((horizontal PP PE).encode x)=true ↔ ValidHorizontal J x := by
  obtain ⟨hrw,ht,hf,hl⟩ := horizontal_parts PP PE J h x
  rw [Data.horizontalValid,hrw,ht,hf,hl,next_eq PP PE J h,Bool.and_eq_true]
  exact and_congr (labels_code PP PE J h x.type x.row x.first)
    (labels_code PP PE J h x.type (finRotate r x.row) x.last)

 theorem square_valid (x : Square r n E) :
    D.squareValid ((square PE).encode x)=true ↔ ValidSquare J x := by
  obtain ⟨hrw,ht,hf,hl⟩ := square_parts PP PE J h x
  rw [Data.squareValid,hrw,ht,hf,hl,next_eq PP PE J h,h.internal,link_encode,
    PrefixDescriptor.Data.join_div _ _ _ (by omega : 0<n+1) x.link.2.isLt,Bool.and_eq_true]
  exact and_congr (h.domain x.link.1 x.row x.first) (h.domain x.link.1 (finRotate r x.row) x.last)

 theorem block_predicate (b : RawBlock r n P E) :
    (if (raw PP PE).encode b<D.horizontals then D.horizontalValid ((raw PP PE).encode b)
      else D.squareValid ((raw PP PE).encode b-D.horizontals))=true ↔ Valid J b := by
  cases b with
  | inl x =>
    change (if (horizontal PP PE).encode x<D.horizontals then _ else _)=true ↔ _
    rw [ite_eq_left (by rw [horizontals_eq PP PE J h]; exact (horizontal PP PE).encode_lt x)]
    exact horizontal_valid PP PE J h x
  | inr x =>
    change (if (horizontal PP PE).bound+(square PE).encode x<D.horizontals then _ else _)=true ↔ _
    rw [horizontals_eq PP PE J h,ite_eq_right (by omega)]
    change D.squareValid ((horizontal PP PE).bound+(square PE).encode x-(horizontal PP PE).bound)=true ↔ _
    rw [Nat.add_sub_cancel_left]
    exact square_valid PP PE J h x

noncomputable def block : Presentation (Block (n := n) J) :=
  (raw PP PE).filter (fun i=>if i<D.horizontals then D.horizontalValid i else D.squareValid (i-D.horizontals))
    (Valid J) (block_predicate PP PE J h)
 theorem block_encode (b : Block (n := n) J) : (block PP PE J h).encode b=(raw PP PE).encode b.val := rfl
 theorem block_bound : (block PP PE J h).bound=D.blocks := (blocks_eq PP PE J h).symm
 theorem block_valid : (block PP PE J h).valid=D.validBlock := by
  funext i
  change ((raw PP PE).valid i && _) = (D.rawValid i && _)
  rw [rawValid_eq PP PE J h]

 theorem left_code (l : Link E n) : D.left ((link PE).encode l)=(vertex PP PE).encode (Subdivision.left J.source l) := by
  rcases l with ⟨e,j⟩
  have hj := j.isLt
  simp only [Data.left,h.internal,link_encode,PrefixDescriptor.Data.join_div _ _ _ (by omega : 0<n+1) hj,
    PrefixDescriptor.Data.join_mod _ _ _ hj]
  by_cases hz : j.val=0
  · rw [ite_eq_left hz,Subdivision.left,dite_eq_left hz,vertex_inl,h.source]
  · rw [ite_eq_right hz,Subdivision.left,dite_eq_right hz,vertex_inr,h.reals]

 theorem right_code (l : Link E n) : D.right ((link PE).encode l)=(vertex PP PE).encode (Subdivision.right J.target l) := by
  rcases l with ⟨e,j⟩
  have hj := j.isLt
  simp only [Data.right,h.internal,link_encode,PrefixDescriptor.Data.join_div _ _ _ (by omega : 0<n+1) hj,
    PrefixDescriptor.Data.join_mod _ _ _ hj]
  by_cases hz : j.val=n
  · rw [ite_eq_left hz,Subdivision.right,dite_eq_left hz,vertex_inl,h.target]
  · rw [ite_eq_right hz,Subdivision.right,dite_eq_right hz,vertex_inr,h.reals]

 theorem output_code (l : Link E n) (i : Fin r) (a : Bool) :
    D.output ((link PE).encode l) i.val a.toNat=(matchOutput J l i a).toNat := by
  rcases l with ⟨e,j⟩
  have hj := j.isLt
  simp only [Data.output,h.internal,link_encode,PrefixDescriptor.Data.join_div _ _ _ (by omega : 0<n+1) hj,
    PrefixDescriptor.Data.join_mod _ _ _ hj,matchOutput]
  split_ifs <;> first | exact h.map e i a | rfl

 theorem horizontalCode_eq (x : Horizontal r n P E) :
    D.horizontalCode x.row.val ((vertex PP PE).encode x.type) x.first.toNat x.last.toNat=(horizontal PP PE).encode x := by
  rw [Data.horizontalCode,horizontal_encode,vertices_eq PP PE J h]
  rfl
 theorem verticalCode_eq (x : Vertical r n E) :
    D.verticalCode x.row.val ((link PE).encode x.link) x.label.toNat=(readout PP PE).encode (.inr x) := by
  rw [Data.verticalCode,links_eq PP PE J h,horizontals_eq PP PE J h]
  change _=(horizontal PP PE).bound+((x.row.val*(link (n := n) PE).bound+(link PE).encode x.link)*2+x.label.toNat)
  omega
 theorem square_faces (s : Square r n E) :
    D.squareLeft ((square PE).encode s)=(readout PP PE).encode (.inl (Blocks.squareLeft J s)) ∧
    D.squareRight ((square PE).encode s)=(readout PP PE).encode (.inl (Blocks.squareRight J s)) ∧
    D.squareBottom ((square PE).encode s)=(readout PP PE).encode (.inr (Blocks.squareBottom s)) ∧
    D.squareTop ((square PE).encode s)=(readout PP PE).encode (.inr (Blocks.squareTop s)) := by
  obtain ⟨hrw,ht,hf,hl⟩ := square_parts PP PE J h s
  simp only [Data.squareLeft,Data.squareRight,Data.squareBottom,Data.squareTop,hrw,ht,hf,hl,
    next_eq PP PE J h,left_code PP PE J h,right_code PP PE J h,output_code PP PE J h]
  exact ⟨horizontalCode_eq PP PE J h (Blocks.squareLeft J s),
    horizontalCode_eq PP PE J h (Blocks.squareRight J s),
    verticalCode_eq PP PE J h (Blocks.squareBottom s),verticalCode_eq PP PE J h (Blocks.squareTop s)⟩

 theorem has_code (b : Block (n := n) J) (a : Readout r n P E) :
    D.has ((block PP PE J h).encode b) ((readout PP PE).encode a)=true ↔ HasReadout J b.val a := by
  rw [block_encode,Data.has]
  cases he : b.val with
  | inl x =>
    change (if (horizontal PP PE).encode x<D.horizontals then _ else _)=true ↔ _
    rw [ite_eq_left (by rw [horizontals_eq PP PE J h]; exact (horizontal PP PE).encode_lt x),decide_eq_true_eq]
    change (readout PP PE).encode a=(readout PP PE).encode (.inl x) ↔ a=.inl x
    exact (readout PP PE).encode_injective.eq_iff
  | inr s =>
    change (if (horizontal PP PE).bound+(square PE).encode s<D.horizontals then _ else _)=true ↔ _
    rw [horizontals_eq PP PE J h,ite_eq_right (by omega)]
    have hs : (raw PP PE).encode (.inr s)-(horizontal (r := r) (n := n) PP PE).bound=(square PE).encode s := by
      change (horizontal PP PE).bound+(square PE).encode s-(horizontal PP PE).bound=_
      omega
    dsimp only
    rw [hs]
    obtain ⟨hl,hr,hb,ht⟩ := square_faces PP PE J h s
    simp only [hl,hr,hb,ht,decide_eq_true_eq,(readout PP PE).encode_injective.eq_iff,HasReadout]
end VariableWL.BlockCatalog

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}
def underThree (P : Expr (n+3)) : Expr (n+4) :=
  P.reindex (Fin.cons 0 (Fin.cons 1 (Fin.cons 2 (fun i=>i.succ.succ.succ.succ))))
end VariableWL.Computation.Stack.PolyRecipe

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_BlockListing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4

namespace VariableWL.BlockCatalog.Program
open Computation.Stack.PolyRecipe Computation.Stack.Recipe
variable {n : ℕ}
structure Listing (n : ℕ) where
  rows : Expr n
  internal : Expr n
  reals : Expr n
  comparisons : Expr n
  validReal : Expr (n+1)
  validComparison : Expr (n+1)
  source : Expr (n+1)
  target : Expr (n+1)
  domain : Expr (n+3)
  map : Expr (n+3)
namespace Listing
variable (D : Listing n)
def eval (v : Env n) : Data where
  rows := D.rows.number v
  internal := D.internal.number v
  reals := D.reals.number v
  comparisons := D.comparisons.number v
  validReal i := D.validReal.bit (cons (List.replicate i true) v)
  validComparison i := D.validComparison.bit (cons (List.replicate i true) v)
  source i := D.source.number (cons (List.replicate i true) v)
  target i := D.target.number (cons (List.replicate i true) v)
  domain i j a := D.domain.bit (cons (List.replicate i true) (cons (List.replicate j true) (cons (List.replicate a true) v)))
  map i j a := D.map.number (cons (List.replicate i true) (cons (List.replicate j true) (cons (List.replicate a true) v)))
def up : Listing (n+1) where
  rows := D.rows.up
  internal := D.internal.up
  reals := D.reals.up
  comparisons := D.comparisons.up
  validReal := underOne D.validReal
  validComparison := underOne D.validComparison
  source := underOne D.source
  target := underOne D.target
  domain := underThree D.domain
  map := underThree D.map

def vertices : Expr n := add D.reals (mul D.comparisons D.internal)
def links : Expr n := mul D.comparisons (add D.internal (numeral 1))
def horizontals : Expr n := mul (mul D.rows D.vertices) (numeral 4)
def squares : Expr n := mul (mul D.rows D.links) (numeral 4)
def verticals : Expr n := mul (mul D.rows D.links) (numeral 2)
def blocks : Expr n := add D.horizontals D.squares
def reads : Expr n := add D.horizontals D.verticals
def validVertex (I : Expr n) : Expr n := choose (lt I D.reals) (applyNat D.validReal I) (applyNat D.validComparison (div (sub I D.reals) D.internal))
def validLink (I : Expr n) : Expr n := applyNat D.validComparison (div I (add D.internal (numeral 1)))
def validH (I : Expr n) : Expr n := D.validVertex (mod (div I (numeral 4)) D.vertices)
def validS (I : Expr n) : Expr n := D.validLink (mod (div I (numeral 4)) D.links)
def validV (I : Expr n) : Expr n := D.validLink (mod (div I (numeral 2)) D.links)
def rawValid (I : Expr n) : Expr n := choose (lt I D.horizontals) (D.validH I) (D.validS (sub I D.horizontals))
def readValid (I : Expr n) : Expr n := choose (lt I D.horizontals) (D.validH I) (D.validV (sub I D.horizontals))
def hrow (I : Expr n) : Expr n := div (div I (numeral 4)) D.vertices
def htype (I : Expr n) : Expr n := mod (div I (numeral 4)) D.vertices
def srow (I : Expr n) : Expr n := div (div I (numeral 4)) D.links
def slink (I : Expr n) : Expr n := mod (div I (numeral 4)) D.links
def first (I : Expr n) : Expr n := div (mod I (numeral 4)) (numeral 2)
def last (I : Expr n) : Expr n := mod I (numeral 2)
def next (I : Expr n) : Expr n := mod (add I (numeral 1)) D.rows
def labels (T I A : Expr n) : Expr n := choose (lt T D.reals) (literal [true]) (applyNat₃ D.domain (div (sub T D.reals) D.internal) I A)
def horizontalValid (I : Expr n) : Expr n := conj (D.labels (D.htype I) (D.hrow I) (first I)) (D.labels (D.htype I) (D.next (D.hrow I)) (last I))
def squareValid (I : Expr n) : Expr n := conj (applyNat₃ D.domain (div (D.slink I) (add D.internal (numeral 1))) (D.srow I) (first I))
  (applyNat₃ D.domain (div (D.slink I) (add D.internal (numeral 1))) (D.next (D.srow I)) (last I))
def validBlock (I : Expr n) : Expr n := conj (D.rawValid I) (choose (lt I D.horizontals) (D.horizontalValid I) (D.squareValid (sub I D.horizontals)))
def left (L : Expr n) : Expr n := choose (eq (mod L (add D.internal (numeral 1))) (numeral 0)) (applyNat D.source (div L (add D.internal (numeral 1))))
  (add (add D.reals (mul (div L (add D.internal (numeral 1))) D.internal)) (sub (mod L (add D.internal (numeral 1))) (numeral 1)))
def right (L : Expr n) : Expr n := choose (eq (mod L (add D.internal (numeral 1))) D.internal) (applyNat D.target (div L (add D.internal (numeral 1))))
  (add (add D.reals (mul (div L (add D.internal (numeral 1))) D.internal)) (mod L (add D.internal (numeral 1))))
def output (L I A : Expr n) : Expr n := choose (eq (mod L (add D.internal (numeral 1))) D.internal)
  (applyNat₃ D.map (div L (add D.internal (numeral 1))) I A) A
def horizontalCode (I T A B : Expr n) : Expr n := add (add (mul (add (mul I D.vertices) T) (numeral 4)) (mul A (numeral 2))) B
def verticalCode (I L A : Expr n) : Expr n := add (add D.horizontals (mul (add (mul I D.links) L) (numeral 2))) A
def squareLeft (S : Expr n) : Expr n := D.horizontalCode (D.srow S) (D.left (D.slink S)) (first S) (last S)
def squareRight (S : Expr n) : Expr n := D.horizontalCode (D.srow S) (D.right (D.slink S))
  (D.output (D.slink S) (D.srow S) (first S)) (D.output (D.slink S) (D.next (D.srow S)) (last S))
def squareBottom (S : Expr n) : Expr n := D.verticalCode (D.srow S) (D.slink S) (first S)
def squareTop (S : Expr n) : Expr n := D.verticalCode (D.next (D.srow S)) (D.slink S) (last S)
def has (B A : Expr n) : Expr n := choose (lt B D.horizontals) (eq A B)
  (disj (eq A (D.squareLeft (sub B D.horizontals)))
    (disj (eq A (D.squareRight (sub B D.horizontals)))
      (disj (eq A (D.squareBottom (sub B D.horizontals))) (eq A (D.squareTop (sub B D.horizontals))))))

end Listing
end VariableWL.BlockCatalog.Program

namespace VariableWL.AffineAlphabet
open VariableWL.Affine
attribute [local instance] Classical.propDecidable

abbrev SquareCoordinate (d e : ℕ) := (Fin d ⊕ Fin e) ⊕ Bool

def squareCoordinate (d e : ℕ) : SquareVal d e ≃+ (SquareCoordinate d e → Bit) where
  toFun z := Sum.elim (Sum.elim z.1.1 z.1.2) (fun t=>if t then z.2.2 else z.2.1)
  invFun f := ((fun i=>f (.inl (.inl i)),fun i=>f (.inl (.inr i))),(f (.inr false),f (.inr true)))
  left_inv z := by cases z; rfl
  right_inv f := by
    funext i
    rcases i with (i|i)|t
    · rfl
    · rfl
    · cases t <;> rfl
  map_add' z w := by
    funext i
    rcases i with (i|i)|t
    · rfl
    · rfl
    · cases t <;> rfl

noncomputable def horizontalEncode (d : ℕ) : Vec d ≃+ Vec (Fintype.card (Fin d)) where
  toFun z := z ∘ (Fintype.equivFin (Fin d)).symm
  invFun f := f ∘ Fintype.equivFin (Fin d)
  left_inv z := by funext i; simp only [Function.comp_apply,Equiv.symm_apply_apply]
  right_inv f := by funext i; simp only [Function.comp_apply,Equiv.apply_symm_apply]
  map_add' _ _ := rfl

noncomputable def squareEncode (d e : ℕ) : SquareVal d e ≃+ Vec (Fintype.card (SquareCoordinate d e)) where
  toFun z := squareCoordinate d e z ∘ (Fintype.equivFin (SquareCoordinate d e)).symm
  invFun f := (squareCoordinate d e).symm (f ∘ Fintype.equivFin (SquareCoordinate d e))
  left_inv z := by
    simp only [Function.comp_def,Equiv.symm_apply_apply]
    exact (squareCoordinate d e).symm_apply_apply z
  right_inv f := by funext i; simp
  map_add' z w := by funext i; exact congrFun ((squareCoordinate d e).map_add z w) _

 theorem horizontal_count_le (d : Fin 3) : Fintype.card (Fin d.val)≤6 := by simp only [Fintype.card_fin]; omega
 theorem square_count_le (d e : Fin 3) : Fintype.card (SquareCoordinate d.val e.val)≤6 := by
  simp only [SquareCoordinate,Fintype.card_sum,Fintype.card_fin,Fintype.card_bool]
  omega

noncomputable instance linearFintype (d : ℕ) : Fintype (Vec d →ₗ[Bit] Bit) :=
  Fintype.ofInjective (fun L : Vec d →ₗ[Bit] Bit => (L : Vec d → Bit)) DFunLike.coe_injective

abbrev Form := Σd : Fin 3, Vec d.val →ₗ[Bit] Bit
noncomputable instance formFintype : Fintype Form := Fintype.ofFinite _
noncomputable def formNumber : Form ≃ Fin (Fintype.card Form) := Fintype.equivFin _
noncomputable def formCount : ℕ := Fintype.card Form
noncomputable def encodeForm {d : ℕ} (hd : d≤2) (L : Vec d →ₗ[Bit] Bit) : ℕ :=
  (formNumber ⟨⟨d,by omega⟩,L⟩).val
 theorem encodeForm_lt {d : ℕ} (hd : d≤2) (L : Vec d →ₗ[Bit] Bit) : encodeForm hd L<formCount :=
  (formNumber ⟨⟨d,by omega⟩,L⟩).isLt

noncomputable def horizontalLegal (d i : ℕ) : Bool :=
  decide (∃ hd : d≤2,∃z : Vec d,PrefixAlphabet.encode (by simp only [Fintype.card_fin]; omega)
    (horizontalEncode d z)=i)
noncomputable def squareLegal (l r c i : ℕ) : Bool :=
  if hl : l<formCount then if hr : r<formCount then
    let L:=formNumber.symm ⟨l,hl⟩
    let R:=formNumber.symm ⟨r,hr⟩
    decide (∃z : SquareVal L.1.val R.1.val,boundary L.2 R.2 z=(c : Bit) ∧
      PrefixAlphabet.encode (square_count_le L.1 R.1) (squareEncode L.1.val R.1.val z)=i)
  else false else false
 theorem horizontalLegal_eq {d : ℕ} (hd : d≤2) (i : ℕ) :
    horizontalLegal d i=true ↔ ∃z : Vec d,PrefixAlphabet.encode (by simp only [Fintype.card_fin]; omega)
      (horizontalEncode d z)=i := by
  simp only [horizontalLegal,decide_eq_true_eq]
  exact ⟨fun ⟨_,z,hz⟩=>⟨z,hz⟩,fun ⟨z,hz⟩=>⟨hd,z,hz⟩⟩
 theorem encodeForm_heq {d e : ℕ} (hd : d≤2) (he : e≤2)
    (L : Vec d →ₗ[Bit] Bit) (R : Vec e →ₗ[Bit] Bit) (h : d=e) (hLR : HEq L R) : encodeForm hd L=encodeForm he R := by
  subst e
  cases hLR
  rfl
 theorem decodeForm {d : ℕ} (hd : d≤2) (L : Vec d →ₗ[Bit] Bit) :
    formNumber.symm ⟨encodeForm hd L,encodeForm_lt hd L⟩=⟨⟨d,by omega⟩,L⟩ := by
  apply formNumber.injective
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  rfl
 theorem squareLegal_eq {d e : ℕ} (hd : d≤2) (he : e≤2) (L : Vec d →ₗ[Bit] Bit) (R : Vec e →ₗ[Bit] Bit)
    (c : Bit) (i : ℕ) : squareLegal (encodeForm hd L) (encodeForm he R) c.val i=true ↔
    ∃z : SquareVal d e,boundary L R z=c ∧
      PrefixAlphabet.encode (square_count_le ⟨d,by omega⟩ ⟨e,by omega⟩) (squareEncode d e z)=i := by
  rw [squareLegal,dite_eq_left (encodeForm_lt hd L),dite_eq_left (encodeForm_lt he R)]
  dsimp only
  simp only [ZMod.natCast_zmod_val,decide_eq_true_eq]
  let F (X Y : Form) : Prop := ∃z : SquareVal X.1.val Y.1.val,boundary X.2 Y.2 z=c ∧
    PrefixAlphabet.encode (square_count_le X.1 Y.1) (squareEncode X.1.val Y.1.val z)=i
  exact Iff.of_eq (congrArg₂ F (decodeForm hd L) (decodeForm he R))

end VariableWL.AffineAlphabet

namespace VariableWL.AffineAlphabet
open VariableWL.Affine
attribute [local instance] Classical.propDecidable

 theorem embedding_le {m d : ℕ} (e : Fin m ↪ Fin d) : m≤d := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective e e.injective
noncomputable def extend {m d : ℕ} (e : Fin m ↪ Fin d) : Equiv.Perm (Fin d) :=
  (Equiv.Perm.exists_extending_pair
    (fun i : Fin m=>(⟨i.val,lt_of_lt_of_le i.isLt (embedding_le e)⟩ : Fin d)) e
    (fun a b h=>Fin.ext (show a.val=b.val from congrArg (fun x : Fin d=>x.val) h)) e.injective).choose
noncomputable def horizontalEmbedding (d : ℕ) : Fin d ↪ Fin (Fintype.card (Fin d)) :=
  (Function.Embedding.refl (Fin d)).trans (Fintype.equivFin (Fin d)).toEmbedding
noncomputable def leftEmbedding (d e : ℕ) : Fin d ↪ Fin (Fintype.card (SquareCoordinate d e)) :=
  (⟨fun i=>Sum.inl (Sum.inl i),fun _ _ h=>Sum.inl.inj (Sum.inl.inj h)⟩ : Fin d ↪ SquareCoordinate d e).trans
    (Fintype.equivFin (SquareCoordinate d e)).toEmbedding
noncomputable def rightEmbedding (d e : ℕ) : Fin e ↪ Fin (Fintype.card (SquareCoordinate d e)) :=
  (⟨fun i=>Sum.inl (Sum.inr i),fun _ _ h=>Sum.inr.inj (Sum.inl.inj h)⟩ : Fin e ↪ SquareCoordinate d e).trans
    (Fintype.equivFin (SquareCoordinate d e)).toEmbedding
noncomputable def scalarEmbedding (d e : ℕ) (a : Bool) : Fin 1 ↪ Fin (Fintype.card (SquareCoordinate d e)) :=
  (⟨fun _=>Sum.inr a,fun _ _ _=>Subsingleton.elim _ _⟩ : Fin 1 ↪ SquareCoordinate d e).trans
    (Fintype.equivFin (SquareCoordinate d e)).toEmbedding
noncomputable def horizontalOrder (d : ℕ) : ℕ := if hd : d≤2 then
  PrefixAlphabet.encodeOrder (horizontal_count_le ⟨d,by omega⟩) (extend (horizontalEmbedding d)) else 0
noncomputable def squareOrder (d e a : ℕ) : ℕ := if hd : d≤2 then if he : e≤2 then
  PrefixAlphabet.encodeOrder (square_count_le ⟨d,by omega⟩ ⟨e,by omega⟩)
    (if a=0 then extend (leftEmbedding d e) else if a=1 then extend (rightEmbedding d e) else
      extend (scalarEmbedding d e (decide (a≠2)))) else 0 else 0
noncomputable def zeroOrder (d : ℕ) : ℕ := if hd : d≤6 then PrefixAlphabet.encodeOrder hd (Equiv.refl _) else 0
end VariableWL.AffineAlphabet

namespace VariableWL.BlockCoordinates
open Blocks Subdivision VariableWL.Affine
attribute [local instance] Classical.propDecidable
variable {r n : ℕ} {P : Type uVariable3} {E : Type uVariable4} (J : ProductImages.Instance r P E) (hr : 2≤r) (hn : 0<n)
 theorem coordinate_lift_unique {b : RawBlock r n P E} {a : Readout r n P E}
    (ha : HasReadout J b a) (e : Fin (readoutDimension J a) ↪ Coordinate J b)
    (he : ∀z i,coordinateEquiv J b z (e i)=readoutEquiv J a (readout J z ha) i) :
    (coordinate_lift J hr hn ha).choose=e := by
  ext i
  have hh : ∀f : Coordinate J b → Bit,f ((coordinate_lift J hr hn ha).choose i)=f (e i) := by
    intro f
    obtain ⟨z,rfl⟩ := (coordinateEquiv J b).surjective f
    exact ((coordinate_lift J hr hn ha).choose_spec z i).trans (he z i).symm
  by_contra hne
  have h := hh (fun j=>if j=e i then 1 else 0)
  simp only [ite_eq_right hne] at h
  exact zero_ne_one h

 theorem order_eq_extend {b : RawBlock r n P E} {a : Readout r n P E} (ha : HasReadout J b a) :
    (exists_readout_order J hr hn ha).choose=AffineAlphabet.extend (readoutEmbedding J hr hn ha) := rfl

 theorem embedding_horizontal (h : Horizontal r n P E) :
    readoutEmbedding J hr hn (b := .inl h) (a := .inl h) rfl=
      AffineAlphabet.horizontalEmbedding (dimension J h.type) := by
  unfold readoutEmbedding
  have he := coordinate_lift_unique J hr hn (b := .inl h) (a := .inl h) rfl (Function.Embedding.refl _) (by
    intro z i
    rw [readout_eq J hr hn (b := .inl h) (z := z) (a := .inl h) rfl ⟨rfl,HEq.rfl⟩]
    rfl)
  rw [he]
  rfl

 theorem embedding_left (s : Square r n E) :
    readoutEmbedding J hr hn (b := .inr s) (a := .inl (squareLeft J s)) (Or.inl rfl)=
      AffineAlphabet.leftEmbedding (dimension J (left J.source s.link)) (dimension J (right J.target s.link)) := by
  unfold readoutEmbedding
  have he := coordinate_lift_unique J hr hn (b := .inr s) (a := .inl (squareLeft J s)) (Or.inl rfl)
    ⟨fun i=>.inl (.inl i),fun _ _ h=>Sum.inl.inj (Sum.inl.inj h)⟩ (by
      intro z i
      rw [readout_eq J hr hn (b := .inr s) (z := z) (a := .inl (squareLeft J s)) (Or.inl rfl) (Or.inl ⟨rfl,HEq.rfl⟩)]
      rfl)
  rw [he]
  rfl

 theorem embedding_right (s : Square r n E) :
    readoutEmbedding J hr hn (b := .inr s) (a := .inl (squareRight J s)) (Or.inr (Or.inl rfl))=
      AffineAlphabet.rightEmbedding (dimension J (left J.source s.link)) (dimension J (right J.target s.link)) := by
  unfold readoutEmbedding
  have he := coordinate_lift_unique J hr hn (b := .inr s) (a := .inl (squareRight J s)) (Or.inr (Or.inl rfl))
    ⟨fun i=>.inl (.inr i),fun _ _ h=>Sum.inr.inj (Sum.inl.inj h)⟩ (by
      intro z i
      rw [readout_eq J hr hn (b := .inr s) (z := z) (a := .inl (squareRight J s)) (Or.inr (Or.inl rfl)) (Or.inr (Or.inl ⟨rfl,HEq.rfl⟩))]
      rfl)
  rw [he]
  rfl

 theorem embedding_bottom (s : Square r n E) :
    readoutEmbedding J hr hn (b := .inr s) (a := .inr (squareBottom s)) (Or.inr (Or.inr (Or.inl rfl)))=
      AffineAlphabet.scalarEmbedding (dimension J (left J.source s.link)) (dimension J (right J.target s.link)) false := by
  unfold readoutEmbedding
  have he := coordinate_lift_unique J hr hn (b := .inr s) (a := .inr (squareBottom s)) (Or.inr (Or.inr (Or.inl rfl)))
    ⟨fun _=>.inr false,fun i j _=>Fin.ext (by have hi := i.isLt; have hj := j.isLt; change i.val<1 at hi; change j.val<1 at hj; omega)⟩ (by
      intro z i
      rw [readout_eq J hr hn (b := .inr s) (z := z) (a := .inr (squareBottom s)) (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inl ⟨rfl,HEq.rfl⟩)))]
      rfl)
  rw [he]
  rfl

 theorem embedding_top (s : Square r n E) :
    readoutEmbedding J hr hn (b := .inr s) (a := .inr (squareTop s)) (Or.inr (Or.inr (Or.inr rfl)))=
      AffineAlphabet.scalarEmbedding (dimension J (left J.source s.link)) (dimension J (right J.target s.link)) true := by
  unfold readoutEmbedding
  have he := coordinate_lift_unique J hr hn (b := .inr s) (a := .inr (squareTop s)) (Or.inr (Or.inr (Or.inr rfl)))
    ⟨fun _=>.inr true,fun i j _=>Fin.ext (by have hi := i.isLt; have hj := j.isLt; change i.val<1 at hi; change j.val<1 at hj; omega)⟩ (by
      intro z i
      rw [readout_eq J hr hn (b := .inr s) (z := z) (a := .inr (squareTop s)) (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (Or.inr (Or.inr ⟨rfl,HEq.rfl⟩)))]
      rfl)
  rw [he]
  rfl
end VariableWL.BlockCoordinates

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_AffineCatalog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4

namespace VariableWL.AffineCatalog
open Blocks Subdivision Descriptor VariableWL.Affine
attribute [local instance] Classical.propDecidable
structure Data extends BlockCatalog.Data where
  realDimension : ℕ → ℕ
  leftForm : ℕ → ℕ
  rightForm : ℕ → ℕ
  leftConstant : ℕ → ℕ
  rightConstant : ℕ → ℕ
  marked : ℕ
  epsilon : ℕ
namespace Data
variable (D : Data)
def vertexDimension (t : ℕ) : ℕ := if t<D.reals then D.realDimension t else 1
def horizontalDimension (h : ℕ) : ℕ := D.vertexDimension (D.htype h)
def squareLeftDimension (s : ℕ) : ℕ := D.vertexDimension (D.left (D.slink s))
def squareRightDimension (s : ℕ) : ℕ := D.vertexDimension (D.right (D.slink s))
def dimension (b : ℕ) : ℕ := if b<D.horizontals then D.horizontalDimension b else
  D.squareLeftDimension (b-D.horizontals)+D.squareRightDimension (b-D.horizontals)+2
def readDimension (a : ℕ) : ℕ := if a<D.horizontals then D.horizontalDimension a else 1
noncomputable def linkLeft (l : ℕ) : ℕ := if l%(D.internal+1)=0 then D.leftForm (l/(D.internal+1)) else
  AffineAlphabet.encodeForm (by decide : 1≤2) (LinearMap.proj (0 : Fin 1))
noncomputable def linkRight (l : ℕ) : ℕ := if l%(D.internal+1)=D.internal then D.rightForm (l/(D.internal+1)) else
  AffineAlphabet.encodeForm (by decide : 1≤2) (LinearMap.proj (0 : Fin 1))
def linkLeftConstant (l : ℕ) : ℕ := if l%(D.internal+1)=0 then D.leftConstant (l/(D.internal+1)) else 0
def linkRightConstant (l : ℕ) : ℕ := if l%(D.internal+1)=D.internal then D.rightConstant (l/(D.internal+1)) else 0
def constant (s : ℕ) : ℕ := (D.epsilon*(if D.srow s=D.marked then
  D.linkLeftConstant (D.slink s)+D.linkRightConstant (D.slink s) else 0))%2
noncomputable def zeroOrder (b : ℕ) : ℕ := AffineAlphabet.zeroOrder (D.dimension b)
noncomputable def readOrder (b a : ℕ) : ℕ := if b<D.horizontals then AffineAlphabet.horizontalOrder (D.horizontalDimension b) else
  let s:=b-D.horizontals
  AffineAlphabet.squareOrder (D.squareLeftDimension s) (D.squareRightDimension s)
    (if a=D.squareLeft s then 0 else if a=D.squareRight s then 1 else if a=D.squareBottom s then 2 else 3)
noncomputable def legal (b i : ℕ) : Bool := if b<D.horizontals then AffineAlphabet.horizontalLegal (D.horizontalDimension b) i else
  let s:=b-D.horizontals
  AffineAlphabet.squareLegal (D.linkLeft (D.slink s)) (D.linkRight (D.slink s)) (D.constant s) i
noncomputable def core : BlockDescriptor.Core where
  blocks := D.blocks
  validBlock := D.validBlock
  reads := D.reads
  validRead := D.readValid
  has := D.has
  dimension := D.dimension
  readDimension := D.readDimension
  zeroOrder := D.zeroOrder
  readOrder := D.readOrder
  legal := D.legal
end Data
variable {r n : ℕ} {P : Type uVariable1} {E : Type uVariable2} (PP : Presentation P) (PE : Presentation E)
variable (J : ProductImages.Instance r P E) (marked : Fin r) (ε : Bit)
structure Good (D : Data) : Prop extends BlockCatalog.Good (n := n) PP PE J D.toData where
  realDimension : ∀p,D.realDimension (PP.encode p)=J.dimension p
  leftForm : ∀e,D.leftForm (PE.encode e)=AffineAlphabet.encodeForm
    (RealizationSize.dimension_le_two J (n := n) (.inl (J.source e))) (J.linearLeft e)
  rightForm : ∀e,D.rightForm (PE.encode e)=AffineAlphabet.encodeForm
    (RealizationSize.dimension_le_two J (n := n) (.inl (J.target e))) (J.linearRight e)
  leftConstant : ∀e,D.leftConstant (PE.encode e)=(J.constantLeft e).val
  rightConstant : ∀e,D.rightConstant (PE.encode e)=(J.constantRight e).val
  marked : D.marked=marked.val
  epsilon : D.epsilon=ε.val
variable {D : Data} (h : Good (n := n) PP PE J marked ε D)
include h
 theorem vertex_dimension (t : Vertex P E n) : D.vertexDimension ((BlockCatalog.vertex PP PE).encode t)=Blocks.dimension J t := by
  cases t with
  | inl p =>
    rw [Data.vertexDimension,BlockCatalog.vertex_inl,h.reals,ite_eq_left (PP.encode_lt p),h.realDimension]
    rfl
  | inr q =>
    rcases q with ⟨e,j⟩
    rw [Data.vertexDimension,BlockCatalog.vertex_inr,h.reals,ite_eq_right (by omega)]
    rfl
 theorem horizontal_dimension (x : Horizontal r n P E) : D.horizontalDimension ((BlockCatalog.horizontal PP PE).encode x)=dimension J x.type := by
  rw [Data.horizontalDimension,(BlockCatalog.horizontal_parts PP PE J h.toGood x).2.1]
  exact vertex_dimension PP PE J marked ε h x.type
 theorem square_dimensions (s : Square r n E) :
    D.squareLeftDimension ((BlockCatalog.square PE).encode s)=dimension J (left J.source s.link) ∧
    D.squareRightDimension ((BlockCatalog.square PE).encode s)=dimension J (right J.target s.link) := by
  obtain ⟨_,hl,_,_⟩ := BlockCatalog.square_parts PP PE J h.toGood s
  simp only [Data.squareLeftDimension,Data.squareRightDimension,hl,
    BlockCatalog.left_code PP PE J h.toGood,BlockCatalog.right_code PP PE J h.toGood,
    vertex_dimension PP PE J marked ε h]
  exact ⟨trivial,trivial⟩
 theorem dimension_code (b : RawBlock r n P E) : D.dimension ((BlockCatalog.raw PP PE).encode b)=Fintype.card (BlockCoordinates.Coordinate J b) := by
  cases b with
  | inl x =>
    change (if (BlockCatalog.horizontal PP PE).encode x<D.horizontals then _ else _)=_
    rw [ite_eq_left (by rw [BlockCatalog.horizontals_eq PP PE J h.toGood]; exact (BlockCatalog.horizontal PP PE).encode_lt x)]
    change D.horizontalDimension ((BlockCatalog.horizontal PP PE).encode x)=_
    rw [horizontal_dimension PP PE J marked ε h]
    simp only [BlockCoordinates.Coordinate,Fintype.card_fin]
  | inr s =>
    change (if (BlockCatalog.horizontal (r := r) (n := n) PP PE).bound+(BlockCatalog.square PE).encode s<D.horizontals then _ else _)=_
    rw [BlockCatalog.horizontals_eq PP PE J h.toGood,ite_eq_right (by omega)]
    have hs : (BlockCatalog.horizontal (r := r) (n := n) PP PE).bound+(BlockCatalog.square (r := r) (n := n) PE).encode s-
        (BlockCatalog.horizontal (r := r) (n := n) PP PE).bound=(BlockCatalog.square PE).encode s := by omega
    change (BlockCatalog.horizontal (r := r) (n := n) PP PE).bound+(BlockCatalog.square PE).encode s-
      (BlockCatalog.horizontal (r := r) (n := n) PP PE).bound=(BlockCatalog.square PE).encode s at hs
    simp only [BlockCatalog.raw,Presentation.sum_inr,Nat.add_sub_cancel_left] at *
    obtain ⟨hl,hr⟩ := square_dimensions PP PE J marked ε h s
    rw [hl,hr]
    simp only [BlockCoordinates.Coordinate,Fintype.card_sum,Fintype.card_fin,Fintype.card_bool]
 theorem read_dimension (a : Readout r n P E) : D.readDimension ((BlockCatalog.readout PP PE).encode a)=BlockCoordinates.readoutDimension J a := by
  cases a with
  | inl x =>
    change (if (BlockCatalog.horizontal PP PE).encode x<D.horizontals then _ else _)=_
    rw [ite_eq_left (by rw [BlockCatalog.horizontals_eq PP PE J h.toGood]; exact (BlockCatalog.horizontal PP PE).encode_lt x)]
    change D.horizontalDimension ((BlockCatalog.horizontal PP PE).encode x)=_
    rw [horizontal_dimension PP PE J marked ε h]
    rfl
  | inr x =>
    change (if (BlockCatalog.horizontal (r := r) (n := n) PP PE).bound+(BlockCatalog.vertical PE).encode x<D.horizontals then _ else _)=_
    rw [BlockCatalog.horizontals_eq PP PE J h.toGood,ite_eq_right (by omega)]
    rfl
 theorem link_left (l : Link E n) : D.linkLeft ((BlockCatalog.link PE).encode l)=AffineAlphabet.encodeForm
    (RealizationSize.dimension_le_two J (left J.source l)) (Blocks.linkLeft J l) := by
  rcases l with ⟨e,j⟩
  simp only [Data.linkLeft,h.internal,BlockCatalog.link_encode,
    PrefixDescriptor.Data.join_div _ _ _ (by omega : 0<n+1) j.isLt,PrefixDescriptor.Data.join_mod _ _ _ j.isLt]
  by_cases hz : j.val=0
  · simp only [ite_eq_left hz,h.leftForm,Blocks.linkLeft,Subdivision.left,dite_eq_left hz]
    apply AffineAlphabet.encodeForm_heq
    · simp [dimension,hz]
    · exact (cast_heq _ _).symm
  · simp only [ite_eq_right hz,Blocks.linkLeft,Subdivision.left,dite_eq_right hz,Blocks.dimension]
    apply AffineAlphabet.encodeForm_heq
    · simp [hz]
    · exact (cast_heq _ _).symm
 theorem link_right (l : Link E n) : D.linkRight ((BlockCatalog.link PE).encode l)=AffineAlphabet.encodeForm
    (RealizationSize.dimension_le_two J (right J.target l)) (Blocks.linkRight J l) := by
  rcases l with ⟨e,j⟩
  simp only [Data.linkRight,h.internal,BlockCatalog.link_encode,
    PrefixDescriptor.Data.join_div _ _ _ (by omega : 0<n+1) j.isLt,PrefixDescriptor.Data.join_mod _ _ _ j.isLt]
  by_cases hz : j.val=n
  · simp only [ite_eq_left hz,h.rightForm,Blocks.linkRight,Subdivision.right,dite_eq_left hz]
    apply AffineAlphabet.encodeForm_heq
    · simp [dimension,hz]
    · exact (cast_heq _ _).symm
  · simp only [ite_eq_right hz,Blocks.linkRight,Subdivision.right,dite_eq_right hz,Blocks.dimension]
    apply AffineAlphabet.encodeForm_heq
    · simp [hz]
    · exact (cast_heq _ _).symm
 theorem link_left_constant (l : Link E n) : (D.linkLeftConstant ((BlockCatalog.link PE).encode l) : Bit)=Blocks.leftConstant J l := by
  rcases l with ⟨e,j⟩
  simp only [Data.linkLeftConstant,h.internal,BlockCatalog.link_encode,
    PrefixDescriptor.Data.join_div _ _ _ (by omega : 0<n+1) j.isLt,PrefixDescriptor.Data.join_mod _ _ _ j.isLt,
    Blocks.leftConstant,h.leftConstant]
  split_ifs <;> simp only [ZMod.natCast_zmod_val,Nat.cast_zero]
 theorem link_right_constant (l : Link E n) : (D.linkRightConstant ((BlockCatalog.link PE).encode l) : Bit)=Blocks.rightConstant J l := by
  rcases l with ⟨e,j⟩
  simp only [Data.linkRightConstant,h.internal,BlockCatalog.link_encode,
    PrefixDescriptor.Data.join_div _ _ _ (by omega : 0<n+1) j.isLt,PrefixDescriptor.Data.join_mod _ _ _ j.isLt,
    Blocks.rightConstant,h.rightConstant]
  split_ifs <;> simp only [ZMod.natCast_zmod_val,Nat.cast_zero]
 theorem constant_code (s : Square r n E) : (D.constant ((BlockCatalog.square PE).encode s) : Bit)=ε*inhomogeneity J marked (.inr s) := by
  obtain ⟨hrw,hl,_,_⟩ := BlockCatalog.square_parts PP PE J h.toGood s
  rw [Data.constant]
  simp only [hrw,hl,h.marked,h.epsilon,Blocks.inhomogeneity,Blocks.linkConstant]
  rw [ZMod.natCast_mod, Nat.cast_mul,ZMod.natCast_zmod_val]
  by_cases hi : s.row=marked
  · subst marked
    rw [ite_eq_left rfl,Nat.cast_add,link_left_constant PP PE J _ ε h,link_right_constant PP PE J _ ε h]
    simp only [marker,ite_true,one_mul]
  · rw [ite_eq_right (fun he=>hi (Fin.ext he)),Nat.cast_zero,mul_zero]
    simp only [marker,ite_eq_right hi,zero_mul,mul_zero]
end VariableWL.AffineCatalog

namespace VariableWL.AffineCatalog
open Blocks Subdivision Descriptor VariableWL.Affine
attribute [local instance] Classical.propDecidable
variable {r n : ℕ} {P : Type uVariable3} {E : Type uVariable4} (PP : Presentation P) (PE : Presentation E)
variable (J : ProductImages.Instance r P E) (marked : Fin r) (ε : Bit)
variable {D : Data} (h : Good (n := n) PP PE J marked ε D)
include h
 theorem zero_order (b : RawBlock r n P E) : D.zeroOrder ((BlockCatalog.raw PP PE).encode b)=
    PrefixAlphabet.encodeOrder (RealizationSize.coordinate_card J b) (Equiv.refl _) := by
  rw [Data.zeroOrder,dimension_code PP PE J marked ε h,AffineAlphabet.zeroOrder,
    dite_eq_left (RealizationSize.coordinate_card J b)]
 theorem read_order (hr : 2≤r) (hn : 0<n) (b : RawBlock r n P E) (a : Readout r n P E)
    (ha : HasReadout J b a) : D.readOrder ((BlockCatalog.raw PP PE).encode b) ((BlockCatalog.readout PP PE).encode a)=
      PrefixAlphabet.encodeOrder (RealizationSize.coordinate_card J b) (BlockCoordinates.exists_readout_order J hr hn ha).choose := by
  cases b with
  | inl x =>
    have he : a=.inl x := ha
    subst a
    change (if (BlockCatalog.horizontal PP PE).encode x<D.horizontals then _ else _)=_
    rw [ite_eq_left (by rw [BlockCatalog.horizontals_eq PP PE J h.toGood]; exact (BlockCatalog.horizontal PP PE).encode_lt x)]
    change AffineAlphabet.horizontalOrder (D.horizontalDimension ((BlockCatalog.horizontal PP PE).encode x))=_
    rw [horizontal_dimension PP PE J marked ε h]
    have ho := BlockCoordinates.order_eq_extend J hr hn (b := .inl x) (a := .inl x) rfl
    have hb := BlockCoordinates.embedding_horizontal J hr hn x
    rw [ho,hb]
    rw [AffineAlphabet.horizontalOrder,dite_eq_left (RealizationSize.dimension_le_two J x.type)]
    rfl
  | inr s =>
    change (if (BlockCatalog.horizontal (r := r) (n := n) PP PE).bound+(BlockCatalog.square PE).encode s<D.horizontals then _ else _)=_
    rw [BlockCatalog.horizontals_eq PP PE J h.toGood,ite_eq_right (by omega)]
    have hs : (BlockCatalog.horizontal (r := r) (n := n) PP PE).bound+(BlockCatalog.square (r := r) (n := n) PE).encode s-
        (BlockCatalog.horizontal (r := r) (n := n) PP PE).bound=(BlockCatalog.square PE).encode s := by omega
    dsimp only
    change (BlockCatalog.horizontal (r := r) (n := n) PP PE).bound+(BlockCatalog.square PE).encode s-
      (BlockCatalog.horizontal (r := r) (n := n) PP PE).bound=(BlockCatalog.square PE).encode s at hs
    simp only [BlockCatalog.raw,Presentation.sum_inr,Nat.add_sub_cancel_left] at *
    obtain ⟨hl,he⟩ := square_dimensions PP PE J marked ε h s
    obtain ⟨fl,fr,fb,ft⟩ := BlockCatalog.square_faces PP PE J h.toGood s
    rw [hl,he,fl,fr,fb]
    have hi := (BlockCatalog.readout (r := r) (n := n) PP PE).encode_injective
    change a=.inl (squareLeft J s) ∨ a=.inl (squareRight J s) ∨ a=.inr (squareBottom s) ∨ a=.inr (squareTop s) at ha
    rcases ha with ha | ha | ha | ha
    all_goals subst a
    · simp only [ite_true]
      rw [AffineAlphabet.squareOrder,dite_eq_left (RealizationSize.dimension_le_two J (left J.source s.link)),
        dite_eq_left (RealizationSize.dimension_le_two J (right J.target s.link)),ite_eq_left rfl]
      have hh := (BlockCoordinates.order_eq_extend J hr hn (b := .inr s) (a := .inl (squareLeft J s)) (Or.inl rfl)).trans
        (congrArg AffineAlphabet.extend (BlockCoordinates.embedding_left J hr hn s))
      exact (congrArg (PrefixAlphabet.encodeOrder (RealizationSize.coordinate_card J (.inr s))) hh).symm
    · have hnL : (BlockCatalog.readout PP PE).encode (.inl (squareRight J s)) ≠ (BlockCatalog.readout PP PE).encode (.inl (squareLeft J s)) :=
        fun hh=>squareLeft_ne_right J hn s (Sum.inl.inj (hi hh)).symm
      simp only [hnL,ite_false,ite_true]
      rw [AffineAlphabet.squareOrder,dite_eq_left (RealizationSize.dimension_le_two J (left J.source s.link)),
        dite_eq_left (RealizationSize.dimension_le_two J (right J.target s.link)),ite_eq_right (by decide : ¬(1 : ℕ)=0),ite_eq_left rfl]
      have hh := (BlockCoordinates.order_eq_extend J hr hn (b := .inr s) (a := .inl (squareRight J s)) (Or.inr (Or.inl rfl))).trans
        (congrArg AffineAlphabet.extend (BlockCoordinates.embedding_right J hr hn s))
      exact (congrArg (PrefixAlphabet.encodeOrder (RealizationSize.coordinate_card J (.inr s))) hh).symm
    · have hnL : (BlockCatalog.readout PP PE).encode (.inr (squareBottom s)) ≠ (BlockCatalog.readout PP PE).encode (.inl (squareLeft J s)) := fun hh=>Sum.inr_ne_inl (hi hh)
      have hnR : (BlockCatalog.readout PP PE).encode (.inr (squareBottom s)) ≠ (BlockCatalog.readout PP PE).encode (.inl (squareRight J s)) := fun hh=>Sum.inr_ne_inl (hi hh)
      simp only [hnL,hnR,ite_false,ite_true]
      rw [AffineAlphabet.squareOrder,dite_eq_left (RealizationSize.dimension_le_two J (left J.source s.link)),
        dite_eq_left (RealizationSize.dimension_le_two J (right J.target s.link)),ite_eq_right (by decide : ¬(2 : ℕ)=0),ite_eq_right (by decide : ¬(2 : ℕ)=1)]
      have hh := (BlockCoordinates.order_eq_extend J hr hn (b := .inr s) (a := .inr (squareBottom s)) (Or.inr (Or.inr (Or.inl rfl)))).trans
        (congrArg AffineAlphabet.extend (BlockCoordinates.embedding_bottom J hr hn s))
      exact (congrArg (PrefixAlphabet.encodeOrder (RealizationSize.coordinate_card J (.inr s))) hh).symm
    · have hnL : (BlockCatalog.readout PP PE).encode (.inr (squareTop s)) ≠ (BlockCatalog.readout PP PE).encode (.inl (squareLeft J s)) := fun hh=>Sum.inr_ne_inl (hi hh)
      have hnR : (BlockCatalog.readout PP PE).encode (.inr (squareTop s)) ≠ (BlockCatalog.readout PP PE).encode (.inl (squareRight J s)) := fun hh=>Sum.inr_ne_inl (hi hh)
      have hnB : (BlockCatalog.readout PP PE).encode (.inr (squareTop s)) ≠ (BlockCatalog.readout PP PE).encode (.inr (squareBottom s)) := fun hh=>squareBottom_ne_top hr s (Sum.inr.inj (hi hh)).symm
      simp only [hnL,hnR,hnB,ite_false]
      rw [AffineAlphabet.squareOrder,dite_eq_left (RealizationSize.dimension_le_two J (left J.source s.link)),
        dite_eq_left (RealizationSize.dimension_le_two J (right J.target s.link)),ite_eq_right (by decide : ¬(3 : ℕ)=0),ite_eq_right (by decide : ¬(3 : ℕ)=1)]
      have hh := (BlockCoordinates.order_eq_extend J hr hn (b := .inr s) (a := .inr (squareTop s)) (Or.inr (Or.inr (Or.inr rfl)))).trans
        (congrArg AffineAlphabet.extend (BlockCoordinates.embedding_top J hr hn s))
      exact (congrArg (PrefixAlphabet.encodeOrder (RealizationSize.coordinate_card J (.inr s))) hh).symm
 theorem legal_code (b : RawBlock r n P E) (i : ℕ) : D.legal ((BlockCatalog.raw PP PE).encode b) i=true ↔
    ∃z : RawValue J b,LegalValue J marked ε b z ∧
      PrefixAlphabet.encode (RealizationSize.coordinate_card J b) (BlockCoordinates.encode J b z)=i := by
  cases b with
  | inl x =>
    change (if (BlockCatalog.horizontal PP PE).encode x<D.horizontals then _ else _)=true ↔ _
    rw [ite_eq_left (by rw [BlockCatalog.horizontals_eq PP PE J h.toGood]; exact (BlockCatalog.horizontal PP PE).encode_lt x)]
    change AffineAlphabet.horizontalLegal (D.horizontalDimension ((BlockCatalog.horizontal PP PE).encode x)) i=true ↔ _
    rw [horizontal_dimension PP PE J marked ε h,
      AffineAlphabet.horizontalLegal_eq (RealizationSize.dimension_le_two J x.type)]
    simp only [LegalValue,boundaryMap,inhomogeneity,mul_zero,AddMonoidHom.zero_apply,true_and]
    rfl
  | inr s =>
    change (if (BlockCatalog.horizontal (r := r) (n := n) PP PE).bound+(BlockCatalog.square PE).encode s<D.horizontals then _ else _)=true ↔ _
    rw [BlockCatalog.horizontals_eq PP PE J h.toGood,ite_eq_right (by omega)]
    have hs : (BlockCatalog.horizontal (r := r) (n := n) PP PE).bound+(BlockCatalog.square (r := r) (n := n) PE).encode s-
        (BlockCatalog.horizontal (r := r) (n := n) PP PE).bound=(BlockCatalog.square PE).encode s := by omega
    dsimp only
    change (BlockCatalog.horizontal (r := r) (n := n) PP PE).bound+(BlockCatalog.square PE).encode s-
      (BlockCatalog.horizontal (r := r) (n := n) PP PE).bound=(BlockCatalog.square PE).encode s at hs
    simp only [BlockCatalog.raw,Presentation.sum_inr,Nat.add_sub_cancel_left] at *
    rw [(BlockCatalog.square_parts PP PE J h.toGood s).2.1,link_left PP PE J marked ε h,link_right PP PE J marked ε h]
    have hc : D.constant ((BlockCatalog.square PE).encode s)=(ε*inhomogeneity J marked (.inr s)).val := by
      have hh := congrArg ZMod.val (constant_code PP PE J marked ε h s)
      rw [ZMod.val_natCast] at hh
      have hm : D.constant ((BlockCatalog.square PE).encode s)<2 := Nat.mod_lt _ (by decide)
      rwa [Nat.mod_eq_of_lt hm] at hh
    rw [hc,AffineAlphabet.squareLegal_eq]
    rfl
 theorem core_good (hr : 2≤r) (hn : 0<n) : BlockDescriptor.Good J hr hn marked
    (BlockCatalog.block PP PE J h.toGood) (BlockCatalog.readout PP PE)
      (fun b=>RealizationSize.coordinate_card J b.val) ε D.core := by
  refine ⟨(BlockCatalog.block_bound PP PE J h.toGood).symm,BlockCatalog.reads_eq PP PE J h.toGood,
    (BlockCatalog.block_valid PP PE J h.toGood).symm,BlockCatalog.readValid_eq PP PE J h.toGood,
    BlockCatalog.has_code PP PE J h.toGood,?_,read_dimension PP PE J marked ε h,?_,?_,?_⟩
  · intro b; exact dimension_code PP PE J marked ε h b.val
  · intro b; exact zero_order PP PE J marked ε h b.val
  · intro b a ha; exact read_order PP PE J marked ε h hr hn b.val a ha
  · intro b i
    rw [show D.core.legal (BlockCatalog.block PP PE J h.toGood |>.encode b) i=D.legal ((BlockCatalog.raw PP PE).encode b.val) i from rfl,
      legal_code PP PE J marked ε h]
    exact ⟨fun ⟨z,hz,he⟩=>⟨⟨z,hz⟩,he⟩,fun ⟨z,he⟩=>⟨z.val,z.property,he⟩⟩
end VariableWL.AffineCatalog

namespace VariableWL.AffineAlphabet.Program
open Computation.Stack.PolyRecipe Computation.Stack.Recipe
variable {n : ℕ}
noncomputable def horizontalLegal (D I : Expr n) : Expr n :=
  eq (table₂ 3 PrefixAlphabet.vectorCount (fun d i=>if AffineAlphabet.horizontalLegal d i then 1 else 0) D I) (numeral 1)
noncomputable def squareLegalBody (L R C I : Expr n) : Expr n :=
  eq (table₃ formCount formCount (2*PrefixAlphabet.vectorCount)
    (fun l r q=>if AffineAlphabet.squareLegal l r (q/PrefixAlphabet.vectorCount) (q%PrefixAlphabet.vectorCount) then 1 else 0)
    L R (add (mul (mod C (numeral 2)) (numeral PrefixAlphabet.vectorCount)) I)) (numeral 1)
noncomputable def horizontalOrder (D : Expr n) : Expr n := fixedNat 3 (fun d=>AffineAlphabet.horizontalOrder d.val) D
noncomputable def squareOrder (D E A : Expr n) : Expr n := table₃ 3 3 4 AffineAlphabet.squareOrder D E (minimum A (numeral 3))
noncomputable def zeroOrder (D : Expr n) : Expr n := fixedNat 7 (fun d=>AffineAlphabet.zeroOrder d.val) D
noncomputable def squareLegal (L R C I : Expr n) : Expr n :=
  choose (lt I (numeral PrefixAlphabet.vectorCount)) (squareLegalBody L R C I) (literal [false])
end VariableWL.AffineAlphabet.Program

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

namespace VariableWL.AffineCatalog.Program
open Computation.Stack.PolyRecipe Computation.Stack.Recipe
open VariableWL.NumericProgram
variable {n : ℕ}
structure Listing (n : ℕ) extends BlockCatalog.Program.Listing n where
  realDimension : Expr (n+1)
  leftForm : Expr (n+1)
  rightForm : Expr (n+1)
  leftConstant : Expr (n+1)
  rightConstant : Expr (n+1)
  marked : Expr n
  epsilon : Expr n
namespace Listing
variable (D : Listing n)
def eval (v : Env n) : Data where
  toData := D.toListing.eval v
  realDimension i := D.realDimension.number (cons (List.replicate i true) v)
  leftForm i := D.leftForm.number (cons (List.replicate i true) v)
  rightForm i := D.rightForm.number (cons (List.replicate i true) v)
  leftConstant i := D.leftConstant.number (cons (List.replicate i true) v)
  rightConstant i := D.rightConstant.number (cons (List.replicate i true) v)
  marked := D.marked.number v
  epsilon := D.epsilon.number v
def up : Listing (n+1) where
  toListing := D.toListing.up
  realDimension := underOne D.realDimension
  leftForm := underOne D.leftForm
  rightForm := underOne D.rightForm
  leftConstant := underOne D.leftConstant
  rightConstant := underOne D.rightConstant
  marked := D.marked.up
  epsilon := D.epsilon.up
def vertexDimension (T : Expr n) : Expr n := choose (lt T D.reals) (applyNat D.realDimension T) (numeral 1)
def horizontalDimension (H : Expr n) : Expr n := D.vertexDimension (D.toListing.htype H)
def squareLeftDimension (S : Expr n) : Expr n := D.vertexDimension (D.toListing.left (D.toListing.slink S))
def squareRightDimension (S : Expr n) : Expr n := D.vertexDimension (D.toListing.right (D.toListing.slink S))
def dimension (B : Expr n) : Expr n := choose (lt B D.toListing.horizontals) (D.horizontalDimension B)
  (add (add (D.squareLeftDimension (sub B D.toListing.horizontals)) (D.squareRightDimension (sub B D.toListing.horizontals))) (numeral 2))
def readDimension (A : Expr n) : Expr n := choose (lt A D.toListing.horizontals) (D.horizontalDimension A) (numeral 1)
noncomputable def linkLeft (L : Expr n) : Expr n := choose (eq (mod L (add D.internal (numeral 1))) (numeral 0))
  (applyNat D.leftForm (div L (add D.internal (numeral 1))))
  (numeral (AffineAlphabet.encodeForm (by decide : 1≤2) (LinearMap.proj (0 : Fin 1))))
noncomputable def linkRight (L : Expr n) : Expr n := choose (eq (mod L (add D.internal (numeral 1))) D.internal)
  (applyNat D.rightForm (div L (add D.internal (numeral 1))))
  (numeral (AffineAlphabet.encodeForm (by decide : 1≤2) (LinearMap.proj (0 : Fin 1))))
def linkLeftConstant (L : Expr n) : Expr n := choose (eq (mod L (add D.internal (numeral 1))) (numeral 0))
  (applyNat D.leftConstant (div L (add D.internal (numeral 1)))) (numeral 0)
def linkRightConstant (L : Expr n) : Expr n := choose (eq (mod L (add D.internal (numeral 1))) D.internal)
  (applyNat D.rightConstant (div L (add D.internal (numeral 1)))) (numeral 0)
def constant (S : Expr n) : Expr n := mod (mul D.epsilon (choose (eq (D.toListing.srow S) D.marked)
  (add (D.linkLeftConstant (D.toListing.slink S)) (D.linkRightConstant (D.toListing.slink S))) (numeral 0))) (numeral 2)
noncomputable def zeroOrder (B : Expr n) : Expr n := AffineAlphabet.Program.zeroOrder (D.dimension B)
noncomputable def readOrder (B A : Expr n) : Expr n := choose (lt B D.toListing.horizontals)
  (AffineAlphabet.Program.horizontalOrder (D.horizontalDimension B))
  (AffineAlphabet.Program.squareOrder (D.squareLeftDimension (sub B D.toListing.horizontals))
    (D.squareRightDimension (sub B D.toListing.horizontals))
    (choose (eq A (D.toListing.squareLeft (sub B D.toListing.horizontals))) (numeral 0)
      (choose (eq A (D.toListing.squareRight (sub B D.toListing.horizontals))) (numeral 1)
        (choose (eq A (D.toListing.squareBottom (sub B D.toListing.horizontals))) (numeral 2) (numeral 3)))))
noncomputable def legal (B I : Expr n) : Expr n := choose (lt B D.toListing.horizontals)
  (AffineAlphabet.Program.horizontalLegal (D.horizontalDimension B) I)
  (AffineAlphabet.Program.squareLegal (D.linkLeft (D.toListing.slink (sub B D.toListing.horizontals)))
    (D.linkRight (D.toListing.slink (sub B D.toListing.horizontals))) (D.constant (sub B D.toListing.horizontals)) I)

noncomputable def core : BlockDescriptor.Program.Listing n where
  blocks := D.toListing.blocks
  validBlock := D.toListing.up.validBlock (input 0)
  reads := D.toListing.reads
  validRead := D.toListing.up.readValid (input 0)
  has := D.toListing.up.up.has (input 0) (input 1)
  dimension := D.up.dimension (input 0)
  readDimension := D.up.readDimension (input 0)
  zeroOrder := D.up.zeroOrder (input 0)
  readOrder := D.up.up.readOrder (input 0) (input 1)
  legal := D.up.up.legal (input 0) (input 1)

end Listing
end VariableWL.AffineCatalog.Program

namespace VariableWL.Descriptor.Presentation
attribute [local instance] Classical.propDecidable
@[simp] theorem sum_bound {A : Type uVariable1} {B : Type uVariable2} (P : Presentation A) (Q : Presentation B) : (P.sum Q).bound=P.bound+Q.bound := rfl
noncomputable def unit : Presentation Unit := ofEncoding 1 (fun _=>true) (fun _=>0)
  (by intro; decide) (by intro; rfl) (by intro a b _; exact Subsingleton.elim a b)
  (by intro i hi _; exact ⟨(),by omega⟩)
@[simp] theorem unit_encode (u : Unit) : unit.encode u=0 := rfl
def optionEquiv (A : Type uVariable4) : Unit ⊕ A ≃ Option A where
  toFun := Sum.elim (fun _=>none) some
  invFun := Option.elim' (.inl ()) Sum.inr
  left_inv a := by rcases a with u|a; cases u; rfl; rfl
  right_inv a := by cases a <;> rfl
noncomputable def option {A : Type uVariable5} (P : Presentation A) : Presentation (Option A) :=
  (unit.sum P).transport (optionEquiv A)
@[simp] theorem option_none {A : Type uVariable6} (P : Presentation A) : P.option.encode none=0 := rfl
@[simp] theorem option_some {A : Type uVariable7} (P : Presentation A) (a : A) : P.option.encode (some a)=1+P.encode a := rfl
end VariableWL.Descriptor.Presentation

namespace VariableWL.CircuitCatalog
open Descriptor Circuit VariableWL.Affine
attribute [local instance] Classical.propDecidable
structure Data where
  rows : ℕ
  internal : ℕ
  scalars : ℕ
  ands : ℕ
  edges : ℕ
  requests : ℕ
  validScalar : ℕ → Bool
  validAnd : ℕ → Bool
  validEdge : ℕ → Bool
  validRequest : ℕ → Bool
  source : ℕ → ℕ
  destination : ℕ → ℕ
  destinationForm : ℕ → ℕ
  domain : ℕ → ℕ → ℕ → Bool
  map : ℕ → ℕ → ℕ → ℕ
  requestGate : ℕ → ℕ
  requestTest : ℕ → ℕ
  requestDomain : ℕ → ℕ → ℕ → Bool
  marked : ℕ
  epsilon : ℕ
namespace Data
variable (D : Data)
def gates : ℕ := D.scalars+D.ands
def edgeCode (c : ℕ) : ℕ := if c<D.edges then c else if c<2*D.edges then c-D.edges else c-2*D.edges
noncomputable def affine : AffineCatalog.Data where
  rows := D.rows
  internal := D.internal
  reals := D.gates+(D.edges+1)
  comparisons := D.edges+(D.edges+D.edges)+D.requests
  validReal i := if i<D.gates then (if i<D.scalars then D.validScalar i else D.validAnd (i-D.scalars))
    else if i-D.gates<D.edges then D.validEdge (i-D.gates) else true
  validComparison c := if c<D.edges+(D.edges+D.edges) then
    (if c<D.edges then D.validEdge c else if c-D.edges<D.edges then D.validEdge (c-D.edges)
      else D.validEdge (c-D.edges-D.edges)) else D.validRequest (c-(D.edges+(D.edges+D.edges)))
  source c := if c<2*D.edges then D.source (D.edgeCode c) else
    if c<3*D.edges then D.gates+D.edgeCode c else D.requestGate (c-3*D.edges)
  target c := if c<2*D.edges then D.gates+D.edgeCode c else
    if c<3*D.edges then D.destination (D.edgeCode c) else D.gates+D.edges
  domain c i a := if c<3*D.edges then D.domain (D.edgeCode c) i a else D.requestDomain (c-3*D.edges) i a
  map c i a := if 2*D.edges≤c ∧ c<3*D.edges then D.map (D.edgeCode c) i a else a
  realDimension p := if p<D.scalars then 1 else if p<D.gates+D.edges then 2 else 1
  leftForm c := if c<2*D.edges then
    (if D.source (D.edgeCode c)<D.scalars then AffineAlphabet.encodeForm (by decide : 1≤2) (LinearMap.proj 0)
      else AffineAlphabet.encodeForm (by decide : 2≤2) ((LinearMap.proj (0 : Fin 2) : Vec 2 →ₗ[Bit] Bit)+LinearMap.proj 1))
    else if c<3*D.edges then AffineAlphabet.encodeForm (by decide : 2≤2)
      ((LinearMap.proj (0 : Fin 2) : Vec 2 →ₗ[Bit] Bit)+LinearMap.proj 1)
    else AffineAlphabet.encodeForm (by decide : 1≤2) (LinearMap.proj 0)
  rightForm c := if c<D.edges then AffineAlphabet.encodeForm (by decide : 2≤2) (LinearMap.proj 0)
    else if c<2*D.edges then AffineAlphabet.encodeForm (by decide : 2≤2) (LinearMap.proj 1)
    else if c<3*D.edges then D.destinationForm (D.edgeCode c)
    else AffineAlphabet.encodeForm (by decide : 1≤2) 0
  leftConstant _ := 0
  rightConstant c := if c<3*D.edges then 0 else D.requestTest (c-3*D.edges)
  marked := D.marked
  epsilon := D.epsilon
end Data
variable {r n : ℕ} {S : Type uVariable8} {A : Type uVariable9} {E : Type uVariable10} {R : Type uVariable11}
variable (PS : Presentation S) (PA : Presentation A) (PE : Presentation E) (PR : Presentation R)
noncomputable def real : Presentation (Description.Real (S := S) (A := A) (E := E)) :=
  (PS.sum PA).sum (PE.sum Presentation.unit)
noncomputable def comparison : Presentation (Description.Comparison (E := E) (R := R)) :=
  (PE.sum (PE.sum PE)).sum PR
structure Good (C : Description r S A E R) (marked : Fin r) (ε : Bit) (D : Data) : Prop where
  rows : D.rows=r
  internal : D.internal=n
  scalars : D.scalars=PS.bound
  ands : D.ands=PA.bound
  edges : D.edges=PE.bound
  requests : D.requests=PR.bound
  validScalar : D.validScalar=PS.valid
  validAnd : D.validAnd=PA.valid
  validEdge : D.validEdge=PE.valid
  validRequest : D.validRequest=PR.valid
  source : ∀e,D.source (PE.encode e)=(PS.sum PA).encode (C.source e)
  destination : ∀e,D.destination (PE.encode e)=(PS.sum PA).encode (target S A (C.destination e))
  destinationForm : ∀e,D.destinationForm (PE.encode e)=AffineAlphabet.encodeForm
    (by cases C.destination e <;> simp only [dimension] <;> decide) (inputLinear (C.destination e))
  domain : ∀e i a,D.domain (PE.encode e) i.val a.toNat=true ↔ a ∈ C.domain e i
  map : ∀e i a,D.map (PE.encode e) i.val a.toNat=(C.map e i a).toNat
  requestGate : ∀b,D.requestGate (PR.encode b)=PS.encode (C.requestGate b)
  requestTest : ∀b,D.requestTest (PR.encode b)=(if C.requestTest b then 1 else 0)
  requestDomain : ∀b i a,D.requestDomain (PR.encode b) i.val a.toNat=true ↔ a ∈ C.requestDomain b i
  marked : D.marked=marked.val
  epsilon : D.epsilon=ε.val
end VariableWL.CircuitCatalog

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_CellularCatalog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5

namespace VariableWL.CircuitCatalog.Program
open Computation.Stack.PolyRecipe Computation.Stack.Recipe VariableWL.NumericProgram
variable {n : ℕ}
structure Listing (n : ℕ) where
  rows : Expr n
  internal : Expr n
  scalars : Expr n
  ands : Expr n
  edges : Expr n
  requests : Expr n
  validScalar : Expr (n+1)
  validAnd : Expr (n+1)
  validEdge : Expr (n+1)
  validRequest : Expr (n+1)
  source : Expr (n+1)
  destination : Expr (n+1)
  destinationForm : Expr (n+1)
  domain : Expr (n+3)
  map : Expr (n+3)
  requestGate : Expr (n+1)
  requestTest : Expr (n+1)
  requestDomain : Expr (n+3)
  marked : Expr n
  epsilon : Expr n
namespace Listing
variable (D : Listing n)
def eval (v : Env n) : Data where
  rows := D.rows.number v
  internal := D.internal.number v
  scalars := D.scalars.number v
  ands := D.ands.number v
  edges := D.edges.number v
  requests := D.requests.number v
  validScalar i := D.validScalar.bit (cons (List.replicate i true) v)
  validAnd i := D.validAnd.bit (cons (List.replicate i true) v)
  validEdge i := D.validEdge.bit (cons (List.replicate i true) v)
  validRequest i := D.validRequest.bit (cons (List.replicate i true) v)
  source i := D.source.number (cons (List.replicate i true) v)
  destination i := D.destination.number (cons (List.replicate i true) v)
  destinationForm i := D.destinationForm.number (cons (List.replicate i true) v)
  domain i j a := D.domain.bit (cons (List.replicate i true) (cons (List.replicate j true) (cons (List.replicate a true) v)))
  map i j a := D.map.number (cons (List.replicate i true) (cons (List.replicate j true) (cons (List.replicate a true) v)))
  requestGate i := D.requestGate.number (cons (List.replicate i true) v)
  requestTest i := D.requestTest.number (cons (List.replicate i true) v)
  requestDomain i j a := D.requestDomain.bit (cons (List.replicate i true) (cons (List.replicate j true) (cons (List.replicate a true) v)))
  marked := D.marked.number v
  epsilon := D.epsilon.number v
def up : Listing (n+1) where
  rows := D.rows.up
  internal := D.internal.up
  scalars := D.scalars.up
  ands := D.ands.up
  edges := D.edges.up
  requests := D.requests.up
  validScalar := underOne D.validScalar
  validAnd := underOne D.validAnd
  validEdge := underOne D.validEdge
  validRequest := underOne D.validRequest
  source := underOne D.source
  destination := underOne D.destination
  destinationForm := underOne D.destinationForm
  domain := underThree D.domain
  map := underThree D.map
  requestGate := underOne D.requestGate
  requestTest := underOne D.requestTest
  requestDomain := underThree D.requestDomain
  marked := D.marked.up
  epsilon := D.epsilon.up
def gates : Expr n := add D.scalars D.ands
def edgeCode (C : Expr n) : Expr n := choose (lt C D.edges) C
  (choose (lt C (mul (numeral 2) D.edges)) (sub C D.edges) (sub C (mul (numeral 2) D.edges)))
noncomputable def affineSource (C : Expr n) : Expr n := choose (lt C (mul (numeral 2) D.edges))
  (applyNat D.source (D.edgeCode C)) (choose (lt C (mul (numeral 3) D.edges))
    (add D.gates (D.edgeCode C)) (applyNat D.requestGate (sub C (mul (numeral 3) D.edges))))
noncomputable def affineTarget (C : Expr n) : Expr n := choose (lt C (mul (numeral 2) D.edges))
  (add D.gates (D.edgeCode C)) (choose (lt C (mul (numeral 3) D.edges))
    (applyNat D.destination (D.edgeCode C)) (add D.gates D.edges))
noncomputable def affineDomain (C I A : Expr n) : Expr n := choose (lt C (mul (numeral 3) D.edges))
  (applyNat₃ D.domain (D.edgeCode C) I A) (applyNat₃ D.requestDomain (sub C (mul (numeral 3) D.edges)) I A)
noncomputable def affineMap (C I A : Expr n) : Expr n := choose
  (conj (le (mul (numeral 2) D.edges) C) (lt C (mul (numeral 3) D.edges)))
    (applyNat₃ D.map (D.edgeCode C) I A) A
noncomputable def affineDimension (P : Expr n) : Expr n := choose (lt P D.scalars) (numeral 1)
  (choose (lt P (add D.gates D.edges)) (numeral 2) (numeral 1))
noncomputable def affineLeft (C : Expr n) : Expr n := choose (lt C (mul (numeral 2) D.edges))
  (choose (lt (applyNat D.source (D.edgeCode C)) D.scalars)
    (numeral (AffineAlphabet.encodeForm (by decide : 1≤2) (LinearMap.proj 0)))
    (numeral (AffineAlphabet.encodeForm (by decide : 2≤2) ((LinearMap.proj (0 : Fin 2) : Affine.Vec 2 →ₗ[Affine.Bit] Affine.Bit)+LinearMap.proj 1))))
  (choose (lt C (mul (numeral 3) D.edges))
    (numeral (AffineAlphabet.encodeForm (by decide : 2≤2) ((LinearMap.proj (0 : Fin 2) : Affine.Vec 2 →ₗ[Affine.Bit] Affine.Bit)+LinearMap.proj 1)))
    (numeral (AffineAlphabet.encodeForm (by decide : 1≤2) (LinearMap.proj 0))))
noncomputable def affineRight (C : Expr n) : Expr n := choose (lt C D.edges)
  (numeral (AffineAlphabet.encodeForm (by decide : 2≤2) (LinearMap.proj 0)))
  (choose (lt C (mul (numeral 2) D.edges)) (numeral (AffineAlphabet.encodeForm (by decide : 2≤2) (LinearMap.proj 1)))
    (choose (lt C (mul (numeral 3) D.edges)) (applyNat D.destinationForm (D.edgeCode C))
      (numeral (AffineAlphabet.encodeForm (by decide : 1≤2) 0))))
noncomputable def affineConstant (C : Expr n) : Expr n := choose (lt C (mul (numeral 3) D.edges))
  (numeral 0) (applyNat D.requestTest (sub C (mul (numeral 3) D.edges)))
noncomputable def affineValidReal (I : Expr n) : Expr n := choose (lt I D.gates)
  (choose (lt I D.scalars) (applyNat D.validScalar I) (applyNat D.validAnd (sub I D.scalars)))
  (choose (lt (sub I D.gates) D.edges) (applyNat D.validEdge (sub I D.gates)) (literal [true]))
noncomputable def affineValidComparison (C : Expr n) : Expr n := choose (lt C (add D.edges (add D.edges D.edges)))
  (choose (lt C D.edges) (applyNat D.validEdge C) (choose (lt (sub C D.edges) D.edges)
    (applyNat D.validEdge (sub C D.edges)) (applyNat D.validEdge (sub (sub C D.edges) D.edges))))
  (applyNat D.validRequest (sub C (add D.edges (add D.edges D.edges))))
noncomputable def affine : AffineCatalog.Program.Listing n where
  rows := D.rows
  internal := D.internal
  reals := add D.gates (add D.edges (numeral 1))
  comparisons := add (add D.edges (add D.edges D.edges)) D.requests
  validReal := D.up.affineValidReal (input 0)
  validComparison := D.up.affineValidComparison (input 0)
  source := D.up.affineSource (input 0)
  target := D.up.affineTarget (input 0)
  domain := D.up.up.up.affineDomain (input 0) (input 1) (input 2)
  map := D.up.up.up.affineMap (input 0) (input 1) (input 2)
  realDimension := D.up.affineDimension (input 0)
  leftForm := D.up.affineLeft (input 0)
  rightForm := D.up.affineRight (input 0)
  leftConstant := numeral 0
  rightConstant := D.up.affineConstant (input 0)
  marked := D.marked
  epsilon := D.epsilon
end Listing
end VariableWL.CircuitCatalog.Program

namespace VariableWL.Binary
 theorem number_bit {d : ℕ} (x : Digits d) : ∀i : Fin d,(number x).testBit i.val=x i := by
  induction d with
  | zero => intro i; exact Fin.elim0 i
  | succ d ih =>
    intro i
    have he : number x=Nat.bit (x 0) (number (fun j : Fin d=>x j.succ)) := by
      cases hb : x 0 <;> simp [number,hb,Nat.bit,Nat.add_comm]
    rw [he]
    refine Fin.cases ?_ (fun j=>?_) i
    · cases hb : x 0 <;> simp [Nat.bit,Nat.testBit_eq_decide_div_mod_eq]
    · rw [Fin.val_succ,Nat.testBit_bit_succ]
      exact ih (fun j : Fin d=>x j.succ) j
end VariableWL.Binary
namespace VariableWL.Circuit.ProductCellular.Data
 theorem threshold_bit {L : Type uVariable1} {d m : ℕ} (D : Data L d m) (i : Fin d) : m.testBit i.val=D.threshold i := by
  simpa only [D.number_threshold] using (Binary.number_bit D.threshold i)
end VariableWL.Circuit.ProductCellular.Data

namespace VariableWL.CellularCatalog
open Descriptor Circuit VariableWL.Affine
attribute [local instance] Classical.propDecidable
variable {L : Type uVariable3} {d m : ℕ} (P : Presentation L)
noncomputable def triple : Presentation (Cellular.Triple L) := P.product (P.product P)
noncomputable def ands : Presentation (Cellular.Triple L × Bool) := (triple P).product Presentation.boolean
noncomputable def kind (d : ℕ) : Presentation (ProductCellular.Kind d) :=
  ((Presentation.fin d).product (Presentation.fin d).option).sum
    ((Presentation.fin d).sum (((Presentation.fin d).product (Presentation.fin d).option).sum Presentation.boolean))
noncomputable def edge : Presentation (ProductCellular.Edge L d) := (triple P).product (kind d)
noncomputable def zeroBit (D : ProductCellular.Data L d m) : Presentation {h : Fin d // D.threshold h=false} :=
  (Presentation.fin d).filter (fun i=>!(m.testBit i)) (fun h=>D.threshold h=false)
    (by intro i; simp only [Presentation.fin_encode,←D.threshold_bit i,Bool.not_eq_true'])
noncomputable def accepting (D : ProductCellular.Data L d m) : Presentation {f : L // f∈D.accepting} :=
  P.filter (fun i=>decide (∃f,P.encode f=i ∧ f∈D.accepting)) (fun f=>f∈D.accepting)
    (by intro f; simp only [decide_eq_true_eq,P.encode_injective.eq_iff]; simp)
noncomputable def request (D : ProductCellular.Data L d m) : Presentation D.Request :=
  ((Presentation.fin m).sum (zeroBit D).option).sum (accepting P D)
structure Data where
  bits : ℕ
  inputLength : ℕ
  letters : ℕ
  internal : ℕ
  rule : ℕ → ℕ → ℕ → ℕ
  input : ℕ → ℕ
  blank : ℕ
  accepting : ℕ → Bool
  marked : ℕ
  epsilon : ℕ
namespace Data
variable (D : Data)
def leftEnd : ℕ := D.bits*(1+D.bits)
def centerEnd : ℕ := D.leftEnd+D.bits
def rightEnd : ℕ := D.centerEnd+D.leftEnd
def kinds : ℕ := D.rightEnd+2
def triples : ℕ := D.letters*(D.letters*D.letters)
def tripleCode (e : ℕ) : ℕ := e/D.kinds
def kindCode (e : ℕ) : ℕ := e%D.kinds
def first (t : ℕ) : ℕ := t/(D.letters*D.letters)
def second (t : ℕ) : ℕ := (t/D.letters)%D.letters
def third (t : ℕ) : ℕ := t%D.letters
def kindTime (k : ℕ) : ℕ := if k<D.leftEnd then k/(1+D.bits) else
  if k<D.centerEnd then k-D.leftEnd else (k-D.centerEnd)/(1+D.bits)
def kindPosition (k : ℕ) : ℕ := if k<D.leftEnd then k%(1+D.bits) else (k-D.centerEnd)%(1+D.bits)
def source (e : ℕ) : ℕ := let k:=D.kindCode e; let t:=D.tripleCode e
  if k<D.leftEnd then D.first t else if k<D.centerEnd then D.second t else
    if k<D.rightEnd then D.third t else D.letters+(t*2+(k-D.rightEnd))
def destination (e : ℕ) : ℕ := let k:=D.kindCode e; let t:=D.tripleCode e
  if k<D.centerEnd then D.letters+t*2 else if k<D.rightEnd+1 then D.letters+(t*2+1)
    else D.rule (D.first t) (D.second t) (D.third t)
noncomputable def destinationForm (e : ℕ) : ℕ := let k:=D.kindCode e
  if k<D.leftEnd then AffineAlphabet.encodeForm (by decide : 2≤2) (LinearMap.proj 0)
    else if k<D.rightEnd then AffineAlphabet.encodeForm (by decide : 2≤2) (LinearMap.proj 1)
    else if k<D.rightEnd+1 then AffineAlphabet.encodeForm (by decide : 2≤2) (LinearMap.proj 0)
    else AffineAlphabet.encodeForm (by decide : 1≤2) (LinearMap.proj 0)
def carryDomain (bit : ℕ) (h i a : ℕ) : Bool := if i<h then decide (a=bit) else if i=h then decide (a=1-bit) else true
def cyclicDomain (bit : ℕ) (h i a : ℕ) : Bool := if h=0 then decide (a=bit) else carryDomain bit (h-1) i a
def domain (e i a : ℕ) : Bool := let k:=D.kindCode e
  if k<D.rightEnd then if i<D.bits then carryDomain 1 (D.kindTime k) i a
    else if k<D.leftEnd then cyclicDomain 1 (D.kindPosition k) (i-D.bits) a
    else if k<D.centerEnd then true else cyclicDomain 0 (D.kindPosition k) (i-D.bits) a
  else true
def map (e i a : ℕ) : ℕ := let k:=D.kindCode e
  if k<D.rightEnd then if i<D.bits then (if i≤D.kindTime k then 1-a else a)
    else if k<D.leftEnd ∨ D.centerEnd≤k then
      (if D.kindPosition k=0 ∨ i-D.bits<D.kindPosition k then 1-a else a) else a
  else a
def initialEnd : ℕ := D.inputLength+(1+D.bits)
def validRequest (b : ℕ) : Bool := if b<D.inputLength then true else if b=D.inputLength then true
  else if b<D.initialEnd then !(D.inputLength.testBit (b-D.inputLength-1)) else D.accepting (b-D.initialEnd)
def requestGate (b : ℕ) : ℕ := if b<D.inputLength then D.input b else if b<D.initialEnd then D.blank else b-D.initialEnd
def requestTest (b : ℕ) : ℕ := if b<D.initialEnd then 0 else 1
def requestPositionDomain (b i a : ℕ) : Bool := if b<D.inputLength then decide (a=(b.testBit i).toNat)
  else if b<D.initialEnd then
    (if b=D.inputLength ∨ b - D.inputLength - 1 < i then decide (a=(D.inputLength.testBit i).toNat)
      else if i=b-D.inputLength-1 then decide (a=1) else true) else true
def requestDomain (b i a : ℕ) : Bool := if i<D.bits then decide (a=D.requestTest b)
  else D.requestPositionDomain b (i-D.bits) a
noncomputable def catalog : CircuitCatalog.Data where
  rows := D.bits+D.bits
  internal := D.internal
  scalars := D.letters
  ands := D.triples*2
  edges := D.triples*D.kinds
  requests := D.initialEnd+D.letters
  validScalar _ := true
  validAnd _ := true
  validEdge _ := true
  validRequest := D.validRequest
  source := D.source
  destination := D.destination
  destinationForm := D.destinationForm
  domain := D.domain
  map := D.map
  requestGate := D.requestGate
  requestTest := D.requestTest
  requestDomain := D.requestDomain
  marked := D.marked
  epsilon := D.epsilon
end Data
end VariableWL.CellularCatalog

namespace VariableWL.Descriptor.Presentation
variable {A : Type uVariable4} {B : Type uVariable5}
@[simp] theorem product_bound (P : Presentation A) (Q : Presentation B) : (P.product Q).bound=P.bound*Q.bound := rfl
@[simp] theorem product_valid (P : Presentation A) (Q : Presentation B) (i : ℕ) : (P.product Q).valid i=(P.valid (i/Q.bound) && Q.valid (i%Q.bound)) := rfl
@[simp] theorem sum_valid (P : Presentation A) (Q : Presentation B) (i : ℕ) : (P.sum Q).valid i=(if i<P.bound then P.valid i else Q.valid (i-P.bound)) := rfl
@[simp] theorem filter_bound (P : Presentation A) (Q : ℕ → Bool) (T : A → Prop) (h) : (P.filter Q T h).bound=P.bound := rfl
@[simp] theorem filter_valid (P : Presentation A) (Q : ℕ → Bool) (T : A → Prop) (h) (i : ℕ) : (P.filter Q T h).valid i=(P.valid i && Q i) := rfl
@[simp] theorem option_bound (P : Presentation A) : P.option.bound=1+P.bound := rfl
@[simp] theorem option_valid (P : Presentation A) (i : ℕ) : P.option.valid i=(if i<1 then true else P.valid (i-1)) := rfl
@[simp] theorem fin_bound (d : ℕ) : (fin d).bound=d := rfl
@[simp] theorem fin_valid (d i : ℕ) : (fin d).valid i=true := rfl
end VariableWL.Descriptor.Presentation

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_CellularListing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4

namespace VariableWL.CellularCatalog
open Descriptor Circuit VariableWL.Affine
attribute [local instance] Classical.propDecidable
variable {L : Type uVariable1} {d m n : ℕ} (P : Presentation L) (C : ProductCellular.Data L d m)
variable (marked : Fin (d+d)) (ε : Bit)
structure Good (D : Data) : Prop where
  bits : D.bits=d
  inputLength : D.inputLength=m
  letters : D.letters=P.bound
  valid : P.valid=fun _=>true
  internal : D.internal=n
  rule : ∀a b c,D.rule (P.encode a) (P.encode b) (P.encode c)=P.encode (C.rule a b c)
  input : ∀j : Fin m,D.input j.val=P.encode (C.input j)
  blank : D.blank=P.encode C.blank
  accepting : ∀i,D.accepting i=decide (∃f,P.encode f=i ∧ f∈C.accepting)
  marked : D.marked=marked.val
  epsilon : D.epsilon=ε.val
end VariableWL.CellularCatalog

namespace VariableWL.CellularCatalog.Program
open Computation.Stack.PolyRecipe Computation.Stack.Recipe VariableWL.NumericProgram
variable {n : ℕ}
structure Listing (n : ℕ) where
  bits : Expr n
  inputLength : Expr n
  letters : Expr n
  internal : Expr n
  rule : Expr (n+3)
  input : Expr (n+1)
  blank : Expr n
  accepting : Expr (n+1)
  marked : Expr n
  epsilon : Expr n
namespace Listing
variable (D : Listing n)
def eval (v : Env n) : Data where
  bits := D.bits.number v
  inputLength := D.inputLength.number v
  letters := D.letters.number v
  internal := D.internal.number v
  rule i j a := D.rule.number (cons (List.replicate i true) (cons (List.replicate j true) (cons (List.replicate a true) v)))
  input i := D.input.number (cons (List.replicate i true) v)
  blank := D.blank.number v
  accepting i := D.accepting.bit (cons (List.replicate i true) v)
  marked := D.marked.number v
  epsilon := D.epsilon.number v
def up : Listing (n+1) where
  bits := D.bits.up
  inputLength := D.inputLength.up
  letters := D.letters.up
  internal := D.internal.up
  rule := underThree D.rule
  input := underOne D.input
  blank := D.blank.up
  accepting := underOne D.accepting
  marked := D.marked.up
  epsilon := D.epsilon.up
noncomputable def leftEnd : Expr n := (mul D.bits (add (numeral 1) D.bits))
noncomputable def centerEnd : Expr n := (add D.leftEnd D.bits)
noncomputable def rightEnd : Expr n := (add D.centerEnd D.leftEnd)
noncomputable def kinds : Expr n := (add D.rightEnd (numeral 2))
noncomputable def triples : Expr n := (mul D.letters (mul D.letters D.letters))
noncomputable def tripleCode (E : Expr n) : Expr n := (div E D.kinds)
noncomputable def kindCode (E : Expr n) : Expr n := (mod E D.kinds)
noncomputable def first (T : Expr n) : Expr n := (div T (mul D.letters D.letters))
noncomputable def second (T : Expr n) : Expr n := (mod (div T D.letters) D.letters)
noncomputable def third (T : Expr n) : Expr n := (mod T D.letters)
noncomputable def kindTime (K : Expr n) : Expr n := (choose (lt K D.leftEnd) (div K (add (numeral 1) D.bits)) (choose (lt K D.centerEnd) (sub K D.leftEnd) (div (sub K D.centerEnd) (add (numeral 1) D.bits))))
noncomputable def kindPosition (K : Expr n) : Expr n := (choose (lt K D.leftEnd) (mod K (add (numeral 1) D.bits)) (mod (sub K D.centerEnd) (add (numeral 1) D.bits)))
noncomputable def source (E : Expr n) : Expr n := (choose (lt (D.kindCode E) D.leftEnd) (D.first (D.tripleCode E)) (choose (lt (D.kindCode E) D.centerEnd) (D.second (D.tripleCode E)) (choose (lt (D.kindCode E) D.rightEnd) (D.third (D.tripleCode E)) (add D.letters (add (mul (D.tripleCode E) (numeral 2)) (sub (D.kindCode E) D.rightEnd))))))
noncomputable def destination (E : Expr n) : Expr n := (choose (lt (D.kindCode E) D.centerEnd) (add D.letters (mul (D.tripleCode E) (numeral 2))) (choose (lt (D.kindCode E) (add D.rightEnd (numeral 1))) (add D.letters (add (mul (D.tripleCode E) (numeral 2)) (numeral 1))) (applyNat₃ D.rule (D.first (D.tripleCode E)) (D.second (D.tripleCode E)) (D.third (D.tripleCode E)))))
noncomputable def destinationForm (E : Expr n) : Expr n := (choose (lt (D.kindCode E) D.leftEnd) (numeral (AffineAlphabet.encodeForm (by decide : 2≤2) (LinearMap.proj 0))) (choose (lt (D.kindCode E) D.rightEnd) (numeral (AffineAlphabet.encodeForm (by decide : 2≤2) (LinearMap.proj 1))) (choose (lt (D.kindCode E) (add D.rightEnd (numeral 1))) (numeral (AffineAlphabet.encodeForm (by decide : 2≤2) (LinearMap.proj 0))) (numeral (AffineAlphabet.encodeForm (by decide : 1≤2) (LinearMap.proj 0))))))
def carryDomain (_D : Listing n) (B H I A : Expr n) : Expr n := (choose (lt I H) (eq A B) (choose (eq I H) (eq A (sub (numeral 1) B)) (literal [true])))
def cyclicDomain (D : Listing n) (B H I A : Expr n) : Expr n := (choose (eq H (numeral 0)) (eq A B) (D.carryDomain B (sub H (numeral 1)) I A))
noncomputable def domain (E I A : Expr n) : Expr n := (choose (lt (D.kindCode E) D.rightEnd) (choose (lt I D.bits) (D.carryDomain (numeral 1) (D.kindTime (D.kindCode E)) I A) (choose (lt (D.kindCode E) D.leftEnd) (D.cyclicDomain (numeral 1) (D.kindPosition (D.kindCode E)) (sub I D.bits) A) (choose (lt (D.kindCode E) D.centerEnd) (literal [true]) (D.cyclicDomain (numeral 0) (D.kindPosition (D.kindCode E)) (sub I D.bits) A)))) (literal [true]))
noncomputable def map (E I A : Expr n) : Expr n := (choose (lt (D.kindCode E) D.rightEnd) (choose (lt I D.bits) (choose (le I (D.kindTime (D.kindCode E))) (sub (numeral 1) A) A) (choose (disj (lt (D.kindCode E) D.leftEnd) (le D.centerEnd (D.kindCode E))) (choose (disj (eq (D.kindPosition (D.kindCode E)) (numeral 0)) (lt (sub I D.bits) (D.kindPosition (D.kindCode E)))) (sub (numeral 1) A) A) A)) A)
noncomputable def initialEnd : Expr n := (add D.inputLength (add (numeral 1) D.bits))
noncomputable def validRequest (B : Expr n) : Expr n := (choose (lt B D.inputLength) (literal [true]) (choose (eq B D.inputLength) (literal [true]) (choose (lt B D.initialEnd) (neg (binaryDigit D.inputLength (sub (sub B D.inputLength) (numeral 1)))) (applyNat D.accepting (sub B D.initialEnd)))))
noncomputable def requestGate (B : Expr n) : Expr n := (choose (lt B D.inputLength) (applyNat D.input B) (choose (lt B D.initialEnd) D.blank (sub B D.initialEnd)))
noncomputable def requestTest (B : Expr n) : Expr n := (choose (lt B D.initialEnd) (numeral 0) (numeral 1))
noncomputable def requestPositionDomain (B I A : Expr n) : Expr n := (choose (lt B D.inputLength) (eq A (choose (binaryDigit B I) (numeral 1) (numeral 0))) (choose (lt B D.initialEnd) (choose (disj (eq B D.inputLength) (lt (sub (sub B D.inputLength) (numeral 1)) I)) (eq A (choose (binaryDigit D.inputLength I) (numeral 1) (numeral 0))) (choose (eq I (sub (sub B D.inputLength) (numeral 1))) (eq A (numeral 1)) (literal [true]))) (literal [true])))
noncomputable def requestDomain (B I A : Expr n) : Expr n := (choose (lt I D.bits) (eq A (D.requestTest B)) (D.requestPositionDomain B (sub I D.bits) A))
noncomputable def catalog : CircuitCatalog.Program.Listing n where
  rows := add D.bits D.bits
  internal := D.internal
  scalars := D.letters
  ands := mul D.triples (numeral 2)
  edges := mul D.triples D.kinds
  requests := add D.initialEnd D.letters
  validScalar := literal [true]
  validAnd := literal [true]
  validEdge := literal [true]
  validRequest := D.up.validRequest (Computation.Stack.PolyRecipe.input 0)
  source := D.up.source (Computation.Stack.PolyRecipe.input 0)
  destination := D.up.destination (Computation.Stack.PolyRecipe.input 0)
  destinationForm := D.up.destinationForm (Computation.Stack.PolyRecipe.input 0)
  domain := D.up.up.up.domain (Computation.Stack.PolyRecipe.input 0) (Computation.Stack.PolyRecipe.input 1) (Computation.Stack.PolyRecipe.input 2)
  map := D.up.up.up.map (Computation.Stack.PolyRecipe.input 0) (Computation.Stack.PolyRecipe.input 1) (Computation.Stack.PolyRecipe.input 2)
  requestGate := D.up.requestGate (Computation.Stack.PolyRecipe.input 0)
  requestTest := D.up.requestTest (Computation.Stack.PolyRecipe.input 0)
  requestDomain := D.up.up.up.requestDomain (Computation.Stack.PolyRecipe.input 0) (Computation.Stack.PolyRecipe.input 1) (Computation.Stack.PolyRecipe.input 2)
  marked := D.marked
  epsilon := D.epsilon
end Listing
end VariableWL.CellularCatalog.Program

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

namespace VariableWL.AffineCatalog
open Blocks BlockCoordinates Descriptor VariableWL.Affine
attribute [local instance] Classical.propDecidable
namespace Data
 def resign (D : Data) (ε : Bit) : Data := {D with epsilon:=ε.val}
 noncomputable def descriptor (D : Data) (ε : Bit) : Descriptor.Data :=
   (D.resign ε).core.toPrefix.portData.expanded
end Data
theorem sortPredicate_congr {X Y : PrefixDescriptor.Data}
    (hv : X.validBlock=Y.validBlock) (hc : X.channelBound=Y.channelBound)
    (hd : X.dimension=Y.dimension) (hch : X.channels=Y.channels)
    (hr : X.root=Y.root) : X.sortPredicate=Y.sortPredicate := by
  cases X
  cases Y
  dsimp only at hv hc hd hch hr
  cases hv
  cases hc
  cases hd
  cases hch
  cases hr
  rfl
variable {r n : ℕ} {P : Type uVariable1} {E : Type uVariable2} [Fintype P] [Fintype E]
variable (PP : Presentation P) (PE : Presentation E) (J : ProductImages.Instance r P E)
variable (hr : 2≤r) (hn : 0<n) (marked : Fin r) {D : Data} {ε₀ : Bit}
variable (h : Good (n := n) PP PE J marked ε₀ D)
omit [Fintype P] [Fintype E] in
include h in
 theorem resign_good (ε : Bit) : Good (n := n) PP PE J marked ε (D.resign ε) := by
  exact ⟨h.toGood,h.realDimension,h.leftForm,h.rightForm,h.leftConstant,h.rightConstant,h.marked,rfl⟩
noncomputable def blockPresentation := BlockCatalog.block PP PE J h.toGood
noncomputable def readPresentation := BlockCatalog.readout (r := r) (n := n) PP PE
omit [Fintype P] [Fintype E] in
theorem coordinateBound : ∀b : Block (n := n) J,
    Fintype.card (BlockCoordinates.Coordinate J b.val)≤6 :=
  fun b => RealizationSize.coordinate_card J b.val
omit [Fintype P] [Fintype E] in
include h in
 theorem core_resign_good (ε : Bit) :
    BlockDescriptor.Good J hr hn marked (blockPresentation PP PE J marked h)
      (readPresentation (r := r) (n := n) PP PE) (coordinateBound (n := n) J) ε (D.resign ε).core :=
    core_good PP PE J marked ε (resign_good PP PE J marked h ε) hr hn
@[instance_reducible] noncomputable def properNumbering : ∀b : Block (n := n) J, FiniteNumbering (Proper J b) :=
  BlockDescriptor.properNumberings J hr hn marked (blockPresentation PP PE J marked h)
    (readPresentation (r := r) (n := n) PP PE) (coordinateBound (n := n) J) 0
    (core_resign_good PP PE J hr hn marked h 0)
include h in
 theorem properNumbering_eq (ε : Bit) :
    BlockDescriptor.properNumberings J hr hn marked (blockPresentation PP PE J marked h)
      (readPresentation (r := r) (n := n) PP PE) (coordinateBound (n := n) J) ε
      (core_resign_good PP PE J hr hn marked h ε)=properNumbering PP PE J hr hn marked h := rfl
include h in
 theorem prefix_resign_good (ε : Bit) :
    let _ := properNumbering PP PE J hr hn marked h
    PrefixDescriptor.Good (blockPresentation PP PE J marked h) (data J hr hn marked)
      (coordinateBound (n := n) J) ε (D.resign ε).core.toPrefix := by
  have ht := BlockDescriptor.prefix_good J hr hn marked (blockPresentation PP PE J marked h)
    (readPresentation (r := r) (n := n) PP PE) (coordinateBound (n := n) J) ε
    (core_resign_good PP PE J hr hn marked h ε)
  rw [properNumbering_eq PP PE J hr hn marked h ε] at ht
  exact ht
include h in
 theorem matching_resign_good (ε : Bit) :
    let _ := properNumbering PP PE J hr hn marked h
    PrefixDescriptor.MatchingGood (blockPresentation PP PE J marked h) (data J hr hn marked)
      (D.resign ε).core.toPrefix (wiring J hr hn marked) := by
  have ht := BlockDescriptor.matching_good J hr hn marked (blockPresentation PP PE J marked h)
    (readPresentation (r := r) (n := n) PP PE) (coordinateBound (n := n) J) ε
    (core_resign_good PP PE J hr hn marked h ε)
  rw [properNumbering_eq PP PE J hr hn marked h ε] at ht
  exact ht
include hr hn h in
 theorem descriptor_sound (ε : Bit) : (D.descriptor ε).Sound := by
  let : ∀b : Block (n := n) J,FiniteNumbering (Proper J b) := properNumbering PP PE J hr hn marked h
  exact Descriptor.PortData.sound_expanded _
    (PrefixDescriptor.port_sound (blockPresentation PP PE J marked h) (data J hr hn marked)
      (coordinateBound (n := n) J) ε (prefix_resign_good PP PE J hr hn marked h ε)
      (wiring J hr hn marked) (matching_resign_good PP PE J hr hn marked h ε))
noncomputable def sortPresentation :
    let _ := properNumbering PP PE J hr hn marked h
    Presentation (PrefixParts.Wiring.SortTag (data J hr hn marked)) := by
  letI : ∀b : Block (n := n) J,FiniteNumbering (Proper J b) := properNumbering PP PE J hr hn marked h
  exact Classical.choose (PrefixDescriptor.sortPresentation (blockPresentation PP PE J marked h)
    (data J hr hn marked) (coordinateBound (n := n) J) 0 (prefix_resign_good PP PE J hr hn marked h 0))
 theorem core_proper_resign (ε : Bit) :
    (D.resign ε).core.proper=(D.resign 0).core.proper := by
  funext b i
  rfl
 theorem core_channels_resign (ε : Bit) :
    (D.resign ε).core.channels=(D.resign 0).core.channels := by
  funext b
  simp only [BlockDescriptor.Core.channels,core_proper_resign]
  rfl
 theorem core_dimension_resign (ε : Bit) :
    (D.resign ε).core.dimension=(D.resign 0).core.dimension := by
  funext b
  rfl
 theorem core_readDimension_resign (ε : Bit) :
    (D.resign ε).core.readDimension=(D.resign 0).core.readDimension := by
  funext b
  rfl
 theorem core_root_resign (ε : Bit) :
    (D.resign ε).core.root=(D.resign 0).core.root := by
  funext b c
  simp only [BlockDescriptor.Core.root,BlockDescriptor.Core.readout,
    BlockDescriptor.Core.select,core_readDimension_resign,core_proper_resign]
  rfl
 theorem prefix_channelBound_resign (ε : Bit) :
    (D.resign ε).core.toPrefix.channelBound=(D.resign 0).core.toPrefix.channelBound := by
  simp only [BlockDescriptor.Core.toPrefix,BlockDescriptor.Core.channelBound,
    BlockDescriptor.Core.properBound,Data.core,Data.resign]
 theorem prefix_sortPredicate_resign (ε : Bit) :
    (D.resign ε).core.toPrefix.sortPredicate=(D.resign 0).core.toPrefix.sortPredicate := by
  exact sortPredicate_congr (X := (D.resign ε).core.toPrefix)
    (Y := (D.resign 0).core.toPrefix) rfl (prefix_channelBound_resign (D := D) ε)
    (core_dimension_resign (D := D) ε)
    (core_channels_resign (D := D) ε) (core_root_resign (D := D) ε)
 theorem prefix_tag_resign (ε : Bit) :
    (D.resign ε).core.toPrefix.tag=(D.resign 0).core.toPrefix.tag := by
  funext x
  simp only [PrefixDescriptor.Data.tag,BlockDescriptor.Core.toPrefix,
    BlockDescriptor.Core.channelBound,BlockDescriptor.Core.properBound,Data.core,Data.resign]
include h in
 theorem sort_spec :
    let _ := properNumbering PP PE J hr hn marked h
    let S := sortPresentation PP PE J hr hn marked h
    let X := (D.resign 0).core.toPrefix
    S.bound=X.sortBound ∧ S.valid=X.sortPredicate ∧
      ∀s,S.encode s=X.tag (PrefixDescriptor.sortRaw (blockPresentation PP PE J marked h) (data J hr hn marked) s) := by
  let : ∀b : Block (n := n) J,FiniteNumbering (Proper J b) := properNumbering PP PE J hr hn marked h
  exact Classical.choose_spec (PrefixDescriptor.sortPresentation (blockPresentation PP PE J marked h)
    (data J hr hn marked) (coordinateBound (n := n) J) 0 (prefix_resign_good PP PE J hr hn marked h 0))
include h in
 theorem sort_valid (ε : Bit) :
    (sortPresentation PP PE J hr hn marked h).valid=(D.resign ε).core.toPrefix.sortPredicate := by
  rw [prefix_sortPredicate_resign]
  exact (sort_spec PP PE J hr hn marked h).2.1
include h in
 theorem sort_encode (ε : Bit) :
    let _ := properNumbering PP PE J hr hn marked h
    ∀s,(sortPresentation PP PE J hr hn marked h).encode s=
      (D.resign ε).core.toPrefix.tag (PrefixDescriptor.sortRaw (blockPresentation PP PE J marked h) (data J hr hn marked) s) := by
  intro _ s
  rw [prefix_tag_resign]
  exact (sort_spec PP PE J hr hn marked h).2.2 s
noncomputable def descriptor_iso (ε : Bit) :
    let _ := properNumbering PP PE J hr hn marked h
    let _ : FiniteNumbering (Block (n := n) J) := (blockPresentation PP PE J marked h).numbering
    let _ : FiniteNumbering (PrefixParts.Wiring.SortTag (data J hr hn marked)) := (sortPresentation PP PE J hr hn marked h).numbering
    ((D.descriptor ε).graph (descriptor_sound PP PE J hr hn marked h ε)).graph ≃g
      (Subcubic.finiteGraph J hr hn marked ε).graph := by
  letI : ∀b : Block (n := n) J,FiniteNumbering (Proper J b) := properNumbering PP PE J hr hn marked h
  letI : FiniteNumbering (Block (n := n) J) := (blockPresentation PP PE J marked h).numbering
  letI : FiniteNumbering (PrefixParts.Wiring.SortTag (data J hr hn marked)) := (sortPresentation PP PE J hr hn marked h).numbering
  exact (PrefixDescriptor.uncoloredIso (blockPresentation PP PE J marked h) (data J hr hn marked)
    (coordinateBound (n := n) J) ε (prefix_resign_good PP PE J hr hn marked h ε)
    (wiring J hr hn marked) (matching_resign_good PP PE J hr hn marked h ε)
    (sortPresentation PP PE J hr hn marked h) (sort_valid PP PE J hr hn marked h ε)
    (sort_encode PP PE J hr hn marked h ε)).trans (TypedGame.numbering (Subcubic.graph J hr hn marked ε))
end VariableWL.AffineCatalog

namespace VariableWL.AffineCatalog.Program.Listing
open Computation.Stack.PolyRecipe
variable {n : ℕ} (D : Listing n)
noncomputable def graph : GraphListing n := D.core.toPrefix.portListing.expanded
end VariableWL.AffineCatalog.Program.Listing
namespace VariableWL.CellularCatalog.Program.Listing
open Computation.Stack.PolyRecipe
variable {n : ℕ} (D : Listing n)
noncomputable def graph : GraphListing n := D.catalog.affine.graph
end VariableWL.CellularCatalog.Program.Listing
namespace VariableWL.CellularCatalog.Data
 def resign (D : Data) (ε : Affine.Bit) : Data := {D with epsilon:=ε.val}
end VariableWL.CellularCatalog.Data

end OAI
end


