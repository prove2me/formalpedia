-- Prove2me | Definitions.Def_OAIFAE000
-- name    : OAIFAE000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-24T19:22:33.573212+00:00
-- url     : https://prove2.me/theorems/dfbc324c-08ed-45d0-ad99-1c5bef252ce9
-- title:
--   Definitions bundle OAIFAE000 of the split of OpenAI, Finite algebraic envelopes and the Boone–Higman conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.FiniteAlgebraicEnvelopes.main`, carved from OpenAI's openai/math development (OpenAI, *Finite algebraic envelopes and the Boone–Higman conjecture*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1065 declarations of OpenAI's Lean: 435 definitions, 44 inductive types or structures, 21 instances and 565 theorems. The definitions and types are `OAI.FiniteAlgebraicEnvelopes.Adjacent.Presentation`, `OAI.FiniteAlgebraicEnvelopes.Adjacent.Relations`, `OAI.FiniteAlgebraicEnvelopes.Adjacent.descending`, `OAI.FiniteAlgebraicEnvelopes.Adjacent.finEvaluation`, `OAI.FiniteAlgebraicEnvelopes.Adjacent.finSwap`, `OAI.FiniteAlgebraicEnvelopes.Adjacent.first`, `OAI.FiniteAlgebraicEnvelopes.Adjacent.generator`, `OAI.FiniteAlgebraicEnvelopes.Adjacent.inclusion`, `OAI.FiniteAlgebraicEnvelopes.Adjacent.lift`, `OAI.FiniteAlgebraicEnvelopes.Adjacent.natEvaluation`, `OAI.FiniteAlgebraicEnvelopes.Adjacent.natExtend`, `OAI.FiniteAlgebraicEnvelopes.Adjacent.natSwap`, `OAI.FiniteAlgebraicEnvelopes.Adjacent.permutationEquiv`, `OAI.FiniteAlgebraicEnvelopes.Adjacent.permutationLift`, `OAI.FiniteAlgebraicEnvelopes.Adjacent.relators`, `OAI.FiniteAlgebraicEnvelopes.AffineAction.Group`, `OAI.FiniteAlgebraicEnvelopes.AffineAction.action`, `OAI.FiniteAlgebraicEnvelopes.AffineAction.elementary`, `OAI.FiniteAlgebraicEnvelopes.AffineAction.transvection`, `OAI.FiniteAlgebraicEnvelopes.AffinePermutation.stabilizerEquivalenceAt`, `OAI.FiniteAlgebraicEnvelopes.AffinePresentation.X`, `OAI.FiniteAlgebraicEnvelopes.AffinePresentation.lift`, `OAI.FiniteAlgebraicEnvelopes.AffinePresentation.other`, `OAI.FiniteAlgebraicEnvelopes.AffinePresentation.rowMap`, `OAI.FiniteAlgebraicEnvelopes.AffinePresentation.translations`, `OAI.FiniteAlgebraicEnvelopes.AffinePresentation.translationsAdd`, `OAI.FiniteAlgebraicEnvelopes.AffinePresentation.w`, `OAI.FiniteAlgebraicEnvelopes.AffinePresentation.wAdd`, `OAI.FiniteAlgebraicEnvelopes.AffinePresentation.wcolumn`, `OAI.FiniteAlgebraicEnvelopes.AlgebraGenerators.tensorGenerators`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Absorbs`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Base.absorption`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Base.table`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.BlockCode`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.BlockCode.Alphabet`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.BlockCode.block`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.BlockCode.encode`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Canonical.candidates`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Canonical.least`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Canonical.pickStep` and 439 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory/BooneHigman, lean/OAI/Computability/FiniteCompiler, in whole or in part: `ActionEnvelope`, `AdjacentPermutations`, `Affine`, `AlgebraPresentations`, `BinaryCoherence`, `Control`, `Effectivity`, `Machines`, `MonoidAlgebras`, `Normalization`, `PartialAffine`, `Paths`, `Quotients`, `Rewriting`, `Selectors`, `SelfReference`, `Simulator`, `Steinberg`, `Surface`, `TapeFolding`, `Transition`, `UniformControl`, `UniformMachines`, `UniformPaths`, `Validator`.
--
--   **Imports.** It imports the published bundle `Def_BooneHigman`.
--
--   **Imported by** (directly, in this split): the bundles `OAIFAE002` and `OAIFAE003`.
-- source:
--   OpenAI, Finite algebraic envelopes and the Boone–Higman conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Finite-algebraic-envelopes-and-the-Boone-Higman-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory/BooneHigman, lean/OAI/Computability/FiniteCompiler at commit adc7f12

import Mathlib
import Definitions.Def_BooneHigman

section
-- module Solutions.OAIFAE.Compat
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
-- module Solutions.OAIFAE.Steinberg
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
Nonunital correction, Steinberg groups, corners, and kernel annihilation.
-/


namespace FiniteAlgebraicEnvelopes

universe u


/-! The correction for a nonunital coefficient map in the affine transition and product identities.
The proof works over a noncommutative ring. -/


/-! The Steinberg presentation in the Steinberg kernel argument.  No stability or centrality
 theorem is assumed.  Root indices are restricted to the off-diagonal. -/
namespace Steinberg
open scoped commutatorElement

abbrev Index (ι : Type*) := {p : ι × ι // p.1 ≠ p.2}
abbrev Generator (ι R : Type*) := Index ι × R

def freeRoot {ι R : Type*} (i j : ι) (h : i ≠ j) (a : R) :
    FreeGroup (Generator ι R) := FreeGroup.of (⟨(i, j), h⟩, a)

inductive Relation (ι R : Type*) [Ring R] : FreeGroup (Generator ι R) → Prop
  | additive (i j : ι) (h : i ≠ j) (a b : R) :
      Relation ι R (freeRoot i j h a * freeRoot i j h b *
        (freeRoot i j h (a + b))⁻¹)
  | chain (i j k : ι) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
      Relation ι R (⁅freeRoot i j hij a, freeRoot j k hjk b⁆ *
        (freeRoot i k hik (a * b))⁻¹)
  | distant (i j k l : ι) (hij : i ≠ j) (hkl : k ≠ l)
      (hil : i ≠ l) (hjk : j ≠ k) (a b : R) :
      Relation ι R ⁅freeRoot i j hij a, freeRoot k l hkl b⁆

abbrev Group (ι R : Type*) [Ring R] := PresentedGroup {w | Relation ι R w}

variable {ι R S : Type*} [Ring R] [Ring S]

def root (i j : ι) (h : i ≠ j) (a : R) : Group ι R :=
  PresentedGroup.of (⟨(i, j), h⟩, a)

@[simp] theorem mk_freeRoot (i j : ι) (h : i ≠ j) (a : R) :
    PresentedGroup.mk {w | Relation ι R w} (freeRoot i j h a) = root i j h a := rfl

theorem root_add (i j : ι) (h : i ≠ j) (a b : R) :
    root i j h a * root i j h b = root i j h (a + b) := by
  exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (Relation.additive i j h a b)

theorem root_chain (i j k : ι) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : R) : ⁅root i j hij a, root j k hjk b⁆ = root i k hik (a * b) := by
  simpa only [map_commutatorElement, mk_freeRoot] using
    (PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := {w | Relation ι R w}) (Relation.chain i j k hij hjk hik a b))

theorem root_distant (i j k l : ι) (hij : i ≠ j) (hkl : k ≠ l)
    (hil : i ≠ l) (hjk : j ≠ k) (a b : R) :
    Commute (root i j hij a) (root k l hkl b) := by
  apply commutatorElement_eq_one_iff_commute.mp
  simpa only [map_commutatorElement, mk_freeRoot] using
    PresentedGroup.one_of_mem (rels := {w | Relation ι R w}) (Relation.distant i j k l hij hkl hil hjk a b)

@[simp] theorem root_zero (i j : ι) (h : i ≠ j) : root i j h (0 : R) = 1 := by
  have h0 := root_add i j h (0 : R) 0
  simpa using h0

@[simp] theorem root_neg (i j : ι) (h : i ≠ j) (a : R) :
    root i j h (-a) = (root i j h a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [root_add, add_neg_cancel, root_zero]

/-- Every additive multiplicative coefficient map induces a Steinberg map;
it is not required to preserve one. -/
def coefficientMap (ψ : R →ₙ+* S) : Group ι R →* Group ι S :=
  PresentedGroup.toGroup (f := fun z : Generator ι R =>
    root z.1.1.1 z.1.1.2 z.1.2 (ψ z.2)) (by
      intro w hw
      cases hw with
      | additive i j h a b =>
        simp only [map_mul, map_inv, freeRoot, FreeGroup.lift_apply_of, map_add]
        rw [root_add, mul_inv_cancel]
      | chain i j k hij hjk hik a b =>
        simp only [map_mul, map_inv, map_commutatorElement, freeRoot,
          FreeGroup.lift_apply_of, map_mul]
        rw [root_chain i j k hij hjk hik, mul_inv_cancel]
      | distant i j k l hij hkl hil hjk a b =>
        simp only [map_commutatorElement, freeRoot, FreeGroup.lift_apply_of]
        exact (root_distant i j k l hij hkl hil hjk (ψ a) (ψ b)).commutator_eq)

@[simp] theorem coefficientMap_root (ψ : R →ₙ+* S) (i j : ι) (h : i ≠ j) (a : R) :
    coefficientMap ψ (root i j h a) = root i j h (ψ a) :=
  PresentedGroup.toGroup.of _


section TotalRoots
variable [DecidableEq ι]

/-- A total notation: the unused diagonal root is the identity. -/
def x (i j : ι) (a : R) : Group ι R := if h : i = j then 1 else root i j h a

@[simp] theorem x_self (i : ι) (a : R) : x i i a = 1 := by simp [x]

theorem x_of_ne (i j : ι) (h : i ≠ j) (a : R) : x i j a = root i j h a := by
  simp [x, h]

@[simp] theorem x_zero (i j : ι) : x i j (0 : R) = 1 := by
  unfold x
  split_ifs <;> simp

theorem x_add (i j : ι) (a b : R) : x i j (a + b) = x i j a * x i j b := by
  by_cases h : i = j
  · subst j; simp
  · simp only [x_of_ne i j h]
    exact (root_add i j h a b).symm

@[simp] theorem x_neg (i j : ι) (a : R) : x i j (-a) = (x i j a)⁻¹ := by
  by_cases h : i = j
  · subst j; simp
  · simp only [x_of_ne i j h, root_neg]

theorem x_distant (i j k l : ι) (hil : i ≠ l) (hjk : j ≠ k) (a b : R) :
    Commute (x i j a) (x k l b) := by
  by_cases hij : i = j
  · subst j; simp
  by_cases hkl : k = l
  · subst l; simp
  simp only [x_of_ne i j hij, x_of_ne k l hkl]
  exact root_distant i j k l hij hkl hil hjk a b

theorem x_chain (i j k : ι) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : R) : ⁅x i j a, x j k b⁆ = x i k (a * b) := by
  simp only [x_of_ne i j hij, x_of_ne j k hjk, x_of_ne i k hik]
  exact root_chain i j k hij hjk hik a b

/-- Additive root parametrization, without assuming a commutative ring. -/
def xAddHom (i j : ι) : R →+ Additive (Group ι R) where
  toFun a := Additive.ofMul (x i j a)
  map_zero' := x_zero i j
  map_add' := x_add i j

@[simp] theorem xAddHom_apply (i j : ι) (a : R) :
    xAddHom i j a = Additive.ofMul (x i j a) := rfl

end TotalRoots

section MatrixRepresentation
variable [Fintype ι] [DecidableEq ι]

/-- Elementary matrices over an arbitrary, possibly noncommutative, ring. -/
def elementary (i j : ι) (h : i ≠ j) (a : R) : (Matrix ι ι R)ˣ where
  val := 1 + Matrix.single i j a
  inv := 1 - Matrix.single i j a
  val_inv := by
    have h0 : Matrix.single i j a * Matrix.single i j a = 0 :=
      Matrix.single_mul_single_of_ne a i j i h.symm a
    calc
      (1 + Matrix.single i j a) * (1 - Matrix.single i j a) =
          1 - Matrix.single i j a * Matrix.single i j a := by noncomm_ring
      _ = 1 := by rw [h0, sub_zero]
  inv_val := by
    have h0 : Matrix.single i j a * Matrix.single i j a = 0 :=
      Matrix.single_mul_single_of_ne a i j i h.symm a
    calc
      (1 - Matrix.single i j a) * (1 + Matrix.single i j a) =
          1 - Matrix.single i j a * Matrix.single i j a := by noncomm_ring
      _ = 1 := by rw [h0, sub_zero]

@[simp] theorem elementary_val (i j : ι) (h : i ≠ j) (a : R) :
    (elementary i j h a : Matrix ι ι R) = 1 + Matrix.single i j a := rfl

@[simp] theorem elementary_inv_val (i j : ι) (h : i ≠ j) (a : R) :
    ((elementary i j h a)⁻¹).val = 1 - Matrix.single i j a := rfl

theorem elementary_add (i j : ι) (h : i ≠ j) (a b : R) :
    elementary i j h a * elementary i j h b = elementary i j h (a + b) := by
  apply Units.ext
  simp only [Units.val_mul, elementary_val, Matrix.single_add]
  simp only [add_mul, mul_add, one_mul, mul_one,
    Matrix.single_mul_single_of_ne a i j i h.symm b, add_zero]
  abel

theorem elementary_chain (i j k : ι) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : R) : ⁅elementary i j hij a, elementary j k hjk b⁆ =
      elementary i k hik (a * b) := by
  apply Units.ext
  simp only [commutatorElement_def, Units.val_mul, elementary_val, elementary_inv_val]
  simp only [add_mul, mul_add, mul_sub, sub_mul, one_mul, mul_one,
    Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne _ _ _ _ hij.symm,
    Matrix.single_mul_single_of_ne _ _ _ _ hjk.symm,
    Matrix.single_mul_single_of_ne _ _ _ _ hik.symm, zero_mul]
  noncomm_ring

theorem elementary_distant (i j k l : ι) (hij : i ≠ j) (hkl : k ≠ l)
    (hil : i ≠ l) (hjk : j ≠ k) (a b : R) :
    Commute (elementary i j hij a) (elementary k l hkl b) := by
  apply Units.ext
  simp only [Units.val_mul, elementary_val, add_mul, mul_add, one_mul, mul_one,
    Matrix.single_mul_single_of_ne _ _ _ _ hjk,
    Matrix.single_mul_single_of_ne _ _ _ _ hil.symm, add_zero]
  abel

/-- The matrix action of the presented Steinberg group.  Its codomain here is
all matrix units rather than the equal image subgroup E_n(R). -/
def matrixMap : Group ι R →* (Matrix ι ι R)ˣ :=
  PresentedGroup.toGroup (f := fun z : Generator ι R =>
    elementary z.1.1.1 z.1.1.2 z.1.2 z.2) (by
      intro w hw
      cases hw with
      | additive i j h a b =>
        simp only [map_mul, map_inv, freeRoot, FreeGroup.lift_apply_of]
        rw [elementary_add, mul_inv_cancel]
      | chain i j k hij hjk hik a b =>
        simp only [map_mul, map_inv, map_commutatorElement, freeRoot,
          FreeGroup.lift_apply_of]
        rw [elementary_chain i j k hij hjk hik, mul_inv_cancel]
      | distant i j k l hij hkl hil hjk a b =>
        simp only [map_commutatorElement, freeRoot, FreeGroup.lift_apply_of]
        exact (elementary_distant i j k l hij hkl hil hjk a b).commutator_eq)

@[simp] theorem matrixMap_root (i j : ι) (h : i ≠ j) (a : R) :
    matrixMap (root i j h a) = elementary i j h a := PresentedGroup.toGroup.of _

omit [Fintype ι] in
theorem column_roots_commute (i j k : ι) (a b : R) :
    Commute (x i k a) (x j k b) := by
  by_cases hi : i = k
  · subst i; simp
  by_cases hj : j = k
  · subst j; simp
  exact x_distant i k j k hi (Ne.symm hj) a b

def columnAddHom (k : ι) : (ι → R) →+ Additive (Group ι R) :=
  AddMonoidHom.noncommPiCoprod (fun i => xAddHom i k) (by
    intro i j _ a b
    exact column_roots_commute i j k a b)

def column (k : ι) (v : ι → R) : Group ι R := (columnAddHom k v).toMul

@[simp] theorem column_single (k i : ι) (a : R) :
    column k (Pi.single i a) = x i k a :=
  congrArg Additive.toMul (AddMonoidHom.noncommPiCoprod_single (fun i => xAddHom i k) i a)

@[simp] theorem column_zero (k : ι) : column k (0 : ι → R) = 1 :=
  (columnAddHom k).map_zero

/-- Additive notation for conjugation in the Steinberg group. -/
def conjugateAddHom (g : Group ι R) : Additive (Group ι R) →+ Additive (Group ι R) :=
  (MulAut.conj g).toMonoidHom.toAdditive

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem conjugateAddHom_apply (g z : Group ι R) :
    conjugateAddHom g (Additive.ofMul z) = Additive.ofMul (g * z * g⁻¹) := rfl

omit [Fintype ι] in
theorem row_roots_commute (i j k : ι) (a b : R) :
    Commute (x k i a) (x k j b) := by
  by_cases hi : k = i
  · subst i; simp
  by_cases hj : k = j
  · subst j; simp
  exact x_distant k i k j hj (Ne.symm hi) a b

def rowAddHom (k : ι) : (ι → R) →+ Additive (Group ι R) :=
  AddMonoidHom.noncommPiCoprod (fun i => xAddHom k i) (by
    intro i j _ a b
    exact row_roots_commute i j k a b)

def row (k : ι) (v : ι → R) : Group ι R := (rowAddHom k v).toMul

@[simp] theorem row_single (k i : ι) (a : R) :
    row k (Pi.single i a) = x k i a :=
  congrArg Additive.toMul (AddMonoidHom.noncommPiCoprod_single (fun i => xAddHom k i) i a)

@[simp] theorem row_zero (k : ι) : row k (0 : ι → R) = 1 := (rowAddHom k).map_zero

end MatrixRepresentation


/-! Orthogonal equivalent corners, as specified by (corner-equivalence)
in the Steinberg kernel argument. The symbol `e` below is the specified d*, not an involution. -/

end Steinberg

end FiniteAlgebraicEnvelopes

end OAI
end

section
-- module Solutions.OAIFAE.Affine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
Rank-six affine relations, modules, and finite affine presentations.
-/


/- The rank-six affine presentation. -/
namespace FiniteAlgebraicEnvelopes
namespace AffinePresentation
open scoped commutatorElement

variable {R Q : Type*} [Ring R] [Group Q]
variable (ρ : Steinberg.Group (Fin 6) R →* Q) (p : Fin 6 → Q)

abbrev X (a b : Fin 6) (r : R) := ρ (Steinberg.x a b r)

@[simp] theorem X_zero (a b : Fin 6) : X ρ a b (0 : R) = 1 := by simp [X]
theorem X_add (a b : Fin 6) (r s : R) : X ρ a b (r+s) = X ρ a b r * X ρ a b s := by
  simp only [X, Steinberg.x_add, map_mul]
@[simp] theorem X_neg (a b : Fin 6) (r : R) : X ρ a b (-r) = (X ρ a b r)⁻¹ := by simp [X]
theorem X_chain (a b c : Fin 6) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (r s : R) :
    ⁅X ρ a b r, X ρ b c s⁆ = X ρ a c (r*s) := by
  rw [← map_commutatorElement, Steinberg.x_chain a b c hab hbc hac]
theorem X_distant (a b c d : Fin 6) (had : a ≠ d) (hbc : b ≠ c) (r s : R) :
    Commute (X ρ a b r) (X ρ c d s) := (Steinberg.x_distant a b c d had hbc r s).map ρ

theorem fresh (a b c : Fin 6) : ∃ h : Fin 6, h ≠ a ∧ h ≠ b ∧ h ≠ c := by
  have h : ∃ i ∈ (Finset.univ : Finset (Fin 6)), i ∉ ({a,b,c} : Finset (Fin 6)) := by
    apply Finset.exists_mem_notMem_of_card_lt_card
    have : ({a,b,c} : Finset (Fin 6)).card ≤ 3 := by
      exact le_trans (Finset.card_insert_le _ _) (by
        simpa only [Finset.card_singleton] using
          Nat.add_le_add_right (Finset.card_insert_le b {c}) 1)
    simpa using (show ({a,b,c} : Finset (Fin 6)).card < 6 by omega)
  simpa only [Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton,
    not_or] using h

theorem commutator_commute {a b c : Q} (hb : Commute a b) (hc : Commute a c) :
    Commute a ⁅b,c⁆ := by
  rw [commutatorElement_def]
  exact ((hb.mul_right hc).mul_right hb.inv_right).mul_right hc.inv_right

/-- The finite coefficient relations propagate to every coefficient. -/
theorem coefficients (F : Finset R) (h1 : (1:R) ∈ F)
    (hgen : Subring.closure (↑F : Set R) = ⊤)
    (hc : ∀ r ∈ F, ∀ a b c : Fin 6, c ≠ b → Commute (X ρ a b r) (p c)) :
    ∀ r : R, ∀ a b c : Fin 6, c ≠ b → Commute (X ρ a b r) (p c) := by
  intro r
  have hr : r ∈ Subring.closure (↑F : Set R) := by rw [hgen]; trivial
  induction hr using Subring.closure_induction with
  | mem r hr => exact hc r hr
  | zero => intro a b c _; simp
  | one => exact hc 1 h1
  | add r s _ _ hr hs => intro a b c h; rw [X_add]; exact (hr a b c h).mul_left (hs a b c h)
  | neg r _ hr => intro a b c h; rw [X_neg]; exact (hr a b c h).inv_left
  | mul r s _ _ hr hs =>
    intro a b c hcb
    by_cases hab : a = b
    · subst b; simp [X]
    obtain ⟨h,ha,hb,hc'⟩ := fresh a b c
    rw [← X_chain ρ a h b ha.symm hb hab]
    exact (commutator_commute (hr a h c hc'.symm).symm (hs h b c hcb).symm).symm

variable (hp : ∀ a b, Commute (p a) (p b))
variable (hc : ∀ r : R, ∀ a b c : Fin 6, c ≠ b → Commute (X ρ a b r) (p c))
variable (hu : ∀ a b, a ≠ b → ⁅X ρ a b 1, p b⁆ = p a)

def wcolumn (a b : Fin 6) (r : R) : Q := ⁅X ρ a b r, p b⁆

theorem conj_of_commute {x y : Q} (h : Commute x y) : MulAut.conj x y = y := by
  rw [conj_eq_commutatorElement_mul, h.commutator_eq, one_mul]

theorem mul_eq_commutator (x y : Q) : x*y = ⁅x,y⁆*y*x := by
  simp [commutatorElement_def, mul_assoc]

include hp hc hu

/-- Independence of the auxiliary column in the presentation. -/
theorem wcolumn_independent (a b h : Fin 6) (hab : a ≠ b) (hah : a ≠ h) (hbh : b ≠ h) (r : R) :
    wcolumn ρ p a b r = wcolumn ρ p a h r := by
  have hxy : X ρ a h r * X ρ h b 1 = X ρ a b r * X ρ h b 1 * X ρ a h r := by
    rw [mul_eq_commutator, X_chain ρ a h b hah hbh.symm hab, mul_one]
  have hy : MulAut.conj (X ρ h b 1) (p b) = p h * p b := by
    rw [conj_eq_commutatorElement_mul, hu h b hbh.symm]
  have hx : MulAut.conj (X ρ a h r) (p b) = p b := conj_of_commute (hc r a h b hbh)
  have hz : MulAut.conj (X ρ a b r) (p h) = p h := conj_of_commute (hc r a b h hbh.symm)
  have hh := congrArg (fun q => MulAut.conj q (p b)) hxy
  simp only [map_mul, MulAut.mul_apply] at hh
  simp only [hy, map_mul, hx, hz] at hh
  rw [conj_eq_commutatorElement_mul, conj_eq_commutatorElement_mul] at hh
  have cc : Commute (p h) (wcolumn ρ p a b r) :=
    commutator_commute (hc r a b h hbh.symm).symm (hp h b)
  change (wcolumn ρ p a h r * p h) * p b = p h * (wcolumn ρ p a b r * p b) at hh
  have he : wcolumn ρ p a h r * p h = p h * wcolumn ρ p a b r :=
    mul_right_cancel (by simpa only [mul_assoc] using hh)
  rw [cc.eq] at he
  exact (mul_right_cancel he).symm


noncomputable def other (a : Fin 6) : Fin 6 := (fresh a a a).choose

omit hp hc hu in
theorem other_ne (a : Fin 6) : other a ≠ a := (fresh a a a).choose_spec.1

noncomputable def w (a : Fin 6) (r : R) : Q := wcolumn ρ p a (other a) r

theorem w_eq_column (a b : Fin 6) (hab : a ≠ b) (r : R) :
    w ρ p a r = wcolumn ρ p a b r := by
  by_cases hb : other a = b
  · simp [w, hb]
  · exact wcolumn_independent ρ p hp hc hu a (other a) b (other_ne a).symm hab hb r

theorem w_commute_p (a c : Fin 6) (r : R) : Commute (w ρ p a r) (p c) := by
  obtain ⟨b,ha,hc',_⟩ := fresh a c c
  rw [w_eq_column ρ p hp hc hu a b ha.symm]
  exact (commutator_commute (hc r a b c hc'.symm).symm (hp c b)).symm

theorem w_commute_X (a c d : Fin 6) (hda : d ≠ a) (r s : R) :
    Commute (w ρ p a r) (X ρ c d s) := by
  obtain ⟨b,ha,hb,hbd⟩ := fresh a c d
  rw [w_eq_column ρ p hp hc hu a b ha.symm]
  exact (commutator_commute (X_distant ρ a b c d hda.symm hb r s).symm
    (hc s c d b hbd)).symm

theorem w_commute (a c : Fin 6) (r s : R) : Commute (w ρ p a r) (w ρ p c s) := by
  obtain ⟨b,ha,hb,_⟩ := fresh a c c
  rw [w_eq_column ρ p hp hc hu c b hb.symm]
  exact commutator_commute (w_commute_X ρ p hp hc hu a c b ha r s)
    (w_commute_p ρ p hp hc hu a b r)

omit hp hc hu in
@[simp] theorem w_zero (a : Fin 6) : w ρ p a (0:R) = 1 := by
  simp [w, wcolumn]

theorem w_add (a : Fin 6) (r s : R) : w ρ p a (r+s) = w ρ p a r * w ρ p a s := by
  let b := other a
  have hab := (other_ne a).symm
  rw [w_eq_column ρ p hp hc hu a b hab, wcolumn, X_add,
    commutatorElement_mul_left_eq_conj_mul]
  change MulAut.conj (X ρ a b r) (wcolumn ρ p a b s) * wcolumn ρ p a b r = _
  rw [← w_eq_column ρ p hp hc hu a b hab, ← w_eq_column ρ p hp hc hu a b hab,
    conj_of_commute (w_commute_X ρ p hp hc hu a a b hab.symm s r).symm,
    (w_commute ρ p hp hc hu a a s r).eq]

omit hp hc in
@[simp] theorem w_one (a : Fin 6) : w ρ p a (1:R) = p a :=
  hu a (other a) (other_ne a).symm

noncomputable def wAdd (a : Fin 6) : R →+ Additive Q where
  toFun r := Additive.ofMul (w ρ p a r)
  map_zero' := w_zero ρ p a
  map_add' := w_add ρ p hp hc hu a

/-- This is exactly the elementary action on a column, derived in the presentation. -/
theorem root_conjugation (c a : Fin 6) (hca : c ≠ a) (s r : R) :
    MulAut.conj (X ρ c a s) (w ρ p a r) = w ρ p a r * w ρ p c (s*r) := by
  obtain ⟨b,hba,hbc,_⟩ := fresh a c c
  have hxy : MulAut.conj (X ρ c a s) (X ρ a b r) = X ρ c b (s*r) * X ρ a b r := by
    rw [conj_eq_commutatorElement_mul, X_chain ρ c a b hca hba.symm hbc.symm]
  have hp' : MulAut.conj (X ρ c a s) (p b) = p b := conj_of_commute (hc s c a b hba)
  rw [w_eq_column ρ p hp hc hu a b hba.symm, wcolumn, map_commutatorElement,
    hxy, hp', commutatorElement_mul_left_eq_conj_mul]
  change MulAut.conj (X ρ c b (s*r)) (wcolumn ρ p a b r) * wcolumn ρ p c b (s*r) = _
  rw [← w_eq_column ρ p hp hc hu a b hba.symm,
    ← w_eq_column ρ p hp hc hu c b hbc.symm,
    conj_of_commute (w_commute_X ρ p hp hc hu a c b hba r (s*r)).symm]
  rw [w_eq_column ρ p hp hc hu a b hba.symm]
  rfl

/-- The finite ideal relations imply all relations in the left ideal they generate. -/
theorem w_span (D : Set R) (hd : ∀ d ∈ D, ∀ a b, a ≠ b → ⁅X ρ a b d, p b⁆ = 1)
    {r : R} (hr : r ∈ Submodule.span R D) (c : Fin 6) : w ρ p c r = 1 := by
  suffices hh : ∀ c, w ρ p c r = 1 from hh c
  induction hr using Submodule.span_induction with
  | mem d hd' => intro c; exact hd d hd' c (other c) (other_ne c).symm
  | zero => intro c; exact w_zero ρ p c
  | add r s _ _ hr hs => intro c; rw [w_add ρ p hp hc hu, hr, hs, one_mul]
  | smul s r _ hr =>
    intro c
    have h := root_conjugation ρ p hp hc hu c (other c) (other_ne c).symm s r
    rw [hr, map_one, one_mul] at h
    exact h.symm


variable (D : Set R)
variable (hd : ∀ d ∈ D, ∀ a b, a ≠ b → ⁅X ρ a b d, p b⁆ = 1)

noncomputable def rowMap (a : Fin 6) : (R ⧸ Submodule.span R D) →+ Additive Q :=
  QuotientAddGroup.lift (Submodule.span R D).toAddSubgroup (wAdd ρ p hp hc hu a) (by
    intro r hr
    exact w_span ρ p hp hc hu D hd hr a)

@[simp] theorem rowMap_mk (a : Fin 6) (r : R) :
    rowMap ρ p hp hc hu D hd a (Submodule.Quotient.mk r) = Additive.ofMul (w ρ p a r) := rfl

noncomputable def translationsAdd : (Fin 6 → R ⧸ Submodule.span R D) →+ Additive Q :=
  AddMonoidHom.noncommPiCoprod (rowMap ρ p hp hc hu D hd) (by
    intro a b _ x y
    obtain ⟨r,rfl⟩ := Submodule.Quotient.mk_surjective (Submodule.span R D) x
    obtain ⟨s,rfl⟩ := Submodule.Quotient.mk_surjective (Submodule.span R D) y
    exact w_commute ρ p hp hc hu a b r s)

noncomputable def translations : Multiplicative (Fin 6 → R ⧸ Submodule.span R D) →* Q :=
  (MulEquiv.multiplicativeAdditive Q).toMonoidHom.comp
    (AddMonoidHom.toMultiplicative (translationsAdd ρ p hp hc hu D hd))

@[simp] theorem translations_single (a : Fin 6) (x : R ⧸ Submodule.span R D) :
    translations ρ p hp hc hu D hd (Multiplicative.ofAdd (Pi.single a x)) =
      (rowMap ρ p hp hc hu D hd a x).toMul := by
  change (translationsAdd ρ p hp hc hu D hd) (Pi.single a x) = _
  exact AddMonoidHom.noncommPiCoprod_single (rowMap ρ p hp hc hu D hd) a x

@[simp] theorem translations_single_mk (a : Fin 6) (r : R) :
    translations ρ p hp hc hu D hd (Multiplicative.ofAdd (Pi.single a (Submodule.Quotient.mk r))) = w ρ p a r := by
  rw [translations_single, rowMap_mk]; rfl

end AffinePresentation

namespace AffineAction
open scoped commutatorElement
variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

/-- A matrix elementary operation on columns in an arbitrary left module. -/
def transvection (a b : Fin 6) (hab : a ≠ b) (r : R) : (Fin 6 → V) ≃+ (Fin 6 → V) where
  toFun v i := if i = a then v i + r • v b else v i
  invFun v i := if i = a then v i - r • v b else v i
  left_inv v := by
    funext i
    by_cases h : i=a <;> simp [h, hab.symm]
  right_inv v := by
    funext i
    by_cases h : i=a <;> simp [h, hab.symm]
  map_add' v w := by
    funext i
    by_cases h : i=a <;> simp [h,smul_add]; abel

@[simp] theorem transvection_apply (a b : Fin 6) (hab) (r : R) (v : Fin 6 → V) (i) :
    transvection a b hab r v i = if i=a then v i + r • v b else v i := rfl

def elementary (a b : Fin 6) (hab : a ≠ b) (r : R) : MulAut (Multiplicative (Fin 6 → V)) :=
  AddEquiv.toMultiplicative (transvection a b hab r)

@[simp] theorem elementary_apply (a b : Fin 6) (hab) (r : R) (v : Multiplicative (Fin 6 → V)) (i) :
    (elementary a b hab r v).toAdd i = if i=a then v.toAdd i + r • v.toAdd b else v.toAdd i := rfl


/-- The elementary displacement is supported in the one prescribed row. -/
theorem elementary_column (a b : Fin 6) (hab) (r : R) (v : Fin 6 → V) :
    (elementary a b hab r (Multiplicative.ofAdd v)).toAdd = v + Pi.single a (r • v b) := by
  funext i
  simp only [elementary_apply, toAdd_ofAdd, Pi.add_apply, Pi.single_apply]
  by_cases hi : i=a
  · subst i; simp
  · simp [hi]

theorem elementary_add (a b : Fin 6) (hab) (r s : R) :
    elementary (V:=V) a b hab r * elementary a b hab s = elementary a b hab (r+s) := by
  apply MulEquiv.ext
  intro v
  apply Multiplicative.toAdd.injective
  funext i
  change (elementary a b hab r (elementary a b hab s v)).toAdd i = _
  simp only [elementary_apply]
  by_cases h : i=a <;> simp [h,hab.symm,add_smul]; abel

@[simp] theorem elementary_zero (a b : Fin 6) (hab) : elementary (R:=R) (V:=V) a b hab 0 = 1 := by
  apply MulEquiv.ext
  intro v
  apply Multiplicative.toAdd.injective
  funext i
  change (elementary a b hab (0:R) v).toAdd i = v.toAdd i
  simp only [elementary_apply, zero_smul, add_zero, ite_self]

@[simp] theorem elementary_neg (a b : Fin 6) (hab) (r : R) :
    elementary (V:=V) a b hab (-r) = (elementary a b hab r)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [elementary_add, add_neg_cancel, elementary_zero]

theorem elementary_chain (a b c : Fin 6) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (r s : R) :
    ⁅elementary (V:=V) a b hab r, elementary (V:=V) b c hbc s⁆ = elementary a c hac (r*s) := by
  rw [commutatorElement_def, ← elementary_neg, ← elementary_neg]
  apply MulEquiv.ext
  intro v
  apply Multiplicative.toAdd.injective
  funext i
  change (elementary a b hab r (elementary b c hbc s
    (elementary a b hab (-r) (elementary b c hbc (-s) v)))).toAdd i = _
  simp only [elementary_apply]
  by_cases hi : i=a
  · subst i; simp [hab,hab.symm,hbc.symm,hac.symm,smul_add,smul_smul]; abel
  · by_cases hj : i=b
    · subst i; simp [hab.symm,hbc.symm,hac.symm]
    · simp [hi,hj]

theorem elementary_distant (a b c d : Fin 6) (hab : a ≠ b) (hcd : c ≠ d)
    (had : a ≠ d) (hbc : b ≠ c) (r s : R) :
    Commute (elementary (V:=V) a b hab r) (elementary c d hcd s) := by
  change elementary a b hab r * elementary c d hcd s = elementary c d hcd s * elementary a b hab r
  apply MulEquiv.ext
  intro v
  apply Multiplicative.toAdd.injective
  funext i
  change (elementary a b hab r (elementary c d hcd s v)).toAdd i =
    (elementary c d hcd s (elementary a b hab r v)).toAdd i
  simp only [elementary_apply]
  simp only [ite_eq_right hbc, ite_eq_right had.symm]
  split_ifs <;> abel

/-- The actual Steinberg action, with its three defining relations verified. -/
def action : Steinberg.Group (Fin 6) R →* MulAut (Multiplicative (Fin 6 → V)) :=
  PresentedGroup.toGroup (f := fun z : Steinberg.Generator (Fin 6) R =>
    elementary z.1.1.1 z.1.1.2 z.1.2 z.2) (by
      intro w hw
      cases hw with
      | additive a b hab r s =>
        simp only [map_mul,map_inv,Steinberg.freeRoot,FreeGroup.lift_apply_of]
        rw [elementary_add,mul_inv_cancel]
      | chain a b c hab hbc hac r s =>
        simp only [map_mul,map_inv,map_commutatorElement,Steinberg.freeRoot,FreeGroup.lift_apply_of]
        rw [elementary_chain a b c hab hbc hac,mul_inv_cancel]
      | distant a b c d hab hcd had hbc r s =>
        simp only [map_commutatorElement,Steinberg.freeRoot,FreeGroup.lift_apply_of]
        exact (elementary_distant a b c d hab hcd had hbc r s).commutator_eq)

@[simp] theorem action_root (a b : Fin 6) (hab) (r : R) :
    action (V:=V) (Steinberg.root a b hab r) = elementary a b hab r := PresentedGroup.toGroup.of _

abbrev Group := SemidirectProduct (Multiplicative (Fin 6 → V)) (Steinberg.Group (Fin 6) R) (action (R:=R) (V:=V))


/-- It suffices to check equivariance on actual Steinberg generators. -/
theorem equivariant_of_roots {Q : Type*} [_root_.Group Q]
    (τ : Multiplicative (Fin 6 → V) →* Q) (ρ : Steinberg.Group (Fin 6) R →* Q)
    (hr : ∀ a b hab r v, τ (elementary a b hab r v) =
      MulAut.conj (ρ (Steinberg.root a b hab r)) (τ v)) :
    ∀ g v, τ (action (R:=R) (V:=V) g v) = MulAut.conj (ρ g) (τ v) := by
  let C : Subgroup (Steinberg.Group (Fin 6) R) := {
    carrier := {g | ∀ v, τ (action g v) = MulAut.conj (ρ g) (τ v)}
    one_mem' := by intro v; simp
    mul_mem' := by
      intro g h hg hh v
      change ∀ v, _ at hg hh
      simp only [map_mul, MulAut.mul_apply, hg, hh]
    inv_mem' := by
      intro g hg v
      have he := hg (action (g⁻¹) v)
      have he1 : action (R:=R) (V:=V) g (action (g⁻¹) v) = v := by
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl
      rw [he1] at he
      have he2 := congrArg (MulAut.conj (ρ (g⁻¹))) he
      have he3 : MulAut.conj (ρ (g⁻¹)) (MulAut.conj (ρ g) (τ (action (g⁻¹) v))) =
          τ (action (g⁻¹) v) := by
        rw [← MulAut.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
        rfl
      rw [he3] at he2
      exact he2.symm }
  have ht : ⊤ ≤ C := by
    rw [← PresentedGroup.closure_range_of]
    apply (Subgroup.closure_le C).mpr
    rintro _ ⟨⟨⟨⟨a,b⟩,hab⟩,r⟩,rfl⟩
    change ∀ v, τ (action (Steinberg.root a b hab r) v) = _
    rw [action_root]
    exact hr a b hab r
  intro g
  exact ht (Subgroup.mem_top g)

end AffineAction

namespace AffinePresentation
open scoped commutatorElement
variable {R Q : Type*} [Ring R] [Group Q]
variable (ρ : Steinberg.Group (Fin 6) R →* Q) (p : Fin 6 → Q)
variable (hp : ∀ a b, Commute (p a) (p b))
variable (hc : ∀ r : R, ∀ a b c : Fin 6, c ≠ b → Commute (X ρ a b r) (p c))
variable (hu : ∀ a b, a ≠ b → ⁅X ρ a b 1, p b⁆ = p a)
variable (D : Set R) (hd : ∀ d ∈ D, ∀ a b, a ≠ b → ⁅X ρ a b d,p b⁆ = 1)

/-- The finite presentation relations build an actual semidirect-product homomorphism. -/
theorem translations_equivariant (g : Steinberg.Group (Fin 6) R) :
    (translations ρ p hp hc hu D hd).comp (AffineAction.action g).toMonoidHom =
      (MulAut.conj (ρ g)).toMonoidHom.comp (translations ρ p hp hc hu D hd) := by
  apply MonoidHom.ext
  change ∀ v, translations ρ p hp hc hu D hd (AffineAction.action g v) = _
  apply AffineAction.equivariant_of_roots
  intro a b hab r
  suffices he : (translations ρ p hp hc hu D hd).comp
      (AffineAction.elementary a b hab r).toMonoidHom =
      (MulAut.conj (ρ (Steinberg.root a b hab r))).toMonoidHom.comp
        (translations ρ p hp hc hu D hd) from DFunLike.congr_fun he
  apply MonoidHom.toAdditive.injective
  apply AddMonoidHom.pi_ext
  intro c x
  obtain ⟨s,rfl⟩ := Submodule.Quotient.mk_surjective (Submodule.span R D) x
  change translations ρ p hp hc hu D hd
      (AffineAction.elementary a b hab r (Multiplicative.ofAdd (Pi.single c (Submodule.Quotient.mk s)))) =
    MulAut.conj (ρ (Steinberg.root a b hab r))
      (translations ρ p hp hc hu D hd (Multiplicative.ofAdd (Pi.single c (Submodule.Quotient.mk s))))
  rw [translations_single_mk]
  have hx : ρ (Steinberg.root a b hab r) = X ρ a b r := by rw [X, Steinberg.x_of_ne a b hab]
  rw [hx]
  have he := AffineAction.elementary_column a b hab r (Pi.single c (Submodule.Quotient.mk s) : Fin 6 → R ⧸ Submodule.span R D)
  apply_fun Multiplicative.ofAdd at he
  rw [ofAdd_toAdd] at he
  rw [he, ofAdd_add, map_mul, translations_single_mk]
  by_cases hcb : c=b
  · subst c
    simp only [Pi.single_eq_same]
    have hs : r • (Submodule.Quotient.mk s : R ⧸ Submodule.span R D) = Submodule.Quotient.mk (r*s) := rfl
    rw [hs,translations_single_mk,root_conjugation ρ p hp hc hu a b hab]
  · rw [Pi.single_eq_of_ne (Ne.symm hcb),smul_zero,Pi.single_zero,ofAdd_zero,map_one,mul_one]
    exact (conj_of_commute (w_commute_X ρ p hp hc hu c a b (Ne.symm hcb) s r).symm).symm

noncomputable def lift : AffineAction.Group (R:=R) (V:= R ⧸ Submodule.span R D) →* Q :=
  SemidirectProduct.lift (translations ρ p hp hc hu D hd) ρ (translations_equivariant ρ p hp hc hu D hd)

end AffinePresentation
namespace AffineAction
open scoped commutatorElement
variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

/-- Commutators with a root are the elementary displacement, not an assumed action law. -/
theorem root_translation (a b : Fin 6) (hab : a ≠ b) (r : R) (v : Fin 6 → V) :
    ⁅(SemidirectProduct.inr (Steinberg.root a b hab r) : Group (R:=R) (V:=V)),
      (SemidirectProduct.inl (Multiplicative.ofAdd v) : Group (R:=R) (V:=V))⁆ =
      SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single a (r • v b))) := by
  rw [commutatorElement_def, ← map_inv, ← SemidirectProduct.inl_aut, ← map_inv, ← map_mul]
  congr 1
  apply Multiplicative.toAdd.injective
  rw [action_root]
  change (elementary a b hab r (Multiplicative.ofAdd v)).toAdd + -v = _
  rw [elementary_column]
  abel

end AffineAction

end FiniteAlgebraicEnvelopes

end OAI
end

section
-- module Solutions.OAIFAE.Transition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite weak transition components and finite-scan instruction semantics.
-/

namespace FiniteAlgebraicEnvelopes.Compiler
open Relation

variable {α : Type*} {r : α → α → Prop}

section FiniteSearch
variable [Fintype α] [DecidableEq α] (r : α → α → Prop) [DecidableRel r]

/-- One effective expansion by undirected internal edges. -/
def expand (s : Finset α) : Finset α :=
  s ∪ Finset.univ.filter (fun b => ∃ a ∈ s, r a b ∨ r b a)

@[simp] theorem mem_expand (s : Finset α) (b : α) :
    b ∈ expand r s ↔ b ∈ s ∨ ∃ a ∈ s, r a b ∨ r b a := by
  simp [expand]

theorem subset_expand (s : Finset α) : s ⊆ expand r s :=
  fun _ h => (mem_expand r _ _).mpr (Or.inl h)

/-- This finite algorithm never calls the simulated partial function. -/
def search (a : α) : ℕ → Finset α
  | 0 => {a}
  | n+1 => expand r (search a n)

theorem search_mono (a : α) : Monotone (search r a) := by
  apply monotone_nat_of_le_succ
  intro n
  exact subset_expand r _

theorem search_stabilizes (a : α) :
    search r a (Fintype.card α + 1) = search r a (Fintype.card α) := by
  have hs : ∀ n, (search r a n).card ≤ Fintype.card α :=
    fun _ => Finset.card_le_univ _
  have hm : Monotone (fun n => (search r a n).card) :=
    fun _ _ h => Finset.card_le_card (search_mono r a h)
  have hstep : ∀ n, (search r a n).card = (search r a (n+1)).card →
      (search r a (n+1)).card = (search r a (n+2)).card := by
    intro n hn
    have he : search r a n = search r a (n+1) :=
      Finset.eq_of_subset_of_card_le (search_mono r a (Nat.le_succ n)) hn.ge
    exact congrArg Finset.card (congrArg (expand r) he)
  exact (Finset.eq_of_subset_of_card_le
    (search_mono r a (Nat.le_succ (Fintype.card α)))
    (Nat.stabilises_of_monotone hm hs hstep (Nat.le_succ _)).le).symm

/-- Entire weak component, computed by at most the known number of vertices
    many finite expansions. Unlike running the machine, this always terminates. -/
def component (a : α) : Finset α := search r a (Fintype.card α)

theorem self_mem_component (a : α) : a ∈ component r a :=
  search_mono r a (Nat.zero_le _) (by simp [search])

theorem component_saturated (a b c : α) (hb : b ∈ component r a)
    (hbc : r b c ∨ r c b) : c ∈ component r a := by
  have h := (mem_expand r (component r a) c).mpr (Or.inr ⟨b, hb, hbc⟩)
  change c ∈ search r a (Fintype.card α + 1) at h
  rw [search_stabilizes] at h
  exact h

theorem mem_search_connected (a b : α) (n : ℕ) (h : b ∈ search r a n) :
    EqvGen r a b := by
  induction n generalizing b with
  | zero =>
    have : b=a := by simpa [search] using h
    subst b
    exact .refl a
  | succ n ih =>
    rcases (mem_expand r (search r a n) b).mp h with h | ⟨c, hc, hcb⟩
    · exact ih b h
    · refine EqvGen.trans _ _ _ (ih c hc) ?_
      rcases hcb with h | h
      · exact .rel _ _ h
      · exact .symm _ _ (.rel _ _ h)

/-- Exactness of the finite component search on malformed as well as genuine
    configurations. -/
theorem mem_component_iff (a b : α) : b ∈ component r a ↔ EqvGen r a b := by
  constructor
  · exact mem_search_connected r a b _
  · intro h
    have h' : ReflTransGen (SymmGen r) a b := by
      rw [EqvGen.reflTransGen_symmGen]
      exact h
    clear h
    induction h' with
    | refl => exact self_mem_component r a
    | @tail b c _ hbc ih => exact component_saturated r a b c ih hbc

end FiniteSearch

/- The actual finite-scan instruction semantics of the finite compiler.
   The immutable bases are not part of what an instruction may update. -/
inductive Base (S : Type*)
  | anchor : S → Base S
  | cutC : Base S
  | cutD : Base S
  | workspace : Base S
  deriving DecidableEq, Fintype

structure Tag (S Γ : Type*) where
  anchorRead : Bool
  workspaceFilled : Bool
  work : Γ
  outputRead : Bool
  output : Option S
  deriving DecidableEq, Fintype

/-- The same clean tag is used on every base, including its unused fields. -/
def clean {S Γ : Type*} (blank : Γ) : Tag S Γ :=
  ⟨false, false, blank, false, none⟩

inductive Direction
  | left | right
  deriving DecidableEq

structure Instruction (Head Tag : Type*) where
  head : Head
  tag : Tag
  cross : Bool
  deriving DecidableEq, Fintype

/-- Each state designates one reading side. A cell test has at most one result;
    boundary tests only change the state. A failed (or absent-boundary) test
    has no result. This is exactly the source's disjoint-case convention. -/
structure Table (Head Base Tag : Type*) where
  direction : Head → Direction
  cell : Head → Base → Tag → Option (Instruction Head Tag)
  boundary : Head → Option Head

end FiniteAlgebraicEnvelopes.Compiler

end OAI
end

section
-- module Solutions.OAIFAE.Validator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite tape validation, scan reversal, and bounded cleanup.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.Validator

section
open Relation

/-- The validator states I,J,J',N,V and its fresh machine handoff. -/
inductive Head
  | initial | left | right | workspace | suffix | start
  deriving DecidableEq

/-- A cell includes every tag field, even unused ones. -/
abbrev Cell (S Γ : Type*) := Base S × Tag S Γ

def cell {S Γ : Type*} (blank : Γ) (base : Base S) : Cell S Γ :=
  (base, clean blank)

/-- A headed sector in zipper notation. The left list is in reverse order,
    so its head is exactly the cell adjacent to the validator. -/
structure Sector (S Γ : Type*) where
  head : Head
  left : List (Cell S Γ)
  right : List (Cell S Γ)
  leftBoundary : Bool
  rightBoundary : Bool
  deriving DecidableEq

/-- Literal internal equations compiler-validation, oriented as in the source.
    There is no entry from P and no transition from the machine back here. -/
inductive Step {S Γ : Type*} (blank : Γ) : Sector S Γ → Sector S Γ → Prop
  | initial_workspace (l r : List (Cell S Γ)) (lb rb : Bool) :
      Step blank ⟨.initial, cell blank .workspace :: l, r, lb, rb⟩
        ⟨.initial, l, cell blank .workspace :: r, lb, rb⟩
  | initial_cut (l r : List (Cell S Γ)) (lb rb : Bool) :
      Step blank ⟨.initial, cell blank .cutC :: l, r, lb, rb⟩
        ⟨.left, l, cell blank .cutC :: r, lb, rb⟩
  | left_anchor (a : S) (l r : List (Cell S Γ)) (lb rb : Bool) :
      Step blank ⟨.left, cell blank (.anchor a) :: l, r, lb, rb⟩
        ⟨.left, l, cell blank (.anchor a) :: r, lb, rb⟩
  | left_boundary (r : List (Cell S Γ)) (rb : Bool) :
      Step blank ⟨.left, [], r, true, rb⟩ ⟨.right, [], r, true, rb⟩
  | right_anchor (a : S) (l r : List (Cell S Γ)) (lb rb : Bool) :
      Step blank ⟨.right, l, cell blank (.anchor a) :: r, lb, rb⟩
        ⟨.right, cell blank (.anchor a) :: l, r, lb, rb⟩
  | right_cut (l r : List (Cell S Γ)) (lb rb : Bool) :
      Step blank ⟨.right, l, cell blank .cutC :: r, lb, rb⟩
        ⟨.workspace, cell blank .cutC :: l, r, lb, rb⟩
  | workspace (l r : List (Cell S Γ)) (lb rb : Bool) :
      Step blank ⟨.workspace, l, cell blank .workspace :: r, lb, rb⟩
        ⟨.workspace, cell blank .workspace :: l, r, lb, rb⟩
  | workspace_cut (l r : List (Cell S Γ)) (lb rb : Bool) :
      Step blank ⟨.workspace, l, cell blank .cutD :: r, lb, rb⟩
        ⟨.suffix, cell blank .cutD :: l, r, lb, rb⟩
  | suffix_anchor (a : S) (l r : List (Cell S Γ)) (lb rb : Bool) :
      Step blank ⟨.suffix, l, cell blank (.anchor a) :: r, lb, rb⟩
        ⟨.suffix, cell blank (.anchor a) :: l, r, lb, rb⟩
  | suffix_boundary (l : List (Cell S Γ)) (lb : Bool) :
      Step blank ⟨.suffix, l, [], lb, true⟩ ⟨.start, l, [], lb, true⟩

open Relation

end

open Relation

end FiniteAlgebraicEnvelopes.Compiler.Validator

namespace FiniteAlgebraicEnvelopes.Compiler.Validator
open Relation
variable {S Γ : Type*} (blank : Γ)

/-- The machine may alter tags but never these ordered bases or outer flags. -/
def baseSkeleton (s : Sector S Γ) : List (Base S) × Bool × Bool :=
  ((s.left.reverse ++ s.right).map Prod.fst, s.leftBoundary, s.rightBoundary)

end FiniteAlgebraicEnvelopes.Compiler.Validator

namespace FiniteAlgebraicEnvelopes.Compiler.Validator.Extended
open Relation
variable {S Γ M : Type*} (blank : Γ)
abbrev Cfg (S Γ M : Type*) := Sector S Γ ⊕ M

/-- Only the fresh handoff and machine configurations participate in simulation;
    in particular there is no return to I,J,J',N,V. -/
def Active : Cfg S Γ M → Prop
  | .inl v => v.head = .start
  | .inr _ => True

variable (bases : M → List (Base S) × Bool × Bool)

def baseSkeleton : Cfg S Γ M → List (Base S) × Bool × Bool
  | .inl v => Validator.baseSkeleton v
  | .inr q => bases q

end FiniteAlgebraicEnvelopes.Compiler.Validator.Extended

namespace FiniteAlgebraicEnvelopes.Compiler.Scan

/-- A list zipper for the same finite-scan semantics. Left cells are nearest
    first. This representation permits induction on literal scan paths. -/
structure Sector (Head Base Tag : Type*) where
  left : List (Base × Tag)
  head : Head
  right : List (Base × Tag)
  leftBoundary : Bool
  rightBoundary : Bool
  deriving DecidableEq

variable {H B T : Type*}

def step (table : Table H B T) (v : Sector H B T) : Option (Sector H B T) :=
  match table.direction v.head with
  | .left => match v.left with
    | (b,t) :: l => (table.cell v.head b t).map fun a =>
        if a.cross then { v with left := l, head := a.head, right := (b,a.tag) :: v.right }
        else { v with left := (b,a.tag) :: l, head := a.head }
    | [] => if v.leftBoundary then
        (table.boundary v.head).map fun q => { v with head := q } else none
  | .right => match v.right with
    | (b,t) :: r => (table.cell v.head b t).map fun a =>
        if a.cross then { v with left := (b,a.tag) :: v.left, head := a.head, right := r }
        else { v with head := a.head, right := (b,a.tag) :: r }
    | [] => if v.rightBoundary then
        (table.boundary v.head).map fun q => { v with head := q } else none

def Step (table : Table H B T) (v w : Sector H B T) : Prop := step table v = some w

def baseSkeleton (v : Sector H B T) : List B × Bool × Bool :=
  ((v.left.reverse ++ v.right).map Prod.fst, v.leftBoundary, v.rightBoundary)

theorem step_skeleton (table : Table H B T) {v w : Sector H B T}
    (h : Step table v w) : baseSkeleton v = baseSkeleton w := by
  rcases v with ⟨l,q,r,lb,rb⟩
  unfold Step step at h
  cases hd : table.direction q <;> simp only [hd] at h
  · cases l with
    | nil =>
      cases lb <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
      · contradiction
      · cases hb : table.boundary q <;> simp only [hb, Option.map_none, Option.map_some] at h
        · contradiction
        · cases Option.some.inj h; rfl
    | cons a l =>
      rcases a with ⟨b,t⟩
      cases hc : table.cell q b t <;> simp only [hc, Option.map_none, Option.map_some] at h
      · contradiction
      · rename_i ins
        cases hm : ins.cross <;> simp only [hm, Bool.false_eq_true, ↓reduceIte] at h <;> cases Option.some.inj h <;>
          simp [baseSkeleton, List.reverse_cons, List.append_assoc]
  · cases r with
    | nil =>
      cases rb <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
      · contradiction
      · cases hb : table.boundary q <;> simp only [hb, Option.map_none, Option.map_some] at h
        · contradiction
        · cases Option.some.inj h; rfl
    | cons a r =>
      rcases a with ⟨b,t⟩
      cases hc : table.cell q b t <;> simp only [hc, Option.map_none, Option.map_some] at h
      · contradiction
      · rename_i ins
        cases hm : ins.cross <;> simp only [hm, Bool.false_eq_true, ↓reduceIte] at h <;> cases Option.some.inj h <;>
          simp [baseSkeleton, List.reverse_cons, List.append_assoc]

end FiniteAlgebraicEnvelopes.Compiler.Scan

end OAI
end

section
-- module Solutions.OAIFAE.Simulator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Literal finite-quota machine simulation and readout correctness.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.Simulator

/-- Finite work alphabet, including a literal code for every input letter and
    a distinct blank. The remaining symbols are rejected by output reading. -/
structure Alphabet (S Γ : Type*) where
  blank : Γ
  input : S → Γ
  output : Γ → Option S
  output_input : ∀ a, output (input a) = some a
  output_blank : output blank = none

inductive Move
  | stay | left | right
  deriving DecidableEq

instance instFintypeMove : Fintype Move := ⟨{.stay, .left, .right}, by intro x; cases x <;> simp⟩

structure Command (Q Γ : Type*) where
  state : Q
  write : Γ
  move : Move
  deriving DecidableEq, Fintype

/-- A deterministic left-ended one-tape machine. `none` is halt, recognized
    only while the head is at a workspace cell. -/
structure Machine (Q Γ : Type*) where
  initial : Q
  transition : Q → Γ → Option (Command Q Γ)

inductive Resume (S : Type*)
  | input | fill : S → Resume S
  | spare | first | readout | put : S → Resume S
  deriving DecidableEq, Fintype

/-- Distinct phases make every scan's designated reading side unambiguous. -/
inductive Head (S Q : Type*)
  | start
  | rewind : Resume S → Head S Q
  | scan : Resume S → Head S Q
  | run : Q → Head S Q
  | left : Q → Head S Q
  | finish | ok
  deriving DecidableEq, Fintype

variable {S Γ Q : Type*}

/-- The cell table is finite when the alphabets and state set are finite. All
    tests and assignments are precisely the source's scan expansion. -/
def cell (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]
    (q : Head S Q) (b : Base S) (t : Tag S Γ) :
    Option (Instruction (Head S Q) (Tag S Γ)) :=
  match q with
  | .start | .ok => none
  | .rewind s => some ⟨.rewind s,t,true⟩
  | .scan .input => match b with
    | .anchor a => if t.anchorRead then some ⟨q,t,true⟩
      else some ⟨.rewind (.fill a),{t with anchorRead := true},false⟩
    | _ => some ⟨q,t,true⟩
  | .scan (.fill a) => match b with
    | .workspace => if t.workspaceFilled then some ⟨q,t,true⟩
      else some ⟨.rewind .input,{t with workspaceFilled := true, work := A.input a},false⟩
    | _ => some ⟨q,t,true⟩
  | .scan .spare => match b with
    | .workspace => if t.workspaceFilled then some ⟨q,t,true⟩
      else some ⟨.rewind .first,t,false⟩
    | _ => some ⟨q,t,true⟩
  | .scan .first => match b with
    | .workspace => some ⟨.run M.initial,t,false⟩
    | _ => some ⟨q,t,true⟩
  | .run c => match b with
    | .workspace => match M.transition c t.work with
      | none => some ⟨.rewind .readout,t,false⟩
      | some d => some ⟨(if d.move = .left then .left d.state else .run d.state),
          {t with work := d.write}, d.move == .right⟩
    | _ => none
  | .left c => match b with
    | .workspace => some ⟨.run c,t,true⟩
    | .cutC => some ⟨.run c,t,false⟩
    | _ => none
  | .scan .readout => match b with
    | .workspace => if t.outputRead then some ⟨q,t,true⟩
      else if t.work = A.blank then some ⟨.finish,t,false⟩
      else (A.output t.work).map fun a => ⟨.rewind (.put a),{t with outputRead := true},false⟩
    | _ => some ⟨q,t,true⟩
  | .scan (.put a) => match b with
    | .anchor _ => match t.output with
      | none => some ⟨.rewind .readout,{t with output := some a},false⟩
      | some _ => some ⟨q,t,true⟩
    | _ => some ⟨q,t,true⟩
  | .finish => some ⟨q,t,true⟩

def table (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ] :
    Table (Head S Q) (Base S) (Tag S Γ) where
  direction
    | .rewind _ | .left _ => .left
    | _ => .right
  cell := cell A M
  boundary
    | .start => some (.rewind .input)
    | .rewind s => some (.scan s)
    | .scan .input => some (.rewind .spare)
    | .finish => some .ok
    | _ => none

end FiniteAlgebraicEnvelopes.Compiler.Simulator

namespace FiniteAlgebraicEnvelopes.Compiler.Simulator

section
open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]

abbrev Cells (S Γ : Type*) := List (Base S × Tag S Γ)

/-- Tags following the copy phase; unused full-tag fields remain literally
    clean, as required by the validator/simulator convention. -/
def readAnchor (a : S) (read : Bool) : Base S × Tag S Γ :=
  (.anchor a,{clean A.blank with anchorRead := read})

def filledWork (a : S) : Base S × Tag S Γ :=
  (.workspace,{clean A.blank with workspaceFilled := true, work := A.input a})

def bare (b : Base S) : Base S × Tag S Γ := (b,clean A.blank)

/-- The whole tape during copying: read and unread anchor prefixes on either
    side of the reserved workspace, with a filled prefix followed by blanks. -/
def body (xp xs yp ys w : List S) (n : ℕ) : Cells S Γ :=
  xp.map (readAnchor A · true) ++ xs.map (readAnchor A · false) ++
  [bare A .cutC] ++ w.map (filledWork A) ++ List.replicate n (bare A .workspace) ++
  [bare A .cutD] ++ yp.map (readAnchor A · true) ++ ys.map (readAnchor A · false)

def Pass (s : Resume S) (c : Base S × Tag S Γ) : Prop :=
  cell A M (.scan s) c.1 c.2 = some ⟨.scan s,c.2,true⟩

@[simp] theorem pass_read (a : S) : Pass A M .input (readAnchor A a true) := by
  rfl
@[simp] theorem pass_input_bareC : Pass A M .input (bare A .cutC) := by rfl
@[simp] theorem pass_input_bareD : Pass A M .input (bare A .cutD) := by rfl
@[simp] theorem pass_input_bareW : Pass A M .input (bare A .workspace) := by rfl
@[simp] theorem pass_input_filled (a : S) : Pass A M .input (filledWork A a) := by rfl
@[simp] theorem pass_fill_anchor (a b : S) (r : Bool) :
    Pass A M (.fill a) (readAnchor A b r) := by rfl
@[simp] theorem pass_fill_bareC (a : S) : Pass A M (.fill a) (bare A .cutC) := by rfl
@[simp] theorem pass_fill_filled (a b : S) : Pass A M (.fill a) (filledWork A b) := by rfl

@[simp] theorem pass_spare_anchor (a : S) (r : Bool) :
    Pass A M .spare (readAnchor A a r) := by rfl
@[simp] theorem pass_spare_C : Pass A M .spare (bare A .cutC) := by rfl
@[simp] theorem pass_spare_filled (a : S) : Pass A M .spare (filledWork A a) := by rfl
@[simp] theorem pass_first_anchor (a : S) (r : Bool) :
    Pass A M .first (readAnchor A a r) := by rfl
@[simp] theorem pass_first_C : Pass A M .first (bare A .cutC) := by rfl

end

section
open Relation
variable {S Γ Q : Type*}

/-- A literal bounded workspace. The left list is in reverse tape order, and
    an empty right list is outside the supplied quota, not a fresh blank cell. -/
structure Tape where
  state : Q
  left : List (Tag S Γ)
  right : List (Tag S Γ)

/-- Update only the simulated work track; all auxiliary tag fields are retained. -/
def writeWork (t : Tag S Γ) (a : Γ) : Tag S Γ := { t with work := a }

/-- The intended finite-quota operations of the finite compiler. These are
    defined from the given machine table, not postulated accepting transitions. -/
inductive TapeStep (M : Machine Q Γ) : Tape (S := S) (Γ := Γ) (Q := Q) → Tape → Prop
  | stay {q l t r d} (h : M.transition q t.work = some d) (hm : d.move = .stay) :
      TapeStep M ⟨q,l,t::r⟩ ⟨d.state,l,writeWork t d.write::r⟩
  | right {q l t r d} (h : M.transition q t.work = some d) (hm : d.move = .right) :
      TapeStep M ⟨q,l,t::r⟩ ⟨d.state,writeWork t d.write::l,r⟩
  | leftEdge {q t r d} (h : M.transition q t.work = some d) (hm : d.move = .left) :
      TapeStep M ⟨q,[],t::r⟩ ⟨d.state,[],writeWork t d.write::r⟩
  | left {q v l t r d} (h : M.transition q t.work = some d) (hm : d.move = .left) :
      TapeStep M ⟨q,v::l,t::r⟩ ⟨d.state,l,v::writeWork t d.write::r⟩

def workCells (l : List (Tag S Γ)) : Cells S Γ := l.map fun t => (.workspace,t)

end

section
open Relation
variable {S Γ Q : Type*}

def workView (l : Cells S Γ) : List (Bool × Γ) :=
  l.filterMap fun c => match c.1 with
    | .workspace => some (c.2.outputRead,c.2.work)
    | _ => none

def anchorView (l : Cells S Γ) : List (Option S) :=
  l.filterMap fun c => match c.1 with
    | .anchor _ => some c.2.output
    | _ => none

@[simp] theorem workView_append (l r : Cells S Γ) :
    workView (l ++ r) = workView l ++ workView r := List.filterMap_append
@[simp] theorem anchorView_append (l r : Cells S Γ) :
    anchorView (l ++ r) = anchorView l ++ anchorView r := List.filterMap_append

end

section
open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]

omit [DecidableEq Γ] in
theorem input_ne_blank (a : S) : A.input a ≠ A.blank := by
  intro h
  have := A.output_input a
  rw [h, A.output_blank] at this
  contradiction

end

section
open Relation
variable {S Γ Q : Type*}

/-- Appending untouched blank cells reserves quota without altering any already
    represented tape position. -/
def pad (A : Alphabet S Γ) (c : Tape (S := S) (Γ := Γ) (Q := Q)) (n : ℕ) : Tape (S := S) (Γ := Γ) (Q := Q) :=
  { c with right := c.right ++ List.replicate n (clean A.blank) }

/-- Unbounded left-ended tape semantics. A cell beyond the finite represented
    region is blank; it is materialized only when reached. No output fact or
    acceptance relation is built into these transition constructors. -/
inductive UnboundedStep (A : Alphabet S Γ) (M : Machine Q Γ) :
    Tape (S := S) (Γ := Γ) (Q := Q) → Tape (S := S) (Γ := Γ) (Q := Q) → Prop
  | within {c d} (h : TapeStep M c d) : UnboundedStep A M c d
  | extend {q l d} (h : TapeStep M ⟨q,l,[clean A.blank]⟩ d) :
      UnboundedStep A M ⟨q,l,[]⟩ d

end

section
open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ) (M : Machine Q Γ)

/-- Initial finite representation after copying, before adding blank quota. -/
def initialTape (w : List S) : Tape (S := S) (Γ := Γ) (Q := Q) :=
  ⟨M.initial,[],w.map fun a => (filledWork A a).2⟩

/-- The halt test includes the implicit blank at the first unrepresented cell. -/
def Halted (c : Tape (S := S) (Γ := Γ) (Q := Q)) : Prop :=
  M.transition c.state (c.right.headD (clean A.blank)).work = none

/-- The returned string begins at position zero and is delimited by its first
    blank. Extra blanks may lie outside the finite represented portion. -/
def Returns (c : Tape (S := S) (Γ := Γ) (Q := Q)) (out : List S) : Prop :=
  ∃ n tail, (c.left.reverse ++ c.right).map Tag.work ++ List.replicate n A.blank =
    out.map A.input ++ A.blank::tail

@[simp] theorem pad_left (c : Tape (S := S) (Γ := Γ) (Q := Q)) (n : ℕ) :
    (pad A c n).left = c.left := rfl

@[simp] theorem pad_right (c : Tape (S := S) (Γ := Γ) (Q := Q)) (n : ℕ) :
    (pad A c n).right = c.right ++ List.replicate n (clean A.blank) := rfl

@[simp] theorem anchorView_workCells (ts : List (Tag S Γ)) :
    anchorView (workCells ts) = [] := by simp [workCells,anchorView,List.filterMap_map]

@[simp] theorem anchorView_readAnchors (xs : List S) (r : Bool) :
    anchorView (xs.map (readAnchor A · r)) = List.replicate xs.length none := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      change none :: anchorView (xs.map (readAnchor A · r)) = _
      rw [ih]
      rfl

@[simp] theorem workView_readAnchors (xs : List S) (r : Bool) :
    workView (xs.map (readAnchor A · r)) = [] := by
  simp [workView,readAnchor,List.filterMap_map]

end

section
open Relation
variable {S Γ Q : Type*}

/-- Semantic one-sided tape: its right end is an infinite blank tail, not an
    extra halting edge. Auxiliary simulator tags do not enter this semantics. -/
structure SemanticTape (Γ Q : Type*) where
  state : Q
  left : List Γ
  right : Stream' Γ

/-- The literal machine command interpreted on an infinite right-hand tape. -/
def semanticStep (M : Machine Q Γ) (c : SemanticTape Γ Q) : Option (SemanticTape Γ Q) :=
  (M.transition c.state c.right.head).map fun d =>
    match d.move with
    | .stay => ⟨d.state,c.left,Stream'.cons d.write c.right.tail⟩
    | .right => ⟨d.state,d.write::c.left,c.right.tail⟩
    | .left => match c.left with
      | [] => ⟨d.state,[],Stream'.cons d.write c.right.tail⟩
      | a::l => ⟨d.state,l,Stream'.cons a (Stream'.cons d.write c.right.tail)⟩

def SemanticStep (M : Machine Q Γ) (c d : SemanticTape Γ Q) : Prop :=
  semanticStep M c = some d

def interpret (A : Alphabet S Γ) (c : Tape (S := S) (Γ := Γ) (Q := Q)) : SemanticTape Γ Q :=
  ⟨c.state,c.left.map Tag.work,
    Stream'.appendStream' (c.right.map Tag.work) (Stream'.const A.blank)⟩

theorem replicate_append_const (b : Γ) (n : ℕ) :
    Stream'.appendStream' (List.replicate n b) (Stream'.const b) = Stream'.const b := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [List.replicate_succ,Stream'.appendStream',ih]
      exact (Stream'.const_eq b).symm

@[simp] theorem interpret_pad (A : Alphabet S Γ)
    (c : Tape (S := S) (Γ := Γ) (Q := Q)) (n : ℕ) :
    interpret A (pad A c n) = interpret A c := by
  rcases c with ⟨q,l,r⟩
  simp [interpret,pad,List.map_append,List.map_replicate,clean,replicate_append_const]

/-- Each bounded transition is exactly one transition of the semantic machine. -/
theorem tapeStep_interpret (A : Alphabet S Γ) (M : Machine Q Γ)
    {c d : Tape (S := S) (Γ := Γ) (Q := Q)} (h : TapeStep M c d) :
    SemanticStep M (interpret A c) (interpret A d) := by
  cases h <;>
    simp_all [SemanticStep,semanticStep,interpret,Stream'.appendStream',writeWork]

/-- Materializing an implicit blank never changes the semantic tape. -/
theorem unboundedStep_interpret (A : Alphabet S Γ) (M : Machine Q Γ)
    {c d : Tape (S := S) (Γ := Γ) (Q := Q)} (h : UnboundedStep A M c d) :
    SemanticStep M (interpret A c) (interpret A d) := by
  cases h with
  | within h => exact tapeStep_interpret A M h
  | @extend q l d h =>
      have hi : interpret A (⟨q,l,[clean A.blank]⟩ : Tape (S := S) (Γ := Γ) (Q := Q)) =
          interpret A (⟨q,l,[]⟩ : Tape (S := S) (Γ := Γ) (Q := Q)) := by
        exact interpret_pad A ⟨q,l,[]⟩ 1
      rw [← hi]
      exact tapeStep_interpret A M h

theorem unboundedRun_interpret (A : Alphabet S Γ) (M : Machine Q Γ)
    {c d : Tape (S := S) (Γ := Γ) (Q := Q)} (h : ReflTransGen (UnboundedStep A M) c d) :
    ReflTransGen (SemanticStep M) (interpret A c) (interpret A d) :=
  h.lift (interpret A) (fun _ _ => unboundedStep_interpret A M)

end

section
open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ)

/-- The whole semantic tape, read in physical order starting at cell zero. -/
def semanticContent (c : SemanticTape Γ Q) : Stream' Γ :=
  Stream'.appendStream' c.left.reverse c.right

/-- Standard literal, first-blank-delimited machine output. -/
def SemanticReturns (c : SemanticTape Γ Q) (w : List S) : Prop :=
  ∃ tail, semanticContent c = Stream'.appendStream' (w.map A.input) (Stream'.cons A.blank tail)

theorem returns_interpret {c : Tape (S := S) (Γ := Γ) (Q := Q)} {w : List S}
    (h : Returns A c w) : SemanticReturns A (interpret A c) w := by
  obtain ⟨n,tail,h⟩ := h
  refine ⟨Stream'.appendStream' tail (Stream'.const A.blank),?_⟩
  have hi := congrArg (fun l => Stream'.appendStream' l (Stream'.const A.blank)) h
  simpa [semanticContent,interpret,List.map_append,List.map_reverse,
    Stream'.append_append_stream,replicate_append_const,Stream'.appendStream'] using hi

theorem input_injective : Function.Injective A.input := by
  intro a b h
  have hi := congrArg A.output h
  simpa only [A.output_input,Option.some.injEq] using hi

/-- The input alphabet excludes the delimiter, so two literal returned prefixes
    of the same infinite tape must be the same list, including empty output. -/
theorem delimited_prefix_unique (x y : List S) (r s : Stream' Γ)
    (h : Stream'.appendStream' (x.map A.input) (Stream'.cons A.blank r) =
      Stream'.appendStream' (y.map A.input) (Stream'.cons A.blank s)) : x = y := by
  induction x generalizing y with
  | nil =>
      cases y with
      | nil => rfl
      | cons b y =>
          have hi := congrArg Stream'.head h
          simp only [List.map_nil,List.map_cons,Stream'.appendStream',Stream'.head_cons] at hi
          exact False.elim (input_ne_blank A b hi.symm)
  | cons a x ih =>
      cases y with
      | nil =>
          have hi := congrArg Stream'.head h
          simp only [List.map_nil,List.map_cons,Stream'.appendStream',Stream'.head_cons] at hi
          exact False.elim (input_ne_blank A a hi)
      | cons b y =>
          have hi := congrArg Stream'.head h
          have ht := congrArg Stream'.tail h
          simp only [List.map_cons,Stream'.appendStream',Stream'.head_cons] at hi
          simp only [List.map_cons,Stream'.appendStream',Stream'.tail_cons] at ht
          exact congrArg₂ List.cons (input_injective A hi) (ih y ht)

theorem semanticReturns_unique {c : SemanticTape Γ Q} {x y : List S}
    (hx : SemanticReturns A c x) (hy : SemanticReturns A c y) : x = y := by
  obtain ⟨r,hr⟩ := hx
  obtain ⟨s,hs⟩ := hy
  exact delimited_prefix_unique A x y r s (hr.symm.trans hs)

end

open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]

@[simp] theorem pass_fill_bareD (a : S) : Pass A M (.fill a) (bare A .cutD) := by rfl
@[simp] theorem pass_spare_D : Pass A M .spare (bare A .cutD) := by rfl

end FiniteAlgebraicEnvelopes.Compiler.Simulator

end OAI
end

section
-- module Solutions.OAIFAE.Control
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite control and bounded compiler orbit normalization.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.Cleanup
open Relation
variable {S Γ : Type*}

inductive Head
  | cleanup | raw
  deriving DecidableEq

abbrev Sector (S Γ : Type*) := Scan.Sector Head (Base S) (Tag S Γ)

/-- Exactly the cleanup letter prescribed in the finite compiler. Output marks
    on nonanchors are deliberately ignored even on dirty configurations. -/
def emit (c : Base S × Tag S Γ) : Option S :=
  match c.1 with
  | .anchor _ => c.2.output
  | _ => none

def letter (blank : Γ) (a : S) : Base S × Tag S Γ := (.anchor a,clean blank)

def output (blank : Γ) (l : List (Base S × Tag S Γ)) : List (Base S × Tag S Γ) :=
  (l.filterMap emit).map (letter blank)

/-- The left sweep deletes every consumed tagged cell, and only marks on
    anchors produce a clean right-hand anchor. The boundary test is literal. -/
def step (blank : Γ) (v : Sector S Γ) : Option (Sector S Γ) :=
  match v.head with
  | .raw => none
  | .cleanup => match v.left with
    | c::l => some { v with left := l, right := (emit c).toList.map (letter blank) ++ v.right }
    | [] => if v.leftBoundary then some {v with head := .raw} else none

@[simp] theorem output_nil (blank : Γ) : output (S := S) blank [] = [] := rfl

@[simp] theorem output_append (blank : Γ) (l r : List (Base S × Tag S Γ)) :
    output blank (l++r) = output blank l ++ output blank r := by
  simp [output,List.filterMap_append]

@[simp] theorem output_singleton (blank : Γ) (c : Base S × Tag S Γ) :
    output blank [c] = (emit c).toList.map (letter blank) := by
  cases h : emit c <;> simp [output,h]

/-- Normalization of a cleanup head, with or without a left boundary. -/
def normal (blank : Γ) (v : Sector S Γ) : Sector S Γ :=
  match v.head with
  | .raw => v
  | .cleanup => ⟨[],if v.leftBoundary then .raw else .cleanup,
      output blank v.left.reverse ++ v.right,v.leftBoundary,v.rightBoundary⟩

def grade : Base S → ℕ
  | .cutC => 2
  | .workspace => 0
  | _ => 1

def cellsGrade (l : List (Base S × Tag S Γ)) : ℕ := (l.map (grade ∘ Prod.fst)).sum

@[simp] theorem cellsGrade_append (l r : List (Base S × Tag S Γ)) :
    cellsGrade (l++r) = cellsGrade l + cellsGrade r := by simp [cellsGrade]

@[simp] theorem cellsGrade_reverse (l : List (Base S × Tag S Γ)) :
    cellsGrade l.reverse = cellsGrade l := by simp [cellsGrade,List.map_reverse]

end FiniteAlgebraicEnvelopes.Compiler.Cleanup

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
open Relation
variable {H B T : Type*}

/-- An explicit bounded list enumeration, used only for finite internal search.
    This bound counts cells, not grade, and thus never admits quota insertion. -/
def boundedLists (α : Type*) [Fintype α] [DecidableEq α] : ℕ → Finset (List α)
  | 0 => {[]}
  | n+1 => {[]} ∪ ((Finset.univ : Finset α) ×ˢ boundedLists α n).image (fun p => p.1::p.2)

@[simp] theorem mem_boundedLists (α : Type*) [Fintype α] [DecidableEq α]
    (n : ℕ) (l : List α) : l ∈ boundedLists α n ↔ l.length ≤ n := by
  induction n generalizing l with
  | zero => simp [boundedLists]
  | succ n ih =>
      cases l with
      | nil => simp [boundedLists]
      | cons a l => simp [boundedLists,ih]

variable [Fintype H] [Fintype B] [Fintype T]
variable [DecidableEq H] [DecidableEq B] [DecidableEq T]

/-- The finite search universe consists of actual list-zipper sectors. -/
def boundedSectors (k : ℕ) : Finset (Sector H B T) :=
  (((((Finset.univ : Finset H) ×ˢ boundedLists (B×T) k) ×ˢ boundedLists (B×T) k) ×ˢ
      (Finset.univ : Finset Bool)) ×ˢ (Finset.univ : Finset Bool)).image
    (fun p => ⟨p.1.1.1.2,p.1.1.1.1,p.1.1.2,p.1.2,p.2⟩)

@[simp] theorem mem_boundedSectors (k : ℕ) (v : Sector H B T) :
    v ∈ boundedSectors k ↔ v.left.length ≤ k ∧ v.right.length ≤ k := by
  rcases v with ⟨l,q,r,a,b⟩
  simp [boundedSectors,Sector.mk.injEq]

/-- Filtering by bases and boundary flags gives exactly the source's fixed
    internal-search state space. This is computable from the literal sector. -/
def searchUniverse (v : Sector H B T) : Finset (Sector H B T) :=
  (boundedSectors (v.left.length+v.right.length)).filter
    (fun w => baseSkeleton w = baseSkeleton v)

omit [Fintype H] [Fintype B] [Fintype T] [DecidableEq H] [DecidableEq B] [DecidableEq T] in
theorem skeleton_length {v w : Sector H B T} (h : baseSkeleton v = baseSkeleton w) :
    v.left.length+v.right.length = w.left.length+w.right.length := by
  have hl := congrArg (fun p : List B × Bool × Bool => p.1.length) h
  simpa [baseSkeleton] using hl

@[simp] theorem mem_universe (v w : Sector H B T) :
    w ∈ searchUniverse v ↔ baseSkeleton w = baseSkeleton v := by
  simp only [searchUniverse,Finset.mem_filter,mem_boundedSectors,and_iff_right_iff_imp]
  intro h
  have hl := skeleton_length h
  constructor <;> omega

abbrev Fixed (v : Sector H B T) := {w : Sector H B T // baseSkeleton w = baseSkeleton v}

instance fixedFintype (v : Sector H B T) : Fintype (Fixed v) :=
  Fintype.subtype (searchUniverse v) (mem_universe v)

def fixedSelf (v : Sector H B T) : Fixed v := ⟨v,rfl⟩

def fixedStep (table : Table H B T) (v : Sector H B T) (a b : Fixed v) : Prop :=
  Step table a.val b.val

instance fixedStepDecidable (table : Table H B T) (v : Sector H B T) :
    DecidableRel (fixedStep table v) := fun _ _ => inferInstanceAs (Decidable (_ = _))

omit [Fintype H] [Fintype B] [Fintype T] [DecidableEq H] [DecidableEq B] [DecidableEq T] in
theorem connected_skeleton (table : Table H B T) {x y : Sector H B T}
    (h : EqvGen (Step table) x y) : baseSkeleton x = baseSkeleton y := by
  induction h with
  | rel _ _ h => exact step_skeleton table h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

omit [Fintype H] [Fintype B] [Fintype T] [DecidableEq H] [DecidableEq B] [DecidableEq T] in
/-- A weak path with fixed baselines lifts to the finite search universe. -/
theorem fixedConnected_iff (table : Table H B T) (v : Sector H B T) (a b : Fixed v) :
    EqvGen (fixedStep table v) a b ↔ EqvGen (Step table) a.val b.val := by
  constructor
  · intro h
    induction h with
    | rel _ _ h => exact .rel _ _ h
    | refl => exact .refl _
    | symm _ _ _ ih => exact .symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂
  · intro h
    have lift : ∀ x y, EqvGen (Step table) x y →
        ∀ (hx : baseSkeleton x = baseSkeleton v),
        ∃ (hy : baseSkeleton y = baseSkeleton v),
          EqvGen (fixedStep table v) ⟨x,hx⟩ ⟨y,hy⟩ := by
      intro x y h
      induction h with
      | rel x y h =>
          intro hx
          exact ⟨(step_skeleton table h).symm.trans hx,.rel _ _ h⟩
      | refl x => intro hx; exact ⟨hx,.refl _⟩
      | symm x y h ih =>
          intro hy
          have hbase := connected_skeleton table h
          obtain ⟨_,hr⟩ := ih (hbase.trans hy)
          exact ⟨hbase.trans hy,.symm _ _ hr⟩
      | trans x y z _ _ ih₁ ih₂ =>
          intro hx
          obtain ⟨hy,hxy⟩ := ih₁ hx
          obtain ⟨hz,hyz⟩ := ih₂ hy
          exact ⟨hz,.trans _ _ _ hxy hyz⟩
    obtain ⟨_,h'⟩ := lift a.val b.val h a.property
    exact h'

end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Compiler.Compiled

section
open Relation
variable {S Γ Q : Type*}
abbrev MachineSector (S Γ Q : Type*) := Scan.Sector (Simulator.Head S Q) (Base S) (Tag S Γ)
abbrev Cfg (S Γ Q : Type*) := Validator.Extended.Cfg S Γ (MachineSector S Γ Q)

/-- The fresh handoff is one state, not two copies joined by an artificial edge. -/
def embed (v : MachineSector S Γ Q) : Cfg S Γ Q :=
  match v.head with
  | .start => .inl ⟨.start,v.left,v.right,v.leftBoundary,v.rightBoundary⟩
  | _ => .inr v

def project : Cfg S Γ Q → MachineSector S Γ Q
  | .inl v => ⟨v.left,.start,v.right,v.leftBoundary,v.rightBoundary⟩
  | .inr v => v

@[simp] theorem project_embed (v : MachineSector S Γ Q) : project (embed v) = v := by
  rcases v with ⟨l,q,r,a,b⟩
  cases q <;> rfl

@[simp] theorem embed_active (v : MachineSector S Γ Q) : Validator.Extended.Active (embed v) := by
  unfold embed
  split <;> trivial

@[simp] theorem embed_project {v : Cfg S Γ Q} (hv : Validator.Extended.Active v)
    (hc : ∀ u, v = .inr u → u.head ≠ .start) : embed (project v) = v := by
  cases v with
  | inl v => simp only [Validator.Extended.Active] at hv; cases v; cases hv; rfl
  | inr v =>
      have h := hc v rfl
      simp only [project,embed]

variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ) [DecidableEq Γ]

abbrev bases : Cfg S Γ Q → List (Base S) × Bool × Bool :=
  Validator.Extended.baseSkeleton Scan.baseSkeleton

omit [DecidableEq Γ] in
@[simp] theorem embed_bases (v : MachineSector S Γ Q) : bases (embed v) = Scan.baseSkeleton v := by
  unfold embed
  split <;> rfl

end

open Relation
variable {S Γ Q : Type*}

def handoff (blank : Γ) (x y : List S) (s : ℕ) : Validator.Sector S Γ :=
  ⟨.start,(y.map (fun a => Validator.cell blank (.anchor a))).reverse ++
    Validator.cell blank .cutD :: (List.replicate s (Validator.cell blank .workspace) ++
    Validator.cell blank .cutC :: (x.map (fun a => Validator.cell blank (.anchor a))).reverse),
    [],true,true⟩

variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ) [DecidableEq Γ]

omit [DecidableEq Γ] in
@[simp] theorem project_handoff (x y : List S) (s : ℕ) :
    (project (.inl (handoff A.blank x y s)) : MachineSector S Γ Q) =
      ⟨(Simulator.body A [] x [] y [] s).reverse,.start,[],true,true⟩ := by
  simp [project,handoff,Simulator.body,Simulator.readAnchor,Simulator.bare,Validator.cell,
    clean,List.append_assoc]

end FiniteAlgebraicEnvelopes.Compiler.Compiled

namespace FiniteAlgebraicEnvelopes.Compiler.Validator
variable {S Γ : Type*}

def toScan (v : Sector S Γ) : Scan.Sector Head (Base S) (Tag S Γ) :=
  ⟨v.left,v.head,v.right,v.leftBoundary,v.rightBoundary⟩

def ofScan (v : Scan.Sector Head (Base S) (Tag S Γ)) : Sector S Γ :=
  ⟨v.head,v.left,v.right,v.leftBoundary,v.rightBoundary⟩

@[simp] theorem toScan_ofScan (v : Scan.Sector Head (Base S) (Tag S Γ)) :
    toScan (ofScan v) = v := rfl
@[simp] theorem ofScan_toScan (v : Sector S Γ) : ofScan (toScan v) = v := rfl

variable (blank : Γ) [DecidableEq S] [DecidableEq Γ]

/-- The displayed validator equations as an executable finite scan table. -/
def table : Table Head (Base S) (Tag S Γ) where
  direction
    | .initial | .left => .left
    | _ => .right
  cell q b t := if t = clean blank then
    match q,b with
    | .initial,.workspace => some ⟨.initial,t,true⟩
    | .initial,.cutC => some ⟨.left,t,true⟩
    | .left,.anchor _ => some ⟨.left,t,true⟩
    | .right,.anchor _ => some ⟨.right,t,true⟩
    | .right,.cutC => some ⟨.workspace,t,true⟩
    | .workspace,.workspace => some ⟨.workspace,t,true⟩
    | .workspace,.cutD => some ⟨.suffix,t,true⟩
    | .suffix,.anchor _ => some ⟨.suffix,t,true⟩
    | _,_ => none
    else none
  boundary
    | .left => some .right
    | .suffix => some .start
    | _ => none

theorem step_toScan {v w : Sector S Γ} (h : Step blank v w) :
    Scan.Step (table blank) (toScan v) (toScan w) := by
  cases h <;> simp [Scan.Step,Scan.step,toScan,table,cell]

theorem step_ofScan {v w : Scan.Sector Head (Base S) (Tag S Γ)}
    (h : Scan.Step (table blank) v w) : Step blank (ofScan v) (ofScan w) := by
  rcases v with ⟨l,q,r,a,b⟩
  cases q with
  | initial =>
      cases l with
      | nil => cases a <;> simp [Scan.Step,Scan.step,table] at h
      | cons c l =>
          rcases c with ⟨base,t⟩
          by_cases ht : t = clean blank
          · subst t
            cases base <;> simp [Scan.Step,Scan.step,table] at h
            all_goals subst w; first | exact .initial_cut _ _ _ _ | exact .initial_workspace _ _ _ _
          · simp [Scan.Step,Scan.step,table,ht] at h
  | left =>
      cases l with
      | nil =>
          cases a <;> simp [Scan.Step,Scan.step,table] at h
          subst w; exact .left_boundary _ _
      | cons c l =>
          rcases c with ⟨base,t⟩
          by_cases ht : t = clean blank
          · subst t
            cases base <;> simp [Scan.Step,Scan.step,table] at h
            subst w; exact .left_anchor _ _ _ _ _
          · simp [Scan.Step,Scan.step,table,ht] at h
  | right =>
      cases r with
      | nil => cases b <;> simp [Scan.Step,Scan.step,table] at h
      | cons c r =>
          rcases c with ⟨base,t⟩
          by_cases ht : t = clean blank
          · subst t
            cases base <;> simp [Scan.Step,Scan.step,table] at h
            all_goals subst w; first | exact .right_anchor _ _ _ _ _ | exact .right_cut _ _ _ _
          · simp [Scan.Step,Scan.step,table,ht] at h
  | workspace =>
      cases r with
      | nil => cases b <;> simp [Scan.Step,Scan.step,table] at h
      | cons c r =>
          rcases c with ⟨base,t⟩
          by_cases ht : t = clean blank
          · subst t
            cases base <;> simp [Scan.Step,Scan.step,table] at h
            all_goals subst w; first | exact .workspace _ _ _ _ | exact .workspace_cut _ _ _ _
          · simp [Scan.Step,Scan.step,table,ht] at h
  | suffix =>
      cases r with
      | nil =>
          cases b <;> simp [Scan.Step,Scan.step,table] at h
          subst w; exact .suffix_boundary _ _
      | cons c r =>
          rcases c with ⟨base,t⟩
          by_cases ht : t = clean blank
          · subst t
            cases base <;> simp [Scan.Step,Scan.step,table] at h
            subst w; exact .suffix_anchor _ _ _ _ _
          · simp [Scan.Step,Scan.step,table,ht] at h
  | start =>
      cases r with
      | nil => cases b <;> simp [Scan.Step,Scan.step,table] at h
      | cons c r =>
          rcases c with ⟨base,t⟩
          by_cases ht : t = clean blank <;> simp [Scan.Step,Scan.step,table,ht] at h

@[simp] theorem step_iff_scan (v w : Sector S Γ) :
    Step blank v w ↔ Scan.Step (table blank) (toScan v) (toScan w) :=
  ⟨step_toScan blank,step_ofScan blank⟩

end FiniteAlgebraicEnvelopes.Compiler.Validator

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
variable {H H' B T : Type*}

def mapHead (f : H → H') (v : Sector H B T) : Sector H' B T :=
  ⟨v.left,f v.head,v.right,v.leftBoundary,v.rightBoundary⟩

def mapInstruction (f : H → H') (v : Instruction H T) : Instruction H' T :=
  ⟨f v.head,v.tag,v.cross⟩

@[simp] theorem skeleton_mapHead (f : H → H') (v : Sector H B T) :
    baseSkeleton (mapHead f v) = baseSkeleton v := rfl

end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Compiler.Control

section
open Relation
variable {S Γ Q : Type*}

/-- Finite internal-head alphabet, with a single fresh handoff/start state. -/
inductive Head (S Q : Type*)
  | initial | left | right | workspace | suffix
  | machine : Simulator.Head S Q → Head S Q
  deriving DecidableEq, Fintype

def validatorHead : Validator.Head → Head S Q
  | .initial => .initial
  | .left => .left
  | .right => .right
  | .workspace => .workspace
  | .suffix => .suffix
  | .start => .machine .start

def toValidator : Head S Q → Option Validator.Head
  | .initial => some .initial
  | .left => some .left
  | .right => some .right
  | .workspace => some .workspace
  | .suffix => some .suffix
  | .machine _ => none

abbrev Sector (S Γ Q : Type*) := Scan.Sector (Head S Q) (Base S) (Tag S Γ)

def validator (v : Validator.Sector S Γ) : Sector S Γ Q :=
  Scan.mapHead validatorHead (Validator.toScan v)

def machine (v : Compiled.MachineSector S Γ Q) : Sector S Γ Q :=
  Scan.mapHead Head.machine v

def toCfg (v : Sector S Γ Q) : Compiled.Cfg S Γ Q :=
  match v.head with
  | .initial => .inl ⟨.initial,v.left,v.right,v.leftBoundary,v.rightBoundary⟩
  | .left => .inl ⟨.left,v.left,v.right,v.leftBoundary,v.rightBoundary⟩
  | .right => .inl ⟨.right,v.left,v.right,v.leftBoundary,v.rightBoundary⟩
  | .workspace => .inl ⟨.workspace,v.left,v.right,v.leftBoundary,v.rightBoundary⟩
  | .suffix => .inl ⟨.suffix,v.left,v.right,v.leftBoundary,v.rightBoundary⟩
  | .machine q => Compiled.embed ⟨v.left,q,v.right,v.leftBoundary,v.rightBoundary⟩

@[simp] theorem cfg_validator (v : Validator.Sector S Γ) : toCfg (validator (Q := Q) v) = .inl v := by
  cases v with | mk q l r a b => cases q <;> rfl

@[simp] theorem cfg_machine (v : Compiled.MachineSector S Γ Q) :
    toCfg (machine v) = Compiled.embed v := rfl

variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ]

/-- The literal finite union of validation and simulation equations. -/
def table : Table (Head S Q) (Base S) (Tag S Γ) where
  direction q := match toValidator q with
    | some v => (Validator.table (S := S) A.blank).direction v
    | none => match q with
      | .machine v => (Simulator.table A M).direction v
      | _ => .right
  cell q b t := match toValidator q with
    | some v => ((Validator.table (S := S) A.blank).cell v b t).map (Scan.mapInstruction validatorHead)
    | none => match q with
      | .machine v => ((Simulator.table A M).cell v b t).map (Scan.mapInstruction Head.machine)
      | _ => none
  boundary q := match toValidator q with
    | some v => ((Validator.table (S := S) A.blank).boundary v).map validatorHead
    | none => match q with
      | .machine v => ((Simulator.table A M).boundary v).map Head.machine
      | _ => none

end

open Relation
variable {S Γ Q : Type*}

def ofCfg : Compiled.Cfg S Γ Q → Sector S Γ Q
  | .inl v => validator v
  | .inr v => machine v

@[simp] theorem ofCfg_embed (v : Compiled.MachineSector S Γ Q) :
    ofCfg (Compiled.embed v) = machine v := by
  rcases v with ⟨l,q,r,a,b⟩
  cases q <;> rfl

@[simp] theorem ofCfg_toCfg (v : Sector S Γ Q) : ofCfg (toCfg v) = v := by
  rcases v with ⟨l,q,r,a,b⟩
  cases q <;> first | rfl | exact ofCfg_embed _

end FiniteAlgebraicEnvelopes.Compiler.Control

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
open Relation
variable {H B T : Type*} [Fintype H] [Fintype B] [Fintype T]
  [DecidableEq H] [DecidableEq B] [DecidableEq T]

/-- Literal configurations, rather than an oracle for connectivity, returned
    by exhaustive search on the fixed finite base skeleton. -/
def literalComponent (table : Table H B T) (v : Sector H B T) : Finset (Sector H B T) :=
  (component (fixedStep table v) (fixedSelf v)).image Subtype.val

@[simp] theorem mem_literalComponent (table : Table H B T) (v w : Sector H B T) :
    w ∈ literalComponent table v ↔ EqvGen (Step table) v w := by
  constructor
  · intro h
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp h
    exact (fixedConnected_iff table v _ _).mp ((mem_component_iff _ _ _).mp hu)
  · intro h
    let u : Fixed v := ⟨w,(connected_skeleton table h).symm⟩
    apply Finset.mem_image.mpr
    refine ⟨u,?_,rfl⟩
    exact (mem_component_iff _ _ _).mpr ((fixedConnected_iff table v _ _).mpr h)

theorem literalComponent_nonempty (table : Table H B T) (v : Sector H B T) :
    (literalComponent table v).Nonempty :=
  ⟨v,(mem_literalComponent table v v).mpr (.refl v)⟩

end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Compiler
variable {α : Type*}

/-- The priority order in source compiler-normalization: entry first, success
    second, and arbitrary component member only when neither is present. -/
def prioritySet (P Q : α → Prop) [DecidablePred P] [DecidablePred Q] (s : Finset α) : Finset α :=
  if (s.filter P).Nonempty then s.filter P
  else if (s.filter Q).Nonempty then s.filter Q else s

theorem prioritySet_nonempty (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    (s : Finset α) (hs : s.Nonempty) : (prioritySet P Q s).Nonempty := by
  unfold prioritySet
  split
  · assumption
  · split <;> assumption

end FiniteAlgebraicEnvelopes.Compiler

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
open Relation
variable {H B T : Type*} [Fintype H] [Fintype B] [Fintype T]
  [DecidableEq H] [DecidableEq B] [DecidableEq T] [LinearOrder (Sector H B T)]
variable (table : Table H B T) (P Q : Sector H B T → Prop) [DecidablePred P] [DecidablePred Q]

def representative (v : Sector H B T) : Sector H B T :=
  (prioritySet P Q (literalComponent table v)).min'
    (prioritySet_nonempty P Q _ (literalComponent_nonempty table v))

end FiniteAlgebraicEnvelopes.Compiler.Scan

end OAI
end

section
-- module Solutions.OAIFAE.Surface
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Surface alphabet, preprocessing, and grading estimates.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.Surface

section
open Relation

/-- The complete head alphabet; internal control excludes raw, quota and cleanup. -/
inductive Head (H : Type*)
  | raw | pending | cleanup
  | internal : H → Head H
  deriving DecidableEq, Fintype

abbrev Sector (S Γ H : Type*) := Scan.Sector (Head H) (Base S) (Tag S Γ)
variable {S Γ H : Type*}
abbrev Cells (S Γ : Type*) := List (Base S × Tag S Γ)

def grade (v : Sector S Γ H) : ℕ :=
  Cleanup.cellsGrade v.left + 1 + Cleanup.cellsGrade v.right +
    (if v.leftBoundary then 1 else 0) + (if v.rightBoundary then 1 else 0)

variable (blank : Γ) [DecidableEq S] [DecidableEq Γ]

def rawSweep : Cells S Γ → Cells S Γ → Bool → Bool → Sector S Γ H
  | [],r,lb,rb => ⟨[],.raw,r,lb,rb⟩
  | (b,t)::l,r,lb,rb => match b with
    | .anchor _a => if t = clean blank then rawSweep l ((b,t)::r) lb rb
        else ⟨(b,t)::l,.raw,r,lb,rb⟩
    | _ => ⟨(b,t)::l,.raw,r,lb,rb⟩

def rawNormal (v : Sector S Γ H) : Sector S Γ H :=
  match v.head with
  | .raw => rawSweep blank v.left v.right v.leftBoundary v.rightBoundary
  | _ => v

/-- Literal raw singleton; in particular no program is evaluated on it. -/
def raw (w : List S) : Sector S Γ H :=
  ⟨[],.raw,w.map (Validator.cell blank ∘ Base.anchor),true,true⟩

@[simp] theorem rawNormal_raw (w : List S) : rawNormal blank (raw (H := H) blank w) = raw blank w := rfl

end

section
open Relation
variable {S Γ H : Type*} (blank : Γ)

variable [DecidableEq S] [DecidableEq Γ]

def trimQuota : Cells S Γ → Cells S Γ
  | [] => []
  | c::l => if c = Validator.cell blank .workspace then trimQuota l else c::l

def quotaNormal (v : Sector S Γ H) : Sector S Γ H :=
  match v.head,v.right with
  | .pending,d::_ => if d = Validator.cell blank .cutD then {v with left := trimQuota blank v.left} else v
  | _,_ => v

/-- Unmerge after trimming. The outer boundaries may be absent and the outer
    cells may be arbitrarily dirty. Only the two displayed cut cells are tested. -/
def unmerge (v : Sector S Γ H) : List (Sector S Γ H) :=
  match v.left,v.head,v.right with
  | c::l,.pending,d::r =>
    if c = Validator.cell blank .cutC ∧ d = Validator.cell blank .cutD then
      [rawNormal blank ⟨l,.raw,[],v.leftBoundary,true⟩,
        rawNormal blank ⟨[],.raw,r,true,v.rightBoundary⟩]
    else [v]
  | _,_,_ => [v]

def pendingPreprocess (v : Sector S Γ H) : List (Sector S Γ H) :=
  unmerge blank (quotaNormal blank v)

end

open Relation
variable {S Γ H : Type*}

def cleanupHead : Cleanup.Head → Head H
  | .cleanup => .cleanup
  | .raw => .raw

def ofCleanup (v : Cleanup.Sector S Γ) : Sector S Γ H := Scan.mapHead cleanupHead v

def cleanupNormal (blank : Γ) (v : Sector S Γ H) : Sector S Γ H :=
  match v.head with
  | .cleanup => ofCleanup (Cleanup.normal blank
      ⟨v.left,.cleanup,v.right,v.leftBoundary,v.rightBoundary⟩)
  | _ => v

@[simp] theorem cleanupNormal_ofCleanup (blank : Γ) (v : Cleanup.Sector S Γ) :
    cleanupNormal blank (ofCleanup (H := H) v) = ofCleanup (Cleanup.normal blank v) := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q <;> rfl

variable (blank : Γ) [DecidableEq S] [DecidableEq Γ]

def cleanupPreprocess (v : Sector S Γ H) : Sector S Γ H :=
  rawNormal blank (cleanupNormal blank v)

@[simp] theorem cleanupPreprocess_ofCleanup (v : Cleanup.Sector S Γ) :
    cleanupPreprocess blank (ofCleanup (H := H) v) =
      rawNormal blank (ofCleanup (Cleanup.normal blank v)) := by
  rw [cleanupPreprocess,cleanupNormal_ofCleanup]

@[simp] theorem cleanupPreprocess_raw (w : List S) :
    cleanupPreprocess blank (raw (H := H) blank w) = raw blank w := rfl

end FiniteAlgebraicEnvelopes.Compiler.Surface

namespace FiniteAlgebraicEnvelopes.Compiler.Control
open Relation
variable {S Γ Q : Type*}

/-- Literal entry and successful exit tests, both finite data predicates. -/
def Entry (blank : Γ) (v : Sector S Γ Q) : Prop :=
  v.head = .initial ∧ v.right.head? = some (Validator.cell blank .cutD)

def Success (v : Sector S Γ Q) : Prop :=
  v.head = .machine .ok ∧ v.right = [] ∧ v.rightBoundary = true

instance entryDecidable (blank : Γ) [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] :
    DecidablePred (Entry (S := S) (Q := Q) blank) := fun _ => inferInstanceAs (Decidable (_ ∧ _))

instance successDecidable [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] :
    DecidablePred (Success (S := S) (Γ := Γ) (Q := Q)) := fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ]

variable [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
  [LinearOrder (Sector S Γ Q)]

def representative (v : Sector S Γ Q) : Sector S Γ Q :=
  Scan.representative (table A M) (Entry A.blank) Success v

end FiniteAlgebraicEnvelopes.Compiler.Control

namespace FiniteAlgebraicEnvelopes.Compiler.Surface

section
open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

/-- Internal finite-component search, with entry priority. No invocation of the
    compiled machine as an evaluator occurs here. -/
def internalPreprocess (v : Control.Sector S Γ Q) : List (Sector S Γ (Control.Head S Q)) :=
  let w := Control.representative A M v
  if Control.Entry A.blank w then
    pendingPreprocess A.blank ⟨w.left,.pending,w.right,w.leftBoundary,w.rightBoundary⟩
  else if Control.Success w then
    [cleanupPreprocess A.blank ⟨w.left,.cleanup,w.right,w.leftBoundary,w.rightBoundary⟩]
  else [Scan.mapHead Head.internal w]

/-- Complete sector preprocessing, prior to the only partial operation: maximal
    full-raw-run evaluation. Headless sectors will be preserved by the parser. -/
def preprocess (v : Sector S Γ (Control.Head S Q)) : List (Sector S Γ (Control.Head S Q)) :=
  match v.head with
  | .raw => [rawNormal A.blank v]
  | .pending => pendingPreprocess A.blank v
  | .cleanup => [cleanupPreprocess A.blank v]
  | .internal q => internalPreprocess A M ⟨v.left,q,v.right,v.leftBoundary,v.rightBoundary⟩

@[simp] theorem preprocess_raw (w : List S) : preprocess A M (raw A.blank w) = [raw A.blank w] := rfl

end

open Relation
variable {S Γ H H' : Type*}

variable {Q : Type*} (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

@[simp] theorem preprocess_ofCleanup (v : Cleanup.Sector S Γ) :
    preprocess A M (ofCleanup v) = [cleanupPreprocess A.blank (ofCleanup v)] := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q <;> rfl

end FiniteAlgebraicEnvelopes.Compiler.Surface

/- Literal path alphabet and sector parsing for the finite compiler.
   All definitions are independent of the partial program. -/

end OAI
end

section
-- module Solutions.OAIFAE.Paths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Path alphabet, sectors, cuts, and contextual preparation.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.Path

section

inductive Vertex
  | outer | left | right
  deriving DecidableEq

instance instFintypeVertex : Fintype Vertex := ⟨{.outer,.left,.right}, by intro x; cases x <;> simp⟩

/-- There are no vertex-identity letters. `zero` is the absorbing letter. -/
inductive Letter (C H : Type*)
  | zero | enter | leave
  | head : H → Letter C H
  | left : C → Letter C H
  | right : C → Letter C H
  deriving DecidableEq, Fintype

/-- Boundary type of a word; `unit` belongs only to the empty word. -/
inductive Shape
  | zero | unit
  | path : Vertex → Vertex → Shape
  deriving DecidableEq

instance instFintypeShape : Fintype Shape :=
  ⟨{.zero,.unit} ∪ Finset.univ.biUnion (fun a => Finset.univ.image (Shape.path a)), by
    intro x; cases x <;> simp⟩

def Shape.comp : Shape → Shape → Shape
  | .zero,_ => .zero
  | _,.zero => .zero
  | .unit,b => b
  | a,.unit => a
  | .path a b,.path c d => if b = c then .path a d else .zero

instance instMonoidShape : Monoid Shape where
  mul := Shape.comp
  one := .unit
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide

@[simp] theorem unit_mul (s : Shape) : Shape.unit * s = s := one_mul s
@[simp] theorem mul_unit (s : Shape) : s * Shape.unit = s := mul_one s

@[simp] theorem zero_mul (s : Shape) : Shape.zero * s = .zero := rfl
@[simp] theorem mul_zero (s : Shape) : s * Shape.zero = .zero := by cases s <;> rfl
@[simp] theorem path_mul_path (a b c d : Vertex) :
    Shape.path a b * Shape.path c d = if b = c then .path a d else .zero := rfl

variable {C H : Type*}

def typeOf : Letter C H → Shape
  | .zero => .zero
  | .enter => .path .outer .left
  | .leave => .path .right .outer
  | .head _ => .path .left .right
  | .left _ => .path .left .left
  | .right _ => .path .right .right

def shape (w : List (Letter C H)) : Shape := (w.map typeOf).prod

@[simp] theorem shape_nil : shape ([] : List (Letter C H)) = .unit := rfl
@[simp] theorem shape_cons (a : Letter C H) (w : List (Letter C H)) :
    shape (a::w) = typeOf a * shape w := by simp [shape]
@[simp] theorem shape_append (u v : List (Letter C H)) :
    shape (u++v) = shape u * shape v := by simp [shape]
@[simp] theorem shape_singleton (a : Letter C H) : shape [a] = typeOf a := by simp

@[simp] theorem typeOf_ne_unit (a : Letter C H) : typeOf a ≠ .unit := by
  cases a <;> simp [typeOf]

/-- A headed sector written literally. Cells left of the head are supplied in
    nearest-first zipper order. -/
def headed (l : List C) (q : H) (r : List C) (lb rb : Bool) : List (Letter C H) :=
  (if lb then [.enter] else []) ++ l.reverse.map .left ++ [.head q] ++
    r.map .right ++ (if rb then [.leave] else [])

@[simp] theorem shape_left (l : List C) :
    shape (l.map (Letter.left : C → Letter C H)) =
      if l = [] then .unit else .path .left .left := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases l with
    | nil => simp [typeOf]
    | cons b l => simp_all [typeOf]

@[simp] theorem shape_right (l : List C) :
    shape (l.map (Letter.right : C → Letter C H)) =
      if l = [] then .unit else .path .right .right := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases l with
    | nil => simp [typeOf]
    | cons b l => simp_all [typeOf]

@[simp] theorem shape_headed (l : List C) (q : H) (r : List C) (lb rb : Bool) :
    shape (headed l q r lb rb) =
      .path (if lb then .outer else .left) (if rb then .outer else .right) := by
  classical
  unfold headed
  simp only [shape_append,shape_left,shape_right,shape_singleton,List.reverse_eq_nil_iff]
  cases lb <;> cases rb <;> by_cases hl : l = [] <;> by_cases hr : r = [] <;>
    simp [hl,hr,typeOf]

def heads : List (Letter C H) → List H := List.filterMap fun
  | .head q => some q
  | _ => none

def lefts : List (Letter C H) → List C := List.filterMap fun
  | .left c => some c
  | _ => none

def rights : List (Letter C H) → List C := List.filterMap fun
  | .right c => some c
  | _ => none

@[simp] theorem heads_headed (l : List C) (q : H) (r : List C) (lb rb : Bool) :
    heads (headed l q r lb rb) = [q] := by
  cases lb <;> cases rb <;> simp [headed,heads,List.filterMap_map]

@[simp] theorem lefts_headed (l : List C) (q : H) (r : List C) (lb rb : Bool) :
    lefts (headed l q r lb rb) = l.reverse := by
  cases lb <;> cases rb <;> simp [headed,lefts,List.filterMap_map]

@[simp] theorem rights_headed (l : List C) (q : H) (r : List C) (lb rb : Bool) :
    rights (headed l q r lb rb) = r := by
  cases lb <;> cases rb <;> simp [headed,rights,List.filterMap_map]

/-- Prefix a (possibly empty) fragment to the first sector, creating a sector
    only when the fragment is nonempty. -/
def glue (u : List (Letter C H)) (cs : List (List (Letter C H))) : List (List (Letter C H)) :=
  match cs with
  | c::cs => (u++c)::cs
  | [] => match u with
    | [] => []
    | _::_ => [u]

@[simp] theorem glue_nil (cs : List (List (Letter C H))) : glue [] cs = cs := by
  cases cs <;> rfl

@[simp] theorem glue_cons (u c : List (Letter C H)) (cs : List (List (Letter C H))) :
    glue u (c::cs) = (u++c)::cs := rfl

theorem glue_assoc (u v : List (Letter C H)) (cs : List (List (Letter C H))) :
    glue u (glue v cs) = glue (u++v) cs := by
  cases cs <;> cases u <;> cases v <;> simp [glue,List.append_assoc]

/-- Cut immediately after an omega, omitting the empty final sector. On paths
    every interior cut is exactly omega-alpha, including headless end sectors. -/
def cuts : List (Letter C H) → List (List (Letter C H))
  | [] => []
  | .leave::w => [.leave] :: cuts w
  | a::w => glue [a] (cuts w)

@[simp] theorem cuts_nil : cuts ([] : List (Letter C H)) = [] := rfl
@[simp] theorem cuts_leave (w : List (Letter C H)) : cuts (.leave::w) = [.leave]::cuts w := rfl

theorem cuts_cons {a : Letter C H} (ha : a ≠ .leave) (w : List (Letter C H)) :
    cuts (a::w) = glue [a] (cuts w) := by cases a <;> simp_all [cuts]

@[simp] theorem flatten_glue (u : List (Letter C H)) (cs : List (List (Letter C H))) :
    (glue u cs).flatten = u ++ cs.flatten := by
  cases cs <;> cases u <;> simp [glue,List.append_assoc]

@[simp] theorem flatten_cuts (w : List (Letter C H)) : (cuts w).flatten = w := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp [cuts,ih]

theorem cuts_append_nonleave (u v : List (Letter C H)) (hu : Letter.leave ∉ u) :
    cuts (u++v) = glue u (cuts v) := by
  induction u with
  | nil => simp
  | cons a u ih =>
    have ha : a ≠ .leave := fun h => hu (by simp [h])
    have hu' : Letter.leave ∉ u := fun h => hu (List.mem_cons_of_mem _ h)
    rw [List.cons_append,cuts_cons ha,ih hu',glue_assoc]
    rfl

theorem cuts_of_noLeave (u : List (Letter C H)) (hu : Letter.leave ∉ u) :
    cuts u = glue u [] := by simpa using cuts_append_nonleave u [] hu

@[simp] theorem headed_ne_nil (l : List C) (q : H) (r : List C) (lb rb : Bool) :
    headed l q r lb rb ≠ [] := by
  intro he
  have hh := congrArg heads he
  rw [heads_headed] at hh
  change [q] = [] at hh
  cases hh

@[simp] theorem cuts_headed (l : List C) (q : H) (r : List C) (lb rb : Bool) :
    cuts (headed l q r lb rb) = [headed l q r lb rb] := by
  have hn : (Letter.leave : Letter C H) ∉ headed l q r lb false := by
    cases lb <;> simp [headed]
  have hne := headed_ne_nil l q r lb false
  cases rb
  · rw [cuts_of_noLeave _ hn]
    cases he : headed l q r lb false with
    | nil => exact (hne he).elim
    | cons a w => rfl
  · have he : headed l q r lb true = headed l q r lb false ++ [.leave] := by
      simp [headed,List.append_assoc]
    rw [he,cuts_append_nonleave _ _ hn]
    rfl

def Shape.act : Shape → Vertex → Option Vertex
  | .zero,_ => none
  | .unit,v => some v
  | .path a b,v => if v = a then some b else none

def walk (v : Vertex) (w : List (Letter C H)) : Option Vertex := (shape w).act v

@[simp] theorem walk_nil (v : Vertex) : walk v ([] : List (Letter C H)) = some v := rfl

structure Sector (C H : Type*) where
  left : List C
  head : H
  right : List C
  leftBoundary : Bool
  rightBoundary : Bool
  deriving DecidableEq

def encode (v : Sector C H) : List (Letter C H) :=
  headed v.left v.head v.right v.leftBoundary v.rightBoundary

@[simp] theorem enter_mem_headed (l : List C) (q : H) (r : List C) (lb rb : Bool) :
    (Letter.enter : Letter C H) ∈ headed l q r lb rb ↔ lb = true := by
  cases lb <;> cases rb <;> simp [headed]

@[simp] theorem leave_mem_headed (l : List C) (q : H) (r : List C) (lb rb : Bool) :
    (Letter.leave : Letter C H) ∈ headed l q r lb rb ↔ rb = true := by
  cases lb <;> cases rb <;> simp [headed]

variable [DecidableEq C] [DecidableEq H]

/-- An entirely literal decoder, including a final equality check. It does not
    assume that its input is a path or that any tag is clean. -/
def decode (w : List (Letter C H)) : Option (Sector C H) :=
  match heads w with
  | [q] =>
    let v : Sector C H := ⟨(lefts w).reverse,q,rights w,
      decide (.enter ∈ w),decide (.leave ∈ w)⟩
    if encode v = w then some v else none
  | _ => none

@[simp] theorem decode_encode (v : Sector C H) : decode (encode v) = some v := by
  rcases v with ⟨l,q,r,lb,rb⟩
  simp only [encode,decode,heads_headed,lefts_headed,rights_headed,List.reverse_reverse,
    enter_mem_headed,leave_mem_headed,Bool.decide_eq_true]
  rfl

end

section
open Relation
variable {C H : Type*}

/-- These are exactly the absorbing-letter and incompatible-arrow equations,
    oriented toward the zero letter. -/
inductive ZeroStep : List (Letter C H) → List (Letter C H) → Prop
  | pair (a b : Letter C H) (h : typeOf a * typeOf b = .zero) : ZeroStep [a,b] [.zero]

/-- Additive grade on literal words. The head and boundary letters each have
    grade one, while all cell-tag data is ignored by a supplied base grade. -/
def letterGrade (g : C → ℕ) : Letter C H → ℕ
  | .zero => 0
  | .left c | .right c => g c
  | _ => 1

def grade (g : C → ℕ) (w : List (Letter C H)) : ℕ := (w.map (letterGrade g)).sum

@[simp] theorem grade_nil (g : C → ℕ) : grade g ([] : List (Letter C H)) = 0 := rfl
@[simp] theorem grade_cons (g : C → ℕ) (a : Letter C H) (w : List (Letter C H)) :
    grade g (a::w) = letterGrade g a + grade g w := rfl
@[simp] theorem grade_append (g : C → ℕ) (u v : List (Letter C H)) :
    grade g (u++v) = grade g u + grade g v := by simp [grade]

@[simp] theorem grade_headed (g : C → ℕ) (l : List C) (q : H) (r : List C) (lb rb : Bool) :
    grade g (headed l q r lb rb) = (l.map g).sum + 1 + (r.map g).sum +
      (if lb then 1 else 0) + (if rb then 1 else 0) := by
  cases lb <;> cases rb <;> simp [headed,grade,letterGrade,List.map_reverse,List.map_map,Function.comp_def] <;> ac_rfl

end

section
variable {C H : Type*}

 theorem glue_append_of_ne_nil (u : List (Letter C H))
    (cs ds : List (List (Letter C H))) (h : cs ≠ []) :
    glue u (cs++ds) = glue u cs ++ ds := by
  cases cs with
  | nil => exact (h rfl).elim
  | cons c cs => rfl

 theorem cuts_append_leave (u v : List (Letter C H)) :
    cuts (u ++ .leave::v) = cuts (u++[.leave]) ++ cuts v := by
  induction u with
  | nil => rfl
  | cons a u ih =>
    by_cases ha : a = .leave
    · subst a
      simp only [List.cons_append,cuts_leave,ih]
    · simp only [List.cons_append,cuts_cons ha,ih]
      apply glue_append_of_ne_nil
      intro hh
      have := congrArg List.flatten hh
      simp at this

end

section
variable {C H : Type*} [DecidableEq C] [DecidableEq H]

/-- Preprocessing is applied only to headed sectors. Headless pieces retain
    their literal words; no implicit boundary or identity generator is added. -/
def prepareChunk (P : Sector C H → List (Sector C H)) (w : List (Letter C H)) :
    List (List (Letter C H)) :=
  match decode w with
  | none => [w]
  | some v => (P v).map encode

def prepareChunks (P : Sector C H → List (Sector C H))
    (cs : List (List (Letter C H))) : List (List (Letter C H)) := cs.flatMap (prepareChunk P)

def prepare (P : Sector C H → List (Sector C H)) (w : List (Letter C H)) :
    List (List (Letter C H)) := prepareChunks P (cuts w)

@[simp] theorem prepareChunk_encode (P : Sector C H → List (Sector C H)) (v : Sector C H) :
    prepareChunk P (encode v) = (P v).map encode := by simp [prepareChunk]

@[simp] theorem prepareChunks_append (P : Sector C H → List (Sector C H))
    (cs ds : List (List (Letter C H))) :
    prepareChunks P (cs++ds) = prepareChunks P cs ++ prepareChunks P ds := by
  simp [prepareChunks]

 theorem prepareChunks_singleton (P : Sector C H → List (Sector C H)) (v : Sector C H) :
    prepareChunks P [encode v] = (P v).map encode := by simp [prepareChunks]

end

end FiniteAlgebraicEnvelopes.Compiler.Path

/- Maximal full-raw-run normalization and its one exceptional equation,
   the finite compiler. Nonraw sectors are opaque separators here. -/

end OAI
end

section
-- module Solutions.OAIFAE.Normalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Raw-run folds, full word compilation, partial budgets, and bounded normalization.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.RawRuns
variable {C S : Type*}

abbrev Item (C S : Type*) := Sum C (List S)

/-- Full raw sectors have three structural letters alpha,Q,omega. -/
def itemGrade (g : C → ℕ) : Item C S → ℕ
  | .inl c => g c
  | .inr w => w.length + 3

def grade (g : C → ℕ) (w : List (Item C S)) : ℕ := (w.map (itemGrade g)).sum

@[simp] theorem grade_nil (g : C → ℕ) : grade g ([] : List (Item C S)) = 0 := rfl
@[simp] theorem grade_cons (g : C → ℕ) (a : Item C S) (w : List (Item C S)) :
    grade g (a::w) = itemGrade g a + grade g w := rfl
@[simp] theorem grade_append (g : C → ℕ) (u v : List (Item C S)) :
    grade g (u++v) = grade g u + grade g v := by simp [grade]

/-- Fold a nonempty raw run by adjacent pair replacement. We prove below that
    it agrees with the source's single call on the concatenated maximal run. -/
def prepend (f : List S → List S) : Item C S → List (Item C S) → List (Item C S)
  | .inr x,.inr y::w => .inr (f (x++y))::w
  | a,w => a::w

def normalize (f : List S → List S) : List (Item C S) → List (Item C S)
  | [] => []
  | a::w => prepend f a (normalize f w)

@[simp] theorem normalize_nil (f : List S → List S) : normalize f ([] : List (Item C S)) = [] := rfl
@[simp] theorem normalize_cons (f : List S → List S) (a : Item C S) (w : List (Item C S)) :
    normalize f (a::w) = prepend f a (normalize f w) := rfl

variable {f : List S → List S} {m : ℕ}

/-- On one full raw sector the evaluator never calls the program. -/
@[simp] theorem normalize_singleton (x : List S) :
    normalize f ([.inr x] : List (Item C S)) = [.inr x] := rfl

/-- Split off the entire initial raw run, without changing raw contents. -/
def splitRun : List (Item C S) → List (List S) × List (Item C S)
  | [] => ([],[])
  | .inl c::w => ([],.inl c::w)
  | .inr x::w => let p := splitRun w; (x::p.1,p.2)

@[simp] theorem splitRun_join (w : List (Item C S)) :
    (splitRun w).1.map .inr ++ (splitRun w).2 = w := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp_all [splitRun]

theorem splitRun_length (w : List (Item C S)) : (splitRun w).2.length ≤ w.length := by
  have hh := congrArg List.length (splitRun_join w)
  simp only [List.length_append,List.length_map] at hh
  omega

@[simp] theorem grade_raws (g : C → ℕ) (ws : List (List S)) :
    grade g (ws.map (Sum.inr : List S → Item C S)) = ws.flatten.length + 3*ws.length := by
  induction ws with
  | nil => simp
  | cons w ws ih => simp only [List.map_cons,grade_cons,itemGrade,ih,List.flatten_cons,
      List.length_append,List.length_cons]; omega

/-- The literal source algorithm: a singleton does not invoke f; every longer
    maximal raw run invokes f once on its unmodified concatenation. -/
def source (f : List S → List S) : List (Item C S) → List (Item C S)
  | [] => []
  | .inl c::w => .inl c::source f w
  | .inr x::w =>
    let p := splitRun w
    let z := match p.1 with
      | [] => x
      | _::_ => f (x++p.1.flatten)
    .inr z :: source f p.2
termination_by w => w.length
decreasing_by
  · simp_wf
  · have := splitRun_length w
    simp_wf
    omega

end FiniteAlgebraicEnvelopes.Compiler.RawRuns

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
variable {H B T K : Type*}

/-- Only a change of representation. The cell order and both literal boundary
    flags are retained exactly. -/
def literal (m : H → K) (v : Sector H B T) : Path.Sector (B×T) K :=
  ⟨v.left,m v.head,v.right,v.leftBoundary,v.rightBoundary⟩

def unliteral (v : Path.Sector (B×T) H) : Sector H B T :=
  ⟨v.left,v.head,v.right,v.leftBoundary,v.rightBoundary⟩

@[simp] theorem literal_unliteral (v : Path.Sector (B×T) H) : literal id (unliteral v) = v := by
  cases v; rfl
@[simp] theorem unliteral_literal (v : Sector H B T) : unliteral (literal id v) = v := by
  cases v; rfl

namespace Literal
open _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.Path

/-- Zipper fragments of a literal cell instruction, before and after the
    specified cross/stay move. -/
def inLeft (d : Direction) (c : B×T) : List (B×T) := if d = .left then [c] else []
def inRight (d : Direction) (c : B×T) : List (B×T) := if d = .right then [c] else []
def outLeft (d : Direction) (cross : Bool) (c : B×T) : List (B×T) :=
  if (d = .left ∧ cross = false) ∨ (d = .right ∧ cross = true) then [c] else []
def outRight (d : Direction) (cross : Bool) (c : B×T) : List (B×T) :=
  if (d = .right ∧ cross = false) ∨ (d = .left ∧ cross = true) then [c] else []

inductive Rule (table : Table H B T) (m : H → K) :
    List (Letter (B×T) K) → List (Letter (B×T) K) → Prop
  | cell (q : H) (b : B) (t : T) (i : Instruction H T) (h : table.cell q b t = some i) :
      Rule table m
        (headed (inLeft (table.direction q) (b,t)) (m q) (inRight (table.direction q) (b,t)) false false)
        (headed (outLeft (table.direction q) i.cross (b,i.tag)) (m i.head)
          (outRight (table.direction q) i.cross (b,i.tag)) false false)
  | left (q q' : H) (hd : table.direction q = .left) (h : table.boundary q = some q') :
      Rule table m [.enter,.head (m q)] [.enter,.head (m q')]
  | right (q q' : H) (hd : table.direction q = .right) (h : table.boundary q = some q') :
      Rule table m [.head (m q),.leave] [.head (m q'),.leave]

end Literal
end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Compiler.Word

section
open _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.Path
variable {S Γ Q : Type*}

abbrev Cell (S Γ : Type*) := Base S × Tag S Γ
abbrev Head (S Q : Type*) := Surface.Head (Control.Head S Q)
abbrev Letter (S Γ Q : Type*) := Path.Letter (Cell S Γ) (Head S Q)
abbrev Sector (S Γ Q : Type*) := Path.Sector (Cell S Γ) (Head S Q)

def encode (v : Surface.Sector S Γ (Control.Head S Q)) : List (Letter S Γ Q) :=
  Path.encode (Scan.literal id v)

/-- The actual source equations, separate from the exceptional accepting exit
    for which only the *complete* raw-run evaluator is invariant. -/
inductive Ordinary (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
    [DecidableEq S] [DecidableEq Γ] : List (Letter S Γ Q) → List (Letter S Γ Q) → Prop
  | raw (a : S) : Ordinary A M
      [.left (Validator.cell A.blank (.anchor a)),.head .raw]
      [.head .raw,.right (Validator.cell A.blank (.anchor a))]
  | merge : Ordinary A M [.head .raw,.leave,.enter,.head .raw]
      [.left (Validator.cell A.blank .cutC),.head .pending,.right (Validator.cell A.blank .cutD)]
  | quota : Ordinary A M
      [.left (Validator.cell A.blank .workspace),.head .pending,.right (Validator.cell A.blank .cutD)]
      [.head .pending,.right (Validator.cell A.blank .cutD)]
  | entry : Ordinary A M [.head .pending,.right (Validator.cell A.blank .cutD)]
      [.head (.internal .initial),.right (Validator.cell A.blank .cutD)]
  | internal {u v} (h : Scan.Literal.Rule (Control.table A M) Surface.Head.internal u v) :
      Ordinary A M u v
  | clean (c : Cell S Γ) : Ordinary A M [.left c,.head .cleanup]
      ([.head .cleanup]++((Cleanup.emit c).toList.map (Cleanup.letter A.blank)).map .right)
  | finish : Ordinary A M [.enter,.head .cleanup] [.enter,.head .raw]

inductive Rule (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
    [DecidableEq S] [DecidableEq Γ] : List (Letter S Γ Q) → List (Letter S Γ Q) → Prop
  | zero {u v} (h : Path.ZeroStep u v) : Rule A M u v
  | ordinary {u v} (h : Ordinary A M u v) : Rule A M u v
  | exit : Rule A M [.head (.internal (.machine .ok)),.leave] [.head .cleanup,.leave]

variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ]

variable [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
  [LinearOrder (Control.Sector S Γ Q)]

def sectorPreprocess (v : Sector S Γ Q) : List (Sector S Γ Q) :=
  (Surface.preprocess A M (Scan.unliteral v)).map (Scan.literal id)

def preprocess (w : List (Letter S Γ Q)) : List (List (Letter S Γ Q)) :=
  Path.prepare (sectorPreprocess A M) w

@[simp] theorem sectorPreprocess_literal (v : Surface.Sector S Γ (Control.Head S Q)) :
    sectorPreprocess A M (Scan.literal id v) = (Surface.preprocess A M v).map (Scan.literal id) := by
  simp [sectorPreprocess]

end

section
open Relation
variable {S Γ Q : Type*}

def gradeCell (c : Cell S Γ) : ℕ := Cleanup.grade c.1
def grade (w : List (Letter S Γ Q)) : ℕ := Path.grade gradeCell w
def chunksGrade (ws : List (List (Letter S Γ Q))) : ℕ := (ws.map grade).sum

@[simp] theorem grade_encode (v : Surface.Sector S Γ (Control.Head S Q)) :
    grade (encode v) = Surface.grade v := by
  rcases v with ⟨l,q,r,lb,rb⟩
  simp [grade,encode,Scan.literal,Path.encode,Path.grade_headed,Surface.grade,
    Cleanup.cellsGrade,Function.comp_def]
  rfl

@[simp] theorem grade_append (u v : List (Letter S Γ Q)) : grade (u++v) = grade u+grade v :=
  Path.grade_append _ _ _

@[simp] theorem chunksGrade_append (u v : List (List (Letter S Γ Q))) :
    chunksGrade (u++v) = chunksGrade u+chunksGrade v := by simp [chunksGrade]

@[simp] theorem chunksGrade_flatten (ws : List (List (Letter S Γ Q))) :
    grade ws.flatten = chunksGrade ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [List.flatten_cons,chunksGrade,ih]

@[simp] theorem grade_raw (b : Γ) (w : List S) :
    grade (encode (Surface.raw (H := Control.Head S Q) b w)) = w.length + 3 := by
  rw [grade_encode]
  simp [Surface.raw,Surface.grade,Cleanup.cellsGrade,Validator.cell,Cleanup.grade,List.map_map,
    Function.comp_def]
  omega

end

variable {S Γ Q : Type*} (blank : Γ)

def raw (w : List S) : List (Letter S Γ Q) := encode (Surface.raw blank w)

/-- Candidate extraction followed by a literal check recognizes *only* full,
    clean raw sectors. Dirty tags or absent boundaries cannot silently pass. -/
def rawLetters (w : List (Letter S Γ Q)) : List S := w.filterMap fun a =>
  match a with
  | .right (.anchor s,_) => some s
  | _ => none

@[simp] theorem rawLetters_raw (w : List S) : rawLetters (raw (Q := Q) blank w) = w := by
  simp [raw,encode,Scan.literal,Path.encode,Surface.raw,Path.headed,rawLetters,
    List.filterMap_append,List.filterMap_map,Validator.cell,Function.comp_def]

variable [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]

def readRaw (w : List (Letter S Γ Q)) : Option (List S) :=
  let x := rawLetters w
  if raw blank x = w then some x else none

@[simp] theorem readRaw_raw (w : List S) : readRaw blank (raw (Q := Q) blank w) = some w := by
  simp [readRaw]

 theorem readRaw_sound {w : List (Letter S Γ Q)} {x : List S} (h : readRaw blank w = some x) :
    raw blank x = w := by
  dsimp only [readRaw] at h
  split at h
  · cases h; assumption
  · cases h

abbrev Item (S Γ Q : Type*) := RawRuns.Item (List (Letter S Γ Q)) S

def classify (w : List (Letter S Γ Q)) : Item S Γ Q :=
  match readRaw blank w with
  | some x => .inr x
  | none => .inl w

def realize : Item S Γ Q → List (Letter S Γ Q)
  | .inl w => w
  | .inr x => raw blank x

@[simp] theorem classify_raw (w : List S) : classify blank (raw (Q := Q) blank w) = .inr w := by
  simp [classify]

@[simp] theorem realize_classify (w : List (Letter S Γ Q)) : realize blank (classify blank w) = w := by
  unfold classify
  cases he : readRaw blank w with
  | none => rfl
  | some x => exact readRaw_sound blank he

@[simp] theorem itemGrade_classify (w : List (Letter S Γ Q)) :
    RawRuns.itemGrade grade (classify blank w) = grade w := by
  unfold classify
  cases he : readRaw blank w with
  | none => rfl
  | some x => rw [←readRaw_sound blank he]; exact (grade_raw blank x).symm

omit [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] in
@[simp] theorem grade_realize (w : Item S Γ Q) :
    grade (realize blank w) = RawRuns.itemGrade grade w := by
  cases w with
  | inl w => rfl
  | inr x => exact grade_raw blank x

@[simp] theorem classify_grade (ws : List (List (Letter S Γ Q))) :
    RawRuns.grade grade (ws.map (classify blank)) = chunksGrade ws := by
  simp only [RawRuns.grade,List.map_map,Function.comp_def,itemGrade_classify,chunksGrade]

omit [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] in
@[simp] theorem realizeList_grade (ws : List (Item S Γ Q)) :
    grade (ws.flatMap (realize blank)) = RawRuns.grade grade ws := by
  rw [List.flatMap_def,chunksGrade_flatten]
  simp only [chunksGrade,List.map_map,Function.comp_def,grade_realize,RawRuns.grade]

end FiniteAlgebraicEnvelopes.Compiler.Word

namespace FiniteAlgebraicEnvelopes.Compiler.Word
open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

/-- The source algorithm, with the partial call separated as f. Its actual
    computable domain/realization is established at the program boundary. -/
def normal (f : List S → List S) (w : List (Letter S Γ Q)) : List (Letter S Γ Q) :=
  if Path.shape w = .zero then [.zero] else
    (RawRuns.source f ((preprocess A M w).map (classify A.blank))).flatMap (realize A.blank)

@[simp] theorem preprocess_raw (w : List S) : preprocess A M (raw (Q := Q) A.blank w) =
    [raw A.blank w] := by
  unfold preprocess raw encode Path.prepare Path.encode
  rw [Path.cuts_headed]
  change Path.prepareChunks (sectorPreprocess A M) [Path.encode (Scan.literal id (Surface.raw A.blank w))] = _
  rw [Path.prepareChunks_singleton,sectorPreprocess_literal]
  rfl

@[simp] theorem normal_raw (f : List S → List S) (w : List S) :
    normal A M f (raw (Q := Q) A.blank w) = raw A.blank w := by
  have hn : Path.shape (raw (Q := Q) A.blank w) ≠ .zero := by
    simp [raw,encode,Path.encode]
  simp [normal,hn,RawRuns.source,RawRuns.splitRun,realize]

end FiniteAlgebraicEnvelopes.Compiler.Word

namespace FiniteAlgebraicEnvelopes.Compiler.Word

section
open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

/-- The compiler's finite monoid presentation is formed from the literal rule
    table; neither a normalizer nor program totality enters its definition. -/
abbrev Rel (u v : FreeMonoid (Letter S Γ Q)) : Prop := Rule A M u v
abbrev Presentation := PresentedMonoid (Rel A M)
def present (w : List (Letter S Γ Q)) : Presentation A M := PresentedMonoid.mk (Rel A M) w

end

open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

@[simp] theorem normal_nil (f : List S → List S) : normal A M f [] = [] := by
  simp [normal,preprocess,Path.prepare,Path.prepareChunks,RawRuns.source]

@[simp] theorem normal_omega (f : List S → List S) :
    normal A M f [.zero] = [.zero] := by simp [normal,Path.typeOf]

@[simp] theorem preprocess_raw_pair (u v : List S) :
    preprocess A M (raw (Q := Q) A.blank u ++ raw A.blank v) =
      [raw A.blank u,raw A.blank v] := by
  have hr (w : List S) : raw (Q := Q) A.blank w =
      [.enter,.head .raw] ++ (w.map (Validator.cell A.blank ∘ Base.anchor)).map Path.Letter.right ++ [.leave] := by
    simp [raw,encode,Surface.raw,Scan.literal,Path.encode,Path.headed]
  have hc : Path.cuts (raw (Q := Q) A.blank u ++ raw A.blank v) =
      Path.cuts (raw A.blank u) ++ Path.cuts (raw A.blank v) := by
    rw [hr u]
    rw [List.append_assoc, List.singleton_append, Path.cuts_append_leave]
  unfold preprocess Path.prepare
  rw [hc]
  change Path.prepareChunks (sectorPreprocess A M)
    (Path.cuts (raw A.blank u) ++ Path.cuts (raw A.blank v)) = _
  rw [Path.prepareChunks_append]
  exact congrArg₂ List.append (preprocess_raw A M u) (preprocess_raw A M v)

end FiniteAlgebraicEnvelopes.Compiler.Word

/- The actual partial evaluator is a finite plan followed by partial calls.
   Its definition has no budget and does not totalize an undefined program. -/
namespace FiniteAlgebraicEnvelopes.Compiler.RawRuns
variable {C S : Type*}

/-- A nonraw literal sector, an unchanged singleton raw sector, or a genuine
    program call on an entire maximal raw run. -/
inductive Action (C S : Type*)
  | keep (c : C)
  | raw (w : List S)
  | call (w : List S)
  deriving DecidableEq

def plan : List (Item C S) → List (Action C S)
  | [] => []
  | .inl c::w => .keep c::plan w
  | .inr x::w =>
    let p := splitRun w
    let z := match p.1 with
      | [] => Action.raw x
      | _::_ => Action.call (x++p.1.flatten)
    z :: plan p.2
termination_by w => w.length
decreasing_by
  · simp_wf
  · have := splitRun_length w
    simp_wf
    omega

def Action.total (f : List S → List S) : Action C S → Item C S
  | .keep c => .inl c
  | .raw x => .inr x
  | .call x => .inr (f x)

def Action.partial (f : List S → Part (List S)) : Action C S → Part (Item C S)
  | .keep c => Part.some (.inl c)
  | .raw x => Part.some (.inr x)
  | .call x => (f x).map Sum.inr

def execute (f : List S → Part (List S)) : List (Action C S) → Part (List (Item C S))
  | [] => Part.some []
  | a::w => (a.partial f).bind fun b => (execute f w).map (b::·)

def partialSource (f : List S → Part (List S)) (w : List (Item C S)) : Part (List (Item C S)) :=
  execute f (plan w)

end FiniteAlgebraicEnvelopes.Compiler.RawRuns

namespace FiniteAlgebraicEnvelopes.Compiler.Word
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

/-- The manuscript's partial normalizer. It is defined even for a divergent
    program; no arbitrary value is inserted for an undefined call. -/
def partialNormal (f : List S → Part (List S)) (w : List (Letter S Γ Q)) : Part (List (Letter S Γ Q)) :=
  if Path.shape w = .zero then Part.some [.zero] else
    (RawRuns.partialSource f ((preprocess A M w).map (classify A.blank))).map
      (List.flatMap (realize A.blank))

end FiniteAlgebraicEnvelopes.Compiler.Word

namespace FiniteAlgebraicEnvelopes.Compiler.Word
open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

/-- The finite-machine adapter has to *prove* this execution specification for
    any supplied partial-recursive program. It is not an extra main hypothesis. -/
def Realizes (f : List S → Part (List S)) : Prop :=
  ∀ w out, out ∈ f w ↔ ∃ c,
    ReflTransGen (Simulator.UnboundedStep A M) (Simulator.initialTape A M w) c ∧
    Simulator.Halted A M c ∧ Simulator.Returns A c out

end FiniteAlgebraicEnvelopes.Compiler.Word

end OAI
end

section
-- module Solutions.OAIFAE.Effectivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Primitive recursive encodings and effective finite compiler data.
-/

/- Effectivity dependencies for the source compiler and its bounded recursive
   evaluator. No partial function is completed by classical choice. -/
namespace FiniteAlgebraicEnvelopes.Effect
variable {α β : Type*}

def traverse (f : α →. β) : List α →. List β
  | [] => Part.some []
  | a::l => (f a).bind fun b => (traverse f l).map (b::·)

end FiniteAlgebraicEnvelopes.Effect

namespace FiniteAlgebraicEnvelopes.Effect.Graph
open Relation
variable {α : Type*} [DecidableEq α]

def expand (r : α → α → Bool) (u s : List α) : List α :=
  s ++ u.filter (fun b => s.any (fun a => r a b || r b a))

def search (r : α → α → Bool) (u : List α) (a : α) : ℕ → List α
  | 0 => [a]
  | n+1 => expand r u (search r u a n)

omit [DecidableEq α] in
@[simp] theorem mem_expand (r : α → α → Bool) (u s : List α) (b : α) :
    b ∈ expand r u s ↔ b ∈ s ∨ b ∈ u ∧ ∃ a ∈ s, r a b = true ∨ r b a = true := by
  simp [expand]

omit [DecidableEq α] in
theorem search_sub (r : α → α → Bool) {u : List α} {a : α} (ha : a ∈ u) (n : ℕ) :
    ∀ b ∈ search r u a n, b ∈ u := by
  induction n with
  | zero => simpa [search] using ha
  | succ n ih =>
    intro b hb
    rcases (mem_expand r u _ b).mp hb with hb | ⟨hb,_⟩
    · exact ih b hb
    · exact hb

theorem search_mono (r : α → α → Bool) (u : List α) (a : α) :
    Monotone (fun n => (search r u a n).toFinset) := by
  apply monotone_nat_of_le_succ
  intro n b hb
  simp only [List.mem_toFinset] at hb ⊢
  exact (mem_expand r u _ b).mpr (Or.inl hb)

theorem expand_ext (r : α → α → Bool) (u : List α) {s t : List α}
    (h : s.toFinset = t.toFinset) : (expand r u s).toFinset = (expand r u t).toFinset := by
  have hh : ∀ a, a ∈ s ↔ a ∈ t := fun a => by
    simpa only [List.mem_toFinset] using Finset.ext_iff.mp h a
  ext b
  simp only [List.mem_toFinset,mem_expand,hh]

theorem search_stable (r : α → α → Bool) {u : List α} {a : α} (ha : a ∈ u) :
    (search r u a (u.length+1)).toFinset = (search r u a u.length).toFinset := by
  have hs : ∀ n, (search r u a n).toFinset.card ≤ u.length := by
    intro n
    exact (Finset.card_le_card (fun b hb => by
      simp only [List.mem_toFinset] at hb ⊢
      exact search_sub r ha n b hb)).trans (List.toFinset_card_le u)
  have hm : Monotone (fun n => (search r u a n).toFinset.card) :=
    fun _ _ h => Finset.card_le_card (search_mono r u a h)
  have hstep : ∀ n, (search r u a n).toFinset.card = (search r u a (n+1)).toFinset.card →
      (search r u a (n+1)).toFinset.card = (search r u a (n+2)).toFinset.card := by
    intro n hn
    have he := Finset.eq_of_subset_of_card_le (search_mono r u a (Nat.le_succ n)) hn.ge
    exact congrArg Finset.card (expand_ext r u he)
  exact (Finset.eq_of_subset_of_card_le
    (search_mono r u a (Nat.le_succ u.length))
    (Nat.stabilises_of_monotone hm hs hstep (Nat.le_succ _)).le).symm

def component (r : α → α → Bool) (u : List α) (a : α) : List α := search r u a u.length

omit [DecidableEq α] in
theorem mem_search_connected (r : α → α → Bool) (u : List α) (a : α) (n : ℕ)
    {b : α} (hb : b ∈ search r u a n) : EqvGen (fun a b => r a b = true) a b := by
  induction n generalizing b with
  | zero =>
    have : b = a := by simpa [search] using hb
    subst b
    exact .refl _
  | succ n ih =>
    rcases (mem_expand r u _ b).mp hb with hb | ⟨_,c,hc,hcb | hbc⟩
    · exact ih hb
    · exact .trans _ _ _ (ih hc) (.rel _ _ hcb)
    · exact .trans _ _ _ (ih hc) (.symm _ _ (.rel _ _ hbc))

theorem mem_component_iff (r : α → α → Bool) {u : List α} {a b : α} (ha : a ∈ u)
    (hclosed : ∀ c ∈ u, ∀ d, (r c d = true ∨ r d c = true) → d ∈ u) :
    b ∈ component r u a ↔ EqvGen (fun a b => r a b = true) a b := by
  constructor
  · exact mem_search_connected r u a u.length
  · intro h
    have hh : ReflTransGen (SymmGen (fun a b => r a b = true)) a b := by
      rw [EqvGen.reflTransGen_symmGen]; exact h
    clear h
    induction hh with
    | refl =>
      have := search_mono r u a (Nat.zero_le u.length)
        (show a ∈ (search r u a 0).toFinset by simp [search])
      simpa only [List.mem_toFinset,component] using this
    | @tail c d hp hs ih =>
      have hc := search_sub r ha u.length c ih
      have hed : r c d = true ∨ r d c = true := hs
      have hd := hclosed c hc d hed
      have hm := (mem_expand r u _ d).mpr (Or.inr ⟨hd,c,ih,hed⟩)
      have he : d ∈ (search r u a (u.length+1)).toFinset := List.mem_toFinset.mpr hm
      rw [search_stable r ha] at he
      exact List.mem_toFinset.mp he

end FiniteAlgebraicEnvelopes.Effect.Graph

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
open FiniteAlgebraicEnvelopes.Effect.Graph
variable {H B T : Type*}

def Sector.code : Sector H B T ≃ List (B×T) × (H × (List (B×T) × (Bool × Bool))) where
  toFun v := (v.left,v.head,v.right,v.leftBoundary,v.rightBoundary)
  invFun p := ⟨p.1,p.2.1,p.2.2.1,p.2.2.2.1,p.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instPrimcodableSector [Primcodable H] [Primcodable B] [Primcodable T] : Primcodable (Sector H B T) :=
  Primcodable.ofEquiv _ Sector.code

variable [Primcodable H] [Primcodable B] [Primcodable T]

variable [Fintype H] [Fintype B] [Fintype T]

-- All finite choices below are literal lists. No finset or finite-connectivity
-- decision is used as a computability oracle.
noncomputable def finiteList (α : Type*) [Fintype α] : List α := (Finset.univ : Finset α).toList

@[simp] theorem mem_finiteList {α : Type*} [Fintype α] (a : α) : a ∈ finiteList α := by
  classical
  simp [finiteList]

noncomputable def wordList (α : Type*) [Fintype α] : ℕ → List (List α)
  | 0 => [[]]
  | n+1 => [] :: (finiteList α).flatMap (fun a => (wordList α n).map (a::·))

@[simp] theorem mem_wordList {α : Type*} [Fintype α] (n : ℕ) (w : List α) :
    w ∈ wordList α n ↔ w.length ≤ n := by
  induction n generalizing w with
  | zero => simp [wordList]
  | succ n ih =>
    cases w with
    | nil => simp [wordList]
    | cons a w => simp [wordList,ih]

noncomputable def sectorList (n : ℕ) : List (Sector H B T) :=
  (finiteList H).flatMap fun q =>
    (wordList (B×T) n).flatMap fun l =>
      (wordList (B×T) n).flatMap fun r =>
        [⟨l,q,r,false,false⟩,⟨l,q,r,false,true⟩,⟨l,q,r,true,false⟩,⟨l,q,r,true,true⟩]

omit [Primcodable H] [Primcodable B] [Primcodable T] in
@[simp] theorem mem_sectorList (n : ℕ) (v : Sector H B T) :
    v ∈ sectorList n ↔ v.left.length ≤ n ∧ v.right.length ≤ n := by
  rcases v with ⟨l,q,r,a,b⟩
  cases a <;> cases b <;> simp [sectorList,Sector.mk.injEq]

variable [DecidableEq H] [DecidableEq B] [DecidableEq T]

noncomputable def universeList (v : Sector H B T) : List (Sector H B T) :=
  (sectorList (v.left.length+v.right.length)).filter fun w => baseSkeleton w = baseSkeleton v

omit [Primcodable H] [Primcodable B] [Primcodable T] [DecidableEq H] [DecidableEq T] in
@[simp] theorem mem_universeList (v w : Sector H B T) :
    w ∈ universeList v ↔ baseSkeleton w = baseSkeleton v := by
  simp only [universeList,List.mem_filter,mem_sectorList,decide_eq_true_eq,and_iff_right_iff_imp]
  intro h
  have hl := skeleton_length h
  constructor <;> omega

end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
open Relation
open FiniteAlgebraicEnvelopes.Effect.Graph
variable {H B T : Type*}

variable [Primcodable H] [Primcodable B] [Primcodable T]

variable [Fintype H] [Fintype B] [Fintype T] (table : Table H B T)

variable [DecidableEq H] [DecidableEq B] [DecidableEq T]

def stepBool (v w : Sector H B T) : Bool := decide (step table v = some w)

noncomputable def componentList (v : Sector H B T) : List (Sector H B T) :=
  FiniteAlgebraicEnvelopes.Effect.Graph.component (stepBool table) (universeList v) v

omit [Primcodable H] [Primcodable B] [Primcodable T] in
@[simp] theorem mem_componentList (v w : Sector H B T) :
    w ∈ componentList table v ↔ EqvGen (Step table) v w := by
  change w ∈ componentList table v ↔ EqvGen (fun a b => step table a = some b) v w
  simpa only [componentList,stepBool,decide_eq_true_eq,Step] using
    (FiniteAlgebraicEnvelopes.Effect.Graph.mem_component_iff (stepBool table)
      (b := w) ((mem_universeList v v).mpr rfl) (by
        intro c hc d hd
        rw [mem_universeList] at hc ⊢
        rcases hd with hd | hd
        · exact (step_skeleton table ((show Step table c d from of_decide_eq_true (p := step table c = some d) hd))).symm.trans hc
        · exact (step_skeleton table ((show Step table d c from of_decide_eq_true (p := step table d = some c) hd))).trans hc))

end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Effect
open FiniteAlgebraicEnvelopes.Effect.Graph
variable {α : Type*} [Primcodable α] [DecidableEq α]

 def priorityList (p q : α → Bool) (s : List α) : List α :=
  if (s.filter p).isEmpty then
    if (s.filter q).isEmpty then s else s.filter q
  else s.filter p

end FiniteAlgebraicEnvelopes.Effect

namespace FiniteAlgebraicEnvelopes.Effect
@[instance_reducible] noncomputable def finitePrimcodable (α : Type*) [Fintype α] : Primcodable α :=
  Primcodable.ofEquiv (Fin (Fintype.card α)) (Fintype.equivFin α)

@[instance_reducible] def codeOrder (α : Type*) [Primcodable α] : LinearOrder α :=
  LinearOrder.lift' Encodable.encode Encodable.encode_injective

end FiniteAlgebraicEnvelopes.Effect

namespace FiniteAlgebraicEnvelopes.Compiler
open FiniteAlgebraicEnvelopes.Effect
noncomputable instance instPrimcodableBaseOfFintype {S : Type*} [Fintype S] : Primcodable (Base S) := finitePrimcodable _
noncomputable instance instPrimcodableTagOfFintype {S Γ : Type*} [Fintype S] [Fintype Γ] : Primcodable (Tag S Γ) := finitePrimcodable _
end FiniteAlgebraicEnvelopes.Compiler

namespace FiniteAlgebraicEnvelopes.Compiler.Simulator
open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ) (M : Machine Q Γ)

theorem semanticStep_lift_head (q : Q) (l : List (Tag S Γ)) (t : Tag S Γ) (r : List (Tag S Γ))
    {d : SemanticTape Γ Q} (h : SemanticStep M (interpret A (⟨q,l,t::r⟩ : Tape)) d) :
    ∃ e, TapeStep M (⟨q,l,t::r⟩ : Tape) e ∧ interpret A e = d := by
  unfold SemanticStep semanticStep interpret at h
  simp only [List.map_cons,Stream'.appendStream',Stream'.head_cons] at h
  cases hc : M.transition q t.work with
  | none => simp only [hc,Option.map_none] at h; cases h
  | some cmd =>
    simp only [hc,Option.map_some,Option.some.injEq] at h
    subst d
    rcases cmd with ⟨q',a,mv⟩
    cases mv with
    | stay => exact ⟨_,.stay hc rfl,rfl⟩
    | right => exact ⟨_,.right hc rfl,rfl⟩
    | left =>
      cases l with
      | nil => exact ⟨_,.leftEdge hc rfl,rfl⟩
      | cons b l => exact ⟨_,.left hc rfl,rfl⟩

/-- Infinite semantic transitions can always be realized by materializing at
most one implicit blank. This is a completeness statement, not an assumption
on accepting trajectories. -/
theorem semanticStep_lift {c : Tape (S := S) (Γ := Γ) (Q := Q)}
    {d : SemanticTape Γ Q} (h : SemanticStep M (interpret A c) d) :
    ∃ e, UnboundedStep A M c e ∧ interpret A e = d := by
  rcases c with ⟨q,l,r⟩
  cases r with
  | nil =>
    have hh : SemanticStep M (interpret A (⟨q,l,[clean A.blank]⟩ : Tape)) d := by
      have hp := interpret_pad A (⟨q,l,[]⟩ : Tape) 1
      simpa only [pad,List.nil_append,List.replicate_one] using hp ▸ h
    obtain ⟨e,he,hde⟩ := semanticStep_lift_head A M q l (clean A.blank) [] hh
    exact ⟨e,.extend he,hde⟩
  | cons t r =>
    obtain ⟨e,he,hde⟩ := semanticStep_lift_head A M q l t r h
    exact ⟨e,.within he,hde⟩

 theorem semanticRun_lift {c : Tape (S := S) (Γ := Γ) (Q := Q)}
    {d : SemanticTape Γ Q} (h : ReflTransGen (SemanticStep M) (interpret A c) d) :
    ∃ e, ReflTransGen (UnboundedStep A M) c e ∧ interpret A e = d := by
  induction h with
  | refl => exact ⟨c,.refl,rfl⟩
  | tail _ hs ih =>
    rcases ih with ⟨e,he,rfl⟩
    rcases semanticStep_lift A M hs with ⟨f,hf,rfl⟩
    exact ⟨f,he.tail hf,rfl⟩

 theorem semantic_halted_iff (c : Tape (S := S) (Γ := Γ) (Q := Q)) :
    semanticStep M (interpret A c) = none ↔ Halted A M c := by
  rcases c with ⟨q,l,r⟩
  cases r <;> simp [Halted,interpret,semanticStep,Stream'.appendStream',clean,
    Stream'.head,Stream'.get,Stream'.const,Stream'.cons]

end FiniteAlgebraicEnvelopes.Compiler.Simulator

end OAI
end

section
-- module Solutions.OAIFAE.Rewriting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Newman normalization, block coding, canonical representatives, and static tests.
-/

/- Rewriting layer for the self-reference construction.  No assumptions on
   either main theorem are introduced here. -/
namespace FiniteAlgebraicEnvelopes.Bootstrap

section
open Relation

variable {S : Type*}

/-- One directed rule in an arbitrary two-sided context. -/
inductive Step (rules : List (List S × List S)) : List S → List S → Prop
  | apply {u v} (h : (u,v) ∈ rules) (x y) : Step rules (x++u++y) (x++v++y)

abbrev Steps (rules : List (List S × List S)) := ReflTransGen (Step rules)

theorem step_context {rules : List (List S × List S)} {u v : List S}
    (h : Step rules u v) (x y : List S) : Step rules (x++u++y) (x++v++y) := by
  cases h with
  | apply h a b => simpa only [List.append_assoc] using Step.apply h (x++a) (b++y)

theorem steps_context {rules : List (List S × List S)} {u v : List S}
    (h : Steps rules u v) (x y : List S) : Steps rules (x++u++y) (x++v++y) :=
  h.lift (fun w => x++w++y) (fun _ _ h => step_context h x y)

variable [DecidableEq S]

/-- The fixed choice of rule at the leftmost position, then table order. -/
def rootNext (w : List S) : List (List S × List S) → Option (List S)
  | [] => none
  | (u,v)::rs => if w.take u.length = u then some (v ++ w.drop u.length) else rootNext w rs

def next (rules : List (List S × List S)) : List S → Option (List S)
  | [] => rootNext [] rules
  | a::w => (rootNext (a::w) rules).or ((next rules w).map (a::·))

end

/- The marker/constant-width code used in the self-reference construction.
   A block has its marker only at the start, not at the end. -/

structure BlockCode (A S : Type*) where
  marker : S
  tail : A → List S
  width : ℕ
  tail_length : ∀ a, (tail a).length = width
  tail_avoids : ∀ a, marker ∉ tail a
  injective : Function.Injective tail

namespace BlockCode
variable {A S : Type*} (C : BlockCode A S)

def block (a : A) : List S := C.marker :: C.tail a

def encode (w : List A) : List S := w.flatMap C.block

@[simp] theorem block_length (a : A) : (C.block a).length = C.width+1 := by
  simp [block,C.tail_length]

@[simp] theorem encode_nil : C.encode [] = [] := rfl
@[simp] theorem encode_cons (a : A) (w : List A) : C.encode (a::w) = C.block a ++ C.encode w := rfl
@[simp] theorem encode_append (u v : List A) : C.encode (u++v) = C.encode u ++ C.encode v := by
  simp [encode]
@[simp] theorem encode_length (w : List A) : (C.encode w).length = (C.width+1)*w.length := by
  induction w with
  | nil => simp
  | cons a w ih => simp [ih,Nat.mul_add,Nat.add_comm]

 theorem block_injective : Function.Injective C.block := by
  intro a b h
  exact C.injective (List.cons.inj h).2

 theorem prefix_decode {u v : List A} {y : List S} (h : C.encode v = C.encode u ++ y) :
    ∃ w, v = u++w ∧ y = C.encode w := by
  induction u generalizing v with
  | nil => exact ⟨v,rfl,h.symm⟩
  | cons a u ih =>
    cases v with
    | nil => simp [block] at h
    | cons b v =>
      simp only [encode_cons,List.append_assoc] at h
      obtain ⟨hab,ht⟩ := List.append_inj h (by simp)
      have : b=a := C.block_injective hab
      subst b
      obtain ⟨w,rfl,rfl⟩ := ih ht
      exact ⟨w,rfl,rfl⟩

 theorem encode_injective : Function.Injective C.encode := by
  intro u v h
  obtain ⟨w,hu,hw⟩ := C.prefix_decode (y := []) (by simpa using h)
  have he := congrArg List.length hw
  have : w=[] := by simpa using he
  simpa [this] using hu

 theorem split_past_avoiding {b : S} {t z x y : List S} (ht : b ∉ t)
    (h : t++z = x++b::y) : ∃ x', x=t++x' ∧ z=x'++b::y := by
  induction t generalizing x with
  | nil => exact ⟨x,rfl,h⟩
  | cons a t ih =>
    cases x with
    | nil =>
      have ha : a=b := (List.cons.inj h).1
      exact False.elim (ht (by simp [ha]))
    | cons c x =>
      obtain ⟨rfl,htail⟩ := List.cons.inj h
      obtain ⟨x',rfl,hz⟩ := ih (fun hh => ht (List.mem_cons_of_mem _ hh)) htail
      exact ⟨x',rfl,hz⟩

/-- Every marker inside an encoded word starts a complete generator block. -/
 theorem marker_alignment {v : List A} {x y : List S}
    (h : C.encode v = x ++ C.marker :: y) :
    ∃ u a w, v=u++a::w ∧ x=C.encode u ∧ y=C.tail a ++ C.encode w := by
  induction v generalizing x with
  | nil => simp at h
  | cons a v ih =>
    cases x with
    | nil =>
      have hy : C.tail a ++ C.encode v = y := (List.cons.inj h).2
      exact ⟨[],a,v,rfl,rfl,hy.symm⟩
    | cons b x =>
      obtain ⟨hb,hv⟩ := List.cons.inj h
      subst b
      obtain ⟨x',rfl,hv'⟩ := split_past_avoiding (C.tail_avoids a) hv
      obtain ⟨u,b,w,rfl,hx,hy⟩ := ih hv'
      exact ⟨a::u,b,w,rfl,by simp [block,hx],hy⟩

/-- A nonempty code occurrence in a code sequence has both boundaries aligned. -/
 theorem occurrence_decode {v u : List A} (hu : u≠[]) {x y : List S}
    (h : C.encode v = x++C.encode u++y) :
    ∃ p q, v=p++u++q ∧ x=C.encode p ∧ y=C.encode q := by
  cases u with
  | nil => contradiction
  | cons a u =>
    have hm : C.encode v = x++C.marker::(C.tail a++C.encode u++y) := by
      simpa [block,List.append_assoc] using h
    obtain ⟨p,b,w,hv,rfl,hy⟩ := C.marker_alignment hm
    have hh : C.encode (b::w) = C.encode (a::u)++y := by
      apply List.append_cancel_left (as := C.encode p)
      simpa only [hv,encode_append,List.append_assoc] using h
    obtain ⟨q,hq,hqy⟩ := C.prefix_decode hh
    refine ⟨p,q,?_,rfl,hqy⟩
    rw [hv,hq,List.append_assoc]

/-- Overlapping code left sides have a union which is itself a full code;
    the common part is an entire (nonempty) code suffix/prefix. -/
 theorem overlap_decode {u v : List A} {p middle q : List S}
    (hm : middle≠[]) (h₁ : C.encode u = p++middle)
    (h₂ : C.encode v = middle++q) :
    ∃ a b c, u=a++b ∧ v=b++c ∧ p=C.encode a ∧
      middle=C.encode b ∧ q=C.encode c := by
  cases v with
  | nil => simp at h₂; exact False.elim (hm h₂.1)
  | cons v vs =>
    cases middle with
    | nil => contradiction
    | cons m middle =>
      have hmark : m=C.marker := (List.cons.inj h₂).1.symm
      subst m
      obtain ⟨a,b,bs,hu,hp,ht⟩ := C.marker_alignment h₁
      have hs : C.marker::middle = C.encode (b::bs) := by simp [block,ht]
      have hv : C.encode (v::vs) = C.encode (b::bs)++q := by simpa [hs] using h₂
      obtain ⟨c,hv,hq⟩ := C.prefix_decode hv
      exact ⟨a,b::bs,c,hu,hv,hp,hs,hq⟩

end BlockCode

namespace Canonical
variable {A Q : Type*} {r : A → A → Prop} (wf : WellFounded r)
variable (q : List A → Q)

/-- Exactly the bounded tested-class candidate set in the self-reference construction. -/
def candidates (w : List A) : Set (List A) := {v | v.length ≤ w.length ∧ q v=q w}

noncomputable def least (w : List A) : List A :=
  (List.Shortlex.wf wf).min (candidates q w) ⟨w,le_rfl,rfl⟩

theorem least_mem (w : List A) : least wf q w ∈ candidates q w :=
  (List.Shortlex.wf wf).min_mem _ _

theorem least_length (w : List A) : (least wf q w).length ≤ w.length :=
  (least_mem wf q w).1

theorem least_class (w : List A) : q (least wf q w)=q w := (least_mem wf q w).2

theorem least_min {w v : List A} (hv : v.length≤w.length) (hq : q v=q w) :
    ¬ List.Shortlex r v (least wf q w) :=
  (List.Shortlex.wf wf).not_lt_min (candidates q w) ⟨hv,hq⟩

theorem least_global_min {w v : List A} (hq : q v=q w) : ¬ List.Shortlex r v (least wf q w) := by
  intro hd
  have hlen : v.length≤w.length := by
    have hm := least_length wf q w
    have he := List.shortlex_def.mp hd
    omega
  exact least_min wf q hlen hq hd

/-- Changing the finite search bound to that of another same-class candidate
    cannot change the result, including when the result is empty. -/
theorem least_congr [Std.Trichotomous r] {u v : List A} (hq : q u=q v) :
    least wf q u=least wf q v := by
  apply Std.Trichotomous.trichotomous (r := List.Shortlex r)
  · exact least_global_min wf q ((least_class wf q u).trans hq)
  · exact least_global_min wf q ((least_class wf q v).trans hq.symm)

theorem least_nil : least wf q []=[] := by
  have hh := least_length wf q []
  simpa using hh

end Canonical

open Relation
variable {S : Type*}

theorem step_mono {rs rt : List (List S × List S)} (h : ∀ p∈rs, p∈rt)
    {u v : List S} (huv : Step rs u v) : Step rt u v := by
  cases huv with
  | apply hp x y => exact .apply (h _ hp) x y

theorem steps_mono {rs rt : List (List S × List S)} (h : ∀ p∈rs, p∈rt)
    {u v : List S} (huv : Steps rs u v) : Steps rt u v := by
  induction huv with
  | refl => exact .refl
  | tail hh hs ih => exact .tail ih (step_mono h hs)

/-- The absorbing equations, stated as finite-table membership, not as an
    additional computation oracle. -/
def Absorbs (rs : List (List S × List S)) (z : S) : Prop :=
  ∀ a, ([z,a],[z])∈rs ∧ ([a,z],[z])∈rs

theorem absorbs_context {rs : List (List S × List S)} {z : S} (hz : Absorbs rs z)
    (x y : List S) : Steps rs (x++[z]++y) [z] := by
  have hr : ∀ y : List S, Steps rs ([z]++y) [z] := by
    intro y
    induction y with
    | nil => exact .refl
    | cons a y ih =>
      have hs : Steps rs ([z]++a::y) ([z]++y) :=
        .single (by simpa using Step.apply (hz a).1 [] y)
      exact hs.trans ih
  induction x with
  | nil => exact hr y
  | cons a x ih =>
    have hh := steps_context ih [a] []
    have hs : Step rs [a,z] [z] := by simpa using Step.apply (hz a).2 [] []
    have hh' : Steps rs (a::x++[z]++y) [a,z] := by simpa using hh
    exact hh'.trans (.single hs)

namespace Static
variable {A Q : Type*} [Fintype A] [DecidableEq S]
variable {r : A → A → Prop}
variable (C : BlockCode A S) (wf : WellFounded r) (q : List A → Option Q) (z : S)

noncomputable def letters (A : Type*) [Fintype A] : List A := (Finset.univ : Finset A).toList
noncomputable def words (A : Type*) [Fintype A] : ℕ → List (List A)
  | 0 => [[]]
  | n+1 => [] :: (letters A).flatMap (fun a => (words A n).map (a::·))

@[simp] theorem mem_words (n : ℕ) (w : List A) : w∈words A n ↔ w.length≤n := by
  classical
  induction n generalizing w with
  | zero => simp [words]
  | succ n ih =>
    cases w with
    | nil => simp [words]
    | cons a w => simp [words,letters,ih]

noncomputable def output (v : List A) : List S :=
  if q v=none then [z] else C.encode (Canonical.least wf q v)

noncomputable def table (n : ℕ) : List (List S × List S) :=
  ((words A n).filter fun v => v≠[] ∧ output C wf q z v≠C.encode v).map
    (fun v => (C.encode v,output C wf q z v))

theorem mem_table {n : ℕ} {a b : List S} : (a,b)∈table C wf q z n ↔
    ∃ v, v.length≤n ∧ v≠[] ∧ output C wf q z v≠C.encode v ∧
      a=C.encode v ∧ b=output C wf q z v := by
  simp only [table,List.mem_map,List.mem_filter,mem_words,decide_eq_true_eq,Prod.mk.injEq]
  aesop

omit [Fintype A] [DecidableEq S] in
theorem output_congr [Std.Trichotomous r] {u v : List A} (hq : q u=q v) :
    output C wf q z u=output C wf q z v := by
  simp only [output,hq,Canonical.least_congr wf q hq]

omit [Fintype A] [DecidableEq S] in
theorem output_nil (hzero : q []≠none) : output C wf q z []=[] := by
  simp [output,hzero,Canonical.least_nil]

theorem whole_steps (hzero : q []≠none) {n : ℕ} {v : List A} (hv : v.length≤n) :
    Steps (table C wf q z n) (C.encode v) (output C wf q z v) := by
  by_cases hn : v=[]
  · subst v
    rw [C.encode_nil,output_nil C wf q z hzero]
  by_cases he : output C wf q z v=C.encode v
  · rw [he]
  · exact .single (by simpa using Step.apply ((mem_table C wf q z).mpr ⟨v,hv,hn,he,rfl,rfl⟩) [] [])

/-- Precisely the bounded contextual tests used at source bootstrap:273–297. -/
def Contextual (n : ℕ) : Prop :=
  ∀ a b u v : List A, (a++u++b).length≤n → (a++v++b).length≤n → q u=q v →
    q (a++u++b)=q (a++v++b)

def ZeroIdeal (n : ℕ) : Prop :=
  ∀ a b u : List A, (a++u++b).length≤n → q u=none → q (a++u++b)=none

variable [Std.Trichotomous r]

/-- A single contextual static replacement inside a full code reduces to the
    same literal whole-code output. Both endpoint bounds are proved separately. -/
theorem branch_normalizes {n : ℕ} {rs : List (List S × List S)}
    (hzero : q []≠none) (hz : Absorbs rs z)
    (ht : ∀ p∈table C wf q z n, p∈rs)
    (hc : Contextual q n) (hi : ZeroIdeal q n)
    {v : List A} {a b : List A} (hlen : (a++v++b).length≤n) :
    Steps rs (C.encode a++output C wf q z v++C.encode b) (output C wf q z (a++v++b)) := by
  by_cases hq : q v=none
  · have hzq := hi a b v hlen hq
    simp only [output,ite_eq_left hq,ite_eq_left hzq]
    exact absorbs_context hz _ _
  · let v' := Canonical.least wf q v
    have hlen' : (a++v'++b).length≤n := by
      have hh := Canonical.least_length wf q v
      simp only [List.length_append] at hlen ⊢
      dsimp only [v']
      omega
    have hqq : q (a++v'++b)=q (a++v++b) :=
      hc a b v' v hlen' hlen (Canonical.least_class wf q v)
    have hh := steps_mono ht (whole_steps C wf q z hzero hlen')
    rw [output_congr C wf q z hqq] at hh
    simpa only [output,ite_eq_right hq,BlockCode.encode_append,v'] using hh

/-- Contained code occurrences are aligned, so the preceding branch analysis
    applies at exactly the source code boundaries. -/
theorem occurrence_normalizes {n : ℕ} {rs : List (List S × List S)}
    (hzero : q []≠none) (hz : Absorbs rs z)
    (ht : ∀ p∈table C wf q z n, p∈rs)
    (hc : Contextual q n) (hi : ZeroIdeal q n)
    {w v : List A} {x y : List S} (hw : w.length≤n) (hv : v≠[])
    (he : C.encode w=x++C.encode v++y) :
    Steps rs (x++output C wf q z v++y) (output C wf q z w) := by
  obtain ⟨a,b,rfl,rfl,rfl⟩ := C.occurrence_decode hv he
  exact branch_normalizes C wf q z hzero hz ht hc hi hw

/-- Static containment criticals join at the canonical output of the union. -/
theorem critical_containment {n k l : ℕ} {rs : List (List S × List S)}
    (hzero : q []≠none) (hz : Absorbs rs z)
    (ht : ∀ p∈table C wf q z n, p∈rs)
    (hc : Contextual q n) (hi : ZeroIdeal q n)
    {u u' v v' x y : List S}
    (hu : (u,u')∈table C wf q z k) (hv : (v,v')∈table C wf q z l)
    (he : u=x++v++y) (hlen : u.length≤(C.width+1)*n) :
    Join (Steps rs) u' (x++v'++y) := by
  obtain ⟨a,_,_,_,rfl,rfl⟩ := (mem_table C wf q z).mp hu
  obtain ⟨b,_,hbn,_,rfl,rfl⟩ := (mem_table C wf q z).mp hv
  have ha : a.length≤n := by
    rw [C.encode_length] at hlen
    exact Nat.le_of_mul_le_mul_left hlen (by omega)
  exact ⟨output C wf q z a,.refl,
    occurrence_normalizes C wf q z hzero hz ht hc hi ha hbn he⟩

/-- Static boundary criticals have a full, aligned code union, and both
    contextual branches reach its same literal output. -/
theorem critical_overlap {n k l : ℕ} {rs : List (List S × List S)}
    (hzero : q []≠none) (hz : Absorbs rs z)
    (ht : ∀ p∈table C wf q z n, p∈rs)
    (hc : Contextual q n) (hi : ZeroIdeal q n)
    {u u' v v' x middle y : List S}
    (hu : (u,u')∈table C wf q z k) (hv : (v,v')∈table C wf q z l)
    (hm : middle≠[]) (he : u=x++middle) (hf : v=middle++y)
    (hlen : (x++middle++y).length≤(C.width+1)*n) :
    Join (Steps rs) (u'++y) (x++v') := by
  obtain ⟨a,_,_,_,rfl,rfl⟩ := (mem_table C wf q z).mp hu
  obtain ⟨b,_,_,_,rfl,rfl⟩ := (mem_table C wf q z).mp hv
  obtain ⟨c,d,e,rfl,rfl,rfl,rfl,rfl⟩ := C.overlap_decode hm he hf
  have hlen' : (c++d++e).length≤n := by
    have hh : (C.encode (c++d++e)).length≤(C.width+1)*n := by
      simpa only [BlockCode.encode_append] using hlen
    rw [C.encode_length] at hh
    exact Nat.le_of_mul_le_mul_left hh (by omega)
  refine ⟨output C wf q z (c++d++e),?_,?_⟩
  · simpa only [List.nil_append,BlockCode.encode_nil] using
      branch_normalizes C wf q z hzero hz ht hc hi (a := []) (v := c++d) (b := e)
        (by simpa only [List.nil_append] using hlen')
  · simpa only [List.append_nil,BlockCode.encode_nil,List.append_assoc] using
      branch_normalizes C wf q z hzero hz ht hc hi (a := c) (v := d++e) (b := [])
        (by simpa only [List.append_nil,List.append_assoc] using hlen')

end Static
end FiniteAlgebraicEnvelopes.Bootstrap

end OAI
end

section
-- module Solutions.OAIFAE.Selectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Literal selector envelopes, rewrite saturation, and zero recognition.
-/

/- Literal selector envelopes from the self-reference construction. -/
namespace FiniteAlgebraicEnvelopes.Bootstrap

section
namespace Envelopes
variable {S : Type*}

def frame (d l r h : S) (N : ℕ) (w : List S) : List S :=
  d :: (List.replicate N l ++ w ++ List.replicate N r ++ [h])

@[simp] theorem length_frame (d l r h : S) (N : ℕ) (w : List S) :
    (frame d l r h N w).length = 2*N+2+w.length := by
  simp [frame]; omega

@[simp] theorem reverse_frame (d l r h : S) (N : ℕ) (w : List S) :
    (frame d l r h N w).reverse = frame h r l d N w.reverse := by
  simp [frame,List.append_assoc]

end Envelopes

open Relation
variable {S : Type*} {rs : List (List S × List S)}

/-- The two critical configurations, checked only inside the current length ball. -/
def Critical (rs : List (List S × List S)) (n : ℕ) : Prop :=
  (∀ u u' v v', (u,u')∈rs → (v,v')∈rs → ∀ a b, u=a++v++b → u.length≤n →
    Join (Steps rs) u' (a++v'++b)) ∧
  (∀ u u' v v', (u,u')∈rs → (v,v')∈rs → ∀ p m q, m≠[] →
    u=p++m → v=m++q → (p++m++q).length≤n →
    Join (Steps rs) (u'++q) (p++v'))

end

section
open Relation Envelopes
namespace Selectors
variable {S : Type*}

structure Markers (S : Type*) where
  zero : S
  d : S
  l : S
  r : S
  h : S
  distinct : List.Pairwise (· ≠ ·) [zero,d,l,r,h]

namespace Markers
variable (a : Markers S)

abbrev wrap (N : ℕ) (w : List S) : List S := frame a.d a.l a.r a.h N w

end Markers

variable [DecidableEq S] (a : Markers S)

/-- Literal selector rules, with the first member sent to the empty word. -/
def rules (N : ℕ) (ws : List (List S)) : List (List S × List S) :=
  ws.map fun w => (a.wrap N w,if ws.head?=some w then [] else [a.zero])

end Selectors
end

section
open Relation
namespace Selectors
variable {S : Type*} [DecidableEq S] (a : Markers S)

/-- A potential tuple and its envelope size, independent of all class tests. -/
structure Stage (S : Type*) where
  size : ℕ
  bodies : List (List S)

variable {a}

def allowed (rs : List (List S × List S)) (s : Stage S) : Bool :=
  s.bodies.all (fun w => (next rs w).isNone)

def choose (rs : List (List S × List S)) (s : Stage S) (n : ℕ) : List (List S × List S) :=
  if s.size ≤ n ∧ allowed rs s then rs++rules a s.size s.bodies else rs

def process (base : List (List S × List S)) (stages : ℕ → Stage S) (n : ℕ) : ℕ → List (List S × List S)
  | 0 => base
  | j+1 => choose (a:=a) (process base stages n j) (stages j) n

end Selectors
end

namespace Canonical
variable {A Q : Type*} {r : A → A → Prop} [DecidableEq Q] [DecidableRel (List.Shortlex r)]

def pickStep (q : Q) (best : List A) (p : List A × Q) : List A :=
  if p.2=q ∧ List.Shortlex r p.1 best then p.1 else best

end Canonical

end FiniteAlgebraicEnvelopes.Bootstrap

namespace FiniteAlgebraicEnvelopes.Bootstrap.Selectors

section
variable {S : Type*} [DecidableEq S] [Primcodable S]

def maxLength (ws : List (List S)) : ℕ := (ws.map List.length).foldr max 0

def tuples (z : S) (i : ℕ) : List (List S) :=
  let ws := (Encodable.decode (α:=List (List S)) i).getD [[]]
  if ws≠[] ∧ ws.Nodup ∧ (∀ w∈ws,z∉w) then ws else [[]]

/-- Each new size is past the entire preceding potential envelope, not merely
    past those actually selected. The index and current body bounds are included. -/
def sizes (z : S) : ℕ → ℕ
  | 0 => maxLength (tuples z 0)+1
  | i+1 => max (max (i+2) (maxLength (tuples z (i+1))+1))
      (2 * sizes z i+3+maxLength (tuples z i))

def stages (z : S) (i : ℕ) : Stage S := ⟨sizes z i,tuples z i⟩

end

end FiniteAlgebraicEnvelopes.Bootstrap.Selectors

end OAI
end

section
-- module Solutions.OAIFAE.Quotients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Canonical compiler quotients and effective tested classes for word problems.
-/

namespace FiniteAlgebraicEnvelopes.Bootstrap
open Relation
namespace BlockCode
variable {A B S : Type*} (C : BlockCode A S)

def Alphabet : Set S := {s | ∃ a, s ∈ C.block a}

theorem mem_alphabet {w : List A} {s : S} (h : s ∈ C.encode w) : s ∈ C.Alphabet := by
  obtain ⟨a,_,ha⟩ := List.mem_flatMap.mp h
  exact ⟨a,ha⟩

theorem encode_ne_nil {w : List A} (h : w ≠ []) : C.encode w ≠ [] := by
  intro he
  exact h (C.encode_injective (he.trans C.encode_nil.symm))

theorem disjoint_infix (D : BlockCode B S) (hd : Disjoint C.Alphabet D.Alphabet)
    {w : List A} {v : List B} (hv : v ≠ []) (hi : D.encode v <:+: C.encode w) : False := by
  obtain ⟨s,hs⟩ := List.exists_mem_of_ne_nil _ (D.encode_ne_nil hv)
  exact Set.disjoint_left.mp hd (C.mem_alphabet (hi.subset hs)) (D.mem_alphabet hs)

theorem disjoint_overlap (D : BlockCode B S) (hd : Disjoint C.Alphabet D.Alphabet)
    {u : List A} {v : List B} {p m q : List S} (hm : m ≠ [])
    (hu : C.encode u=p++m) (hv : D.encode v=m++q) : False := by
  obtain ⟨s,hs⟩ := List.exists_mem_of_ne_nil _ hm
  exact Set.disjoint_left.mp hd (C.mem_alphabet (hu ▸ List.mem_append_right p hs))
    (D.mem_alphabet (hv ▸ List.mem_append_left q hs))
end BlockCode

namespace Static
variable {S A Q : Type*} [Fintype A] [DecidableEq A] [DecidableEq S] [DecidableEq Q]
variable {r : A → A → Prop} [Std.Trichotomous r]
variable (C : BlockCode A S) (wf : WellFounded r) (q : List A → Option Q) (z : S)

omit [DecidableEq A] [DecidableEq Q] [Std.Trichotomous r] in
theorem table_support {n : ℕ} {p : List S × List S} (hp : p ∈ table C wf q z n) :
    p.1 ≠ [] ∧ ∀ s ∈ p.1,s ∈ C.Alphabet := by
  rcases p with ⟨u,v⟩
  obtain ⟨w,_,hn,_,rfl,rfl⟩ := (mem_table C wf q z).mp hp
  exact ⟨C.encode_ne_nil hn,fun _ hs => C.mem_alphabet hs⟩

omit [DecidableEq A] [DecidableEq Q] in
theorem critical_containment_bound {n : ℕ} {rs : List (List S × List S)}
    (hzero : q [] ≠ none) (hz : Absorbs rs z)
    (ht : ∀ p ∈ table C wf q z (n/(C.width+1)), p ∈ rs)
    (hc : Contextual q (n/(C.width+1))) (hi : ZeroIdeal q (n/(C.width+1)))
    {u u' v v' x y : List S}
    (hu : (u,u') ∈ table C wf q z (n/(C.width+1)))
    (hv : (v,v') ∈ table C wf q z (n/(C.width+1)))
    (he : u=x++v++y) (hlen : u.length ≤ n) : Join (Steps rs) u' (x++v'++y) := by
  apply critical_containment C wf q z hzero hz ht hc hi hu hv he
  obtain ⟨w,hw,_,_,rfl,_⟩ := (mem_table C wf q z).mp hu
  simpa only [C.encode_length] using Nat.mul_le_mul_left (C.width+1) hw

omit [DecidableEq A] [DecidableEq Q] in
theorem critical_overlap_bound {n : ℕ} {rs : List (List S × List S)}
    (hzero : q [] ≠ none) (hz : Absorbs rs z)
    (ht : ∀ p ∈ table C wf q z (n/(C.width+1)), p ∈ rs)
    (hc : Contextual q (n/(C.width+1))) (hi : ZeroIdeal q (n/(C.width+1)))
    {u u' v v' p m t : List S}
    (hu : (u,u') ∈ table C wf q z (n/(C.width+1)))
    (hv : (v,v') ∈ table C wf q z (n/(C.width+1)))
    (hm : m ≠ []) (he : u=p++m) (hf : v=m++t) (hlen : (p++m++t).length ≤ n) :
    Join (Steps rs) (u'++t) (p++v') := by
  apply critical_overlap C wf q z hzero hz ht hc hi hu hv hm he hf
  obtain ⟨a,_,_,_,rfl,_⟩ := (mem_table C wf q z).mp hu
  obtain ⟨b,_,_,_,rfl,_⟩ := (mem_table C wf q z).mp hv
  obtain ⟨c,d,e,rfl,rfl,rfl,rfl,rfl⟩ := C.overlap_decode hm he hf
  have hh : (C.width+1)*(c++d++e).length ≤ n := by
    simpa only [← C.encode_append,C.encode_length] using hlen
  have hdiv : (c++d++e).length ≤ n/(C.width+1) :=
    (Nat.le_div_iff_mul_le (Nat.succ_pos _)).mpr (by simpa [Nat.mul_comm] using hh)
  simpa only [← C.encode_append,C.encode_length] using Nat.mul_le_mul_left (C.width+1) hdiv
end Static

namespace Base
variable {S A B Q R : Type*} [Fintype S] [Fintype A] [Fintype B]
  [DecidableEq S] [DecidableEq A] [DecidableEq B] [DecidableEq Q] [DecidableEq R]
variable {r : A → A → Prop} {s : B → B → Prop} [Std.Trichotomous r] [Std.Trichotomous s]
variable (C : BlockCode A S) (D : BlockCode B S) (wf : WellFounded r) (wg : WellFounded s)
  (f : List A → Option Q) (g : List B → Option R) (z : S)

noncomputable def absorption : List (List S × List S) :=
  (Static.letters S).flatMap fun a => [([z,a],[z]),([a,z],[z])]

omit [DecidableEq S] in
@[simp] theorem mem_absorption {u v : List S} : (u,v) ∈ absorption z ↔
    ∃ a, (u=[z,a] ∨ u=[a,z]) ∧ v=[z] := by
  simp only [absorption,Static.letters,List.mem_flatMap,Finset.mem_toList,Finset.mem_univ,true_and,
    List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq]
  aesop

noncomputable def table (n : ℕ) : List (List S × List S) :=
  absorption z ++ Static.table C wf f z (n/(C.width+1)) ++ Static.table D wg g z (n/(D.width+1))

omit [DecidableEq A] [DecidableEq B] [DecidableEq Q] [DecidableEq R]
  [Std.Trichotomous r] [Std.Trichotomous s] in
theorem mem_table {n : ℕ} {p : List S × List S} : p ∈ table C D wf wg f g z n ↔
    p ∈ absorption z ∨ p ∈ Static.table C wf f z (n/(C.width+1)) ∨
      p ∈ Static.table D wg g z (n/(D.width+1)) := by
  simp only [table,List.mem_append,or_assoc]

omit [DecidableEq A] [DecidableEq B] [DecidableEq Q] [DecidableEq R]
  [Std.Trichotomous r] [Std.Trichotomous s] in
theorem absorbs (n : ℕ) : Absorbs (table C D wf wg f g z n) z := by
  intro a
  constructor <;> apply (mem_table C D wf wg f g z).mpr <;> apply Or.inl <;>
    apply (mem_absorption z).mpr
  · exact ⟨a,Or.inl rfl,rfl⟩
  · exact ⟨a,Or.inr rfl,rfl⟩

omit [DecidableEq A] [DecidableEq B] [DecidableEq Q] [DecidableEq R]
  [Std.Trichotomous r] [Std.Trichotomous s] in
theorem preserves_zero (hC : z ∉ C.Alphabet) (hD : z ∉ D.Alphabet) (n : ℕ) :
    ∀ p ∈ table C D wf wg f g z n, z ∈ p.1 → z ∈ p.2 := by
  intro ⟨u,v⟩ hp hu
  rcases (mem_table C D wf wg f g z).mp hp with hp | hp | hp
  · obtain ⟨a,_,rfl⟩ := (mem_absorption z).mp hp
    simp
  · exact False.elim (hC ((Static.table_support C wf f z hp).2 z hu))
  · exact False.elim (hD ((Static.table_support D wg g z hp).2 z hu))

end Base

open Relation
variable {S : Type*} [DecidableEq S] {r : S → S → Prop}

/-- A successful table has all the finite mathematical certificates needed by
    the bounded Newman argument. No totality of the program is part of this. -/
def GoodTable (T : ℕ → Part (List (List S × List S))) (n : ℕ) : Prop :=
  ∃ rs ∈ T n, (∀ p ∈ rs,List.Shortlex r p.2 p.1) ∧ Critical rs n

end FiniteAlgebraicEnvelopes.Bootstrap

namespace FiniteAlgebraicEnvelopes
namespace Effect
variable {X A B : Type*}

theorem traverse_comp (f : A → Part B) (g : X → A) (l : List X) :
    traverse (fun x => f (g x)) l=traverse f (l.map g) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [traverse,List.map_cons,ih]

end Effect

namespace Bootstrap
namespace Search
variable {A S Q : Type*} [DecidableEq A] [DecidableEq S] [DecidableEq Q]
variable {r : A → A → Prop} [DecidableRel (List.Shortlex r)]

noncomputable def value (f : List A → Part (Option Q)) (w : List A) : Option Q := by
  classical
  exact if h : (f w).Dom then (f w).get h else none

end Search

end Bootstrap
end FiniteAlgebraicEnvelopes

namespace FiniteAlgebraicEnvelopes
namespace Compiler.Word
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

omit [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
  [LinearOrder (Control.Sector S Γ Q)] in
 theorem present_surjective : Function.Surjective (present A M) := by
  intro x
  obtain ⟨w,rfl⟩ := PresentedMonoid.surjective_mk x
  exact ⟨w.toList,rfl⟩

omit [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
  [LinearOrder (Control.Sector S Γ Q)] in
 theorem present_zero_mul (w : List (Letter S Γ Q)) :
    present A M [.zero] * present A M w=present A M [.zero] := by
  induction w with
  | nil => exact mul_one _
  | cons c w ih =>
    have hh : present A M [.zero,c]=present A M [.zero] :=
      PresentedMonoid.mk_eq_mk_of_rel (.zero (.pair _ _ (by simp [Path.typeOf])))
    have hp : present A M (c::w)=present A M [c]*present A M w := rfl
    rw [hp,←mul_assoc]
    change present A M [.zero,c]*present A M w=_
    rw [hh,ih]

omit [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
  [LinearOrder (Control.Sector S Γ Q)] in
 theorem present_mul_zero (w : List (Letter S Γ Q)) :
    present A M w * present A M [.zero]=present A M [.zero] := by
  induction w with
  | nil => exact one_mul _
  | cons c w ih =>
    have hh : present A M [c,.zero]=present A M [.zero] :=
      PresentedMonoid.mk_eq_mk_of_rel (.zero (.pair _ _ (by simp [Path.typeOf])))
    have hp : present A M (c::w)=present A M [c]*present A M w := rfl
    rw [hp,mul_assoc,ih]
    exact hh

@[instance_reducible]
noncomputable def monoidWithZero : MonoidWithZero (Presentation A M) where
  __ := (inferInstance : Monoid (Presentation A M))
  zero := present A M [.zero]
  zero_mul x := by
    obtain ⟨w,rfl⟩ := present_surjective A M x
    exact present_zero_mul A M w
  mul_zero x := by
    obtain ⟨w,rfl⟩ := present_surjective A M x
    exact present_mul_zero A M w

end Compiler.Word

end FiniteAlgebraicEnvelopes

namespace FiniteAlgebraicEnvelopes.Bootstrap.Uniform
variable {A B : Type*}

/-- The finite word ball over an explicit finite support. -/
def words (letters : List A) : ℕ → List (List A)
  | 0 => [[]]
  | n+1 => [] :: letters.flatMap (fun a => (words letters n).map (a::·))

@[simp] theorem mem_words (letters : List A) (n : ℕ) (w : List A) :
    w∈words letters n ↔ w.length≤n ∧ ∀ a∈w,a∈letters := by
  induction n generalizing w with
  | zero => cases w <;> simp [words]
  | succ n ih =>
    cases w with
    | nil => simp [words]
    | cons a w =>
      rw [words,List.mem_cons]
      constructor
      · rintro (he | h)
        · cases he
        · obtain ⟨b,hb,h⟩ := List.mem_flatMap.mp h
          obtain ⟨v,hv,he⟩ := List.mem_map.mp h
          obtain ⟨rfl,rfl⟩ := List.cons.inj he
          obtain ⟨hlen,hs⟩ := (ih v).mp hv
          exact ⟨by simpa using Nat.succ_le_succ hlen,by simpa [List.mem_cons] using And.intro hb hs⟩
      · rintro ⟨hlen,hs⟩
        right
        refine List.mem_flatMap.mpr ⟨a,hs a List.mem_cons_self,List.mem_map.mpr ⟨w,?_,rfl⟩⟩
        exact (ih w).mpr ⟨by simpa using hlen,fun b hb => hs b (List.mem_cons_of_mem _ hb)⟩

theorem words_map (i : A → B) (ls : List A) (n : ℕ) :
    words (ls.map i) n = (words ls n).map (List.map i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [words,ih,List.map_cons,List.map_nil,List.flatMap_map,List.map_flatMap,List.map_map,Function.comp_def]

end FiniteAlgebraicEnvelopes.Bootstrap.Uniform

namespace FiniteAlgebraicEnvelopes.WordProblem

def letterRel (n : ℕ) (a b : Fin n × Bool) : Prop := Encodable.encode a<Encodable.encode b

 theorem letterRel_wf (n : ℕ) : WellFounded (letterRel n) := InvImage.wf Encodable.encode Nat.lt_wfRel.wf

variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
noncomputable def testedClass : Word n → Word n :=
  Bootstrap.Canonical.least (letterRel_wf n) (evalWord s)

end FiniteAlgebraicEnvelopes.WordProblem

end OAI
end

section
-- module Solutions.OAIFAE.PartialAffine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Primitive recursive dyadic partial affine monoid and its six-letter presentation.
-/

namespace FiniteAlgebraicEnvelopes.PartialAffine
/-- An unreduced dyadic numerator difference and a power-of-two denominator.
    Computation never relies on Mathlib's noncomputable coding of `ℚ`. -/
abbrev Dyad := ℕ × ℕ × ℕ
namespace Dyad
def val (a : Dyad) : ℚ := ((a.1:ℚ)-a.2.1)/2^a.2.2
def zero : Dyad := (0,0,0)
def one : Dyad := (1,0,0)
def neg (a : Dyad) : Dyad := (a.2.1,a.1,a.2.2)
def add (a b : Dyad) : Dyad :=
  (a.1*2^b.2.2+b.1*2^a.2.2,a.2.1*2^b.2.2+b.2.1*2^a.2.2,a.2.2+b.2.2)
def mul (a b : Dyad) : Dyad :=
  (a.1*b.1+a.2.1*b.2.1,a.1*b.2.1+a.2.1*b.1,a.2.2+b.2.2)
def le (a b : Dyad) : Bool :=
  decide (a.1*2^b.2.2+b.2.1*2^a.2.2 ≤ b.1*2^a.2.2+a.2.1*2^b.2.2)
def eq (a b : Dyad) : Bool := le a b && le b a
def max (a b : Dyad) : Dyad := if le a b then b else a

@[simp] theorem val_zero : val zero=0 := by norm_num [val,zero]
@[simp] theorem val_one : val one=1 := by norm_num [val,one]
@[simp] theorem val_neg (a : Dyad) : val (neg a) = -val a := by simp [val,neg]; ring
@[simp] theorem val_add (a b : Dyad) : val (add a b)=val a+val b := by
  simp only [val,add,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,pow_add]
  field_simp
  ring
@[simp] theorem val_mul (a b : Dyad) : val (mul a b)=val a*val b := by
  simp only [val,mul,Nat.cast_add,Nat.cast_mul,pow_add]
  field_simp
  ring
@[simp] theorem le_correct (a b : Dyad) : le a b=true ↔ val a≤val b := by
  rw [val,val,div_le_div_iff₀ (by positivity) (by positivity)]
  simp only [le,decide_eq_true_eq]
  rw [← Nat.cast_le (α:=ℚ)]
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  constructor <;> intro h <;> nlinarith
@[simp] theorem eq_correct (a b : Dyad) : eq a b=true ↔ val a=val b := by
  rw [eq, Bool.and_eq_true, le_correct, le_correct]
  exact le_antisymm_iff.symm
@[simp] theorem val_max (a b : Dyad) : val (max a b)=Max.max (val a) (val b) := by
  unfold max
  split
  next h => exact (max_eq_right ((le_correct a b).mp h)).symm
  next h => exact (max_eq_left (le_of_not_ge fun hh => h ((le_correct a b).mpr hh))).symm

end Dyad

abbrev Slope := ℕ × ℕ
namespace Slope
def dyad (a : Slope) : Dyad := (2^a.1,0,a.2)
def val (a : Slope) : ℚ := Dyad.val (dyad a)
def mul (a b : Slope) : Slope := (a.1+b.1,a.2+b.2)
def inv (a : Slope) : Slope := (a.2,a.1)
@[simp] theorem val_eq (a : Slope) : val a=2^a.1/2^a.2 := by simp [val,dyad,Dyad.val]
@[simp] theorem val_mul (a b : Slope) : val (mul a b)=val a*val b := by
  simp only [val_eq,mul,pow_add]
  ring
@[simp] theorem val_inv (a : Slope) : val (inv a)=(val a)⁻¹ := by simp [val_eq,inv]
end Slope

namespace Bound
def dom : Option ℚ → ℚ → Prop
  | none,_ => True
  | some r,x => r≤x
instance instDecidableDom (r : Option ℚ) (x : ℚ) : Decidable (dom r x) := by cases r <;> unfold dom <;> infer_instance

end Bound

abbrev Data := Slope × Dyad × Option Dyad
namespace Data
def act (a : Data) (x : ℚ) : Option ℚ :=
  if Bound.dom (a.2.2.map Dyad.val) x then some (Slope.val a.1*x+Dyad.val a.2.1) else none

def represent (a : Data) : Function.End (Option ℚ) := fun o => o.bind (act a)

end Data

/-- The fixed six-letter alphabet in the algebra construction, in the order
    `u,v,u⁻¹,v⁻¹,e₀,e₁`. -/
abbrev Letter := Fin 6

def generator (i : Letter) : Data :=
  if i=0 then ((0,1),Dyad.zero,none)
  else if i=1 then ((0,1),(1,0,1),none)
  else if i=2 then ((1,0),Dyad.zero,none)
  else if i=3 then ((1,0),(0,1,0),none)
  else if i=4 then ((0,0),Dyad.zero,some Dyad.zero)
  else ((0,0),Dyad.zero,some Dyad.one)

def value (w : List Letter) : Function.End (Option ℚ) := (w.map (Data.represent ∘ generator)).prod

/-- A computable, uniquely comparable coding of the tested class for the
    auxiliary monoid. No rational-number coding is used as an oracle. -/
noncomputable def testedClass : List Letter → List Letter :=
  Bootstrap.Canonical.least (r:=fun a b : Letter => a<b) wellFounded_lt value

end FiniteAlgebraicEnvelopes.PartialAffine

end OAI
end

section
-- module Solutions.OAIFAE.Machines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Stack, binary, TM2, and TM0 realizations of partial recursive programs.
-/

namespace FiniteAlgebraicEnvelopes.MachineRealization.StackLift
open Turing Relation
open Turing.PartrecToTM2

 def swap : K' → K'
  | .main => .rev | .rev => .main | .aux => .aux | .stack => .stack
 @[simp] theorem swap_swap (k : K') : swap (swap k) = k := by cases k <;> rfl

 variable {S Λ : Type*}
 abbrev Symbol (S : Type*) := Γ' ⊕ S
 abbrev Store (S : Type*) := Option (Symbol S)
 inductive Label (S Λ : Type*)
  | pre | emit : S → Label S Λ
  | run : Λ → Label S Λ
  | post | reject
  deriving DecidableEq, Fintype

 def proj : Store S → Option Γ'
  | some (.inl a) => some a | _ => none
 def store (v : Option Γ') : Store S := v.map Sum.inl
 @[simp] theorem proj_store (v : Option Γ') : proj (store (S := S) v) = v := by cases v <;> rfl

 def embedStacks (t : K' → List Γ') : K' → List (Symbol S) := fun k => (t (swap k)).map Sum.inl
 @[simp] theorem embedStacks_swap (t : K' → List Γ') (k : K') :
    embedStacks (S := S) t (swap k) = (t k).map Sum.inl := by simp [embedStacks]
 theorem embedStacks_update (t : K' → List Γ') (k : K') (w : List Γ') :
    embedStacks (S := S) (Function.update t k w) =
      Function.update (embedStacks t) (swap k) (w.map Sum.inl) := by
  funext j
  by_cases h : j = swap k
  · subst j; simp
  · have hh : swap j ≠ k := fun e => h (by rw [←e,swap_swap])
    simp [embedStacks,Function.update_of_ne h,Function.update_of_ne hh]

 def stmt : TM2.Stmt (fun _ : K' => Γ') Λ (Option Γ') →
    TM2.Stmt (fun _ : K' => Symbol S) (Label S Λ) (Store S)
  | .push k f q => .push (swap k) (fun v => .inl (f (proj v))) (stmt q)
  | .peek k f q => .peek (swap k) (fun v a => store (f (proj v) (proj a))) (stmt q)
  | .pop k f q => .pop (swap k) (fun v a => store (f (proj v) (proj a))) (stmt q)
  | .load f q => .load (fun v => store (f (proj v))) (stmt q)
  | .branch f p q => .branch (fun v => f (proj v)) (stmt p) (stmt q)
  | .goto f => .goto (fun v => .run (f (proj v)))
  | .halt => .goto (fun _ => .post)

 def cfg (c : TM2.Cfg (fun _ : K' => Γ') Λ (Option Γ')) :
    TM2.Cfg (fun _ : K' => Symbol S) (Label S Λ) (Store S) :=
  ⟨some (c.l.elim .post .run),store c.var,embedStacks c.stk⟩

 theorem stmt_correct (q : TM2.Stmt (fun _ : K' => Γ') Λ (Option Γ'))
    (v : Option Γ') (t : K' → List Γ') :
    TM2.stepAux (stmt (S := S) q) (store v) (embedStacks t) = cfg (TM2.stepAux q v t) := by
  induction q generalizing v t with
  | push k f q ih =>
      simp only [stmt,TM2.stepAux,proj_store,embedStacks_swap]
      rw [←List.map_cons,←embedStacks_update]
      exact ih _ _
  | peek k f q ih =>
      simp only [stmt,TM2.stepAux,proj_store,embedStacks_swap]
      have he : proj (((t k).map Sum.inl).head? : Store S) = (t k).head? := by
        cases t k <;> rfl
      rw [he]; exact ih _ _
  | pop k f q ih =>
      simp only [stmt,TM2.stepAux,proj_store,embedStacks_swap]
      have he : proj (((t k).map Sum.inl).head? : Store S) = (t k).head? := by
        cases t k <;> rfl
      rw [he,←List.map_tail,←embedStacks_update]
      exact ih _ _
  | load f q ih => simpa only [stmt,TM2.stepAux,proj_store] using ih (f v) t
  | branch f p q ihp ihq =>
      cases h : f v <;> simp only [stmt,TM2.stepAux,proj_store,h,Bool.cond_false,Bool.cond_true]
      · exact ihq _ _
      · exact ihp _ _
  | goto f => simp [stmt,TM2.stepAux,cfg]
  | halt => rfl

 variable (M : Λ → TM2.Stmt (fun _ : K' => Γ') Λ (Option Γ'))
  (W : Label S Λ → TM2.Stmt (fun _ : K' => Symbol S) (Label S Λ) (Store S))
  (hW : ∀ l, W (.run l) = stmt (M l))

 include hW
 theorem step_correct (c : TM2.Cfg (fun _ : K' => Γ') Λ (Option Γ'))
    (d : TM2.Cfg (fun _ : K' => Γ') Λ (Option Γ')) (h : d ∈ TM2.step M c) :
    cfg (S := S) d ∈ TM2.step W (cfg c) := by
  rcases c with ⟨l,v,t⟩
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
      simp only [TM2.step,Option.mem_some_iff] at h
      subst d
      simpa only [cfg,Option.elim_some,TM2.step,hW,Option.mem_some_iff] using stmt_correct (M l) v t

 theorem reaches_correct {c d : TM2.Cfg (fun _ : K' => Γ') Λ (Option Γ')}
    (h : TM2.Reaches M c d) : TM2.Reaches W (cfg (S := S) c) (cfg d) := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.tail (step_correct M W hW _ _ h)

 /-- Until the original interpreter halts, the wrapper cannot escape its run
     sector. This is the divergence/soundness half, not only a terminating test. -/
 theorem path_cases {c : TM2.Cfg (fun _ : K' => Γ') Λ (Option Γ')}
    {z : TM2.Cfg (fun _ : K' => Symbol S) (Label S Λ) (Store S)}
    (h : TM2.Reaches W (cfg c) z) :
    (∃ d, TM2.Reaches M c d ∧ z = cfg d) ∨
    (∃ d, TM2.Reaches M c d ∧ d.l = none ∧ TM2.Reaches W (cfg d) z) := by
  induction h with
  | refl => exact Or.inl ⟨c,.refl,rfl⟩
  | @tail z z' _ hs ih =>
      rcases ih with ⟨d,hd,rfl⟩ | ⟨d,hd,hh,hr⟩
      · cases hl : d.l with
        | none => exact Or.inr ⟨d,hd,hl,ReflTransGen.single hs⟩
        | some l =>
            let e := TM2.stepAux (M l) d.var d.stk
            have he : e ∈ TM2.step M d := by
              rcases d with ⟨ld,vd,td⟩
              simp only at hl
              simp [TM2.step,hl,e]
            have hh := step_correct M W hW d e he
            have hz : z' = cfg e := Option.mem_unique hs hh
            exact Or.inl ⟨e,hd.tail he,hz⟩
      · exact Or.inr ⟨d,hd,hh,hr.tail hs⟩

end FiniteAlgebraicEnvelopes.MachineRealization.StackLift

namespace FiniteAlgebraicEnvelopes.MachineRealization.BinaryCode
open Turing Turing.PartrecToTM2

def value : List Γ' → ℕ
  | [] => 0
  | .bit0 :: l => 2 * value l
  | .bit1 :: l => 2 * value l + 1
  | _ :: l => value l

@[simp] theorem value_pos (n : PosNum) : value (trPosNum n) = (n : ℕ) := by
  induction n with
  | one => rfl
  | bit0 n ih => simpa [trPosNum,value,ih] using (show 2 * (n : ℕ) = (n : ℕ) + (n : ℕ) by omega)
  | bit1 n ih => simpa [trPosNum,value,ih] using (show 2 * (n : ℕ) + 1 = (n : ℕ) + (n : ℕ) + 1 by omega)

@[simp] theorem value_num (n : Num) : value (trNum n) = (n : ℕ) := by cases n <;> simp [trNum,value]
@[simp] theorem value_nat (n : ℕ) : value (trNat n) = n := by simp [trNat]

def block (n : ℕ) : List Γ' := trNat n ++ [.cons]

end FiniteAlgebraicEnvelopes.MachineRealization.BinaryCode

namespace FiniteAlgebraicEnvelopes.MachineRealization.RawTM
open Turing Turing.PartrecToTM2 Relation
open StackLift BinaryCode
variable {S Λ : Type*} [DecidableEq S] [Encodable S]

abbrev Stmt (S Λ : Type*) := TM2.Stmt (fun _ : K' => Symbol S) (Label S Λ) (Store S)
abbrev Config (S Λ : Type*) := TM2.Cfg (fun _ : K' => Symbol S) (Label S Λ) (Store S)

def tracks (out : List S) (binary : List Γ') : K' → List (Symbol S)
  | .main => out.map Sum.inr
  | .rev => binary.map Sum.inl
  | .aux | .stack => []

omit [DecidableEq S] [Encodable S] in
@[simp] theorem tracks_main (out : List S) (binary : List Γ') : tracks out binary .main = out.map Sum.inr := rfl
omit [DecidableEq S] [Encodable S] in
@[simp] theorem tracks_rev (out : List S) (binary : List Γ') : tracks out binary .rev = binary.map Sum.inl := rfl
omit [DecidableEq S] [Encodable S] in
 theorem tracks_update_main (out : List S) (binary : List Γ') (out' : List S) :
    Function.update (tracks out binary) .main (out'.map Sum.inr) = tracks out' binary := by
  funext k; cases k <;> simp [tracks]
omit [DecidableEq S] [Encodable S] in
 theorem tracks_update_rev (out : List S) (binary binary' : List Γ') :
    Function.update (tracks out binary) .rev (binary'.map Sum.inl) = tracks out binary' := by
  funext k; cases k <;> simp [tracks]

def postCfg (out : List S) (binary : List Γ') : Config S Λ := ⟨some .post,none,tracks out binary⟩
def reject : Stmt S Λ := .goto (fun _ => .reject)
def finish (pre : List Γ') : Stmt S Λ :=
  match Encodable.decode (α := S) (value pre.reverse - 1) with
  | some s => .push .main (fun _ => .inr s) (.load (fun _ => none) (.goto (fun _ => .post)))
  | none => reject

def decoder : ℕ → List Γ' → Stmt S Λ
  | n, pre => .pop .rev (fun _ a => a)
      (.branch (fun v => decide (StackLift.proj v = some .cons)) (finish pre)
        (match n with
        | 0 => reject
        | n+1 => .branch (fun v => decide (StackLift.proj v = some .bit0)) (decoder n (.bit0::pre))
            (.branch (fun v => decide (StackLift.proj v = some .bit1)) (decoder n (.bit1::pre)) reject)))

omit [DecidableEq S] in
theorem decoder_correct (fuel : ℕ) (pre l : List Γ') (tail : List Γ')
    (out : List S) (s : S) (v : Store S)
    (hlen : l.length ≤ fuel) (hbits : ∀ a ∈ l, natEnd a = false)
    (hdec : Encodable.decode (α := S) (value (pre.reverse ++ l) - 1) = some s) :
    TM2.stepAux (decoder (Λ := Λ) fuel pre) v (tracks out (l ++ .cons :: tail)) =
      postCfg (s::out) tail := by
  induction l generalizing fuel pre v with
  | nil =>
      simp only [List.append_nil] at hdec
      cases fuel <;> simp only [decoder,TM2.stepAux,tracks_rev,List.nil_append,List.map_cons,
        List.head?_cons,StackLift.proj,List.tail_cons,decide_true,Bool.cond_true,finish,hdec]
      all_goals
        rw [tracks_update_rev]
        simp only [tracks_main]
        rw [← List.map_cons,tracks_update_main]
        rfl
  | cons a l ih =>
      cases fuel with
      | zero => simp at hlen
      | succ fuel =>
          have hb := hbits a List.mem_cons_self
          have hb' : ∀ a ∈ l, natEnd a = false := fun a ha => hbits a (List.mem_cons_of_mem _ ha)
          have hl : l.length ≤ fuel := by simpa using hlen
          cases a <;> try cases hb
          · simp only [decoder,TM2.stepAux,tracks_rev,List.cons_append,List.map_cons,
              List.head?_cons,StackLift.proj,List.tail_cons,decide_true,Bool.cond_true]
            rw [tracks_update_rev]
            apply ih fuel (.bit0::pre) _ hl hb'
            simpa [List.reverse_cons,List.append_assoc] using hdec
          · simp only [decoder,TM2.stepAux,tracks_rev,List.cons_append,List.map_cons,
              List.head?_cons,StackLift.proj,List.tail_cons,decide_true,Bool.cond_true]
            rw [tracks_update_rev]
            apply ih fuel (.bit1::pre) _ hl hb'
            simpa [List.reverse_cons,List.append_assoc] using hdec

omit [DecidableEq S] in
theorem decoder_block (fuel : ℕ) (tail : List Γ') (out : List S) (s : S) (v : Store S)
    (h : (trNat (Encodable.encode s + 1)).length ≤ fuel) :
    TM2.stepAux (decoder (Λ := Λ) fuel []) v
      (tracks out (block (Encodable.encode s + 1) ++ tail)) = postCfg (s::out) tail := by
  simp only [block,List.append_assoc,List.singleton_append]
  apply decoder_correct fuel [] _ tail out s v h (trNat_natEnd _)
  simp

def pushList : List Γ' → Stmt S Λ → Stmt S Λ
  | [], q => q
  | a::l,q => pushList l (.push .rev (fun _ => .inl a) q)

omit [DecidableEq S] [Encodable S] in
theorem pushList_correct (l : List Γ') (q : Stmt S Λ) (v : Store S)
    (out : List S) (binary : List Γ') :
    TM2.stepAux (pushList l q) v (tracks out binary) =
      TM2.stepAux q v (tracks out (l ++ binary)) := by
  induction l generalizing q binary with
  | nil => rfl
  | cons a l ih =>
      rw [pushList,ih]
      simp only [TM2.stepAux,tracks_rev]
      rw [←List.map_cons,tracks_update_rev]
      rfl

def machine (B : ℕ) (M : Λ → TM2.Stmt (fun _ : K' => Γ') Λ (Option Γ')) (start : Λ) :
    Label S Λ → Stmt S Λ
  | .pre => .pop .main (fun _ a => a) (.goto (fun v =>
      match v with
      | some (.inr s) => .emit s
      | none => .run start
      | _ => .reject))
  | .emit s => pushList (block (Encodable.encode s + 1))
      (.load (fun _ => none) (.goto (fun _ => .pre)))
  | .run l => StackLift.stmt (M l)
  | .post => .peek .rev (fun _ a => a)
      (.branch (fun v => v.isNone) (.load (fun _ => none) .halt) (decoder B []))
  | .reject => reject

def preCfg (out : List S) (binary : List Γ') : Config S Λ := ⟨some .pre,none,tracks out binary⟩
def haltCfg (out : List S) : Config S Λ := ⟨none,none,tracks out []⟩
def runCfg (start : Λ) (binary : List Γ') : Config S Λ := ⟨some (.run start),none,tracks [] binary⟩

variable (B : ℕ) (M : Λ → TM2.Stmt (fun _ : K' => Γ') Λ (Option Γ')) (start : Λ)

omit [DecidableEq S] in
theorem pre_cons (s : S) (out : List S) (binary : List Γ') :
    TM2.Reaches (machine B M start) (preCfg (s::out) binary)
      (preCfg out (block (Encodable.encode s + 1) ++ binary)) := by
  let mid : Config S Λ := ⟨some (.emit s),some (.inr s),tracks out binary⟩
  apply ReflTransGen.trans (b := mid) (ReflTransGen.single ?_) (ReflTransGen.single ?_)
  · simp only [preCfg,TM2.step,machine,TM2.stepAux,tracks_main,List.map_cons,
      List.head?_cons,List.tail_cons]
    rw [tracks_update_main]
    rfl
  · simp only [mid,TM2.step,machine]
    rw [pushList_correct]
    rfl

omit [DecidableEq S] in
theorem pre_nil (binary : List Γ') :
    TM2.Reaches (machine (S := S) B M start) (preCfg [] binary) (runCfg start binary) := by
  apply ReflTransGen.single
  simp only [preCfg,TM2.step,machine,TM2.stepAux,tracks_main,List.map_nil,
    List.head?_nil,List.tail_nil]
  rw [show ([] : List (Symbol S)) = [].map Sum.inr from rfl,tracks_update_main]
  rfl

def numbers (w : List S) : List ℕ := w.map (fun s => Encodable.encode s + 1)

omit [DecidableEq S] [Encodable S] in
@[simp] theorem trList_append (u v : List ℕ) : trList (u ++ v) = trList u ++ trList v := by
  induction u with
  | nil => rfl
  | cons a u ih => simp [trList,ih,List.append_assoc]

omit [DecidableEq S] in
theorem pre_complete (w : List S) (binary : List Γ') :
    TM2.Reaches (machine B M start) (preCfg w binary)
      (runCfg start (trList (numbers w.reverse) ++ binary)) := by
  induction w generalizing binary with
  | nil => simpa [numbers] using pre_nil (S := S) B M start binary
  | cons s w ih =>
      apply (pre_cons B M start s w binary).trans
      simpa [TM2.Reaches,List.reverse_cons,numbers,List.map_append,trList,block,List.append_assoc] using
        ih (block (Encodable.encode s + 1) ++ binary)

omit [DecidableEq S] in
theorem post_cons (s : S) (w out : List S)
    (hB : (trNat (Encodable.encode s + 1)).length ≤ B) :
    TM2.Reaches (machine B M start) (postCfg out (trList (numbers (s::w))))
      (postCfg (s::out) (trList (numbers w))) := by
  apply ReflTransGen.single
  simp only [postCfg,TM2.step,machine,TM2.stepAux,tracks_rev]
  have hn : (trList (numbers (s::w))).map (Sum.inl : Γ' → Symbol S) ≠ [] := by
    simp [numbers,trList]
  rw [show ((trList (numbers (s::w))).map (Sum.inl : Γ' → Symbol S)).head?.isNone = false from by
    simpa using hn]
  simp only [Bool.cond_false,numbers,List.map_cons,trList]
  have hh := decoder_block (Λ := Λ) B (trList (numbers w)) out s
      (((trList (numbers (s::w))).map Sum.inl).head?) hB
  simpa only [Option.mem_some_iff,block,List.append_assoc,List.singleton_append,numbers,
      List.map_cons,trList,postCfg] using hh

omit [DecidableEq S] in
theorem post_nil (out : List S) :
    TM2.Reaches (machine B M start) (postCfg out []) (haltCfg out) := by
  apply ReflTransGen.single
  rfl

omit [DecidableEq S] in
theorem post_complete (w out : List S)
    (hB : ∀ s ∈ w, (trNat (Encodable.encode s + 1)).length ≤ B) :
    TM2.Reaches (machine B M start) (postCfg out (trList (numbers w))) (haltCfg (w.reverse ++ out)) := by
  induction w generalizing out with
  | nil => simpa [numbers] using post_nil B M start out
  | cons s w ih =>
      apply (post_cons B M start s w out (hB s List.mem_cons_self)).trans
      simpa [TM2.Reaches,List.reverse_cons,List.append_assoc] using
        ih (s::out) (fun a ha => hB a (List.mem_cons_of_mem _ ha))

def baseCfg (l : Option Λ) (binary : List Γ') : TM2.Cfg (fun _ : K' => Γ') Λ (Option Γ') :=
  ⟨l,none,K'.elim binary [] [] []⟩

omit [DecidableEq S] [Encodable S] in
@[simp] theorem lift_base_some (l : Λ) (binary : List Γ') :
    StackLift.cfg (S := S) (baseCfg (some l) binary) = runCfg l binary := by
  simp only [StackLift.cfg,baseCfg,runCfg,Option.elim_some]
  congr 1
  funext k; cases k <;> rfl
omit [DecidableEq S] [Encodable S] in
@[simp] theorem lift_base_none (binary : List Γ') :
    StackLift.cfg (S := S) (baseCfg (Λ := Λ) none binary) = postCfg [] binary := by
  simp only [StackLift.cfg,baseCfg,postCfg,Option.elim_none]
  congr 1
  funext k; cases k <;> rfl

omit [DecidableEq S] in
 theorem eval_run {w : List S} {f : List S →. List S}
    (hB : ∀ s : S, (trNat (Encodable.encode s + 1)).length ≤ B)
    (hM : StateTransition.eval (TM2.step M) (baseCfg (some start) (trList (numbers w))) =
      (f w).map (fun out => baseCfg none (trList (numbers out)))) :
    StateTransition.eval (TM2.step (machine B M start)) (runCfg start (trList (numbers w))) =
      (f w).map (fun out => haltCfg out.reverse) := by
  have complete : ∀ out ∈ f w, haltCfg out.reverse ∈
      StateTransition.eval (TM2.step (machine B M start)) (runCfg start (trList (numbers w))) := by
    intro out hout
    have ht : baseCfg (Λ := Λ) none (trList (numbers out)) ∈
        StateTransition.eval (TM2.step M) (baseCfg (some start) (trList (numbers w))) := by
      rw [hM]; exact Part.mem_map _ hout
    have hh := StackLift.reaches_correct (S := S) M (machine B M start) (fun _ => rfl)
      (StateTransition.mem_eval.mp ht).1
    simp only [lift_base_some,lift_base_none] at hh
    apply StateTransition.mem_eval.mpr
    refine ⟨hh.trans ?_,rfl⟩
    simpa only [TM2.Reaches,List.append_nil] using post_complete B M start out [] (fun s _ => hB s)
  apply Part.ext
  intro z
  rw [Part.mem_map_iff]
  constructor
  · intro hz
    obtain ⟨hr,ht⟩ := StateTransition.mem_eval.mp hz
    rw [←lift_base_some] at hr
    rcases StackLift.path_cases M (machine B M start) (fun _ => rfl) hr with
        ⟨d,hd,rfl⟩ | ⟨d,hd,hhalt,hdz⟩
    · simp [StackLift.cfg,TM2.step] at ht
    · have hmem : d ∈ StateTransition.eval (TM2.step M)
          (baseCfg (some start) (trList (numbers w))) := by
        apply StateTransition.mem_eval.mpr
        refine ⟨hd,?_⟩
        rcases d with ⟨l,v,t⟩
        simp only at hhalt
        simp [TM2.step,hhalt]
      rw [hM] at hmem
      obtain ⟨out,hout,he⟩ := (Part.mem_map_iff _).mp hmem
      exact ⟨out,hout,Part.mem_unique (complete out hout) hz⟩
  · rintro ⟨out,hout,rfl⟩
    exact complete out hout

omit [DecidableEq S] in
 theorem eval_pre {w : List S} {f : List S →. List S}
    (hB : ∀ s : S, (trNat (Encodable.encode s + 1)).length ≤ B)
    (hM : StateTransition.eval (TM2.step M) (baseCfg (some start) (trList (numbers w))) =
      (f w).map (fun out => baseCfg none (trList (numbers out)))) :
    StateTransition.eval (TM2.step (machine B M start)) (preCfg w.reverse []) =
      (f w).map (fun out => haltCfg out.reverse) := by
  have hp := pre_complete B M start w.reverse []
  simp only [List.reverse_reverse,List.append_nil] at hp
  rw [StateTransition.reaches_eval hp]
  exact eval_run B M start hB hM

end FiniteAlgebraicEnvelopes.MachineRealization.RawTM

/- Actual finite-state extraction from the Mathlib evaluator.  This is a
   dependency of the compiler realization, not a realization assumption. -/
namespace FiniteAlgebraicEnvelopes.MachineRealization
open Turing Relation

namespace FiniteTM2
variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*} [DecidableEq Λ]

 def restrictStmt (S : Finset Λ) (q : TM2.Stmt Γ Λ σ) (h : TM2.SupportsStmt S q) :
    TM2.Stmt Γ {l // l ∈ S} σ :=
  match q with
  | .push k f q => .push k f (restrictStmt S q h)
  | .peek k f q => .peek k f (restrictStmt S q h)
  | .pop k f q => .pop k f (restrictStmt S q h)
  | .load f q => .load f (restrictStmt S q h)
  | .branch f p q => .branch f (restrictStmt S p h.1) (restrictStmt S q h.2)
  | .goto f => .goto (fun v => ⟨f v,h v⟩)
  | .halt => .halt

 def embedCfg (S : Finset Λ) (c : TM2.Cfg Γ {l // l ∈ S} σ) : TM2.Cfg Γ Λ σ :=
  ⟨c.l.map Subtype.val,c.var,c.stk⟩

 variable [DecidableEq K]
omit [DecidableEq Λ] in
 theorem embed_stepAux (S : Finset Λ) (q : TM2.Stmt Γ Λ σ) (h : TM2.SupportsStmt S q)
    (v : σ) (t : ∀ k, List (Γ k)) :
    embedCfg S (TM2.stepAux (restrictStmt S q h) v t) = TM2.stepAux q v t := by
  induction q generalizing v t with
  | push k f q ih | peek k f q ih | pop k f q ih | load f q ih =>
      exact ih h _ _
  | branch f p q ihp ihq =>
      cases hv : f v <;> simp only [restrictStmt,TM2.stepAux,hv,Bool.cond_false,Bool.cond_true]
      · exact ihq h.2 _ _
      · exact ihp h.1 _ _
  | goto f => rfl
  | halt => rfl

 variable [Inhabited Λ] (M : Λ → TM2.Stmt Γ Λ σ) (S : Finset Λ) (h : TM2.Supports M S)
 def machine (l : {l // l ∈ S}) : TM2.Stmt Γ {l // l ∈ S} σ :=
  restrictStmt S (M l.val) (h.2 _ l.property)

omit [DecidableEq Λ] in
 theorem embed_step (c : TM2.Cfg Γ {l // l ∈ S} σ) :
    (TM2.step (machine M S h) c).map (embedCfg S) = TM2.step M (embedCfg S c) := by
  rcases c with ⟨l,v,t⟩
  cases l with
  | none => rfl
  | some l => simpa only [TM2.step,embedCfg,Option.map_some,machine] using
      congrArg some (embed_stepAux S (M l.val) (h.2 _ l.property) v t)

omit [DecidableEq Λ] in
 theorem respects : StateTransition.Respects (TM2.step (machine M S h)) (TM2.step M)
    (fun a b => embedCfg S a = b) := by
  apply StateTransition.fun_respects.mpr
  intro a
  have hh := embed_step M S h a
  cases hc : TM2.step (machine M S h) a with
  | none =>
      change TM2.step M (embedCfg S a) = none
      simpa only [hc,Option.map_none] using hh.symm
  | some b =>
      apply TransGen.single
      change TM2.step M (embedCfg S a) = some (embedCfg S b)
      simpa only [hc,Option.map_some] using hh.symm

omit [DecidableEq Λ] in
 theorem eval_embed (c : TM2.Cfg Γ {l // l ∈ S} σ) :
    StateTransition.eval (TM2.step M) (embedCfg S c) =
      (StateTransition.eval (TM2.step (machine M S h)) c).map (embedCfg S) :=
  StateTransition.tr_eval' _ _ _ (respects M S h) c

end FiniteTM2

end FiniteAlgebraicEnvelopes.MachineRealization

namespace FiniteAlgebraicEnvelopes.MachineRealization.ListCode
open Turing.ToPartrec Encodable

theorem eval_comp (f g : Code) (v : List ℕ) :
    (Code.comp f g).eval v = (g.eval v).bind (fun w => f.eval w) := rfl

attribute [local simp] eval_comp

theorem fix_eval_fwd (c : Code) (w w' : List ℕ)
    (h : Sum.inr w' ∈ Part.map
      (fun v : List ℕ => if v.headI = 0 then Sum.inl v.tail else Sum.inr v.tail) (c.eval w)) :
    (Code.fix c).eval w = (Code.fix c).eval w' :=
  PFun.fix_fwd_eq (α := List ℕ) (β := List ℕ)
    (f := fun v : List ℕ => Part.map
      (fun v : List ℕ => if v.headI = 0 then Sum.inl v.tail else Sum.inr v.tail) (c.eval v))
    (a := w) (a' := w') h

 def prefix₂ : Code := .cons .head (.cons (.comp .head .tail) .nil)
 @[simp] theorem prefix₂_eval (a b : ℕ) (l : List ℕ) :
    prefix₂.eval (a::b::l) = Part.some [a,b] := by simp [prefix₂]

 theorem binary_code {f : ℕ → ℕ → ℕ} (hf : Computable₂ f) :
    ∃ c : Code, ∀ a b l, c.eval (a::b::l) = Part.some [f a b] := by
  obtain ⟨c,hc⟩ := Code.exists_code (Nat.Partrec'.part_iff₂.mpr hf.partrec₂)
  refine ⟨.comp c prefix₂,fun a b l => ?_⟩
  simp only [eval_comp,prefix₂_eval,Part.bind_some]
  have he := hc ⟨[a,b],rfl⟩
  exact he

 def test (t p q : Code) : Code := .comp (.case p (.comp q .tail)) (.cons t .id)
 theorem test_eval (t p q : Code) (w : List ℕ) {n : ℕ}
    (ht : t.eval w = Part.some [n]) :
    (test t p q).eval w = if n = 0 then p.eval w else q.eval w := by
  simp only [test,eval_comp,Code.cons_eval,Code.id_eval,ht]
  cases n <;> simp [List.headI]

 def one : Code := .comp .succ .zero
 @[simp] theorem one_eval (w : List ℕ) : one.eval w = Part.some [1] := by simp [one]

 def encodeStep (c : Code) : Code :=
  test (.comp .head .tail) (.cons .zero .head)
    (.cons one (.cons c (.comp .tail .tail)))
 def encoder (c : Code) : Code := .comp (.fix (encodeStep c)) .zero'

 theorem encodeStep_nil (c : Code) (a : ℕ) :
    (encodeStep c).eval [a] = Part.some [0,a] := by
  rw [encodeStep,test_eval _ _ _ _ (n := 0) (by simp)]
  simp
 theorem encodeStep_cons (c : Code)
    (hc : ∀ a b l, c.eval (a::b::l) = Part.some [Nat.pair (b-1) a + 1])
    (a b : ℕ) (l : List ℕ) :
    (encodeStep c).eval (a::(b+1)::l) = Part.some (1::(Nat.pair b a + 1)::l) := by
  rw [encodeStep,test_eval _ _ _ _ (n := b+1) (by simp)]
  simp [hc]

 theorem encode_loop (c : Code)
    (hc : ∀ a b l, c.eval (a::b::l) = Part.some [Nat.pair (b-1) a + 1])
    (w acc : List ℕ) :
    (Code.fix (encodeStep c)).eval (encode acc :: w.map Nat.succ) =
      Part.some [encode (w.reverse ++ acc)] := by
  induction w generalizing acc with
  | nil =>
      apply Part.eq_some_iff.mpr
      rw [Code.fix_eval]
      apply PFun.fix_stop
      simp [encodeStep_nil]
  | cons b l ih =>
      rw [List.map_cons]
      have hs : Sum.inr (encode (b::acc)::l.map Nat.succ) ∈
          ((encodeStep c).eval (encode acc::(b+1)::l.map Nat.succ)).map
            (fun v => if v.headI = 0 then Sum.inl v.tail else Sum.inr v.tail) := by
        rw [encodeStep_cons c hc]
        simp [encode_list_cons]
      rw [fix_eval_fwd _ _ _ hs,ih]
      simp [List.reverse_cons,List.append_assoc]

 theorem encoder_eval (c : Code)
    (hc : ∀ a b l, c.eval (a::b::l) = Part.some [Nat.pair (b-1) a + 1]) (w : List ℕ) :
    (encoder c).eval (w.map Nat.succ) = Part.some [encode w.reverse] := by
  simp only [encoder,eval_comp,Code.zero'_eval]
  simpa using encode_loop c hc w []

 def decodeStep (h t : Code) : Code :=
  test .head (.cons .zero .tail)
    (.cons one (.cons t (.cons h .tail)))
 def decoder (h t : Code) : Code := .fix (decodeStep h t)
 theorem decodeStep_zero (h t : Code) (l : List ℕ) :
    (decodeStep h t).eval (0::l) = Part.some (0::l) := by
  rw [decodeStep,test_eval _ _ _ _ (n := 0) (by simp)]
  simp
 theorem decodeStep_cons (h t : Code)
    (hh : ∀ n l, h.eval (n::l) = Part.some [(n-1).unpair.1+1])
    (ht : ∀ n l, t.eval (n::l) = Part.some [(n-1).unpair.2])
    (b : ℕ) (w l : List ℕ) :
    (decodeStep h t).eval (encode (b::w)::l) = Part.some (1::encode w::(b+1)::l) := by
  rw [decodeStep,test_eval _ _ _ _ (n := encode (b::w)) (by simp)]
  simp [encode_list_cons,hh,ht]

 theorem decoder_eval (h t : Code)
    (hh : ∀ n l, h.eval (n::l) = Part.some [(n-1).unpair.1+1])
    (ht : ∀ n l, t.eval (n::l) = Part.some [(n-1).unpair.2])
    (w acc : List ℕ) :
    (decoder h t).eval (encode w::acc) = Part.some (w.reverse.map Nat.succ ++ acc) := by
  induction w generalizing acc with
  | nil =>
      apply Part.eq_some_iff.mpr
      rw [decoder,Code.fix_eval]
      apply PFun.fix_stop
      simp [decodeStep_zero]
  | cons b w ih =>
      rw [decoder]
      have hs : Sum.inr (encode w::(b+1)::acc) ∈
          ((decodeStep h t).eval (encode (b::w)::acc)).map
            (fun v => if v.headI = 0 then Sum.inl v.tail else Sum.inr v.tail) := by
        rw [decodeStep_cons h t hh ht]
        simp
      rw [fix_eval_fwd _ _ _ hs]
      change (decoder h t).eval _ = _
      rw [ih]
      simp [List.reverse_cons,List.map_append,List.append_assoc]

 theorem unary_code {f : ℕ → ℕ} (hf : Computable f) :
    ∃ c : Code, ∀ n l, c.eval (n::l) = Part.some [f n] := by
  obtain ⟨c,hc⟩ := Code.exists_code (Nat.Partrec'.part_iff₁.mpr hf.partrec)
  refine ⟨.comp c .head,fun n l => ?_⟩
  simp only [eval_comp,Code.head_eval,List.headI_cons]
  rw [show (pure [n] : Part (List ℕ)) = Part.some [n] from rfl,Part.bind_some]
  have he := hc ⟨[n],rfl⟩
  exact he

 theorem exists_wordCode {f : List ℕ →. List ℕ} (hf : Partrec f) :
    ∃ c : Code, ∀ w, c.eval (w.map Nat.succ) = (f w).map (List.map Nat.succ) := by
  obtain ⟨ce,hce⟩ := binary_code
    ((Computable.succ.comp (Primrec₂.natPair.to_comp.comp
      (Primrec.nat_sub.to_comp.comp Computable.snd (Computable.const 1)) Computable.fst)).to₂)
  obtain ⟨ch,hch⟩ := unary_code
    (Computable.succ.comp (Computable.fst.comp (Primrec.unpair.to_comp.comp
      (Primrec.nat_sub.to_comp.comp Computable.id (Computable.const 1)))))
  obtain ⟨ct,hct⟩ := unary_code
    (Computable.snd.comp (Primrec.unpair.to_comp.comp
      (Primrec.nat_sub.to_comp.comp Computable.id (Computable.const 1))))
  let g : ℕ →. ℕ := fun n => (f (Denumerable.ofNat (List ℕ) n).reverse).map
    (fun l => encode l.reverse)
  have hg : Partrec g :=
    (hf.comp (Computable.list_reverse.comp (Computable.ofNat (List ℕ)))).map
      ((Computable.encode.comp Computable.list_reverse).comp Computable.snd).to₂
  obtain ⟨cf,hcf⟩ := Code.exists_code (Nat.Partrec'.part_iff₁.mpr hg)
  refine ⟨.comp (decoder ch ct) (.comp cf (encoder ce)),fun w => ?_⟩
  simp only [eval_comp,encoder_eval ce hce,Part.bind_some]
  rw [hcf ⟨[encode w.reverse],rfl⟩]
  change ((g (encode w.reverse)).map (fun n => [n])).bind (fun v => (decoder ch ct).eval v) = _
  simp only [g,Denumerable.ofNat_encode,List.reverse_reverse]
  apply Part.ext
  intro out
  simp only [Part.mem_bind_iff,Part.mem_map_iff]
  constructor
  · rintro ⟨_,⟨n,⟨l,hl,rfl⟩,rfl⟩,hd⟩
    have he := decoder_eval ch ct hch hct l.reverse []
    simp only [List.reverse_reverse,List.append_nil] at he
    rw [he,Part.mem_some_iff] at hd
    exact ⟨l,hl,hd.symm⟩
  · rintro ⟨l,hl,rfl⟩
    refine ⟨[encode l.reverse],⟨encode l.reverse,⟨l,hl,rfl⟩,rfl⟩,?_⟩
    rw [decoder_eval ch ct hch hct l.reverse []]
    simp

end FiniteAlgebraicEnvelopes.MachineRealization.ListCode

namespace FiniteAlgebraicEnvelopes.MachineRealization

section
open Turing Turing.ToPartrec Turing.PartrecToTM2
open RawTM

namespace FiniteTM2
variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*} [DecidableEq Λ]
omit [DecidableEq Λ] in
 theorem embedCfg_injective (A : Finset Λ) : Function.Injective (embedCfg (Γ := Γ) (σ := σ) A) := by
  rintro ⟨l,v,t⟩ ⟨l',v',t'⟩ h
  have hl := congrArg TM2.Cfg.l h
  have hv := congrArg TM2.Cfg.var h
  have ht := congrArg TM2.Cfg.stk h
  dsimp only [embedCfg] at hl hv ht
  have he := Option.map_injective Subtype.val_injective hl
  cases he
  cases hv
  cases ht
  rfl
end FiniteTM2

 theorem part_map_injective {A B : Type*} {g : A → B} (hg : Function.Injective g) :
    Function.Injective (Part.map g) := by
  intro p q h
  apply Part.ext
  intro a
  constructor <;> intro ha
  · have hh : g a ∈ p.map g := Part.mem_map _ ha
    rw [h] at hh
    obtain ⟨b,hb,he⟩ := (Part.mem_map_iff _).mp hh
    exact (hg he) ▸ hb
  · have hh : g a ∈ q.map g := Part.mem_map _ ha
    rw [←h] at hh
    obtain ⟨b,hb,he⟩ := (Part.mem_map_iff _).mp hh
    exact (hg he) ▸ hb

namespace WordEvaluator
variable {S : Type} [Primcodable S]

 theorem exists_code {f : List S →. List S} (hf : Partrec f) :
    ∃ c : Code, ∀ w, c.eval (numbers w) = (f w).map numbers := by
  let g : List ℕ →. List ℕ := fun ns =>
    (f (ns.filterMap Encodable.decode)).map (List.map Encodable.encode)
  have hg : Partrec g :=
    (hf.comp (Primrec.listFilterMap Primrec.id (Primrec.decode.comp Primrec.snd).to₂).to_comp).map
      ((Primrec.list_map Primrec.id (Primrec.encode.comp Primrec.snd).to₂).to_comp.comp Computable.snd).to₂
  obtain ⟨c,hc⟩ := ListCode.exists_wordCode hg
  refine ⟨c,fun w => ?_⟩
  have hcc := hc (w.map Encodable.encode)
  have hlist : (w.map Encodable.encode).filterMap Encodable.decode = w := by
    induction w <;> simp_all
  change c.eval (w.map (fun s => Encodable.encode s + 1)) =
    (f w).map (fun out => out.map (fun s => Encodable.encode s + 1))
  simpa only [g,hlist,Part.map_map,List.map_map,Function.comp_def,Nat.succ_eq_add_one] using hcc

 theorem exists_finite {f : List S →. List S} (hf : Partrec f) :
    ∃ (Λ : Type) (_ : Fintype Λ) (start : Λ)
      (M : Λ → TM2.Stmt (fun _ : K' => Γ') Λ (Option Γ')),
      ∀ w, StateTransition.eval (TM2.step M) (baseCfg (some start) (trList (numbers w))) =
        (f w).map (fun out => baseCfg none (trList (numbers out))) := by
  obtain ⟨c,hc⟩ := exists_code hf
  let A := codeSupp c Cont'.halt
  let : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
  have hs : TM2.Supports tr A := tr_supports c Cont'.halt
  let start : {l // l ∈ A} := ⟨trNormal c Cont'.halt,hs.1⟩
  let M := FiniteTM2.machine tr A hs
  refine ⟨{l // l ∈ A},inferInstance,start,M,fun w => ?_⟩
  apply part_map_injective (FiniteTM2.embedCfg_injective A)
  rw [←FiniteTM2.eval_embed tr A hs]
  change StateTransition.eval (TM2.step tr) (init c (numbers w)) = _
  rw [tr_eval,hc]
  simp only [Part.map_eq_map,Part.map_map]
  rfl

variable [Fintype S]
 noncomputable def bound : ℕ := Finset.univ.sup fun s : S => (trNat (Encodable.encode s + 1)).length
 theorem le_bound (s : S) : (trNat (Encodable.encode s + 1)).length ≤ bound (S := S) :=
  Finset.le_sup (f := fun s : S => (trNat (Encodable.encode s + 1)).length) (Finset.mem_univ s)

 theorem exists_raw {f : List S →. List S} (hf : Partrec f) :
    ∃ (Λ : Type) (_ : Fintype Λ) (M : Λ → TM2.Stmt (fun _ : K' => StackLift.Symbol S) Λ (StackLift.Store S))
      (start : Λ), ∀ w,
      StateTransition.eval (TM2.step M)
        ⟨some start,none,tracks w.reverse []⟩ =
          (f w).map (fun out => ⟨none,none,tracks out.reverse []⟩) := by
  classical
  obtain ⟨Λ,hΛ,start,M,hM⟩ := exists_finite hf
  let : Fintype Λ := hΛ
  refine ⟨StackLift.Label S Λ,inferInstance,machine (bound (S := S)) M start,.pre,fun w => ?_⟩
  exact eval_pre (bound (S := S)) M start le_bound (hM w)

end WordEvaluator
end

open Turing Relation
namespace FiniteTM0
variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] [DecidableEq Λ]
variable (M : TM0.Machine Γ Λ) (A : Finset Λ) (h : TM0.Supports M (A : Set Λ))
variable [Inhabited {l // l ∈ A}]

def machine : TM0.Machine Γ {l // l ∈ A} := fun q a =>
  (M q.val a).pmap (fun p hp => (⟨p.1,h.2 hp q.property⟩,p.2)) (fun _ hp => hp)

def embed (c : TM0.Cfg Γ {l // l ∈ A}) : TM0.Cfg Γ Λ := ⟨c.q.val,c.Tape⟩

omit [Inhabited Λ] [DecidableEq Λ] [Inhabited {l // l ∈ A}] in
theorem embed_injective : Function.Injective (embed (Γ := Γ) A) := by
  rintro ⟨q,t⟩ ⟨q',t'⟩ he
  have hq : q = q' := Subtype.ext (congrArg TM0.Cfg.q he)
  have ht := congrArg TM0.Cfg.Tape he
  cases hq
  cases ht
  rfl

omit [DecidableEq Λ] in
theorem embed_step (c : TM0.Cfg Γ {l // l ∈ A}) :
    (TM0.step (machine M A h) c).map (embed A) = TM0.step M (embed A c) := by
  rcases c with ⟨q,t⟩
  cases hc : M q.val t.head with
  | none => simp [TM0.step,machine,embed,hc]
  | some p => rcases p with ⟨q',s⟩; cases s <;> simp [TM0.step,machine,embed,hc]

omit [DecidableEq Λ] in
theorem respects : StateTransition.Respects (TM0.step (machine M A h)) (TM0.step M)
    (fun a b => embed A a = b) := by
  apply StateTransition.fun_respects.mpr
  intro a
  have hh := embed_step M A h a
  cases hc : TM0.step (machine M A h) a with
  | none =>
      change TM0.step M (embed A a) = none
      simpa only [hc,Option.map_none] using hh.symm
  | some b =>
      apply TransGen.single
      change TM0.step M (embed A a) = some (embed A b)
      simpa only [hc,Option.map_some] using hh.symm

omit [DecidableEq Λ] in
theorem eval_embed (c : TM0.Cfg Γ {l // l ∈ A}) :
    StateTransition.eval (TM0.step M) (embed A c) =
      (StateTransition.eval (TM0.step (machine M A h)) c).map (embed A) :=
  StateTransition.tr_eval' _ _ _ (respects M A h) c
end FiniteTM0

namespace StackTape
open Turing.PartrecToTM2 StackLift RawTM
variable {S Λ : Type} [Fintype S] [Fintype Λ] [Inhabited Λ]

 def slice (a : S) : ∀ _ : K', Option (Symbol S) := Function.update (fun _ => none) .main (some (.inr a))
 def stackList (w : List S) : ListBlank (∀ _ : K', Option (Symbol S)) := ListBlank.mk (w.map slice)
 def tape (w : List S) : Turing.Tape (TM2to1.Γ' K' (fun _ => Symbol S)) :=
   Turing.Tape.mk' ∅ (TM2to1.addBottom (stackList w))

omit [Fintype S] in
 theorem tracks_proj (w : List S) (k : K') :
   (stackList w).map (Turing.proj k) = ListBlank.mk (((tracks w.reverse [] k).map some).reverse) := by
  cases k <;> simp [stackList,slice,tracks,Turing.proj,ListBlank.map_mk,List.map_reverse,List.map_map,
    Function.comp_def] <;> exact Quotient.sound (Or.inr ⟨w.length,rfl⟩)

omit [Fintype S] [Fintype Λ] [Inhabited Λ] in
 theorem trCfg (w : List S) (l : Option Λ) (v : Store S) :
   TM2to1.TrCfg (⟨l,v,tracks w.reverse []⟩ : TM2.Cfg (fun _ : K' => Symbol S) Λ (Store S))
     ⟨l.map .normal,v,tape w⟩ := .mk (stackList w) (tracks_proj w)

omit [Fintype S] in
 theorem stackList_unique (w : List S) (L : ListBlank (∀ _ : K', Option (Symbol S)))
    (hL : ∀ k, L.map (Turing.proj k) = ListBlank.mk (((tracks w.reverse [] k).map some).reverse)) :
    L = stackList w := by
  apply ListBlank.ext
  intro n
  funext k
  have he := congrArg (fun l => ListBlank.nth l n) ((hL k).trans (tracks_proj w k).symm)
  simpa only [ListBlank.nth_map,Turing.proj,PointedMap.mk_val] using he

omit [Fintype S] [Fintype Λ] [Inhabited Λ] in
 theorem trCfg_unique (w : List S) (l : Option Λ) (v : Store S)
    {c : TM1.Cfg (TM2to1.Γ' K' (fun _ => Symbol S)) (TM2to1.Λ' K' (fun _ => Symbol S) Λ (Store S)) (Store S)}
    (hc : TM2to1.TrCfg (⟨l,v,tracks w.reverse []⟩ : TM2.Cfg (fun _ : K' => Symbol S) Λ (Store S)) c) :
    c = ⟨l.map .normal,v,tape w⟩ := by
  cases hc with
  | mk L hL => rw [stackList_unique w L hL]; rfl

 variable (M : Λ → TM2.Stmt (fun _ : K' => Symbol S) Λ (Store S))
omit [Fintype S] [Fintype Λ] [Inhabited Λ] in
 theorem eval_tape {f : List S →. List S} (start : Λ)
   (hM : ∀ w, StateTransition.eval (TM2.step M) ⟨some start,none,tracks w.reverse []⟩ =
      (f w).map (fun out => ⟨none,none,tracks out.reverse []⟩)) (w : List S) :
   StateTransition.eval (TM1.step (TM2to1.tr M)) ⟨some (.normal start),none,tape w⟩ =
     (f w).map (fun out => ⟨none,none,tape out⟩) := by
  apply Part.ext
  intro c
  constructor
  · intro hc
    obtain ⟨b,hbc,hb⟩ := StateTransition.tr_eval_rev (TM2to1.tr_respects M) (trCfg w (some start) none) hc
    rw [hM] at hb
    obtain ⟨out,hout,rfl⟩ := (Part.mem_map_iff _).mp hb
    rw [trCfg_unique out none none hbc]
    exact Part.mem_map _ hout
  · intro hc
    obtain ⟨out,hout,rfl⟩ := (Part.mem_map_iff _).mp hc
    have hb : (⟨none,none,tracks out.reverse []⟩ : TM2.Cfg (fun _ : K' => Symbol S) Λ (Store S)) ∈
       StateTransition.eval (TM2.step M) ⟨some start,none,tracks w.reverse []⟩ := by
      rw [hM]; exact Part.mem_map _ hout
    obtain ⟨b,hb,hbe⟩ := StateTransition.tr_eval (TM2to1.tr_respects M) (trCfg w (some start) none) hb
    simpa only [trCfg_unique out none none hb,Option.map_none,Option.map_some] using hbe

omit [Fintype S] [Fintype Λ] in
 theorem eval_post {f : List S →. List S} (start : Λ)
   (hM : ∀ w, StateTransition.eval (TM2.step M) ⟨some start,none,tracks w.reverse []⟩ =
      (f w).map (fun out => ⟨none,none,tracks out.reverse []⟩)) (w : List S) :
   StateTransition.eval (TM0.step (TM1to0.tr (TM2to1.tr M)))
     (TM1to0.trCfg (TM2to1.tr M) ⟨some (.normal start),none,tape w⟩) =
     (f w).map (fun out => (⟨(none,none),tape out⟩ : TM0.Cfg _ _)) := by
   rw [StateTransition.tr_eval' _ _ _ (TM1to0.tr_respects (TM2to1.tr M)),eval_tape M start hM]
   simp only [Part.map_eq_map,Part.map_map]
   rfl

end StackTape

end FiniteAlgebraicEnvelopes.MachineRealization

end OAI
end

section
-- module Solutions.OAIFAE.TapeFolding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Safe tapes, literal folding, and uniform code-machine realization.
-/

namespace FiniteAlgebraicEnvelopes.MachineRealization.OneSided
open Compiler.Simulator Turing Relation
variable {Γ Q : Type*}

structure Cfg (Γ Q : Type*) where
  state : Q
  pos : ℕ
  cell : ℕ → Γ

def step (M : Machine Q Γ) (c : Cfg Γ Q) : Option (Cfg Γ Q) :=
  (M.transition c.state (c.cell c.pos)).map fun cmd =>
    ⟨cmd.state,(match cmd.move with | .stay => c.pos | .left => c.pos-1 | .right => c.pos+1),
      Function.update c.cell c.pos cmd.write⟩

def view (c : SemanticTape Γ Q) : Cfg Γ Q := ⟨c.state,c.left.length,semanticContent c⟩

 theorem append_at (l : List Γ) (s : Stream' Γ) (n : ℕ) :
   Stream'.appendStream' l s (l.length+n) = s n := by
  induction l with
  | nil => simp only [List.length_nil,Nat.zero_add,Stream'.appendStream']
  | cons a l ih => simpa only [List.length_cons,Nat.succ_add,Stream'.appendStream',Stream'.cons] using ih

 theorem replace_at (l : List Γ) (s : Stream' Γ) (a : Γ) :
   Stream'.appendStream' l (Stream'.cons a s.tail) =
     Function.update (Stream'.appendStream' l s) l.length a := by
  unfold Stream' at *
  funext n
  induction l generalizing n with
  | nil => cases n <;> simp [Stream'.appendStream',Stream'.cons,Stream'.tail,Stream'.get]
  | cons b l ih =>
    cases n with
    | zero => simp [Stream'.appendStream',Stream'.cons,Function.update]
    | succ n =>
      by_cases hn : n = l.length
      · subst n
        simpa [Stream'.appendStream',Stream'.cons,Function.update] using ih l.length
      · simpa [Stream'.appendStream',Stream'.cons,Function.update,hn] using ih n

 theorem view_step (M : Machine Q Γ) (c : SemanticTape Γ Q) :
   (semanticStep M c).map view = step M (view c) := by
  rcases c with ⟨q,l,r⟩
  have hh : Stream'.appendStream' l.reverse r l.length = r.head := by
    simpa only [List.length_reverse,Nat.add_zero,Stream'.head,Stream'.get] using append_at l.reverse r 0
  simp only [semanticStep,step,view,semanticContent,hh,Option.map_map]
  congr 1
  funext cmd
  rcases cmd with ⟨q',a,mv⟩
  cases mv with
  | stay =>
      dsimp only [Function.comp_apply,view,semanticContent]
      congr 1
      simpa only [List.length_reverse,Stream'] using replace_at l.reverse r a
  | right =>
      dsimp only [Function.comp_apply,view,semanticContent,List.length_cons]
      congr 1
      simpa only [semanticContent,List.reverse_cons,Stream'.append_append_stream,List.length_cons,
        Stream'.appendStream',List.length_reverse,Stream'] using replace_at l.reverse r a
  | left =>
      cases l with
      | nil =>
          dsimp only [Function.comp_apply,view,semanticContent,List.length_nil,Nat.zero_sub]
          congr 1
          exact replace_at [] r a
      | cons b l =>
          dsimp only [Function.comp_apply,view,semanticContent,List.length_cons]
          simp only [Nat.add_sub_cancel]
          congr 1
          simpa only [semanticContent,List.reverse_cons,Stream'.append_append_stream,List.length_cons,
            Nat.add_sub_cancel,Stream'.appendStream',List.length_reverse,List.length_append,List.length_singleton,List.length_nil,Nat.zero_add,Stream'] using replace_at (l.reverse ++ [b]) r a

 theorem respects (M : Machine Q Γ) : StateTransition.Respects (step M) (semanticStep M)
   (fun a b => view b = a) := by
  intro c s hs
  rw [←hs,←view_step M s]
  cases hc : semanticStep M s with
  | none => rfl
  | some t => exact ⟨t,rfl,TransGen.single hc⟩

end FiniteAlgebraicEnvelopes.MachineRealization.OneSided

namespace FiniteAlgebraicEnvelopes.MachineRealization.TapeFold
open Turing Relation Compiler.Simulator
variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

inductive Side | pos | neg deriving DecidableEq
instance instFintypeSide : Fintype Side := ⟨{.pos,.neg},by intro x; cases x <;> simp⟩
structure Cell (Γ : Type*) where
  origin : Bool
  pos : Γ
  neg : Γ
  deriving DecidableEq, Fintype

def position : Side → ℕ → ℤ
  | .pos,n => n
  | .neg,n => -(n+1 : ℤ)

def read (d : Side) (a : Cell Γ) : Γ := match d with | .pos => a.pos | .neg => a.neg

def command (d : Side) (q : Λ) (a : Cell Γ) : TM0.Stmt Γ → Command (Side × Λ) (Cell Γ)
  | .write b => ⟨(d,q),(match d with | .pos => {a with pos := b} | .neg => {a with neg := b}),.stay⟩
  | .move dr => match d,dr with
    | .pos,.right => ⟨(.pos,q),a,.right⟩
    | .pos,.left => if a.origin then ⟨(.neg,q),a,.stay⟩ else ⟨(.pos,q),a,.left⟩
    | .neg,.left => ⟨(.neg,q),a,.right⟩
    | .neg,.right => if a.origin then ⟨(.pos,q),a,.stay⟩ else ⟨(.neg,q),a,.left⟩

def machine (M : TM0.Machine Γ Λ) (start : Λ) : Machine (Side × Λ) (Cell Γ) :=
  ⟨(.pos,start),fun q a => (M q.2 (read q.1 a)).map fun cmd => command q.1 cmd.1 a cmd.2⟩

/-- The two halves of the integer tape share one physical cell. The immutable
origin flag makes crossing the fold a finite-control, zero-movement operation. -/
def Rel (c : TM0.Cfg Γ Λ) (s : OneSided.Cfg (Cell Γ) (Side × Λ)) : Prop :=
  s.state.2 = c.q ∧ ∀ n,
    (s.cell n).origin = decide (n = 0) ∧
    (s.cell n).pos = c.Tape.nth ((n:ℤ) - position s.state.1 s.pos) ∧
    (s.cell n).neg = c.Tape.nth (-(n+1:ℤ) - position s.state.1 s.pos)

omit [Inhabited Λ] in
theorem read_head {c : TM0.Cfg Γ Λ} {s : OneSided.Cfg (Cell Γ) (Side × Λ)} (h : Rel c s) :
    read s.state.1 (s.cell s.pos) = c.Tape.head := by
  obtain ⟨_,hs⟩ := h
  obtain ⟨_,hp,hn⟩ := hs s.pos
  cases hd : s.state.1 <;> simp only [read,hd,position,sub_self,Tape.nth_zero] at * <;> assumption

omit [Inhabited Γ] [Inhabited Λ] in
 theorem move_position (d : Side) (dr : Dir) (q : Λ) (a : Cell Γ) (p : ℕ)
    (ha : a.origin = decide (p = 0)) :
    let cmd := command d q a (.move dr)
    position cmd.state.1 (match cmd.move with | .stay => p | .left => p-1 | .right => p+1) =
      position d p + (match dr with | .left => -1 | .right => 1) := by
  cases d <;> cases dr <;> simp only [command,ha] <;>
    (try split_ifs) <;> simp_all [position] <;> omega

omit [Inhabited Γ] [Inhabited Λ] in
 theorem move_write (d : Side) (dr : Dir) (q : Λ) (a : Cell Γ) :
    (command d q a (.move dr)).write = a := by
  cases d <;> cases dr <;> simp only [command] <;> (try split_ifs) <;> rfl

omit [Inhabited Γ] [Inhabited Λ] in
 theorem command_state (d : Side) (q : Λ) (a : Cell Γ) (stmt : TM0.Stmt Γ) :
    (command d q a stmt).state.2 = q := by
  cases stmt with
  | write b => cases d <;> rfl
  | move dr => cases d <;> cases dr <;> simp only [command] <;> (try split_ifs) <;> rfl

 theorem step_rel (M : TM0.Machine Γ Λ) (start : Λ)
    {c : TM0.Cfg Γ Λ} {s : OneSided.Cfg (Cell Γ) (Side × Λ)} (hs : Rel c s)
    {cmd : Λ × TM0.Stmt Γ} (hc : M c.q c.Tape.head = some cmd) :
    ∃ t, Rel (⟨cmd.1,match cmd.2 with | .move d => c.Tape.move d | .write b => c.Tape.write b⟩) t ∧
      OneSided.step (machine M start) s = some t := by
  let ins := command s.state.1 cmd.1 (s.cell s.pos) cmd.2
  let t : OneSided.Cfg (Cell Γ) (Side × Λ) :=
    ⟨ins.state,(match ins.move with | .stay => s.pos | .left => s.pos-1 | .right => s.pos+1),
      Function.update s.cell s.pos ins.write⟩
  refine ⟨t,?_,?_⟩
  · refine ⟨command_state _ _ _ _,fun n => ?_⟩
    obtain ⟨hor,hpo,hne⟩ := hs.2 n
    obtain ⟨hop,_,_⟩ := hs.2 s.pos
    cases hcmd : cmd.2 with
    | move d =>
      have hw : ins.write = s.cell s.pos := by dsimp [ins]; rw [hcmd,move_write]
      have hp := move_position s.state.1 d cmd.1 (s.cell s.pos) s.pos hop
      change _ = _ at hp
      have hcelt : t.cell = s.cell := by dsimp [t]; rw [hw,Function.update_eq_self]
      have hpos : position t.state.1 t.pos = position s.state.1 s.pos +
          (match d with | .left => -1 | .right => 1) := by cases d <;> simpa only [t,ins,hcmd] using hp
      change (t.cell n).origin = _ ∧ (t.cell n).pos = _ ∧ (t.cell n).neg = _
      rw [hcelt]
      refine ⟨hor,?_,?_⟩
      · rw [hpos]
        cases d <;> simp only [Tape.move_left_nth,Tape.move_right_nth] <;>
          convert hpo using 1 <;> congr 1 <;> omega
      · rw [hpos]
        cases d <;> simp only [Tape.move_left_nth,Tape.move_right_nth] <;>
          convert hne using 1 <;> congr 1 <;> omega
    | write b =>
      cases hd : s.state.1 <;>
        simp only [t,ins,hcmd,command,hd,position]
      · by_cases hn : n = s.pos
        · subst n
          simp only [Function.update_self]
          refine ⟨hop,?_,?_⟩
          · simp [Tape.write]
          · rw [Tape.write_nth,ite_eq_right (by omega)]
            simpa only [hd,position] using hne
        · rw [Function.update_of_ne hn]
          refine ⟨hor,?_,?_⟩
          · rw [Tape.write_nth,ite_eq_right (by omega)]
            simpa only [hd,position] using hpo
          · rw [Tape.write_nth,ite_eq_right (by omega)]
            simpa only [hd,position] using hne
      · by_cases hn : n = s.pos
        · subst n
          simp only [Function.update_self]
          refine ⟨hop,?_,?_⟩
          · rw [Tape.write_nth,ite_eq_right (by omega)]
            simpa only [hd,position] using hpo
          · simp [Tape.write]
        · rw [Function.update_of_ne hn]
          refine ⟨hor,?_,?_⟩
          · rw [Tape.write_nth,ite_eq_right (by omega)]
            simpa only [hd,position] using hpo
          · rw [Tape.write_nth,ite_eq_right (by omega)]
            simpa only [hd,position] using hne
  · simp only [OneSided.step,machine,hs.1,read_head hs,hc,Option.map_some]
    rfl

 theorem respects (M : TM0.Machine Γ Λ) (start : Λ) :
    StateTransition.Respects (TM0.step M) (OneSided.step (machine M start)) Rel := by
  intro c s hs
  cases hc : M c.q c.Tape.head with
  | none => simp only [TM0.step,hc,Option.map_none,OneSided.step,machine,hs.1,read_head hs]
  | some cmd =>
    simp only [TM0.step,hc,Option.map_some]
    obtain ⟨t,ht,hst⟩ := step_rel M start hs hc
    exact ⟨t,ht,TransGen.single hst⟩

end FiniteAlgebraicEnvelopes.MachineRealization.TapeFold

namespace FiniteAlgebraicEnvelopes.MachineRealization.TapeSafety
open Turing
variable {K : Type} {Γ : K → Type} {Λ σ : Type}

/-- Every writing subinstruction preserves the bottom track. -/
def Safe : TM1.Stmt (TM2to1.Γ' K Γ) Λ σ → Prop
  | .move _ q => Safe q
  | .write f q => (∀ a v, (f a v).1 = a.1) ∧ Safe q
  | .load _ q => Safe q
  | .branch _ q r => Safe q ∧ Safe r
  | .goto _ => True
  | .halt => True

theorem safe_stAct [DecidableEq K] {k : K}
    {q : TM1.Stmt (TM2to1.Γ' K Γ) (TM2to1.Λ' K Γ Λ σ) σ} (hq : Safe q)
    (a : TM2to1.StAct K Γ σ k) : Safe (TM2to1.trStAct q a) := by
  cases a <;> simp [TM2to1.trStAct,Safe,hq]

theorem safe_normal (q : TM2.Stmt Γ Λ σ) : Safe (TM2to1.trNormal q) := by
  induction q <;> simp_all [TM2to1.trNormal,Safe]

theorem safe_tr [DecidableEq K] (M : Λ → TM2.Stmt Γ Λ σ) (q : TM2to1.Λ' K Γ Λ σ) :
    Safe (TM2to1.tr M q) := by
  cases q with
  | normal q => exact safe_normal _
  | go k a q =>
      change Safe (TM2to1.trStAct (.goto fun _ _ => .ret q) a) ∧ True
      exact ⟨safe_stAct (q := .goto fun _ _ => .ret q) trivial a,trivial⟩
  | ret q => simp [TM2to1.tr,Safe,safe_normal]

theorem safe_sub {q r : TM1.Stmt (TM2to1.Γ' K Γ) Λ σ}
    (h : q ∈ TM1.stmts₁ r) (hr : Safe r) : Safe q := by
  classical
  induction r with
    simp only [TM1.stmts₁,Safe,Finset.mem_insert,Finset.mem_union,Finset.mem_singleton] at h hr
  | move d r ih => rcases h with rfl | h; exact hr; exact ih h hr
  | write f r ih => rcases h with rfl | h; exact hr; exact ih h hr.2
  | load f r ih => rcases h with rfl | h; exact hr; exact ih h hr
  | branch p r s ihr ihs => rcases h with rfl | h | h; exact hr; exact ihr h hr.1; exact ihs h hr.2
  | goto l => subst q; trivial
  | halt => subst q; trivial

theorem safe_stmts (M : Λ → TM1.Stmt (TM2to1.Γ' K Γ) Λ σ) (B : Finset Λ)
    (hm : ∀ q, Safe (M q)) {q : TM1.Stmt (TM2to1.Γ' K Γ) Λ σ}
    (hq : some q ∈ TM1.stmts M B) : Safe q := by
  classical
  simp only [TM1.stmts,Finset.mem_insertNone,Option.mem_def,Option.some.injEq,forall_eq',Finset.mem_biUnion] at hq
  obtain ⟨l,_,hl⟩ := hq
  exact safe_sub hl (hm l)

theorem trAux_write (M : Λ → TM1.Stmt (TM2to1.Γ' K Γ) Λ σ)
    (a : TM2to1.Γ' K Γ) (q : TM1.Stmt (TM2to1.Γ' K Γ) Λ σ) (v : σ)
    (hq : Safe q) (b : TM2to1.Γ' K Γ)
    (he : (TM1to0.trAux M a q v).2 = .write b) : b.1 = a.1 := by
  induction q generalizing v with
  | move d q ih => cases he
  | write f q ih => cases he; exact hq.1 a v
  | load f q ih => exact ih _ hq he
  | branch p q r ihq ihr =>
      cases hp : p a v <;> simp only [TM1to0.trAux,hp,Bool.cond_false,Bool.cond_true] at he
      · exact ihr _ hq.2 he
      · exact ihq _ hq.1 he
  | goto l => cases he; rfl
  | halt => cases he; rfl

/-- A machine preserves the distinguished bottom marker on every write. -/
def Preserves {L : Type*} [Inhabited L] (M : TM0.Machine (TM2to1.Γ' K Γ) L) : Prop :=
  ∀ q a q' b, M q a = some (q',.write b) → b.1 = a.1

theorem finite_preserves [Inhabited Λ] [Inhabited σ] [Fintype σ]
    (M : Λ → TM1.Stmt (TM2to1.Γ' K Γ) Λ σ) (B : Finset Λ)
    (hB : TM1.Supports M B) (hm : ∀ q, Safe (M q))
    [Inhabited {l // l ∈ TM1to0.trStmts M B}] :
    Preserves (FiniteTM0.machine (TM1to0.tr M) (TM1to0.trStmts M B) (TM1to0.tr_supports M hB)) := by
  classical
  intro q a q' b he
  have hq := q.property
  rcases q with ⟨⟨q,v⟩,hq'⟩
  cases q with
  | none => simp [FiniteTM0.machine,TM1to0.tr] at he
  | some q =>
    have hqm : some q ∈ TM1.stmts M B := (Finset.mem_product.mp hq').1
    have hs := safe_stmts M B hm hqm
    have hx : (TM1to0.trAux M a q v).2 = .write b := by
      have := congrArg (Option.map (fun (x : {l // l ∈ TM1to0.trStmts M B} × TM0.Stmt _) => x.2)) he
      simpa [FiniteTM0.machine,TM1to0.tr] using this
    exact trAux_write M a q v hs b hx

end FiniteAlgebraicEnvelopes.MachineRealization.TapeSafety

namespace FiniteAlgebraicEnvelopes.MachineRealization
open Turing
namespace WordEvaluator
open Turing.PartrecToTM2 StackLift RawTM StackTape
variable {S : Type} [Fintype S] [Primcodable S]
 theorem exists_safe_tape {f : List S →. List S} (hf : Partrec f) :
   ∃ (Λ : Type) (_ : Fintype Λ) (_ : Inhabited Λ)
     (M : TM0.Machine (TM2to1.Γ' K' (fun _ => Symbol S)) Λ) (start stop : Λ),
     TapeSafety.Preserves M ∧ ∀ w, StateTransition.eval (TM0.step M) ⟨start,tape w⟩ =
       (f w).map (fun out => ⟨stop,tape out⟩) := by
  classical
  obtain ⟨Λ,hΛ,M,start,hM⟩ := exists_raw hf
  let : Fintype Λ := hΛ
  let : Inhabited Λ := ⟨start⟩
  let N := TM2to1.tr M
  let P := TM1to0.tr N
  let B := TM2to1.trSupp M Finset.univ
  have hU : TM2.Supports M Finset.univ := by
    refine ⟨Finset.mem_univ _,fun q _ => ?_⟩
    induction M q <;> simp_all [TM2.SupportsStmt]
  have hB : TM1.Supports N B := TM2to1.tr_supports M hU
  let C := TM1to0.trStmts N B
  have hC : TM0.Supports P (C : Set _) := TM1to0.tr_supports N hB
  let : Inhabited {l // l ∈ C} := ⟨⟨default,hC.1⟩⟩
  have hs : (none,none) ∈ C := by
    change (none,none) ∈ (TM1.stmts N B) ×ˢ (Finset.univ : Finset (Store S))
    exact Finset.mem_product.mpr ⟨Finset.none_mem_insertNone,Finset.mem_univ _⟩
  refine ⟨{l // l ∈ C},inferInstance,inferInstance,FiniteTM0.machine P C hC,default,⟨(none,none),hs⟩,TapeSafety.finite_preserves N B hB (TapeSafety.safe_tr M),fun w => ?_⟩
  apply part_map_injective (FiniteTM0.embed_injective C)
  rw [←FiniteTM0.eval_embed P C hC]
  change StateTransition.eval (TM0.step P) (TM1to0.trCfg N ⟨some (.normal start),none,tape w⟩) = _
  rw [eval_post M start hM]
  simp only [Part.map_map]
  rfl

end WordEvaluator
end FiniteAlgebraicEnvelopes.MachineRealization

namespace FiniteAlgebraicEnvelopes.MachineRealization.TapeFold
open Turing Relation Compiler.Simulator
variable {K : Type} {Γ : K → Type} {Λ : Type} [Inhabited Λ]

 def Marked (s : OneSided.Cfg (Cell (TM2to1.Γ' K Γ)) (Side × Λ)) : Prop :=
  ∀ n, (s.cell n).pos.1 = decide (n=0) ∧ (s.cell n).neg.1 = false

 theorem marked_step (M : TM0.Machine (TM2to1.Γ' K Γ) Λ) (start : Λ)
    (hM : TapeSafety.Preserves M) {s t : OneSided.Cfg (Cell (TM2to1.Γ' K Γ)) (Side × Λ)}
    (hs : Marked s) (hst : OneSided.step (machine M start) s = some t) : Marked t := by
  unfold OneSided.step machine at hst
  cases hc : M s.state.2 (read s.state.1 (s.cell s.pos)) with
  | none => simp only [hc,Option.map_none] at hst; cases hst
  | some cmd =>
    simp only [hc,Option.map_some,Option.some.injEq] at hst
    subst t
    intro n
    dsimp only [OneSided.Cfg.cell]
    by_cases hn : n = s.pos
    · subst n
      rw [Function.update_self]
      cases hd : cmd.2 with
      | move d => simpa only [move_write] using hs s.pos
      | write b =>
        have hp := hM s.state.2 (read s.state.1 (s.cell s.pos)) cmd.1 b (by rw [←hd]; exact hc)
        cases he : s.state.1 <;> simp only [he,read] at hp
        · exact ⟨hp.trans (hs s.pos).1,(hs s.pos).2⟩
        · exact ⟨(hs s.pos).1,hp.trans (hs s.pos).2⟩
    · rw [Function.update_of_ne hn]
      exact hs n

 theorem marked_run (M : TM0.Machine (TM2to1.Γ' K Γ) Λ) (start : Λ)
    (hM : TapeSafety.Preserves M) {s t : OneSided.Cfg (Cell (TM2to1.Γ' K Γ)) (Side × Λ)}
    (hs : Marked s) (hst : ReflTransGen (fun a b => OneSided.step (machine M start) a = some b) s t) : Marked t := by
  induction hst with
  | refl => exact hs
  | tail _ h ih => exact marked_step M start hM ih h

end FiniteAlgebraicEnvelopes.MachineRealization.TapeFold

namespace FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral

section
open Turing Relation Compiler.Simulator TapeFold Turing.PartrecToTM2 StackLift RawTM StackTape
variable {S : Type} {Λ : Type} [Inhabited Λ]
abbrev Gamma (S : Type) := Cell (TM2to1.Γ' K' (fun _ => Symbol S))

theorem cell_ext (a b : Cell (TM2to1.Γ' K' (fun _ => Symbol S)))
    (ho : a.origin=b.origin) (hp : a.pos=b.pos) (hn : a.neg=b.neg) : a=b := by
  cases a; cases b; cases ho; cases hp; cases hn; rfl

def blank : Gamma S := ⟨false,default,default⟩
def input (a : S) : Gamma S := ⟨false,(false,slice a),default⟩
def raw (w : List S) : ℕ → Gamma S := Stream'.appendStream' (w.map input) (Stream'.const blank)
def canon (q : Λ) (w : List S) : OneSided.Cfg (Gamma S) (Side × Λ) :=
  ⟨(.pos,q),0,fun n => ⟨decide (n=0),(tape w).nth n,(tape w).nth (-(n+1:ℤ))⟩⟩

omit [Inhabited Λ] in
theorem canon_rel (q : Λ) (w : List S) : Rel (⟨q,tape w⟩ : TM0.Cfg _ _) (canon q w) := by
  refine ⟨rfl,fun n => ?_⟩
  simp [canon,position]

theorem tape_neg (w : List S) (n : ℕ) : (tape w).nth (-(n+1:ℤ)) = default := by
  change ListBlank.nth (∅ : ListBlank _) n = default
  rfl

theorem tape_fst (w : List S) (n : ℕ) : ((tape w).nth n).1 = decide (n=0) := by
  rw [tape,Tape.mk'_nth_nat]
  cases n with
  | zero => simpa only [ListBlank.nth_zero,decide_true] using TM2to1.addBottom_head_fst (stackList w)
  | succ n => exact TM2to1.addBottom_nth_succ_fst _ n

omit [Inhabited Λ] in
theorem canon_marked (q : Λ) (w : List S) : Marked (canon q w) := by
  intro n
  exact ⟨tape_fst w n,congrArg Prod.fst (tape_neg w n)⟩

theorem raw_cell (w : List S) (n : ℕ) : raw w n = ⟨false,(false,(stackList w).nth n),default⟩ := by
  induction w generalizing n with
  | nil => simp [raw,blank,stackList,ListBlank.nth_mk]; rfl
  | cons a w ih =>
    cases n with
    | zero => rfl
    | succ n => simpa only [raw,List.map_cons,Stream'.appendStream',Stream'.cons,stackList,ListBlank.nth_mk,List.getI_cons_succ] using ih n

def mark (c : Gamma S) : Gamma S := ⟨true,(true,c.pos.2),c.neg⟩
def clear (c : Gamma S) : Gamma S := ⟨false,(false,c.pos.2),c.neg⟩

omit [Inhabited Λ] in
theorem canon_cells (q : Λ) (w : List S) : (canon q w).cell = Function.update (raw w) 0 (mark (raw w 0)) := by
  funext n
  have hh : (canon q w).cell n = ⟨decide (n=0),(decide (n=0),(stackList w).nth n),default⟩ := by
    apply cell_ext
    · rfl
    · exact Prod.ext (tape_fst w n) (by
        change ((tape w).nth (n:ℤ)).2 = _
        rw [tape,Tape.mk'_nth_nat]
        exact TM2to1.addBottom_nth_snd (stackList w) n)
    · exact tape_neg w n
  rw [hh]
  by_cases hn : n=0
  · subst n
    rw [Function.update_self,raw_cell]
    rfl
  · rw [Function.update_of_ne hn,raw_cell]
    simp only [hn,decide_false]

omit [Inhabited Λ] in
theorem canon_clear (q : Λ) (w : List S) :
    Function.update (canon q w).cell 0 (clear ((canon q w).cell 0)) = raw w := by
  rw [canon_cells]
  simp only [Function.update_self]
  have hh : clear (mark (raw w 0)) = raw w 0 := by rw [raw_cell]; rfl
  rw [hh,Function.update_idem,Function.update_eq_self]

omit [Inhabited Λ] in
theorem rel_canon_unique {s : OneSided.Cfg (Gamma S) (Side × Λ)}
    (q : Λ) (w : List S) (hr : Rel (⟨q,tape w⟩ : TM0.Cfg _ _) s) (hm : Marked s) : s = canon q w := by
  have hh := congrArg Prod.fst (read_head hr)
  have hb : (tape w).head.1 = true := TM2to1.addBottom_head_fst _
  rw [hb] at hh
  have hp : s.state.1 = .pos ∧ s.pos = 0 := by
    cases hd : s.state.1 with
    | pos =>
      simp only [hd,TapeFold.read] at hh
      rw [(hm s.pos).1] at hh
      exact ⟨rfl,of_decide_eq_true hh⟩
    | neg => simp only [hd,TapeFold.read,(hm s.pos).2] at hh; cases hh
  rcases s with ⟨⟨d,l⟩,p,c⟩
  obtain ⟨rfl,rfl⟩ := hp
  obtain ⟨rfl,hc⟩ := hr
  congr 1
  funext n
  obtain ⟨ho,hp,hn⟩ := hc n
  apply cell_ext
  · exact ho
  · simpa only [canon,position,Int.natCast_zero,sub_zero] using hp
  · simpa only [canon,position,Int.natCast_zero,sub_zero] using hn

end

open Turing Relation Compiler.Simulator TapeFold Turing.PartrecToTM2 StackLift RawTM StackTape
variable {S Λ : Type} [Inhabited Λ]

theorem folded_eval (M : TM0.Machine (TM2to1.Γ' K' (fun _ => Symbol S)) Λ)
    (start stop : Λ) (hm : TapeSafety.Preserves M) {f : List S →. List S}
    (hM : ∀ w, StateTransition.eval (TM0.step M) ⟨start,tape w⟩ =
      (f w).map (fun out => ⟨stop,tape out⟩)) (w : List S) :
    StateTransition.eval (OneSided.step (TapeFold.machine M start)) (canon start w) =
      (f w).map (canon stop) := by
  apply Part.ext
  intro s
  constructor
  · intro hs
    obtain ⟨c,hc,hce⟩ := StateTransition.tr_eval_rev (TapeFold.respects M start) (canon_rel start w) hs
    rw [hM] at hce
    obtain ⟨out,hout,rfl⟩ := (Part.mem_map_iff _).mp hce
    have hmarked := marked_run M start hm (canon_marked start w) (StateTransition.mem_eval.mp hs).1
    rw [rel_canon_unique stop out hc hmarked]
    exact Part.mem_map _ hout
  · intro hs
    obtain ⟨out,hout,rfl⟩ := (Part.mem_map_iff _).mp hs
    have hb : (⟨stop,tape out⟩ : TM0.Cfg _ _) ∈ StateTransition.eval (TM0.step M) ⟨start,tape w⟩ := by
      rw [hM]; exact Part.mem_map _ hout
    obtain ⟨s,hs,hse⟩ := StateTransition.tr_eval (TapeFold.respects M start) (canon_rel start w) hb
    have hmarked := marked_run M start hm (canon_marked start w) (StateTransition.mem_eval.mp hse).1
    exact rel_canon_unique stop out hs hmarked ▸ hse

end FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral

namespace FiniteAlgebraicEnvelopes.MachineRealization.After
open Relation StateTransition
variable {α β : Type*} (f : α → Option α) (g : β → Option β) (lift finish : α → β)
variable (hs : ∀ a, g (lift a) = (f a).elim (some (finish a)) (fun b => some (lift b)))
variable (hf : ∀ a, g (finish a) = none)
include hs hf

theorem path_cases {a : α} {z : β} (h : Reaches g (lift a) z) :
    (∃ b, Reaches f a b ∧ z=lift b) ∨ (∃ b, b ∈ eval f a ∧ z=finish b) := by
  induction h with
  | refl => exact Or.inl ⟨a,.refl,rfl⟩
  | @tail z z' _ hz ih =>
    change g z = some z' at hz
    rcases ih with ⟨b,hb,rfl⟩ | ⟨b,hb,rfl⟩
    · rw [hs] at hz
      cases hc : f b with
      | none =>
        simp only [hc,Option.elim_none,Option.some.injEq] at hz
        exact Or.inr ⟨b,mem_eval.mpr ⟨hb,hc⟩,hz.symm⟩
      | some c =>
        simp only [hc,Option.elim_some,Option.some.injEq] at hz
        exact Or.inl ⟨c,hb.tail hc,hz.symm⟩
    · rw [hf] at hz; cases hz

omit hf in
theorem lift_reaches {a b : α} (h : Reaches f a b) : Reaches g (lift a) (lift b) := by
  induction h with
  | refl => exact .refl
  | tail _ hc ih => exact ih.tail (by rw [hs,hc]; rfl)

theorem eval_lift (a : α) : eval g (lift a) = (eval f a).map finish := by
  apply Part.ext
  intro z
  constructor
  · intro hz
    obtain ⟨hp,hz⟩ := mem_eval.mp hz
    rcases path_cases f g lift finish hs hf hp with ⟨b,_,rfl⟩ | ⟨b,hb,rfl⟩
    · rw [hs] at hz
      cases hc : f b <;> simp [hc] at hz
    · exact Part.mem_map _ hb
  · intro hz
    obtain ⟨b,hb,rfl⟩ := (Part.mem_map_iff _).mp hz
    obtain ⟨hr,hb⟩ := mem_eval.mp hb
    apply mem_eval.mpr
    exact ⟨(lift_reaches f g lift finish hs hr).tail (by rw [hs,hb]; rfl),hf b⟩

end FiniteAlgebraicEnvelopes.MachineRealization.After

namespace FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral

section
open Turing Relation Compiler.Simulator TapeFold Turing.PartrecToTM2 StackLift RawTM StackTape
variable {S Λ : Type} [Inhabited Λ]
abbrev State (Λ : Type) := Option (Option (Side × Λ))

def wrapper (M : TM0.Machine (TM2to1.Γ' K' (fun _ => Symbol S)) Λ) (start : Λ) :
    Machine (State Λ) (Gamma S) :=
  ⟨none,fun q a => match q with
    | none => some ⟨some (some (.pos,start)),mark a,.stay⟩
    | some none => none
    | some (some q) => match (TapeFold.machine M start).transition q a with
      | none => some ⟨some none,clear a,.stay⟩
      | some c => some ⟨some (some c.state),c.write,c.move⟩⟩

def lift (s : OneSided.Cfg (Gamma S) (Side × Λ)) : OneSided.Cfg (Gamma S) (State Λ) :=
  ⟨some (some s.state),s.pos,s.cell⟩
def finish (s : OneSided.Cfg (Gamma S) (Side × Λ)) : OneSided.Cfg (Gamma S) (State Λ) :=
  ⟨some none,s.pos,Function.update s.cell s.pos (clear (s.cell s.pos))⟩
def initial (w : List S) : OneSided.Cfg (Gamma S) (State Λ) := ⟨none,0,raw w⟩
def final (w : List S) : OneSided.Cfg (Gamma S) (State Λ) := ⟨some none,0,raw w⟩

variable (M : TM0.Machine (TM2to1.Γ' K' (fun _ => Symbol S)) Λ) (start : Λ)
theorem wrapper_lift (s : OneSided.Cfg (Gamma S) (Side × Λ)) :
    OneSided.step (wrapper M start) (lift s) =
      (OneSided.step (TapeFold.machine M start) s).elim (some (finish s)) (fun t => some (lift t)) := by
  simp only [OneSided.step,lift,wrapper]
  cases hc : (TapeFold.machine M start).transition s.state (s.cell s.pos) with
  | none => rfl
  | some cmd => cases cmd.move <;> rfl

theorem wrapper_finish (s : OneSided.Cfg (Gamma S) (Side × Λ)) :
    OneSided.step (wrapper M start) (finish s) = none := rfl

theorem wrapper_initial (w : List S) : OneSided.step (wrapper M start) (initial w) = some (lift (canon start w)) := by
  simp only [OneSided.step,wrapper,initial,Option.map_some,lift,canon]
  congr 2
  exact (canon_cells start w).symm

omit [Inhabited Λ] in
theorem finish_canon (q : Λ) (w : List S) : finish (canon q w) = final (Λ := Λ) w := by
  simp only [finish,canon,final]
  congr 1
  exact canon_clear q w

theorem wrapper_eval (stop : Λ) (hm : TapeSafety.Preserves M) {f : List S →. List S}
    (hM : ∀ w, StateTransition.eval (TM0.step M) ⟨start,tape w⟩ =
      (f w).map (fun out => ⟨stop,tape out⟩)) (w : List S) :
    StateTransition.eval (OneSided.step (wrapper M start)) (initial w) = (f w).map (final (Λ := Λ)) := by
  rw [StateTransition.reaches_eval (ReflTransGen.single (wrapper_initial M start w)),
    After.eval_lift (OneSided.step (TapeFold.machine M start)) (OneSided.step (wrapper M start)) lift finish
      (wrapper_lift M start) (wrapper_finish M start),folded_eval M start stop hm hM]
  simp only [Part.map_map,Function.comp_def,finish_canon]

end

open Turing Compiler.Simulator Turing.PartrecToTM2 StackLift StackTape
variable {S : Type} [DecidableEq S]

instance instFintypeK'_solutions : Fintype K' := ⟨{.main,.rev,.aux,.stack},by intro k; cases k <;> simp⟩

instance instDecidableEqΓ'K'Symbol : DecidableEq (TM2to1.Γ' K' (fun _ => Symbol S)) := by
  unfold TM2to1.Γ'; infer_instance

def output (c : Gamma S) : Option S := match c.pos.2 .main with
  | some (.inr a) => if c = input a then some a else none
  | _ => none

def alphabet : Alphabet S (Gamma S) where
  blank := blank
  input := input
  output := output
  output_input a := by simp [output,input,slice]
  output_blank := rfl

theorem output_decode (c : Gamma S) (a : S) (he : output c = some a) : c = input a := by
  unfold output at he
  cases hc : c.pos.2 .main with
  | none => simp [hc] at he
  | some s =>
    cases s with
    | inl b => simp [hc] at he
    | inr b =>
      simp only [hc] at he
      split_ifs at he with h
      · cases he; exact h

end FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral

namespace FiniteAlgebraicEnvelopes.Compiler.Simulator
open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ)

theorem take_constant (a : Γ) (n : ℕ) : Stream'.take n (Stream'.const a) = List.replicate n a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Stream'.take_succ,Stream'.tail_const,ih,List.replicate_succ]; rfl

theorem interpret_content (c : Tape (S := S) (Γ := Γ) (Q := Q)) :
    semanticContent (interpret A c) = Stream'.appendStream' ((c.left.reverse ++ c.right).map Tag.work) (Stream'.const A.blank) := by
  simp [semanticContent,interpret,List.map_append,List.map_reverse,Stream'.append_append_stream]

theorem semanticReturns_iff {c : Tape (S := S) (Γ := Γ) (Q := Q)} {w : List S} :
    SemanticReturns A (interpret A c) w ↔ Returns A c w := by
  refine ⟨?_,returns_interpret A⟩
  rintro ⟨tail,hh⟩
  let L := (c.left.reverse ++ c.right).map Tag.work
  let W := w.map A.input ++ [A.blank]
  have ht : semanticContent (interpret A c) = Stream'.appendStream' W tail := by
    simpa only [W,Stream'.append_append_stream,Stream'.appendStream'] using hh
  have hsmall : Stream'.take W.length (semanticContent (interpret A c)) = W := by
    rw [ht,Stream'.take_append_of_le_length _ _ _ (le_refl _),List.take_length]
  have hlarge : Stream'.take (L.length+W.length) (semanticContent (interpret A c)) = L++List.replicate W.length A.blank := by
    rw [interpret_content A,←Stream'.append_take,take_constant]
  have hp := Stream'.take_prefix_take_left W.length (L.length+W.length)
    (semanticContent (interpret A c)) (by omega)
  rw [hsmall,hlarge] at hp
  obtain ⟨rest,he⟩ := hp
  exact ⟨W.length,rest,by simpa only [W,List.append_assoc,List.singleton_append] using he.symm⟩

end FiniteAlgebraicEnvelopes.Compiler.Simulator

namespace FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral
open Turing Relation Compiler Compiler.Simulator TapeFold Turing.PartrecToTM2 StackLift RawTM StackTape
variable {S Λ : Type} [DecidableEq S] [Inhabited Λ]
variable (M : TM0.Machine (TM2to1.Γ' K' (fun _ => Symbol S)) Λ) (start : Λ)

theorem view_initial (w : List S) : OneSided.view (interpret alphabet (initialTape alphabet (wrapper M start) w)) = initial (Λ := Λ) w := by
  simp [OneSided.view,initialTape,interpret,semanticContent,filledWork,Function.comp_def,initial,wrapper,raw,alphabet,List.map_map]

omit [Inhabited Λ] in
theorem returns_final {s : SemanticTape (Gamma S) (State Λ)} {out : List S}
    (hs : OneSided.view s = final out) : SemanticReturns alphabet s out := by
  have hc := congrArg OneSided.Cfg.cell hs
  change semanticContent s = raw out at hc
  refine ⟨Stream'.const blank,?_⟩
  rw [hc]
  change Stream'.appendStream' (out.map input) (Stream'.const blank) =
    Stream'.appendStream' (out.map input) (Stream'.cons blank (Stream'.const blank))
  congr 1
  funext n
  cases n <;> rfl

 theorem realizes (stop : Λ) (hm : TapeSafety.Preserves M) {f : List S →. List S}
    (hM : ∀ w, StateTransition.eval (TM0.step M) ⟨start,tape w⟩ =
      (f w).map (fun out => ⟨stop,tape out⟩)) : Word.Realizes alphabet (wrapper M start) f := by
  intro w out
  constructor
  · intro ho
    have hfold : final (Λ := Λ) out ∈ StateTransition.eval (OneSided.step (wrapper M start)) (initial w) := by
      rw [wrapper_eval M start stop hm hM]
      exact Part.mem_map _ ho
    obtain ⟨s,hs,he⟩ := StateTransition.tr_eval (OneSided.respects (wrapper M start)) (view_initial M start w) hfold
    obtain ⟨hr,hhalt⟩ := StateTransition.mem_eval.mp he
    obtain ⟨c,hc,hcs⟩ := semanticRun_lift alphabet (wrapper M start) hr
    refine ⟨c,hc,?_,?_⟩
    · apply (semantic_halted_iff alphabet (wrapper M start) c).mp
      rw [hcs]; exact hhalt
    · apply (semanticReturns_iff alphabet).mp
      rw [hcs]
      exact returns_final hs
  · rintro ⟨c,hc,hh,ho⟩
    have he : interpret alphabet c ∈ StateTransition.eval (semanticStep (wrapper M start))
        (interpret alphabet (initialTape alphabet (wrapper M start) w)) :=
      StateTransition.mem_eval.mpr ⟨unboundedRun_interpret alphabet (wrapper M start) hc,
        (semantic_halted_iff alphabet (wrapper M start) c).mpr hh⟩
    obtain ⟨s,hs,he⟩ := StateTransition.tr_eval_rev (OneSided.respects (wrapper M start)) (view_initial M start w) he
    rw [wrapper_eval M start stop hm hM] at he
    obtain ⟨out',ho',rfl⟩ := (Part.mem_map_iff _).mp he
    have hu : out' = out := semanticReturns_unique alphabet (returns_final hs) (returns_interpret alphabet ho)
    exact hu ▸ ho'

end FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral

namespace FiniteAlgebraicEnvelopes.MachineRealization.WordEvaluator
open Turing Compiler Compiler.Simulator FoldLiteral
variable {S : Type} [Fintype S] [Primcodable S]
/-- Every algorithmic partial word function has an actual one-sided finite
    machine with the literal first-blank readout used by the finite compiler. -/
theorem exists_machine {f : List S →. List S} (hf : Partrec f) :
    ∃ (Γ Q : Type) (_ : Fintype Γ) (_ : Fintype Q)
      (A : Alphabet S Γ) (M : Machine Q Γ),
      (∀ g a, A.output g = some a → g = A.input a) ∧ Word.Realizes A M f := by
  classical
  obtain ⟨Λ,hΛ,iΛ,M,start,stop,hm,hM⟩ := exists_safe_tape hf
  let : Fintype Λ := hΛ
  let : Inhabited Λ := iΛ
  exact ⟨Gamma S,State Λ,inferInstance,inferInstance,alphabet,wrapper M start,
    output_decode,realizes M start stop hm hM⟩

end FiniteAlgebraicEnvelopes.MachineRealization.WordEvaluator

namespace FiniteAlgebraicEnvelopes.WordProgramming
open Encodable
variable {S : Type} [Primcodable S]

/-- An acceptable word-program numbering obtained from the pinned universal
    partial-recursive evaluator. Invalid decoded results remain undefined. -/
def eval (c : Nat.Partrec.Code) (w : List S) : Part (List S) :=
  (c.eval (encode w)).bind (fun n => Part.ofOption (decode n))

theorem partrec_eval : Partrec₂ (eval (S := S)) :=
  ((Nat.Partrec.Code.eval_part.comp Computable.fst
    (Computable.encode.comp Computable.snd)).bind
      ((Computable.decode.comp Computable.snd).ofOption).to₂).to₂

end FiniteAlgebraicEnvelopes.WordProgramming

end OAI
end

section
-- module Solutions.OAIFAE.UniformMachines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Parameterized effective machine realization and uniform finite data.
-/

namespace FiniteAlgebraicEnvelopes.MachineRealization.ParameterMachine
open Compiler.Simulator OneSided Turing Relation
variable {S Γ Q : Type*}

inductive State (Q : Type*) (n : ℕ)
  | start | scan | emit : Fin (n+2) → State Q n
  | rewind | run : Q → State Q n
  deriving DecidableEq, Fintype

variable (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]

def machine (p : S) (n : ℕ) : Machine (State Q n) (Bool × Γ) where
  initial := .start
  transition q a := match q with
    | .start => some ⟨.scan,(true,a.2),.stay⟩
    | .scan => if a.2=A.blank then some ⟨.emit ⟨0,by omega⟩,a,.stay⟩
        else some ⟨.scan,a,.right⟩
    | .emit k => if h : k.val<n+1 then
        some ⟨.emit ⟨k.val+1,by omega⟩,(a.1,A.input p),.right⟩
        else some ⟨.rewind,a,.stay⟩
    | .rewind => if a.1 then some ⟨.run M.initial,(false,a.2),.stay⟩
        else some ⟨.rewind,a,.left⟩
    | .run q => (M.transition q a.2).map fun c => ⟨.run c.state,(false,c.write),c.move⟩

def content (w : List S) : ℕ → Γ := Stream'.appendStream' (w.map A.input) (Stream'.const A.blank)
def marked (w : List S) : ℕ → Bool × Γ := fun i => (decide (i=0),content A w i)
def flat (w : List S) : ℕ → Bool × Γ := fun i => (false,content A w i)

omit [DecidableEq Γ] in
 theorem input_ne_blank (a : S) : A.input a≠A.blank := by
  intro h
  have hh := A.output_input a
  rw [h,A.output_blank] at hh
  cases hh

omit [DecidableEq Γ] in
 theorem content_beyond (w : List S) (i : ℕ) (hi : w.length ≤ i) : content A w i=A.blank := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hi
  simpa [content, Stream'.const] using append_at (w.map A.input) (Stream'.const A.blank) j

omit [DecidableEq Γ] in
 theorem content_before (w : List S) (i : ℕ) (hi : i<w.length) :
    content A w i=A.input w[i] := by
  induction w generalizing i with
  | nil => simp at hi
  | cons a w ih =>
    cases i with
    | zero => rfl
    | succ i =>
      exact ih i (by simpa using hi)

omit [DecidableEq Γ] in
 theorem marked_write (w : List S) (p : S) :
    Function.update (marked A w) w.length (decide (w.length=0),A.input p)=marked A (w++[p]) := by
  funext i
  apply Prod.ext
  · by_cases h : i=w.length
    · subst i; simp [marked]
    · simp [Function.update_of_ne h,marked]
  · by_cases h : i<w.length
    · have hn : i≠w.length := Nat.ne_of_lt h
      rw [Function.update_of_ne hn]
      change content A w i=content A (w++[p]) i
      rw [content_before A w i h,content_before A _ i (by simp; omega)]
      congr 1
      simp [List.getElem_append_left h]
    · by_cases he : i=w.length
      · subst i
        rw [Function.update_self]
        change A.input p=content A (w++[p]) w.length
        rw [content_before A _ _ (by simp)]
        simp
      · rw [Function.update_of_ne he]
        change content A w i=content A (w++[p]) i
        rw [content_beyond A w i (by omega),content_beyond A _ i (by simp; omega)]

omit [DecidableEq Γ] in
 theorem marked_clear (w : List S) :
    Function.update (marked A w) 0 (false,content A w 0)=flat A w := by
  funext i
  by_cases hi : i=0
  · subst i; simp [flat]
  · simp [marked,flat,hi]

variable (p : S) (n : ℕ)

 theorem start_step (w : List S) :
    step (machine A M p n) ⟨.start,0,flat A w⟩=some ⟨.scan,0,marked A w⟩ := by
  simp only [step,machine,flat,Option.map_some]
  congr 2
  funext i
  by_cases hi : i=0
  · subst i; simp [marked]
  · simp [marked,flat,hi]

 theorem scan_step (w : List S) (i : ℕ) (hi : i<w.length) :
    step (machine A M p n) ⟨.scan,i,marked A w⟩=some ⟨.scan,i+1,marked A w⟩ := by
  have hb : content A w i≠A.blank := by rw [content_before A w i hi]; exact input_ne_blank A _
  simp only [step,machine,marked,ite_eq_right hb,Option.map_some]
  congr 2
  exact Function.update_eq_self _ _

 theorem scan_end (w : List S) :
    step (machine A M p n) ⟨.scan,w.length,marked A w⟩=
      some ⟨.emit ⟨0,by omega⟩,w.length,marked A w⟩ := by
  simp only [step,machine,marked,content_beyond A w w.length le_rfl,↓reduceIte,Option.map_some]
  have he : (decide (w.length=0),A.blank)=marked A w w.length := by
    simp [marked,content_beyond A w w.length le_rfl]
  rw [he,Function.update_eq_self]

 theorem scan_run (w : List S) :
    ReflTransGen (fun a b => step (machine A M p n) a=some b)
      ⟨.scan,0,marked A w⟩ ⟨.scan,w.length,marked A w⟩ := by
  have h (i : ℕ) (hi : i ≤ w.length) :
      ReflTransGen (fun a b => step (machine A M p n) a=some b)
        ⟨.scan,0,marked A w⟩ ⟨.scan,i,marked A w⟩ := by
    induction i with
    | zero => exact .refl
    | succ i ih => exact (ih (by omega)).tail (scan_step A M p n w i (by omega))
  exact h _ le_rfl

 theorem emit_step (w : List S) (k : Fin (n+2)) (hk : k.val<n+1) :
    step (machine A M p n) ⟨.emit k,w.length,marked A w⟩=
      some ⟨.emit ⟨k.val+1,by omega⟩,(w++[p]).length,marked A (w++[p])⟩ := by
  simp only [step,machine,dite_eq_left hk,marked,Option.map_some,List.length_append,List.length_singleton]
  congr 2
  exact marked_write A w p

 theorem emit_end (w : List S) :
    step (machine A M p n) ⟨.emit ⟨n+1,by omega⟩,w.length,marked A w⟩=
      some ⟨.rewind,w.length,marked A w⟩ := by
  simp only [step,machine,dite_eq_right (Nat.lt_irrefl (n+1)),Option.map_some]
  rw [Function.update_eq_self]

 theorem emit_run (w : List S) :
    ReflTransGen (fun a b => step (machine A M p n) a=some b)
      ⟨.emit ⟨0,by omega⟩,w.length,marked A w⟩
      ⟨.emit ⟨n+1,by omega⟩,(w++List.replicate (n+1) p).length,
        marked A (w++List.replicate (n+1) p)⟩ := by
  have h (i : ℕ) (hi : i<n+2) :
      ReflTransGen (fun a b => step (machine A M p n) a=some b)
      ⟨.emit ⟨0,by omega⟩,w.length,marked A w⟩
      ⟨.emit ⟨i,hi⟩,(w++List.replicate i p).length,marked A (w++List.replicate i p)⟩ := by
    induction i with
    | zero => simpa using (ReflTransGen.refl (a:= (⟨.emit ⟨0,by omega⟩,w.length,marked A w⟩ : Cfg _ (State Q n))))
    | succ i ih =>
      have hh := (ih (by omega)).tail (emit_step A M p n (w++List.replicate i p) ⟨i,by omega⟩ (by change i<n+1; omega))
      simpa only [List.replicate_succ',List.append_assoc] using hh
  exact h _ (by omega)

 theorem rewind_step (w : List S) (i : ℕ) :
    step (machine A M p n) ⟨.rewind,i+1,marked A w⟩=some ⟨.rewind,i,marked A w⟩ := by
  simp only [step,machine,marked,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,decide_false,
    Bool.false_eq_true, ↓reduceIte,Nat.add_sub_cancel,Option.map_some]
  rw [show (false,content A w (i+1))=marked A w (i+1) by simp [marked]]
  rw [Function.update_eq_self]

 theorem rewind_run (w : List S) (i : ℕ) :
    ReflTransGen (fun a b => step (machine A M p n) a=some b)
      ⟨.rewind,i,marked A w⟩ ⟨.rewind,0,marked A w⟩ := by
  induction i with
  | zero => exact .refl
  | succ i ih => exact ReflTransGen.head (rewind_step A M p n w i) ih

 theorem rewind_end (w : List S) :
    step (machine A M p n) ⟨.rewind,0,marked A w⟩=some ⟨.run M.initial,0,flat A w⟩ := by
  simp only [step,machine,marked,decide_true,↓reduceIte,Option.map_some]
  congr 2
  exact marked_clear A w

 theorem initialize_run (w : List S) :
    ReflTransGen (fun a b => step (machine A M p n) a=some b)
      ⟨.start,0,flat A w⟩
      ⟨.run M.initial,0,flat A (w++List.replicate (n+1) p)⟩ := by
  have ht : ReflTransGen (fun a b => step (machine A M p n) a=some b)
      ⟨.start,0,flat A w⟩ ⟨.scan,0,marked A w⟩ := .single (start_step A M p n w)
  exact ((((ht.trans (scan_run A M p n w)).tail
    (scan_end A M p n w)).trans (emit_run A M p n w)).tail
      (emit_end A M p n _)).trans ((rewind_run A M p n _ _).tail (rewind_end A M p n _))

def lift (c : Cfg Γ Q) : Cfg (Bool × Γ) (State Q n) :=
  ⟨.run c.state,c.pos,fun i => (false,c.cell i)⟩

 theorem step_lift (c : Cfg Γ Q) :
    step (machine A M p n) (lift n c)=(step M c).map (lift n) := by
  simp only [step,machine,lift,Option.map_map]
  congr 1
  funext cmd
  simp only [Function.comp_apply]
  congr 1
  funext i
  by_cases hi : i=c.pos
  · subst i; simp
  · simp [Function.update_of_ne hi]

 theorem lift_respects : StateTransition.Respects (step M) (step (machine A M p n))
    (fun a b => lift n a=b) := by
  rintro c _ rfl
  rw [step_lift]
  cases hc : step M c with
  | none => rfl
  | some d => exact ⟨lift n d,rfl,TransGen.single (by rw [step_lift,hc]; rfl)⟩

 theorem eval_lift (c : Cfg Γ Q) :
    StateTransition.eval (step (machine A M p n)) (lift n c)=
      (StateTransition.eval (step M) c).map (lift n) :=
  StateTransition.tr_eval' _ _ _ (lift_respects A M p n) c

 theorem eval_initialized (w : List S) :
    StateTransition.eval (step (machine A M p n)) ⟨.start,0,flat A w⟩=
      (StateTransition.eval (step M)
        ⟨M.initial,0,content A (w++List.replicate (n+1) p)⟩).map (lift n) := by
  have hi : StateTransition.Reaches (step (machine A M p n))
    ⟨.start,0,flat A w⟩ ⟨.run M.initial,0,flat A (w++List.replicate (n+1) p)⟩ :=
    initialize_run A M p n w
  rw [StateTransition.reaches_eval hi]
  exact eval_lift A M p n
    ⟨M.initial,0,content A (w++List.replicate (n+1) p)⟩

def alphabet : Alphabet S (Bool × Γ) where
  blank := (false,A.blank)
  input s := (false,A.input s)
  output x := if x.1 then none else A.output x.2
  output_input s := A.output_input s
  output_blank := A.output_blank

omit [DecidableEq Γ] in
 theorem output_decode (hA : ∀ g a, A.output g=some a → g=A.input a) :
    ∀ g a, (alphabet A).output g=some a → g=(alphabet A).input a := by
  rintro ⟨b,g⟩ a h
  cases b with
  | true => simp [alphabet] at h
  | false => exact congrArg (false,·) (hA g a h)

omit [DecidableEq Γ] in
 theorem initial_view (w : List S) :
    view (interpret A (initialTape A M w))=⟨M.initial,0,content A w⟩ := by
  simp [view,initialTape,interpret,semanticContent,filledWork,Function.comp_def,content]

omit [DecidableEq Γ] in
 theorem returns_iff (w out : List S) :
    (∃ c, ReflTransGen (UnboundedStep A M) (initialTape A M w) c ∧
      Halted A M c ∧ Returns A c out) ↔
    (∃ c, c ∈ StateTransition.eval (step M) ⟨M.initial,0,content A w⟩ ∧
      ∃ t, c.cell=Stream'.appendStream' (out.map A.input) (Stream'.cons A.blank t)) := by
  constructor
  · rintro ⟨c,hc,hh,ho⟩
    have he : interpret A c ∈ StateTransition.eval (semanticStep M)
        (interpret A (initialTape A M w)) :=
      StateTransition.mem_eval.mpr ⟨unboundedRun_interpret A M hc,
        (semantic_halted_iff A M c).mpr hh⟩
    obtain ⟨d,hd,he⟩ := StateTransition.tr_eval_rev (OneSided.respects M) (initial_view A M w) he
    exact ⟨d,he,by rw [←hd]; exact returns_interpret A ho⟩
  · rintro ⟨c,hc,ho⟩
    obtain ⟨s,hs,he⟩ := StateTransition.tr_eval (OneSided.respects M) (initial_view A M w) hc
    obtain ⟨hr,hh⟩ := StateTransition.mem_eval.mp he
    obtain ⟨d,hd,hds⟩ := semanticRun_lift A M hr
    refine ⟨d,hd,?_,?_⟩
    · apply (semantic_halted_iff A M d).mp
      rw [hds]; exact hh
    · apply (semanticReturns_iff A).mp
      rw [hds]
      rw [←hs] at ho
      exact ho

omit [DecidableEq Γ] in
 theorem lift_returns (c : Cfg Γ Q) (out : List S) :
    (∃ t, (lift n c).cell=Stream'.appendStream' (out.map (alphabet A).input)
        (Stream'.cons (alphabet A).blank t)) ↔
    (∃ t, c.cell=Stream'.appendStream' (out.map A.input) (Stream'.cons A.blank t)) := by
  have hm (l : List Γ) (t : Stream' Γ) :
      (fun i => (false,Stream'.appendStream' l t i))=
        Stream'.appendStream' (l.map (false,·)) (fun i => (false,t i)) := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      funext i; cases i with
      | zero => rfl
      | succ i => exact congrFun ih i
  have hs (l : List (Bool × Γ)) (t : Stream' (Bool × Γ)) :
      (fun i => (Stream'.appendStream' l t i).2)=
        Stream'.appendStream' (l.map Prod.snd) (fun i => (t i).2) := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      funext i; cases i with
      | zero => rfl
      | succ i => exact congrFun ih i
  constructor
  · rintro ⟨t,h⟩
    have hh := congrArg (fun f : ℕ → Bool × Γ => fun i => (f i).2) h
    rw [hs] at hh
    refine ⟨fun i => (t i).2,?_⟩
    have ht : (fun i => (Stream'.cons (alphabet A).blank t i).2)=
        Stream'.cons A.blank (fun i => (t i).2) := by
      funext i; cases i <;> rfl
    rw [ht] at hh
    simpa only [lift,alphabet,List.map_map,Function.comp_def] using hh
  · rintro ⟨t,h⟩
    refine ⟨fun i => (false,t i),?_⟩
    change (fun i => (false,c.cell i))=_
    rw [h,hm]
    simp only [List.map_map,Function.comp_def,alphabet]
    congr 1
    funext i; cases i <;> rfl

 theorem realizes {f : List S → Part (List S)} (hM : Compiler.Word.Realizes A M f) :
    Compiler.Word.Realizes (alphabet A) (machine A M p n)
      (fun w => f (w++List.replicate (n+1) p)) := by
  intro w out
  rw [returns_iff]
  have hi : content (alphabet A) w=flat A w := by
    funext i
    induction w generalizing i with
    | nil => rfl
    | cons a w ih => cases i with
      | zero => rfl
      | succ i => exact ih i
  change out ∈ f (w++List.replicate (n+1) p) ↔ _
  rw [hi]
  change out ∈ f _ ↔ ∃ c, c ∈ StateTransition.eval (step (machine A M p n))
    ⟨.start,0,flat A w⟩ ∧ _
  rw [eval_initialized]
  constructor
  · intro ho
    obtain ⟨c,hc,hr⟩ := (returns_iff A M _ out).mp ((hM _ _).mp ho)
    exact ⟨lift n c,Part.mem_map _ hc,(lift_returns A n c out).mpr hr⟩
  · rintro ⟨c,hc,hr⟩
    obtain ⟨d,hd,rfl⟩ := (Part.mem_map_iff _).mp hc
    exact (hM _ _).mpr ((returns_iff A M _ out).mpr
      ⟨d,hd,(lift_returns A n d out).mp hr⟩)

end FiniteAlgebraicEnvelopes.MachineRealization.ParameterMachine

namespace FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode
open Compiler.Simulator ParameterMachine
variable {S Γ Q : Type*}

/-- A common, countably coded state space for all unary-initialized programs. -/
abbrev Control (Q : Type*) := ℕ ⊕ Q

def encode (n : ℕ) : State Q n → Control Q
  | .start => .inl 0
  | .scan => .inl 1
  | .rewind => .inl 2
  | .emit k => .inl (k.val+3)
  | .run q => .inr q

def decode (n : ℕ) : Control Q → Option (State Q n)
  | .inr q => some (.run q)
  | .inl 0 => some .start
  | .inl 1 => some .scan
  | .inl 2 => some .rewind
  | .inl (k+3) => if h : k<n+2 then some (.emit ⟨k,h⟩) else none

@[simp] theorem decode_encode (n : ℕ) (q : State Q n) : decode n (encode n q)=some q := by
  cases q <;> simp [encode,decode]

 theorem encode_injective (n : ℕ) : Function.Injective (encode (Q := Q) n) := by
  intro a b h
  have h' := congrArg (decode n) h
  simpa only [decode_encode, Option.some.injEq] using h'

abbrev Cmd (Q Γ : Type*) := Control Q × ((Bool×Γ) × Move)

variable (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ] (p : S)

def transition (n : ℕ) (q : Control Q) (a : Bool×Γ) : Option (Cmd Q Γ) := match q with
  | .inr r => (M.transition r a.2).map fun c => (.inr c.state,(false,c.write),c.move)
  | .inl k => if k=0 then some (.inl 1,(true,a.2),.stay)
    else if k=1 then if a.2=A.blank then some (.inl 3,a,.stay) else some (.inl 1,a,.right)
    else if k=2 then if a.1 then some (.inr M.initial,(false,a.2),.stay)
      else some (.inl 2,a,.left)
    else if k-3<n+2 then if k-3<n+1 then some (.inl (k+1),(a.1,A.input p),.right)
      else some (.inl 2,a,.stay)
    else none

variable [Fintype Q] [Fintype Γ] [Primcodable Q] [Primcodable Γ]

noncomputable def support (n : ℕ) : List (Control Q) :=
  ((List.range (n+5)).map Sum.inl) ++ (((Finset.univ : Finset Q).toList).map Sum.inr)

omit [Primcodable Q] in
 theorem mem_support (n : ℕ) (q : State Q n) : encode n q ∈ support (Q := Q) n := by
  cases q <;> simp [support,encode]

end FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode

end OAI
end

section
-- module Solutions.OAIFAE.UniformControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Uniform validation, simulation, and finite control.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.Scan.Uniform
open FiniteAlgebraicEnvelopes.Effect.Graph
variable {P H B T : Type*} [Primcodable P] [Primcodable H] [Primcodable B] [Primcodable T]
variable (table : P → Table H B T)
variable (hb : Primrec (fun x : P × H => (table x.1).boundary x.2))
variable (hd : Primrec (fun x : P × H => decide ((table x.1).direction x.2 = .right)))

/-- Only control heads in the supplied literal support are enumerated. The
    ambient coded head type need not be finite. -/
noncomputable def sectorList [Fintype B] [Fintype T] (heads : List H) (n : ℕ) : List (Sector H B T) :=
  heads.flatMap fun q => (wordList (B×T) n).flatMap fun l =>
    (wordList (B×T) n).flatMap fun r =>
      [⟨l,q,r,false,false⟩,⟨l,q,r,false,true⟩,⟨l,q,r,true,false⟩,⟨l,q,r,true,true⟩]

omit [Primcodable H] [Primcodable B] [Primcodable T] in
@[simp] theorem mem_sectorList [Fintype B] [Fintype T] (heads : List H) (n : ℕ) (v : Sector H B T) :
    v ∈ sectorList heads n ↔ v.head ∈ heads ∧ v.left.length ≤ n ∧ v.right.length ≤ n := by
  rcases v with ⟨l,q,r,a,b⟩
  cases a <;> cases b <;> simp [sectorList,Sector.mk.injEq]

variable [Fintype B] [Fintype T]

variable [DecidableEq H] [DecidableEq B] [DecidableEq T]
noncomputable def universeList (heads : List H) (v : Sector H B T) : List (Sector H B T) :=
  (sectorList heads (v.left.length+v.right.length)).filter fun w => baseSkeleton w=baseSkeleton v

omit [DecidableEq H] [DecidableEq T] in
omit [Primcodable H] [Primcodable B] [Primcodable T] in
@[simp] theorem mem_universeList (heads : List H) (v w : Sector H B T) :
    w ∈ universeList heads v ↔ w.head ∈ heads ∧ baseSkeleton w=baseSkeleton v := by
  simp only [universeList,List.mem_filter,mem_sectorList,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h,_,_⟩,he⟩; exact ⟨h,he⟩
  · rintro ⟨h,he⟩
    have hl := skeleton_length he
    exact ⟨⟨h,by omega,by omega⟩,he⟩

noncomputable def componentList (support : P → List H) (x : P × Sector H B T) : List (Sector H B T) :=
  FiniteAlgebraicEnvelopes.Effect.Graph.component (fun a b => decide (step (table x.1) a=some b)) (universeList (support x.1) x.2) x.2

end FiniteAlgebraicEnvelopes.Compiler.Scan.Uniform

namespace FiniteAlgebraicEnvelopes.Compiler.HeadCodec
open Simulator

inductive Static (S : Type*)
  | start | rewind : Resume S → Static S | scan : Resume S → Static S
  | finish | ok
  deriving DecidableEq, Fintype

variable {S Q Q' H C : Type*}

def ofStatic : Static S → Simulator.Head S Q
  | .start => .start
  | .rewind r => .rewind r
  | .scan r => .scan r
  | .finish => .finish
  | .ok => .ok

def dynamic (p : Bool × Q) : Simulator.Head S Q := if p.1 then .left p.2 else .run p.2

def simCode : Simulator.Head S Q ≃ Static S ⊕ (Bool × Q) where
  toFun
    | .start => .inl .start
    | .rewind r => .inl (.rewind r)
    | .scan r => .inl (.scan r)
    | .finish => .inl .finish
    | .ok => .inl .ok
    | .run q => .inr (false,q)
    | .left q => .inr (true,q)
  invFun := Sum.elim ofStatic dynamic
  left_inv q := by cases q <;> rfl
  right_inv q := by
    cases q with
    | inl q => cases q <;> rfl
    | inr q => rcases q with ⟨a,q⟩; cases a <;> rfl

def controlCode : Control.Head S Q ≃ Fin 5 ⊕ Simulator.Head S Q where
  toFun
    | .initial => .inl 0
    | .left => .inl 1
    | .right => .inl 2
    | .workspace => .inl 3
    | .suffix => .inl 4
    | .machine q => .inr q
  invFun
    | .inl k => if k=0 then .initial else if k=1 then .left else if k=2 then .right
      else if k=3 then .workspace else .suffix
    | .inr q => .machine q
  left_inv q := by cases q <;> rfl
  right_inv q := by
    cases q with
    | inl k => fin_cases k <;> rfl
    | inr q => rfl

noncomputable scoped instance staticPrimcodable [Fintype S] : Primcodable (Static S) :=
  Effect.finitePrimcodable _
noncomputable scoped instance simulatorPrimcodable [Fintype S] [Primcodable Q] :
    Primcodable (Simulator.Head S Q) := Primcodable.ofEquiv _ simCode
noncomputable scoped instance controlPrimcodable [Fintype S] [Primcodable Q] :
    Primcodable (Control.Head S Q) := Primcodable.ofEquiv _ controlCode

end FiniteAlgebraicEnvelopes.Compiler.HeadCodec

namespace FiniteAlgebraicEnvelopes.Compiler.HeadCodec
open Simulator
open scoped HeadCodec
variable {S Γ Q Q' P : Type*}

def stateMap (f : Q → Q') : Simulator.Head S Q → Simulator.Head S Q'
  | .start => .start | .rewind r => .rewind r | .scan r => .scan r
  | .run q => .run (f q) | .left q => .left (f q) | .finish => .finish | .ok => .ok

def controlMap (f : Q → Q') : Control.Head S Q → Control.Head S Q'
  | .initial => .initial | .left => .left | .right => .right
  | .workspace => .workspace | .suffix => .suffix | .machine q => .machine (stateMap f q)

variable [Fintype S] [Primcodable P] [Primcodable Q] [Primcodable Q']

omit [Fintype S] [Primcodable P] [Primcodable Q] [Primcodable Q'] in
theorem stateMap_injective {f : Q → Q'} (hf : Function.Injective f) :
    Function.Injective (stateMap (S := S) f) := by
  intro a b h
  cases a <;> cases b <;> simp_all [stateMap]
  all_goals exact hf h

omit [Fintype S] [Primcodable P] [Primcodable Q] [Primcodable Q'] in
theorem controlMap_injective {f : Q → Q'} (hf : Function.Injective f) :
    Function.Injective (controlMap (S := S) f) := by
  intro a b h
  cases a <;> cases b <;> simp_all [controlMap]
  exact stateMap_injective hf h

end FiniteAlgebraicEnvelopes.Compiler.HeadCodec

namespace FiniteAlgebraicEnvelopes.Compiler.HeadCodec
open Simulator
open scoped HeadCodec
variable {S Γ Q P : Type*} [Fintype S] [Fintype Γ] [DecidableEq S] [DecidableEq Γ]
  [Primcodable Γ] [Primcodable Q] [Primcodable P]
variable (A : Alphabet S Γ) (M : P → Machine Q Γ)
  (hinit : Primrec (fun p => (M p).initial))

def staticControl (k : Fin 5) : Control.Head S Q := controlCode.symm (.inl k)

end FiniteAlgebraicEnvelopes.Compiler.HeadCodec

namespace FiniteAlgebraicEnvelopes.Compiler.HeadCodec
open FiniteAlgebraicEnvelopes.Effect
open scoped HeadCodec
variable {S Q : Type*} [Fintype S]

noncomputable def simSupport (qs : List Q) : List (Simulator.Head S Q) :=
  (Scan.finiteList (Static S)).map ofStatic ++ qs.flatMap (fun q => [.run q,.left q])
noncomputable def controlSupport (qs : List Q) : List (Control.Head S Q) :=
  (Scan.finiteList (Fin 5)).map staticControl ++ (simSupport qs).map Control.Head.machine

@[simp] theorem mem_simSupport (qs : List Q) (h : Simulator.Head S Q) :
    h∈simSupport qs ↔ match h with | .run q | .left q => q∈qs | _ => True := by
  cases h <;> simp [simSupport,ofStatic]
  case start => exact ⟨.start,rfl⟩
  case rewind r => exact ⟨.rewind r,rfl⟩
  case scan r => exact ⟨.scan r,rfl⟩
  case finish => exact ⟨.finish,rfl⟩
  case ok => exact ⟨.ok,rfl⟩
  case run q => intro a ha; cases a <;> cases ha
  case left q => intro a ha; cases a <;> cases ha

@[simp] theorem mem_controlSupport (qs : List Q) (h : Control.Head S Q) :
    h∈controlSupport qs ↔ match h with | .machine (.run q) | .machine (.left q) => q∈qs | _ => True := by
  cases h <;> simp only [controlSupport,List.mem_append,List.mem_map,Scan.mem_finiteList,true_and]
  case initial => exact iff_true_intro (Or.inl ⟨0,rfl⟩)
  case left => exact iff_true_intro (Or.inl ⟨1,rfl⟩)
  case right => exact iff_true_intro (Or.inl ⟨2,rfl⟩)
  case workspace => exact iff_true_intro (Or.inl ⟨3,rfl⟩)
  case suffix => exact iff_true_intro (Or.inl ⟨4,rfl⟩)
  case machine h =>
    have hn : ¬∃ a,staticControl a=Control.Head.machine h := by
      rintro ⟨a,ha⟩; fin_cases a <;> cases ha
    simp only [hn,false_or,Control.Head.machine.injEq,exists_eq_right,mem_simSupport]
    cases h <;> rfl

end FiniteAlgebraicEnvelopes.Compiler.HeadCodec

end OAI
end

section
-- module Solutions.OAIFAE.UniformPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Uniform surface and path normalization with recursive compiler interfaces.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.Scan.Uniform
open FiniteAlgebraicEnvelopes.Effect.Graph
variable {H H' B T : Type*} [Fintype B] [Fintype T]

variable [DecidableEq H] [DecidableEq H'] [DecidableEq B] [DecidableEq T]

variable (i : H → H') (hi : Function.Injective i)
  (t : Table H B T) (u : Table H' B T)
  (hd : ∀ q,u.direction (i q)=t.direction q)
  (hc : ∀ q b a,u.cell (i q) b a=(t.cell q b a).map (mapInstruction i))
  (hb : ∀ q,u.boundary (i q)=(t.boundary q).map i)

omit [Fintype B] [Fintype T] [DecidableEq H] [DecidableEq H'] [DecidableEq B] [DecidableEq T] in
include hi in
theorem mapHead_injective : Function.Injective (mapHead (B := B) (T := T) i) := by
  intro v w hh
  cases v; cases w
  simp only [mapHead,Sector.mk.injEq] at hh ⊢
  exact ⟨hh.1,hi hh.2.1,hh.2.2⟩

end FiniteAlgebraicEnvelopes.Compiler.Scan.Uniform

namespace FiniteAlgebraicEnvelopes.Compiler.Scan.Uniform
open FiniteAlgebraicEnvelopes.Effect
variable {P H B T : Type*} [Primcodable P] [Primcodable H] [Primcodable B] [Primcodable T]
  [Fintype B] [Fintype T] [DecidableEq H] [DecidableEq B] [DecidableEq T]

variable [LinearOrder (Sector H B T)]
noncomputable def representative (table : P → Table H B T) (support : P → List H)
    (entry success : Sector H B T → Bool) (x : P × Sector H B T) : Sector H B T :=
  (priorityList entry success (componentList table support x)).min?.getD x.2

end FiniteAlgebraicEnvelopes.Compiler.Scan.Uniform

namespace FiniteAlgebraicEnvelopes.Compiler
open HeadCodec FiniteAlgebraicEnvelopes.Effect
open scoped HeadCodec

namespace Surface.Uniform
variable {P S Γ Q : Type*} [Fintype S] [Fintype Γ] [Primcodable Q] [Primcodable P]
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
variable (blank : Γ) (rep : P × Control.Sector S Γ Q → Control.Sector S Γ Q)

def internalPreprocess (x : P × Control.Sector S Γ Q) : List (Sector S Γ (Control.Head S Q)) :=
  let w := rep x
  if Control.Entry blank w then
    pendingPreprocess blank ⟨w.left,.pending,w.right,w.leftBoundary,w.rightBoundary⟩
  else if Control.Success w then
    [cleanupPreprocess blank ⟨w.left,.cleanup,w.right,w.leftBoundary,w.rightBoundary⟩]
  else [Scan.mapHead Head.internal w]

def preprocess (x : P × Sector S Γ (Control.Head S Q)) : List (Sector S Γ (Control.Head S Q)) :=
  match x.2.head with
  | .raw => [rawNormal blank x.2]
  | .pending => pendingPreprocess blank x.2
  | .cleanup => [cleanupPreprocess blank x.2]
  | .internal q => internalPreprocess blank rep
      (x.1,⟨x.2.left,q,x.2.right,x.2.leftBoundary,x.2.rightBoundary⟩)

end Surface.Uniform

namespace Word.Uniform
variable {P S Γ Q : Type*} [Fintype S] [Fintype Γ] [Primcodable Q] [Primcodable P]
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
variable (blank : Γ) (rep : P × Control.Sector S Γ Q → Control.Sector S Γ Q)

def sectorPreprocess (x : P × Sector S Γ Q) : List (Sector S Γ Q) :=
  (Surface.Uniform.preprocess blank rep (x.1,Scan.unliteral x.2)).map (Scan.literal id)

def preprocess (x : P × List (Letter S Γ Q)) : List (List (Letter S Γ Q)) :=
  Path.prepare (fun v => sectorPreprocess blank rep (x.1,v)) x.2

end Word.Uniform
end FiniteAlgebraicEnvelopes.Compiler

namespace FiniteAlgebraicEnvelopes.Compiler
open HeadCodec FiniteAlgebraicEnvelopes.Effect
open scoped HeadCodec

namespace Word.Uniform
variable {P S Γ Q : Type*} [Fintype S] [Fintype Γ] [Primcodable Q] [Primcodable P] [Primcodable S]
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
variable (blank : Γ) (rep : P × Control.Sector S Γ Q → Control.Sector S Γ Q)

def partialNormal (f : P × List S → Part (List S))
    (x : P × List (Letter S Γ Q)) : Part (List (Letter S Γ Q)) :=
  if Path.shape x.2 = .zero then Part.some [.zero] else
    (RawRuns.partialSource (fun w => f (x.1,w)) ((preprocess blank rep x).map (classify blank))).map
      (List.flatMap (realize blank))

end Word.Uniform
end FiniteAlgebraicEnvelopes.Compiler

namespace FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode

section
open Compiler Compiler.Simulator Compiler.HeadCodec ParameterMachine
open scoped Compiler.HeadCodec
variable {S Γ Q : Type*}

variable (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ] (p : S)
def codedMachine (n : ℕ) : Machine (Control Q) (Bool×Γ) where
  initial := .inl 0
  transition q a := (transition A M p n q a).map (fun c => ⟨c.1,c.2.1,c.2.2⟩)

variable [Fintype Q] [Fintype Γ] [Primcodable Q] [Primcodable Γ]

omit [Primcodable Q] in
theorem mem_support_iff (n : ℕ) (q : Control Q) :
    q∈support n ↔ ∃ a : State Q n,encode n a=q := by
  constructor
  · intro h
    cases q with
    | inr q => exact ⟨.run q,rfl⟩
    | inl k =>
      have hk : k<n+5 := by simpa [support] using h
      by_cases h0 : k=0
      · subst k; exact ⟨.start,rfl⟩
      by_cases h1 : k=1
      · subst k; exact ⟨.scan,rfl⟩
      by_cases h2 : k=2
      · subst k; exact ⟨.rewind,rfl⟩
      refine ⟨.emit ⟨k-3,by omega⟩,?_⟩
      simp only [encode,Sum.inl.injEq]
      omega
  · rintro ⟨a,rfl⟩
    exact mem_support n a

variable {T : Type*} [Fintype T]
noncomputable def heads (n : ℕ) : List (Compiler.Control.Head T (Control Q)) :=
  controlSupport (support n)

omit [Primcodable Q] in
theorem mem_heads_iff (n : ℕ) (h : Compiler.Control.Head T (Control Q)) :
    h∈heads n ↔ ∃ a : Compiler.Control.Head T (State Q n),controlMap (encode n) a=h := by
  constructor
  · intro hh
    cases h with
    | initial => exact ⟨.initial,rfl⟩
    | left => exact ⟨.left,rfl⟩
    | right => exact ⟨.right,rfl⟩
    | workspace => exact ⟨.workspace,rfl⟩
    | suffix => exact ⟨.suffix,rfl⟩
    | machine h =>
      cases h with
      | start => exact ⟨.machine .start,rfl⟩
      | rewind r => exact ⟨.machine (.rewind r),rfl⟩
      | scan r => exact ⟨.machine (.scan r),rfl⟩
      | finish => exact ⟨.machine .finish,rfl⟩
      | ok => exact ⟨.machine .ok,rfl⟩
      | run q =>
        obtain ⟨a,rfl⟩ := (mem_support_iff n q).mp ((mem_controlSupport _ _).mp hh)
        exact ⟨.machine (.run a),rfl⟩
      | left q =>
        obtain ⟨a,rfl⟩ := (mem_support_iff n q).mp ((mem_controlSupport _ _).mp hh)
        exact ⟨.machine (.left a),rfl⟩
  · rintro ⟨a,rfl⟩
    cases a <;> simp only [heads,mem_controlSupport,controlMap]
    case machine a => cases a <;> simp [stateMap,mem_support]

end

open Compiler Compiler.Simulator Compiler.HeadCodec ParameterMachine
open scoped Compiler.HeadCodec
variable {S T Γ Q : Type*} [Fintype T] [Fintype Γ] [Fintype Q]
  [DecidableEq T] [DecidableEq Γ] [DecidableEq Q] [Primcodable Γ] [Primcodable Q]
variable (A : Alphabet S Γ) (M : Machine Q Γ) (p : S) (B : Alphabet T (Bool×Γ))

noncomputable def codedRepresentative : ℕ × Compiler.Control.Sector T (Bool×Γ) (Control Q) →
    Compiler.Control.Sector T (Bool×Γ) (Control Q) :=
  letI := Effect.codeOrder (Compiler.Control.Sector T (Bool×Γ) (Control Q))
  Scan.Uniform.representative (fun n => Compiler.Control.table B (codedMachine A M p n)) heads
    (fun v => decide (Compiler.Control.Entry B.blank v))
    (fun v => decide (Compiler.Control.Success v))

@[instance_reducible]
noncomputable def finiteOrder (n : ℕ) : LinearOrder (Compiler.Control.Sector T (Bool×Γ) (State Q n)) :=
  letI := Effect.codeOrder (Compiler.Control.Sector T (Bool×Γ) (Control Q))
  LinearOrder.lift' (Scan.mapHead (controlMap (encode n)))
    (Scan.Uniform.mapHead_injective _ (controlMap_injective (encode_injective n)))

end FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode

namespace FiniteAlgebraicEnvelopes.Compiler.Surface
variable {S Γ H H' : Type*}

def headMap (i : H → H') : Head H → Head H'
  | .raw => .raw | .pending => .pending | .cleanup => .cleanup | .internal q => .internal (i q)

theorem headMap_injective {i : H → H'} (hi : Function.Injective i) : Function.Injective (headMap i) := by
  intro a b h; cases a <;> cases b <;> simp_all [headMap]
  exact hi h

end FiniteAlgebraicEnvelopes.Compiler.Surface

namespace FiniteAlgebraicEnvelopes.Compiler.Path
variable {C H H' : Type*}

def mapLetter (i : H → H') : Letter C H → Letter C H'
  | .zero => .zero
  | .enter => .enter
  | .leave => .leave
  | .left c => .left c
  | .right c => .right c
  | .head q => .head (i q)

def mapSector (i : H → H') (v : Sector C H) : Sector C H' :=
  ⟨v.left,i v.head,v.right,v.leftBoundary,v.rightBoundary⟩

variable (i : H → H')
@[simp] theorem typeOf_mapLetter (a : Letter C H) : typeOf (mapLetter i a)=typeOf a := by
  cases a <;> rfl
@[simp] theorem shape_map (w : List (Letter C H)) : shape (w.map (mapLetter i))=shape w := by
  simp [shape,List.map_map,Function.comp_def]

theorem mapLetter_injective (hi : Function.Injective i) : Function.Injective (mapLetter (C := C) i) := by
  intro a b h
  cases a <;> cases b <;> simp_all [mapLetter]
  exact hi h

@[simp] theorem headed_map (l : List C) (q : H) (r : List C) (lb rb : Bool) :
    (headed l q r lb rb).map (mapLetter i)=headed l (i q) r lb rb := by
  cases lb <;> cases rb <;> simp [headed,List.map_map,Function.comp_def,mapLetter]
@[simp] theorem encode_map (v : Sector C H) :
    encode (mapSector i v)=(encode v).map (mapLetter i) := (headed_map i _ _ _ _ _).symm

@[simp] theorem heads_map (w : List (Letter C H)) :
    heads (w.map (mapLetter i))=(heads w).map i := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp only [heads,List.map_cons,List.filterMap_cons,mapLetter] at * <;> simp_all
@[simp] theorem lefts_map (w : List (Letter C H)) : lefts (w.map (mapLetter i))=lefts w := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp only [lefts,List.map_cons,List.filterMap_cons,mapLetter] at * <;> simp_all
@[simp] theorem rights_map (w : List (Letter C H)) : rights (w.map (mapLetter i))=rights w := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp only [rights,List.map_cons,List.filterMap_cons,mapLetter] at * <;> simp_all
@[simp] theorem enter_mem_map (w : List (Letter C H)) :
    .enter ∈ w.map (mapLetter i) ↔ .enter ∈ w := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨a,ha,he⟩; cases a <;> simp [mapLetter] at he; exact ha
  · intro h; exact ⟨.enter,h,rfl⟩
@[simp] theorem leave_mem_map (w : List (Letter C H)) :
    .leave ∈ w.map (mapLetter i) ↔ .leave ∈ w := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨a,ha,he⟩; cases a <;> simp [mapLetter] at he; exact ha
  · intro h; exact ⟨.leave,h,rfl⟩

variable [DecidableEq C] [DecidableEq H] [DecidableEq H']

omit [DecidableEq C] [DecidableEq H] [DecidableEq H'] in
theorem glue_map (w : List (Letter C H)) (ws : List (List (Letter C H))) :
    glue (w.map (mapLetter i)) (ws.map (List.map (mapLetter i)))=
      (glue w ws).map (List.map (mapLetter i)) := by
  cases ws <;> cases w <;> simp [glue]
omit [DecidableEq C] [DecidableEq H] [DecidableEq H'] in
@[simp] theorem cuts_map (w : List (Letter C H)) :
    cuts (w.map (mapLetter i))=(cuts w).map (List.map (mapLetter i)) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have hh := glue_map i [a] (cuts w)
    cases a <;> simp only [List.map_cons,List.map_nil,mapLetter,cuts,ih] at hh ⊢ <;> exact hh

end FiniteAlgebraicEnvelopes.Compiler.Path

namespace FiniteAlgebraicEnvelopes.Compiler.Word
open HeadCodec
variable {S Γ Q Q' : Type*} (i : Q → Q') (blank : Γ)

def headMap : Surface.Head (Control.Head S Q) → Surface.Head (Control.Head S Q') :=
  Surface.headMap (controlMap i)
def letterMap : Letter S Γ Q → Letter S Γ Q' := Path.mapLetter (headMap i)

theorem headMap_injective (hi : Function.Injective i) : Function.Injective (headMap (S := S) i) :=
  Surface.headMap_injective (controlMap_injective hi)
theorem letterMap_injective (hi : Function.Injective i) :
    Function.Injective (letterMap (S := S) (Γ := Γ) i) :=
  Path.mapLetter_injective _ (headMap_injective i hi)

@[simp] theorem raw_map (w : List S) : (raw (Q := Q) blank w).map (letterMap i)=raw blank w := by
  simp only [raw,encode,letterMap,←Path.encode_map]
  rfl

@[simp] theorem rawLetters_map (w : List (Letter S Γ Q)) : rawLetters (w.map (letterMap i))=rawLetters w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    cases a with
    | right c =>
      rcases c with ⟨b,t⟩
      cases b <;> simp_all only [List.map_cons,rawLetters,List.filterMap_cons,letterMap,Path.mapLetter]
    | _ => simp_all only [List.map_cons,rawLetters,List.filterMap_cons,letterMap,Path.mapLetter]

end FiniteAlgebraicEnvelopes.Compiler.Word

namespace FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode

section
open Compiler Compiler.Simulator Compiler.HeadCodec ParameterMachine
open scoped Compiler.HeadCodec
variable {S T Γ Q : Type*} [Fintype T] [Fintype Γ] [Fintype Q]
  [DecidableEq T] [DecidableEq Γ] [DecidableEq Q]
  [Primcodable T] [Primcodable Γ] [Primcodable Q]
variable (A : Alphabet S Γ) (M : Machine Q Γ) (p : S) (B : Alphabet T (Bool×Γ))

noncomputable def codedNormal (f : ℕ × List T → Part (List T)) :
    ℕ × List (Compiler.Word.Letter T (Bool×Γ) (Control Q)) → Part (List (Compiler.Word.Letter T (Bool×Γ) (Control Q))) :=
  Compiler.Word.Uniform.partialNormal B.blank (codedRepresentative A M p B) f

end

open Compiler Compiler.HeadCodec ParameterMachine
open scoped Compiler.HeadCodec
variable {T Γ Q : Type*} [Fintype T] [Fintype Γ] [Fintype Q]
  [DecidableEq T] [DecidableEq Γ] [DecidableEq Q] [Primcodable Q]

noncomputable def surfaces (n : ℕ) : List (Surface.Head (Compiler.Control.Head T (Control Q))) :=
  [.raw,.pending,.cleanup] ++ (heads n).map Surface.Head.internal

noncomputable def letters (n : ℕ) : List (Word.Letter T (Bool×Γ) (Control Q)) :=
  [.zero,.enter,.leave] ++
  (Scan.finiteList (Word.Cell T (Bool×Γ))).map Path.Letter.left ++
  (Scan.finiteList (Word.Cell T (Bool×Γ))).map Path.Letter.right ++
  (surfaces n).map Path.Letter.head

omit [DecidableEq T] [DecidableEq Q] [Primcodable Q] in
theorem mem_surfaces_iff (n : ℕ) (h : Surface.Head (Compiler.Control.Head T (Control Q))) :
    h∈surfaces n ↔ ∃ a : Surface.Head (Compiler.Control.Head T (State Q n)),
      Surface.headMap (controlMap (encode n)) a=h := by
  cases h with
  | raw =>
    constructor
    · intro _; exact ⟨.raw,rfl⟩
    · intro _; simp [surfaces]
  | pending =>
    constructor
    · intro _; exact ⟨.pending,rfl⟩
    · intro _; simp [surfaces]
  | cleanup =>
    constructor
    · intro _; exact ⟨.cleanup,rfl⟩
    · intro _; simp [surfaces]
  | internal q =>
    simp only [surfaces,List.mem_append,List.mem_cons,List.mem_map,
      Surface.Head.internal.injEq,reduceCtorEq,List.not_mem_nil,false_or,exists_eq_right,mem_heads_iff]
    constructor
    · rintro ⟨a,ha⟩; exact ⟨.internal a,congrArg Surface.Head.internal ha⟩
    · rintro ⟨a,ha⟩
      cases a with
      | internal b => exact ⟨b,Surface.Head.internal.inj ha⟩
      | _ => cases ha

omit [DecidableEq T] [DecidableEq Γ] [DecidableEq Q] [Primcodable Q] in
theorem mem_letters_iff (n : ℕ) (h : Word.Letter T (Bool×Γ) (Control Q)) :
    h∈letters n ↔ ∃ a : Word.Letter T (Bool×Γ) (State Q n), Word.letterMap (encode n) a=h := by
  constructor
  · intro hh
    cases h with
    | zero => exact ⟨.zero,rfl⟩
    | enter => exact ⟨.enter,rfl⟩
    | leave => exact ⟨.leave,rfl⟩
    | left c => exact ⟨.left c,rfl⟩
    | right c => exact ⟨.right c,rfl⟩
    | head h =>
      have hm : h∈surfaces n := by simpa [letters] using hh
      obtain ⟨a,rfl⟩ := (mem_surfaces_iff n h).mp hm
      exact ⟨.head a,rfl⟩
  · rintro ⟨a,rfl⟩
    cases a with
    | head a =>
      have hm := (mem_surfaces_iff n (Surface.headMap (controlMap (encode n)) a)).mpr ⟨a,rfl⟩
      simpa [letters,Word.letterMap,Word.headMap,Path.mapLetter] using hm
    | _ => simp [letters,Word.letterMap,Path.mapLetter,Scan.mem_finiteList]

end FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode

end OAI
end

section
-- module Solutions.OAIFAE.SelfReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Controlled shorter-input evaluator calls, fixed points, totality, and tested-class realization.
-/

namespace FiniteAlgebraicEnvelopes.Bootstrap
namespace Projection
variable {A B : Type*}
def left (w : List (A ⊕ B)) : List A :=
  w.filterMap (fun a => match a with | .inl a => some a | .inr _ => none)
def right (w : List (A ⊕ B)) : List B :=
  w.filterMap (fun a => match a with | .inl _ => none | .inr b => some b)

@[simp] theorem left_append (u v : List (A ⊕ B)) : left (u++v)=left u++left v := List.filterMap_append
@[simp] theorem right_append (u v : List (A ⊕ B)) : right (u++v)=right u++right v := List.filterMap_append
end Projection

namespace Tested
open Compiler Compiler.Simulator MachineRealization MachineRealization.ParameterCode
open scoped Compiler.HeadCodec

variable {S T Γ Q : Type*} [Fintype T] [Fintype Γ] [Fintype Q]
  [DecidableEq T] [DecidableEq Γ] [DecidableEq Q]
  [Primcodable T] [Primcodable Γ] [Primcodable Q]
variable (A : Alphabet S Γ) (M : Machine Q Γ) (p : S) (B : Alphabet T (Bool×Γ))

abbrev X (T Γ Q : Type*) := Word.Letter T (Bool×Γ) (ParameterCode.Control Q)
abbrev Y (T Γ Q : Type*) := X T Γ Q ⊕ PartialAffine.Letter
abbrev Class (T Γ Q : Type*) := List (X T Γ Q) × List PartialAffine.Letter

def combine (q : Class T Γ Q) : Option (Class T Γ Q) :=
  if q.1=[.zero] then none else some q

/-- The literal tested class from the self-reference construction: zero precisely for the compiler
    zero output, and otherwise the compiler word together with a canonical,
    decidable coding of the actual auxiliary partial affine map. -/
noncomputable def family (f : ℕ × List T → Part (List T)) (n : ℕ) (w : List (Y T Γ Q)) :
    Part (Option (Class T Γ Q)) :=
  (codedNormal A M p B f (n,Projection.left w)).map
    (fun o => combine (o,PartialAffine.testedClass (Projection.right w)))

noncomputable def letters (n : ℕ) : List (Y T Γ Q) :=
  (ParameterCode.letters (T:=T) (Γ:=Γ) (Q:=Q) n).map Sum.inl ++
    (Static.letters PartialAffine.Letter).map Sum.inr

end Tested
end FiniteAlgebraicEnvelopes.Bootstrap

namespace FiniteAlgebraicEnvelopes.Bootstrap.Uniform

section
variable {P A S Q : Type*} [DecidableEq A] [DecidableEq S] [DecidableEq Q]

def pickStep (lt : List A → List A → Bool) (q : Option Q) (best : List A)
    (v : List A × Option Q) : List A :=
  if v.2=q ∧ lt v.1 best=true then v.1 else best

def pick (lt : List A → List A → Bool) (ps : List (List A × Option Q))
    (w : List A) (q : Option Q) : List A := ps.foldl (pickStep lt q) w

def output (code : List A → List S) (lt : List A → List A → Bool) (z : S)
    (ps : List (List A × Option Q)) (v : List A × Option Q) : List S :=
  if v.2=none then [z] else code (pick lt ps v.1 v.2)

def table (code : List A → List S) (lt : List A → List A → Bool) (z : S)
    (ps : List (List A × Option Q)) : List (List S × List S) :=
  ps.flatMap fun v => if v.1≠[] ∧ output code lt z ps v≠code v.1 then
    [(code v.1,output code lt z ps v)] else []

def compute (ls : List A) (code : List A → List S) (lt : List A → List A → Bool)
    (z : S) (f : List A → Part (Option Q)) (n : ℕ) : Part (List (List S × List S)) :=
  (Effect.traverse (fun w => (f w).map (w,·)) (words ls n)).map (table code lt z)

end

variable {P S A B Q R : Type*} [Primcodable S] [Fintype S]
  [DecidableEq S] [DecidableEq A] [DecidableEq B] [DecidableEq Q] [DecidableEq R]

noncomputable def bases (z : S) (ls : List A) (ms : List B)
    (code : List A → List S) (code' : List B → List S)
    (lt : List A → List A → Bool) (lt' : List B → List B → Bool)
    (d e : ℕ) (f : List A → Part (Option Q)) (g : List B → Part (Option R)) (n : ℕ) :
    Part (List (List S × List S)) :=
  (compute ls code lt z f (n/d)).bind fun rc =>
    (compute ms code' lt' z g (n/e)).map fun rd => Base.absorption z ++ rc ++ rd

noncomputable def tables (a : Selectors.Markers S) (ls : List A) (ms : List B)
    (code : List A → List S) (code' : List B → List S)
    (lt : List A → List A → Bool) (lt' : List B → List B → Bool)
    (d e : ℕ) (f : List A → Part (Option Q)) (g : List B → Part (Option R)) (n : ℕ) :
    Part (List (List S × List S)) :=
  (bases a.zero ls ms code code' lt lt' d e f g n).map fun b =>
    Selectors.process (a:=a) b (Selectors.stages a.zero) n n

end FiniteAlgebraicEnvelopes.Bootstrap.Uniform

namespace FiniteAlgebraicEnvelopes.Bootstrap.LexBinary
variable {A B S : Type*}

/-- Binary tails in their literal lexicographic order, with `a` before `c`. -/
def words (a c : S) : ℕ → List (List S)
  | 0 => [[]]
  | n+1 => (words a c n).map (a::·) ++ (words a c n).map (c::·)

 theorem length_words (a c : S) (n : ℕ) : (words a c n).length=2^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [words,ih,pow_succ,Nat.mul_two]

 theorem mem_length {a c : S} {n : ℕ} {w : List S} (h : w∈words a c n) : w.length=n := by
  induction n generalizing w with
  | zero => simpa [words] using h
  | succ n ih =>
    simp only [words,List.mem_append,List.mem_map] at h
    rcases h with ⟨u,hu,rfl⟩ | ⟨u,hu,rfl⟩ <;> simp [ih hu]

 theorem mem_letters {a c s : S} {n : ℕ} {w : List S} (h : w∈words a c n) (hs : s∈w) : s=a ∨ s=c := by
  induction n generalizing w with
  | zero => simp [words] at h; subst w; cases hs
  | succ n ih =>
    simp only [words,List.mem_append,List.mem_map] at h
    rcases h with ⟨u,hu,rfl⟩ | ⟨u,hu,rfl⟩
    · rcases List.mem_cons.mp hs with rfl | hs
      · exact Or.inl rfl
      · exact ih hu hs
    · rcases List.mem_cons.mp hs with rfl | hs
      · exact Or.inr rfl
      · exact ih hu hs

 theorem nodup {a c : S} (hac : a≠c) (n : ℕ) : (words a c n).Nodup := by
  induction n with
  | zero => simp [words]
  | succ n ih =>
    rw [words,List.nodup_append]
    refine ⟨ih.map (by intro u v h; exact (List.cons.inj h).2),
      ih.map (by intro u v h; exact (List.cons.inj h).2),?_⟩
    intro u hu v hv he
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hu
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hv
    exact hac (List.cons.inj he).1

 theorem ordered {r : S → S → Prop} {a c : S} (hac : r a c) (n : ℕ) :
    (words a c n).Pairwise (List.Lex r) := by
  induction n with
  | zero => simp [words]
  | succ n ih =>
    rw [words,List.pairwise_append]
    refine ⟨?_,?_,?_⟩
    · rw [List.pairwise_map]; exact ih.imp (fun h => List.Lex.cons h)
    · rw [List.pairwise_map]; exact ih.imp (fun h => List.Lex.cons h)
    · intro u hu v hv
      obtain ⟨x,_,rfl⟩ := List.mem_map.mp hu
      obtain ⟨y,_,rfl⟩ := List.mem_map.mp hv
      exact List.Lex.rel hac

variable [DecidableEq A]
def tail (a c : S) (d : ℕ) (ls : List A) (x : A) : List S :=
  (words a c d).getD (ls.idxOf x) []

def encode (b a c : S) (d : ℕ) (ls : List A) (w : List A) : List S :=
  w.flatMap (fun x => b :: tail a c d ls x)

 theorem index_bound {firstSymbol secondSymbol : S} (d : ℕ) (ls : List A)
    (hls : ls.length≤2^d) {x : A} (hx : x∈ls) :
    ls.idxOf x < (words firstSymbol secondSymbol d).length := by
  rw [length_words]
  exact (List.idxOf_lt_length_of_mem hx).trans_le hls

variable [DecidableEq S]
def code (b a c : S) (hba : b≠a) (hbc : b≠c) (hac : a≠c)
    (d : ℕ) (ls : List A) (hls : ls.length≤2^d)
    (i : B → A) (hi : Function.Injective i) (hm : ∀ x,i x∈ls) : BlockCode B S where
  marker := b
  tail x := tail a c d ls (i x)
  width := d
  tail_length x := by
    rw [tail,List.getD_eq_getElem _ _ (index_bound d ls hls (hm x))]
    exact mem_length (List.getElem_mem _)
  tail_avoids x := by
    rw [tail,List.getD_eq_getElem _ _ (index_bound d ls hls (hm x))]
    intro hb
    rcases mem_letters (List.getElem_mem _) hb with h | h
    · exact hba h
    · exact hbc h
  injective := by
    intro x y h
    apply hi
    apply (List.idxOf_inj (hm x)).mp
    simp only [tail] at h
    rw [List.getD_eq_getElem _ _ (index_bound d ls hls (hm x)),
      List.getD_eq_getElem _ _ (index_bound d ls hls (hm y))] at h
    exact (nodup hac d).getElem_inj_iff.mp h

omit [DecidableEq S] in
 theorem code_encode (b a c : S) (hba : b≠a) (hbc : b≠c) (hac : a≠c)
    (d : ℕ) (ls : List A) (hls : ls.length≤2^d)
    (i : B → A) (hi : Function.Injective i) (hm : ∀ x,i x∈ls) (w : List B) :
    (code b a c hba hbc hac d ls hls i hi hm).encode w=encode b a c d ls (w.map i) := by
  simp only [BlockCode.encode,code,encode,List.flatMap_map]
  rfl

omit [DecidableEq S] in
 theorem code_order {r : S → S → Prop} (b a c : S) (hba : b≠a) (hbc : b≠c) (hac : a≠c)
    (hr : r a c) (d : ℕ) (ls : List A) (hls : ls.length≤2^d)
    (i : B → A) (hi : Function.Injective i) (hm : ∀ x,i x∈ls) {x y : B}
    (hxy : ls.idxOf (i x)<ls.idxOf (i y)) :
    List.Lex r ((code b a c hba hbc hac d ls hls i hi hm).block x)
      ((code b a c hba hbc hac d ls hls i hi hm).block y) := by
  apply List.Lex.cons
  change List.Lex r (tail a c d ls (i x)) (tail a c d ls (i y))
  rw [tail,tail,List.getD_eq_get _ _ ⟨_,index_bound d ls hls (hm x)⟩,
    List.getD_eq_get _ _ ⟨_,index_bound d ls hls (hm y)⟩]
  exact (ordered hr d).rel_get_of_lt (a := ⟨_,index_bound d ls hls (hm x)⟩)
    (b := ⟨_,index_bound d ls hls (hm y)⟩) hxy

end FiniteAlgebraicEnvelopes.Bootstrap.LexBinary

namespace FiniteAlgebraicEnvelopes.Bootstrap.Rank
variable {P A B C : Type*} [DecidableEq A]

def word (ls : List A) (w : List A) : List ℕ := w.map ls.idxOf

noncomputable def less (ls : List A) (u v : List A) : Bool := by
  classical
  exact decide (List.Shortlex (fun a b : ℕ => a < b) (word ls u) (word ls v))

 theorem lex_map_iff {f : B → C} (hf : Function.Injective f) {r : C → C → Prop} (u v : List B) :
    List.Lex r (u.map f) (v.map f) ↔ List.Lex (fun a b => r (f a) (f b)) u v := by
  induction u generalizing v with
  | nil => cases v <;> simp
  | cons a u ih => cases v with
    | nil => simp
    | cons b v => simp only [List.map_cons,List.cons_lex_cons_iff,hf.eq_iff,ih]

 theorem shortlex_map_iff {f : B → C} (hf : Function.Injective f) {r : C → C → Prop} (u v : List B) :
    List.Shortlex r (u.map f) (v.map f) ↔ List.Shortlex (fun a b => r (f a) (f b)) u v := by
  simp only [List.shortlex_def,List.length_map,lex_map_iff hf]

 theorem index_injective (ls : List A) (i : B → A) (hi : Function.Injective i) (hm : ∀ b,i b∈ls) :
    Function.Injective (fun b => ls.idxOf (i b)) := by
  intro x y h
  exact hi ((List.idxOf_inj (hm x)).mp h)

 theorem less_map (ls : List A) (i : B → A) (hi : Function.Injective i) (hm : ∀ b,i b∈ls)
    (u v : List B) : less ls (u.map i) (v.map i)=true ↔
      List.Shortlex (fun a b => ls.idxOf (i a)<ls.idxOf (i b)) u v := by
  classical
  simp only [less,word,List.map_map,decide_eq_true_eq]
  exact shortlex_map_iff (index_injective ls i hi hm) u v

end FiniteAlgebraicEnvelopes.Bootstrap.Rank

namespace FiniteAlgebraicEnvelopes.MachineRealization.UniversalMachine
open Compiler.Simulator OneSided ParameterMachine
variable {S Γ Q : Type*} [DecidableEq Γ]

/-- Forget the parameter delimiter as an input/output letter. Work symbols and
    transitions are not changed. -/
def restrict (A : Alphabet (S ⊕ Unit) Γ) : Alphabet S Γ where
  blank := A.blank
  input s := A.input (.inl s)
  output g := (A.output g).bind fun a => match a with | .inl s => some s | .inr _ => none
  output_input s := by simp [A.output_input]
  output_blank := by simp [A.output_blank]

omit [DecidableEq Γ] in
 theorem restrict_decode (A : Alphabet (S ⊕ Unit) Γ)
    (hA : ∀ g a, A.output g=some a → g=A.input a) :
    ∀ g a, (restrict A).output g=some a → g=(restrict A).input a := by
  intro g a h
  obtain ⟨b,hb,hba⟩ := Option.bind_eq_some_iff.mp h
  cases b with
  | inr u => cases hba
  | inl s => cases hba; exact hA _ _ hb

omit [DecidableEq Γ] in
 theorem restrict_content (A : Alphabet (S ⊕ Unit) Γ) (w : List S) :
    content (restrict A) w=content A (w.map Sum.inl) := by
  simp only [content,List.map_map,Function.comp_def,restrict]
  rfl

omit [DecidableEq Γ] in
 theorem restrict_realizes (A : Alphabet (S ⊕ Unit) Γ) (M : Machine Q Γ)
    {f : List S → Part (List S)} {g : List (S ⊕ Unit) → Part (List (S ⊕ Unit))}
    (hM : Compiler.Word.Realizes A M g)
    (hg : ∀ w, g (w.map Sum.inl)=(f w).map (List.map Sum.inl)) :
    Compiler.Word.Realizes (restrict A) M f := by
  intro w out
  have hi : (List.map Sum.inl : List S → List (S ⊕ Unit)) out ∈ g (w.map Sum.inl) ↔ out ∈ f w := by
    rw [hg]
    constructor
    · intro h
      obtain ⟨y,hy,he⟩ := (Part.mem_map_iff _).mp h
      have hyout : y=out := List.map_injective_iff.mpr Sum.inl_injective he
      exact hyout ▸ hy
    · exact Part.mem_map _
  rw [←hi,hM,returns_iff A M,returns_iff (restrict A) M,restrict_content]
  simp only [List.map_map,Function.comp_def,restrict]

def letters (w : List (S ⊕ Unit)) : List S :=
  w.filterMap fun a => match a with | .inl s => some s | .inr _ => none

def parameter (w : List (S ⊕ Unit)) : ℕ :=
  (w.filterMap fun a => match a with | .inl _ => none | .inr _ => some ()).length - 1

 theorem letters_input (w : List S) (n : ℕ) :
    letters (w.map Sum.inl ++ List.replicate (n+1) (.inr ()))=w := by
  simp [letters,List.filterMap_map]

 theorem parameter_input (w : List S) (n : ℕ) :
    parameter (w.map Sum.inl ++ List.replicate (n+1) (.inr ()))=n := by
  simp [parameter,List.filterMap_map]

variable [Primcodable S]

 theorem primrec_letters : Primrec (letters (S := S)) := by
  have h : Primrec (fun a : S ⊕ Unit => match a with | .inl s => some s | .inr _ => none) :=
    (Primrec.sumCasesOn Primrec.id (Primrec.option_some.comp Primrec.snd).to₂ (Primrec.const none).to₂).of_eq
      (fun a => by cases a <;> rfl)
  exact Primrec.listFilterMap Primrec.id (h.comp Primrec.snd).to₂

 theorem primrec_parameter : Primrec (parameter (S := S)) := by
  have h : Primrec (fun a : S ⊕ Unit => match a with | .inl _ => none | .inr _ => some ()) :=
    (Primrec.sumCasesOn Primrec.id (Primrec.const none).to₂ (Primrec.const (some ())).to₂).of_eq
      (fun a => by cases a <;> rfl)
  exact Primrec.nat_sub.comp (Primrec.list_length.comp
    (Primrec.listFilterMap Primrec.id (h.comp Primrec.snd).to₂)) (Primrec.const 1)

def universal (f : ℕ → List S → Part (List S)) (w : List (S ⊕ Unit)) :
    Part (List (S ⊕ Unit)) := (f (parameter w) (letters w)).map (List.map Sum.inl)

omit [Primcodable S] in
 theorem universal_input (f : ℕ → List S → Part (List S)) (w : List S) (n : ℕ) :
    universal f (w.map Sum.inl ++ List.replicate (n+1) (.inr ()))=
      (f n w).map (List.map Sum.inl) := by
  rw [universal,parameter_input,letters_input]

 theorem partrec_universal {f : ℕ → List S → Part (List S)} (hf : Partrec₂ f) :
    Partrec (universal f) :=
  (hf.comp primrec_parameter.to_comp primrec_letters.to_comp).map
    ((Primrec.list_map Primrec.id (Primrec.sumInl.comp Primrec.snd).to₂).to_comp.comp Computable.snd).to₂

/-- The alphabet and all non-initializer control are now fixed once for the whole
    partial-recursive family. The only variable finite control is the explicit
    unary counter `Fin (n+2)`, not a choice of an evaluator for each index. -/
theorem exists_parameter_machine {S : Type} [Fintype S] [Primcodable S]
    {f : ℕ → List S → Part (List S)} (hf : Partrec₂ f) :
    ∃ (Γ Q : Type) (_ : Fintype Γ) (_ : Fintype Q) (_ : DecidableEq Γ)
      (A : Alphabet (S ⊕ Unit) Γ) (M : Machine Q Γ),
      (∀ g a, A.output g=some a → g=A.input a) ∧
      ∀ n, Compiler.Word.Realizes (restrict (alphabet A)) (machine A M (.inr ()) n) (f n) := by
  classical
  obtain ⟨Γ,Q,hΓ,hQ,A,M,hA,hM⟩ := WordEvaluator.exists_machine (partrec_universal hf)
  let : Fintype Γ := hΓ
  let : Fintype Q := hQ
  refine ⟨Γ,Q,hΓ,hQ,inferInstance,A,M,hA,?_⟩
  intro n
  exact restrict_realizes (alphabet A) (machine A M (.inr ()) n)
    (ParameterMachine.realizes A M (.inr ()) n hM) (fun w => universal_input f w n)

end FiniteAlgebraicEnvelopes.MachineRealization.UniversalMachine

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
open Compiler Compiler.Simulator MachineRealization
open scoped Compiler.HeadCodec

abbrev Sigma := Fin 12

def markers : Selectors.Markers Sigma := ⟨11,7,8,9,10,by decide⟩

def raw (n : ℕ) (w : List Sigma) : Part (List Sigma) :=
  WordProgramming.eval ((Encodable.decode n : Option Nat.Partrec.Code).getD .zero) w

 theorem partrec_raw : Partrec₂ raw :=
  WordProgramming.partrec_eval.comp
    (Primrec.option_getD.comp (Primrec.decode.comp Primrec.fst) (Primrec.const .zero)).to_comp Computable.snd

variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)
variable {Γ Q : Type*} [Fintype Γ] [Fintype Q] [DecidableEq Γ] [DecidableEq Q]
  [Primcodable Γ] [Primcodable Q]
variable (A : Alphabet (Sigma ⊕ Unit) Γ) (M : Machine Q Γ)

local instance instDecidableEqXSigma : DecidableEq (Tested.X Sigma Γ Q) := inferInstance

abbrev Y := Tested.Y Sigma Γ Q
abbrev Z (k : ℕ) := Fin k × Bool

noncomputable def yLetters (n : ℕ) : List (Y (Γ:=Γ) (Q:=Q)) := Tested.letters n
noncomputable def zLetters (k : ℕ) : List (Z k) := Static.letters (Z k)

/-- A single common width, chosen effectively only from finite alphabets. -/
noncomputable def width (k n : ℕ) : ℕ :=
  (yLetters (Γ:=Γ) (Q:=Q) n).length+(zLetters k).length+2

noncomputable def codeT (n : ℕ) : List (Y (Γ:=Γ) (Q:=Q)) → List Sigma :=
  LexBinary.encode 0 1 2 (width (Γ:=Γ) (Q:=Q) k n) (yLetters n)
noncomputable def codeG (n : ℕ) : List (Z k) → List Sigma :=
  LexBinary.encode 3 4 5 (width (Γ:=Γ) (Q:=Q) k n) (zLetters k)

noncomputable def testT (n : ℕ) : List (Y (Γ:=Γ) (Q:=Q)) → Part (Option (Tested.Class Sigma Γ Q)) :=
  Tested.family A M (.inr ()) (UniversalMachine.restrict (ParameterMachine.alphabet A))
    (fun p => raw p.1 p.2) n

noncomputable def testG (_ : ℕ) (w : List (Z k)) : Part (Option (List (Z k))) :=
  Part.some (some (WordProblem.testedClass s w))

noncomputable def tables (n : ℕ) : ℕ → Part (List (List Sigma × List Sigma)) :=
  Uniform.tables markers (yLetters n) (zLetters k) (codeT (k:=k) n) (codeG (Γ:=Γ) (Q:=Q) n)
    (Rank.less (yLetters n)) (Rank.less (zLetters k))
    (width (Γ:=Γ) (Q:=Q) k n+1) (width (Γ:=Γ) (Q:=Q) k n+1) (testT A M n) (testG s n)

end FiniteAlgebraicEnvelopes.Bootstrap.Source

namespace FiniteAlgebraicEnvelopes
namespace Effect
variable {A B C : Type*}
theorem traverse_map_output (f : A → Part B) (g : B → C) (ls : List A) :
    traverse (fun a => (f a).map g) ls = (traverse f ls).map (List.map g) := by
  induction ls with
  | nil => simp [traverse]
  | cons a ls ih =>
    simp only [traverse,ih,Part.bind_map,Part.map_bind,Part.map_map,Function.comp_def,List.map_cons]
end Effect

namespace Bootstrap.Uniform
variable {A B S Q : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq S] [DecidableEq Q]
variable (i : A → B) (hi : Function.Injective i)
variable (lt : List A → List A → Bool) (lt' : List B → List B → Bool)
variable (hlt : ∀ u v,lt' (u.map i) (v.map i)=lt u v)

def answerMap (v : List A × Option Q) : List B × Option Q := (v.1.map i,v.2)

include hlt

omit [DecidableEq A] [DecidableEq B] in
 theorem pickStep_map (q : Option Q) (w : List A) (v : List A × Option Q) :
    pickStep lt' q (w.map i) (answerMap i v)=(pickStep lt q w v).map i := by
  simp only [pickStep,answerMap,hlt]
  split <;> rfl

omit [DecidableEq A] [DecidableEq B] in
 theorem pick_map (ps : List (List A × Option Q)) (w : List A) (q : Option Q) :
    pick lt' (ps.map (answerMap i)) (w.map i) q=(pick lt ps w q).map i := by
  unfold pick
  induction ps generalizing w with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.foldl_cons,pickStep_map i lt lt' hlt,ih]

omit [DecidableEq A] [DecidableEq B] [DecidableEq S] in
 theorem output_map (code : List A → List S) (code' : List B → List S)
    (hc : ∀ w,code' (w.map i)=code w) (z : S) (ps : List (List A × Option Q)) (v : List A × Option Q) :
    output code' lt' z (ps.map (answerMap i)) (answerMap i v)=output code lt z ps v := by
  simp only [output,answerMap,pick_map i lt lt' hlt,hc]

omit [DecidableEq A] [DecidableEq B] in
 theorem table_map (code : List A → List S) (code' : List B → List S)
    (hc : ∀ w,code' (w.map i)=code w) (z : S) (ps : List (List A × Option Q)) :
    table code' lt' z (ps.map (answerMap i))=table code lt z ps := by
  simp only [table,List.flatMap_map]
  apply List.flatMap_congr
  intro v _
  rw [output_map i lt lt' hlt code code' hc z ps v]
  simp only [answerMap,hc,ne_eq,List.map_eq_nil_iff]

omit [DecidableEq A] [DecidableEq B] in
 theorem compute_map (code : List A → List S) (code' : List B → List S)
    (hc : ∀ w,code' (w.map i)=code w) (z : S) (ls : List A)
    (f : List A → Part (Option Q)) (g : List B → Part (Option Q))
    (hf : ∀ w,g (w.map i)=f w) (n : ℕ) :
    compute (ls.map i) code' lt' z g n=compute ls code lt z f n := by
  simp only [compute,words_map,←Effect.traverse_comp,hf]
  have hh : (fun w : List A => (f w).map (fun q => (w.map i,q))) =
      (fun w => ((f w).map (w,·)).map (answerMap i)) := by
    funext w
    simp only [Part.map_map,answerMap,Function.comp_def]
  rw [hh,Effect.traverse_map_output,Part.map_map]
  congr 1
  funext ps
  exact table_map i lt lt' hlt code code' hc z ps
end Bootstrap.Uniform
end FiniteAlgebraicEnvelopes

namespace FiniteAlgebraicEnvelopes.Bootstrap.Uniform
variable {S A B Q R : Type*} [Primcodable S] [Fintype S] [Fintype A] [Fintype B]
  [DecidableEq S] [DecidableEq A] [DecidableEq B] [DecidableEq Q] [DecidableEq R]
variable {r : A → A → Prop} {s : B → B → Prop}
  [DecidableRel (List.Shortlex r)] [DecidableRel (List.Shortlex s)]
  [Std.Trichotomous r] [Std.Trichotomous s]
variable (a : Selectors.Markers S) (C : BlockCode A S) (D : BlockCode B S)
  (wf : WellFounded r) (wg : WellFounded s)
variable (ls : List A) (ms : List B) (hls : ∀ x,x∈ls) (hms : ∀ x,x∈ms)
variable (f : List A → Part (Option Q)) (g : List B → Part (Option R))

noncomputable def fullTables : ℕ → Part (List (List S × List S)) :=
  tables a ls ms C.encode D.encode (fun u v => decide (List.Shortlex r u v))
    (fun u v => decide (List.Shortlex s u v)) (C.width+1) (D.width+1) f g

end FiniteAlgebraicEnvelopes.Bootstrap.Uniform

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
open Compiler Compiler.Simulator MachineRealization MachineRealization.ParameterCode
open scoped Compiler.HeadCodec
variable {Γ Q : Type*} [Fintype Γ] [Fintype Q] [DecidableEq Γ] [DecidableEq Q]
  [Primcodable Γ] [Primcodable Q]

abbrev FiniteY (n : ℕ) := Word.Letter Sigma (Bool×Γ) (ParameterMachine.State Q n) ⊕ PartialAffine.Letter

def includeY (n : ℕ) : FiniteY (Γ:=Γ) (Q:=Q) n → Y (Γ:=Γ) (Q:=Q) :=
  Sum.map (Word.letterMap (encode n)) id

local instance instDecidableEqXSigma_1 : DecidableEq (Tested.X Sigma Γ Q) := inferInstance
local instance instDecidableEqY : DecidableEq (Y (Γ:=Γ) (Q:=Q)) := inferInstance

omit [Fintype Γ] [Fintype Q] [DecidableEq Γ] [DecidableEq Q]
    [Primcodable Γ] [Primcodable Q] in
 theorem includeY_injective (n : ℕ) : Function.Injective (includeY (Γ:=Γ) (Q:=Q) n) := by
  exact Sum.map_injective.mpr ⟨Word.letterMap_injective (encode n) (encode_injective n),Function.injective_id⟩

omit [DecidableEq Γ] [DecidableEq Q] [Primcodable Γ] [Primcodable Q] in
 theorem includeY_mem (n : ℕ) (y : FiniteY (Γ:=Γ) (Q:=Q) n) : includeY n y∈yLetters n := by
  cases y with
  | inl y =>
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨_,(mem_letters_iff n _).mpr ⟨y,rfl⟩,rfl⟩
  | inr y =>
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨y,(by simp [Static.letters]),rfl⟩

omit [DecidableEq Γ] [DecidableEq Q] [Primcodable Γ] [Primcodable Q] in
 theorem mem_includeY_range (n : ℕ) {y : Y (Γ:=Γ) (Q:=Q)} (hy : y∈yLetters n) :
    ∃ v : FiniteY (Γ:=Γ) (Q:=Q) n,includeY n v=y := by
  rcases List.mem_append.mp hy with hy | hy
  · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hy
    obtain ⟨v,rfl⟩ := (mem_letters_iff n c).mp hc
    exact ⟨.inl v,rfl⟩
  · obtain ⟨v,_,rfl⟩ := List.mem_map.mp hy
    exact ⟨.inr v,rfl⟩

 theorem list_preimage {A B : Type*} (i : A → B) (ls : List B) (h : ∀ b∈ls,∃a,i a=b) :
    ∃ks : List A,ks.map i=ls := by
  induction ls with
  | nil => exact ⟨[],rfl⟩
  | cons b ls ih =>
    obtain ⟨a,rfl⟩ := h b (by simp)
    obtain ⟨ks,rfl⟩ := ih (fun x hx => h x (by simp [hx]))
    exact ⟨a::ks,rfl⟩

noncomputable def finiteLetters (n : ℕ) : List (FiniteY (Γ:=Γ) (Q:=Q) n) :=
  (list_preimage (includeY n) (yLetters n) (fun _ h => mem_includeY_range n h)).choose

omit [DecidableEq Γ] [DecidableEq Q] [Primcodable Γ] [Primcodable Q] in
 theorem map_finiteLetters (n : ℕ) : (finiteLetters (Γ:=Γ) (Q:=Q) n).map (includeY n)=yLetters n :=
  (list_preimage (includeY n) (yLetters n) (fun _ h => mem_includeY_range n h)).choose_spec

omit [DecidableEq Γ] [DecidableEq Q] [Primcodable Γ] [Primcodable Q] in
 theorem mem_finiteLetters (n : ℕ) (y : FiniteY (Γ:=Γ) (Q:=Q) n) : y∈finiteLetters n := by
  have h := includeY_mem n y
  rw [←map_finiteLetters n] at h
  obtain ⟨v,hv,he⟩ := List.mem_map.mp h
  exact (includeY_injective n he) ▸ hv

noncomputable def rankT (n : ℕ) (y : FiniteY (Γ:=Γ) (Q:=Q) n) : ℕ := @List.idxOf _ instBEqOfDecidableEq (includeY n y) (yLetters n)
noncomputable def rankG (k : ℕ) (z : Z k) : ℕ := @List.idxOf _ instBEqOfDecidableEq z (zLetters k)

omit [Primcodable Γ] [Primcodable Q] in
 theorem rankT_injective (n : ℕ) : Function.Injective (rankT (Γ:=Γ) (Q:=Q) n) := by
  exact Rank.index_injective _ _ (includeY_injective n) (includeY_mem n)
 theorem rankG_injective (k : ℕ) : Function.Injective (rankG k) := by
  exact Rank.index_injective _ id Function.injective_id (by intro x; simp [zLetters,Static.letters])

noncomputable def relT (n : ℕ) (u v : FiniteY (Γ:=Γ) (Q:=Q) n) : Prop := rankT n u<rankT n v
noncomputable def relG (k : ℕ) (u v : Z k) : Prop := rankG k u<rankG k v

omit [Primcodable Γ] [Primcodable Q] in
 theorem wf_relT (n : ℕ) : WellFounded (relT (Γ:=Γ) (Q:=Q) n) := InvImage.wf _ Nat.lt_wfRel.wf
 theorem wf_relG (k : ℕ) : WellFounded (relG k) := InvImage.wf _ Nat.lt_wfRel.wf

instance tri_relT (n : ℕ) : Std.Trichotomous (relT (Γ:=Γ) (Q:=Q) n) := ⟨fun a b hab hba =>
  rankT_injective n (by change ¬rankT n a < rankT n b at hab; change ¬rankT n b < rankT n a at hba; omega)⟩
instance tri_relG (k : ℕ) : Std.Trichotomous (relG k) := ⟨fun a b hab hba =>
  rankG_injective k (by change ¬rankG k a < rankG k b at hab; change ¬rankG k b < rankG k a at hba; omega)⟩

noncomputable instance dec_shortlexT (n : ℕ) : DecidableRel (List.Shortlex (relT (Γ:=Γ) (Q:=Q) n)) := Classical.decRel _
noncomputable instance dec_shortlexG (k : ℕ) : DecidableRel (List.Shortlex (relG k)) := Classical.decRel _

omit [DecidableEq Γ] [DecidableEq Q] [Primcodable Γ] [Primcodable Q] in
 theorem widthBoundT (k n : ℕ) : (yLetters (Γ:=Γ) (Q:=Q) n).length≤2^(width (Γ:=Γ) (Q:=Q) k n) := by
  have h : width (Γ:=Γ) (Q:=Q) k n < 2^(width (Γ:=Γ) (Q:=Q) k n) := Nat.lt_two_pow_self
  unfold width at *
  omega
omit [DecidableEq Γ] [DecidableEq Q] [Primcodable Γ] [Primcodable Q] in
 theorem widthBoundG (k n : ℕ) : (zLetters k).length≤2^(width (Γ:=Γ) (Q:=Q) k n) := by
  have h : width (Γ:=Γ) (Q:=Q) k n < 2^(width (Γ:=Γ) (Q:=Q) k n) := Nat.lt_two_pow_self
  unfold width at *
  omega

noncomputable def finiteCodeT (k n : ℕ) : BlockCode (FiniteY (Γ:=Γ) (Q:=Q) n) Sigma :=
  LexBinary.code 0 1 2 (by decide) (by decide) (by decide) (width k n) (yLetters n)
    (widthBoundT k n) (includeY n) (includeY_injective n) (includeY_mem n)
noncomputable def finiteCodeG (k n : ℕ) : BlockCode (Z k) Sigma :=
  LexBinary.code 3 4 5 (by decide) (by decide) (by decide) (width (Γ:=Γ) (Q:=Q) k n) (zLetters k)
    (widthBoundG k n) id Function.injective_id (by intro x; simp [zLetters,Static.letters])

omit [Primcodable Γ] [Primcodable Q] in
 theorem finiteCodeT_encode (k n : ℕ) (w : List (FiniteY (Γ:=Γ) (Q:=Q) n)) :
    (finiteCodeT k n).encode w=codeT (k:=k) n (w.map (includeY n)) :=
  LexBinary.code_encode ..
omit [DecidableEq Γ] [DecidableEq Q] [Primcodable Γ] [Primcodable Q] in
 theorem finiteCodeG_encode (k n : ℕ) (w : List (Z k)) :
    (finiteCodeG (Γ:=Γ) (Q:=Q) k n).encode w=codeG (Γ:=Γ) (Q:=Q) n w := by
  simpa [finiteCodeG,codeG] using LexBinary.code_encode 3 4 5 (by decide) (by decide) (by decide)
    (width (Γ:=Γ) (Q:=Q) k n) (zLetters k) (widthBoundG k n) id Function.injective_id (by intro x; simp [zLetters,Static.letters]) w

omit [Primcodable Γ] [Primcodable Q] in
 theorem lessT_map (n : ℕ) (u v : List (FiniteY (Γ:=Γ) (Q:=Q) n)) :
    Rank.less (yLetters n) (u.map (includeY n)) (v.map (includeY n))=decide (List.Shortlex (relT n) u v) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  change _ ↔ List.Shortlex (fun a b => @List.idxOf _ instBEqOfDecidableEq (includeY n a) (yLetters n)<@List.idxOf _ instBEqOfDecidableEq (includeY n b) (yLetters n)) u v
  exact Rank.less_map (yLetters n) (includeY n) (includeY_injective n) (includeY_mem n) u v
 theorem lessG_eq (k : ℕ) (u v : List (Z k)) :
    Rank.less (zLetters k) u v=decide (List.Shortlex (relG k) u v) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  change _ ↔ List.Shortlex (fun a b => @List.idxOf _ instBEqOfDecidableEq a (zLetters k)<@List.idxOf _ instBEqOfDecidableEq b (zLetters k)) u v
  simpa using Rank.less_map (zLetters k) id Function.injective_id (by intro x; simp [zLetters,Static.letters]) u v

end FiniteAlgebraicEnvelopes.Bootstrap.Source

namespace FiniteAlgebraicEnvelopes.Bootstrap
namespace LexBinary
variable {A B S : Type*} [DecidableEq A] [DecidableEq S]
omit [DecidableEq S] in
 theorem alphabet_bound (b a c : S) (hba : b≠a) (hbc : b≠c) (hac : a≠c)
    (d : ℕ) (ls : List A) (hls : ls.length≤2^d)
    (i : B → A) (hi : Function.Injective i) (hm : ∀ x,i x∈ls) {s : S}
    (hs : s∈(code b a c hba hbc hac d ls hls i hi hm).Alphabet) : s=b ∨ s=a ∨ s=c := by
  obtain ⟨x,hx⟩ := hs
  rcases List.mem_cons.mp hx with rfl | hx
  · exact Or.inl rfl
  · right
    change s∈tail a c d ls (i x) at hx
    rw [tail,List.getD_eq_getElem _ _ (index_bound d ls hls (hm x))] at hx
    exact mem_letters (List.getElem_mem _) hx
end LexBinary

namespace Source
open Compiler Compiler.Simulator MachineRealization MachineRealization.ParameterCode
open scoped Compiler.HeadCodec
variable {Γ Q : Type*} [Fintype Γ] [Fintype Q] [DecidableEq Γ] [DecidableEq Q]
  [Primcodable Γ] [Primcodable Q]
variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)
variable (A : Alphabet (Sigma ⊕ Unit) Γ) (M : Machine Q Γ)

local instance instDecidableEqXSigma_2 : DecidableEq (Tested.X Sigma Γ Q) := inferInstance
local instance instDecidableEqY_1 : DecidableEq (Y (Γ:=Γ) (Q:=Q)) := inferInstance
local instance instFintypeLetterSigmaProdBoolState (n : ℕ) : Fintype (Word.Letter Sigma (Bool×Γ) (ParameterMachine.State Q n)) := inferInstance

noncomputable def finiteTest (n : ℕ) (w : List (FiniteY (Γ:=Γ) (Q:=Q) n)) := testT A M n (w.map (includeY n))

noncomputable def finiteTables (n : ℕ) :=
  Uniform.fullTables (r:=relT n) (s:=relG k) markers (finiteCodeT (Γ:=Γ) (Q:=Q) k n) (finiteCodeG (Γ:=Γ) (Q:=Q) k n)
    (finiteLetters n) (zLetters k) (finiteTest A M n) (testG s n)

omit [Primcodable Γ] in
 theorem tables_eq_finite (n : ℕ) : tables s A M n=finiteTables s A M n := by
  have hT (j : ℕ) : Uniform.compute (yLetters n) (codeT (k:=k) n) (Rank.less (yLetters n)) markers.zero (testT A M n) j=
      Uniform.compute (finiteLetters n) (finiteCodeT (Γ:=Γ) (Q:=Q) k n).encode (fun u v => decide (List.Shortlex (relT n) u v))
        markers.zero (finiteTest A M n) j := by
    simpa only [map_finiteLetters] using Uniform.compute_map (includeY n) _ _ (lessT_map n) _ _ (fun w => (finiteCodeT_encode k n w).symm)
      markers.zero (finiteLetters n) (finiteTest A M n) (testT A M n) (fun _ => rfl) j
  have hG : codeG (Γ:=Γ) (Q:=Q) (k:=k) n=(finiteCodeG (Γ:=Γ) (Q:=Q) k n).encode :=
    funext (fun w => (finiteCodeG_encode k n w).symm)
  have hlG : Rank.less (zLetters k)=(fun u v => decide (List.Shortlex (relG k) u v)) :=
    funext (fun u => funext (lessG_eq k u))
  funext j
  simp only [tables,finiteTables,Uniform.fullTables,Uniform.tables,Uniform.bases,hT,hG,hlG]
  rfl

omit [Primcodable Γ] [Primcodable Q] in
 theorem codeT_order (k n : ℕ) (a b : FiniteY (Γ:=Γ) (Q:=Q) n) (hab : relT n a b) :
    List.Lex (fun u v : Sigma => u<v) ((finiteCodeT (Γ:=Γ) (Q:=Q) k n).block a) ((finiteCodeT (Γ:=Γ) (Q:=Q) k n).block b) :=
  LexBinary.code_order 0 1 2 (by decide) (by decide) (by decide) (by decide) _ _ _ _ _ _ hab
omit [DecidableEq Γ] [DecidableEq Q] [Primcodable Γ] [Primcodable Q] in
 theorem codeG_order (k n : ℕ) (a b : Z k) (hab : relG k a b) :
    List.Lex (fun u v : Sigma => u<v) ((finiteCodeG (Γ:=Γ) (Q:=Q) k n).block a) ((finiteCodeG (Γ:=Γ) (Q:=Q) k n).block b) :=
  LexBinary.code_order 3 4 5 (by decide) (by decide) (by decide) (by decide) _ _ _ _ _ _ hab

omit [Primcodable Γ] [Primcodable Q] in
 theorem codeT_alphabet (k n : ℕ) {u : Sigma} (hu : u∈(finiteCodeT (Γ:=Γ) (Q:=Q) k n).Alphabet) :
    u=0 ∨ u=1 ∨ u=2 := by
  exact LexBinary.alphabet_bound _ _ _ _ _ _ _ _ _ _ _ _ hu
omit [DecidableEq Γ] [DecidableEq Q] [Primcodable Γ] [Primcodable Q] in
 theorem codeG_alphabet (k n : ℕ) {u : Sigma} (hu : u∈(finiteCodeG (Γ:=Γ) (Q:=Q) k n).Alphabet) :
    u=3 ∨ u=4 ∨ u=5 := by
  exact LexBinary.alphabet_bound _ _ _ _ _ _ _ _ _ _ _ _ hu

omit [Primcodable Γ] [Primcodable Q] in
 theorem codeT_avoid (k n : ℕ) : ∀ b∈[markers.zero,markers.d,markers.l,markers.r,markers.h],
    b∉(finiteCodeT (Γ:=Γ) (Q:=Q) k n).Alphabet := by
  intro b hb hc
  have h := codeT_alphabet k n hc
  simp [markers] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl <;> norm_num [Fin.ext_iff] at h
omit [DecidableEq Γ] [DecidableEq Q] [Primcodable Γ] [Primcodable Q] in
 theorem codeG_avoid (k n : ℕ) : ∀ b∈[markers.zero,markers.d,markers.l,markers.r,markers.h],
    b∉(finiteCodeG (Γ:=Γ) (Q:=Q) k n).Alphabet := by
  intro b hb hc
  have h := codeG_alphabet k n hc
  simp [markers] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl <;> norm_num [Fin.ext_iff] at h
omit [Primcodable Γ] [Primcodable Q] in
 theorem codes_disjoint (k n : ℕ) : Disjoint (finiteCodeT (Γ:=Γ) (Q:=Q) k n).Alphabet (finiteCodeG (Γ:=Γ) (Q:=Q) k n).Alphabet := by
  apply Set.disjoint_left.mpr
  intro b hb hc
  have h := codeT_alphabet k n hb
  have j := codeG_alphabet k n hc
  rcases h with rfl|rfl|rfl <;> norm_num [Fin.ext_iff] at j

end Source
end FiniteAlgebraicEnvelopes.Bootstrap

end OAI
end

section
-- module Solutions.OAIFAE.MonoidAlgebras
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Finite compiler monoids, zero products, both F₂ algebras, and selector constructions.
-/

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
open Compiler Compiler.Simulator MachineRealization MachineRealization.ParameterCode
open scoped Compiler.HeadCodec
variable {Γ Q : Type*} [Fintype Γ] [Fintype Q] [DecidableEq Γ] [DecidableEq Q]
  [Primcodable Γ] [Primcodable Q]
variable (A : Alphabet (Sigma ⊕ Unit) Γ) (M : Machine Q Γ)

abbrev terminalAlphabet := UniversalMachine.restrict (ParameterMachine.alphabet A)
abbrev terminalMachine (n : ℕ) := ParameterMachine.machine A M (.inr ()) n

end FiniteAlgebraicEnvelopes.Bootstrap.Source

namespace FiniteAlgebraicEnvelopes
namespace Compiler.Word
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]
@[simp] theorem partialNormal_nil (f : List S → Part (List S)) : partialNormal A M f []=Part.some [] := by
  simp [partialNormal,preprocess,Path.prepare,Path.prepareChunks,RawRuns.partialSource,RawRuns.plan,RawRuns.execute]
end Compiler.Word

end FiniteAlgebraicEnvelopes

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source

section
open Compiler Compiler.Simulator MachineRealization

/-- The actual finite machine used uniformly in the source bootstrap.  Every
    field is constructed below from partial recursiveness of the universal
    word evaluator; none is an assumption on an input group. -/
structure Family where
  Γ : Type
  Q : Type
  [finiteΓ : Fintype Γ]
  [finiteQ : Fintype Q]
  [decΓ : DecidableEq Γ]
  [decQ : DecidableEq Q]
  [codeΓ : Primcodable Γ]
  [codeQ : Primcodable Q]
  A : Alphabet (Sigma ⊕ Unit) Γ
  M : Machine Q Γ
  decode : ∀ g a,(terminalAlphabet A).output g=some a → g=(terminalAlphabet A).input a
  realizes : ∀ n,Word.Realizes (terminalAlphabet A) (terminalMachine A M n) (raw n)

attribute [instance] Family.finiteΓ Family.finiteQ Family.decΓ Family.decQ Family.codeΓ Family.codeQ

 theorem exists_family : Nonempty Family := by
  classical
  obtain ⟨Γ,Q,hΓ,hQ,dΓ,A,M,hd,hr⟩ := UniversalMachine.exists_parameter_machine partrec_raw
  let : Fintype Γ := hΓ
  let : Fintype Q := hQ
  let : DecidableEq Γ := dΓ
  let : Primcodable Γ := Effect.finitePrimcodable Γ
  let : Primcodable Q := Effect.finitePrimcodable Q
  exact ⟨⟨Γ,Q,A,M,UniversalMachine.restrict_decode (ParameterMachine.alphabet A) (ParameterMachine.output_decode A hd),hr⟩⟩

noncomputable def family : Family := exists_family.some

end

open Compiler Compiler.Simulator MachineRealization
open scoped Compiler.HeadCodec

end FiniteAlgebraicEnvelopes.Bootstrap.Source

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
open Compiler Compiler.Simulator MachineRealization
variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word k => evalWord s w=1))

abbrev KAlphabet := terminalAlphabet family.A

end FiniteAlgebraicEnvelopes.Bootstrap.Source

end

end OAI
end

section
-- module Solutions.OAIFAE.AlgebraPresentations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Finite presentations of tensor, opposite, contracted, unitized, and coefficient algebras.
-/

namespace FiniteAlgebraicEnvelopes.AlgebraGenerators

section
open scoped TensorProduct
variable {k A B : Type*} [CommRing k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

def tensorGenerators (S : Set A) (T : Set B) : Set (A ⊗[k] B) :=
  ((Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B) '' S) ∪ ((Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B) '' T)

end

open scoped TensorProduct

end FiniteAlgebraicEnvelopes.AlgebraGenerators

end

end OAI
end

section
-- module Solutions.OAIFAE.ActionEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Full finitely presented faithful two-transitive action envelope and type-(A) applications.
-/

namespace FiniteAlgebraicEnvelopes.AffinePermutation
variable {Q V : Type*} [Group Q] [Group V] (α : Q →* MulAut V)

instance action : MulAction (V ⋊[α] Q) V where
  smul a v := a.left * α a.right v
  one_smul v := by
    change (1 : V) * α (1 : Q) v = v
    simp
  mul_smul a b v := by
    change (a*b).left * α (a*b).right v = a.left * α a.right (b.left * α b.right v)
    simp [map_mul,mul_assoc]

@[simp] theorem smul_apply (a : V ⋊[α] Q) (v : V) : a • v=a.left*α a.right v := rfl

/-- At every point, evaluation determines the translation from the linear component. -/
def stabilizerEquivalenceAt (v : V) : MulAction.stabilizer (V ⋊[α] Q) v ≃* Q :=
  MulEquiv.ofBijective (SemidirectProduct.rightHom.comp (MulAction.stabilizer (V ⋊[α] Q) v).subtype) (by
    constructor
    · intro a b he
      apply Subtype.ext
      apply SemidirectProduct.ext
      · have ha : a.val.left * α a.val.right v=v := a.property
        have hb : b.val.left * α b.val.right v=v := b.property
        change a.val.right=b.val.right at he
        rw [he] at ha
        exact mul_right_cancel (ha.trans hb.symm)
      · exact he
    · intro q
      refine ⟨⟨⟨v*(α q v)⁻¹,q⟩,?_⟩,rfl⟩
      change (v*(α q v)⁻¹)*α q v=v
      simp)

instance stabilizer_finitelyGenerated [Group.FG Q] (v : V) :
    Group.FG (MulAction.stabilizer (V ⋊[α] Q) v) :=
  Group.fg_of_surjective (f := (stabilizerEquivalenceAt α v).symm.toMonoidHom)
    (stabilizerEquivalenceAt α v).symm.surjective

end FiniteAlgebraicEnvelopes.AffinePermutation

end

end OAI
end

section
-- module Solutions.OAIFAE.AdjacentPermutations
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Coxeter presentation and universal lifts of finite symmetric groups.
-/

/- A normal-form argument for the adjacent transpositions. This is used for
symmetric coherence in the positive-object category of the endpoint quotient. -/
namespace FiniteAlgebraicEnvelopes.Adjacent

section
universe u
variable {H : Type u} [Group H]

/-- The Coxeter relations on the first `n` adjacent generators. -/
structure Relations (r : ℕ → H) (n : ℕ) : Prop where
  square : ∀ i, i < n → r i * r i = 1
  braid : ∀ i, i + 1 < n → r (i+1) * r i * r (i+1) = r i * r (i+1) * r i
  distant : ∀ i j, i + 1 < j → j < n → Commute (r i) (r j)

lemma Relations.mono {r : ℕ → H} {m n : ℕ} (h : Relations r n) (hmn : m ≤ n) :
    Relations r m :=
  ⟨fun i hi => h.square i (hi.trans_le hmn),
   fun i hi => h.braid i (hi.trans_le hmn),
   fun i j hij hj => h.distant i j hij (hj.trans_le hmn)⟩

/-- `r (n-1) ... r i`, with the empty product when `n ≤ i`. -/
def descending (r : ℕ → H) (i : ℕ) : ℕ → H
  | 0 => 1
  | n+1 => if i ≤ n then r n * descending r i n else 1

@[simp] lemma descending_zero (r : ℕ → H) (i : ℕ) : descending r i 0 = 1 := rfl
lemma descending_step (r : ℕ → H) {i n : ℕ} (hi : i ≤ n) :
    descending r i (n+1) = r n * descending r i n := ite_eq_left hi

lemma descending_empty (r : ℕ → H) {i n : ℕ} (hi : n ≤ i) : descending r i n = 1 := by
  cases n with
  | zero => rfl
  | succ n => simp only [descending, ite_eq_right (show ¬ i ≤ n by omega)]

lemma descending_commute {r : ℕ → H} {n : ℕ} (h : Relations r n)
    {j : ℕ} (hj : j < n) (i m : ℕ) (hm : m < j) :
    Commute (descending r i m) (r j) := by
  induction m with
  | zero => exact Commute.one_left _
  | succ m ih =>
    by_cases hi : i ≤ m
    · rw [descending_step r hi]
      exact (h.distant m j (by omega) hj).mul_left (ih (by omega))
    · rw [descending, ite_eq_right hi]
      exact Commute.one_left _

lemma descending_extend (r : ℕ → H) {i n : ℕ} (hi : i < n) :
    descending r (i+1) n * r i = descending r i n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : i = n
    · subst i
      rw [descending_empty r (Nat.le_refl _), descending_step r (Nat.le_refl _),
        descending_empty r (Nat.le_refl _), one_mul, mul_one]
    · rw [descending_step r (by omega), descending_step r (by omega), mul_assoc,
        ih (by omega)]

lemma descending_cancel {r : ℕ → H} {n i : ℕ} (h : Relations r n) (hi : i < n) :
    descending r i n * r i = descending r (i+1) n := by
  rw [← descending_extend r hi, mul_assoc, h.square i hi, mul_one]

lemma descending_last {r : ℕ → H} {n i : ℕ} (h : Relations r (n+1)) (hi : i < n) :
    descending r i (n+1) * r n = r (n-1) * descending r i (n+1) := by
  cases n with
  | zero => omega
  | succ n =>
    rw [descending_step r (by omega), descending_step r (by omega)]
    have hc := descending_commute h (show n+1 < n+1+1 by omega) i n (by omega)
    have hb := h.braid n (by omega)
    simp only [Nat.add_sub_cancel]
    calc
      _ = (r (n+1) * r n * r (n+1)) * descending r i n := by
        rw [mul_assoc, mul_assoc, hc.eq]
        group
      _ = _ := by rw [hb]; group

/-- The elementary normal-form multiplication rules. -/
lemma descending_mul {r : ℕ → H} {n : ℕ} (h : Relations r n)
    (i : ℕ) (hi : i ≤ n) (j : ℕ) (hj : j < n) :
    descending r i n * r j =
      if j+1 < i then r j * descending r i n else
      if j+1 = i then descending r j n else
      if j = i then descending r (i+1) n else
        r (j-1) * descending r i n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hie : i = n+1
    · subst i
      rw [descending_empty r (Nat.le_refl _), one_mul]
      by_cases hje : j = n
      · subst j
        simp only [Nat.lt_irrefl, ↓reduceIte, descending_step r (Nat.le_refl _),
          descending_empty r (Nat.le_refl _), mul_one]
      · simp only [show j+1 < n+1 by omega, ↓reduceIte, mul_one]
    · have hin : i ≤ n := by omega
      by_cases hje : j = n
      · subst j
        by_cases hie : i = n
        · subst i
          simp only [show ¬ n+1 < n by omega, show ¬ n+1 = n by omega,
            ↓reduceIte]
          exact descending_cancel h (by omega)
        · simp only [show ¬ n+1 < i by omega, show ¬ n+1 = i by omega,
            show ¬ n = i by omega, ↓reduceIte]
          exact descending_last h (by omega)
      · have hjn : j < n := by omega
        rw [descending_step r hin, mul_assoc, ih (h.mono (by omega)) hin hjn]
        split_ifs with h₁ h₂ h₃
        · rw [← mul_assoc, (h.distant j n (by omega) (by omega)).eq.symm, mul_assoc]
        · rw [descending_step r (by omega)]
        · rw [descending_step r (by omega)]
        · rw [← mul_assoc, (h.distant (j-1) n (by omega) (by omega)).eq.symm, mul_assoc]

def first (r : ℕ → H) (n : ℕ) : Set H := {g | ∃ i, i < n ∧ r i = g}

/-- Every element generated by `n+1` adjacent generators is in one of `n+2`
right cosets of the subgroup generated by the first `n`. -/
lemma normal_form {r : ℕ → H} {n : ℕ} (h : Relations r (n+1)) {g : H}
    (hg : g ∈ Subgroup.closure (first r (n+1))) :
    ∃ (i : ℕ), i ≤ n+1 ∧ ∃ k ∈ Subgroup.closure (first r n),
      g = k * descending r i (n+1) := by
  have step (g : H) (j : ℕ) (hj : j < n+1)
      (hg : ∃ i, i ≤ n+1 ∧ ∃ k ∈ Subgroup.closure (first r n),
        g = k * descending r i (n+1)) :
      ∃ i, i ≤ n+1 ∧ ∃ k ∈ Subgroup.closure (first r n),
        g * r j = k * descending r i (n+1) := by
    obtain ⟨i,hi,k,hk,rfl⟩ := hg
    rw [mul_assoc,descending_mul h i hi j hj]
    split_ifs with h₁ h₂ h₃
    · refine ⟨i,hi,k*r j,Subgroup.mul_mem _ hk ?_,(mul_assoc _ _ _).symm⟩
      exact Subgroup.subset_closure ⟨j,by omega,rfl⟩
    · exact ⟨j,by omega,k,hk,rfl⟩
    · exact ⟨i+1,by omega,k,hk,rfl⟩
    · refine ⟨i,hi,k*r (j-1),Subgroup.mul_mem _ hk ?_,(mul_assoc _ _ _).symm⟩
      exact Subgroup.subset_closure ⟨j-1,by omega,rfl⟩
  induction hg using Subgroup.closure_induction_right with
  | one =>
    exact ⟨n+1,le_rfl,1,Subgroup.one_mem _,by rw [descending_empty r le_rfl,mul_one]⟩
  | mul_right g hg a ha ih =>
    obtain ⟨i,hi,rfl⟩ := ha
    exact step g i hi ih
  | mul_inv_cancel g hg a ha ih =>
    obtain ⟨i,hi,rfl⟩ := ha
    rw [inv_eq_of_mul_eq_one_right (h.square i hi)]
    exact step g i hi ih

end

section
universe u

/-- The usual finite type-A Coxeter presentation. -/
def relators (n : ℕ) : Set (FreeGroup (Fin n)) := {w |
  (∃ i, w = FreeGroup.of i * FreeGroup.of i) ∨
  (∃ i j : Fin n, (j : ℕ) = (i : ℕ)+1 ∧ w =
    (FreeGroup.of j * FreeGroup.of i * FreeGroup.of j) *
      (FreeGroup.of i * FreeGroup.of j * FreeGroup.of i)⁻¹) ∨
  (∃ i j : Fin n, (i : ℕ)+1 < (j : ℕ) ∧ w =
    (FreeGroup.of i * FreeGroup.of j) * (FreeGroup.of j * FreeGroup.of i)⁻¹)}

abbrev Presentation (n : ℕ) := PresentedGroup (relators n)

noncomputable def generator (n i : ℕ) : Presentation n :=
  if hi : i < n then PresentedGroup.of ⟨i,hi⟩ else 1

@[simp] lemma generator_lt {n i : ℕ} (hi : i < n) :
    generator n i = PresentedGroup.of ⟨i,hi⟩ := dite_eq_left hi
@[simp] lemma generator_ge {n i : ℕ} (hi : n ≤ i) : generator n i = 1 :=
  dite_eq_right (by omega)

lemma generator_relations (n : ℕ) : Relations (generator n) n := by
  constructor
  · intro i hi
    simpa only [generator_lt hi, map_mul, PresentedGroup.of] using
      (PresentedGroup.one_of_mem (rels:=relators n)
        (show FreeGroup.of ⟨i,hi⟩ * FreeGroup.of ⟨i,hi⟩ ∈ relators n from
          Or.inl ⟨⟨i,hi⟩,rfl⟩))
  · intro i hi
    have h := PresentedGroup.one_of_mem (rels:=relators n)
      (show (FreeGroup.of ⟨i+1,hi⟩ * FreeGroup.of ⟨i,by omega⟩ * FreeGroup.of ⟨i+1,hi⟩) *
          (FreeGroup.of ⟨i,by omega⟩ * FreeGroup.of ⟨i+1,hi⟩ * FreeGroup.of ⟨i,by omega⟩)⁻¹ ∈ relators n from
        Or.inr (Or.inl ⟨⟨i,by omega⟩,⟨i+1,hi⟩,rfl,rfl⟩))
    simpa only [map_mul,map_inv,PresentedGroup.of,mul_inv_eq_one,generator_lt hi,
      generator_lt (show i<n by omega)] using h
  · intro i j hij hj
    have h := PresentedGroup.one_of_mem (rels:=relators n)
      (show (FreeGroup.of ⟨i,by omega⟩ * FreeGroup.of ⟨j,hj⟩) *
          (FreeGroup.of ⟨j,hj⟩ * FreeGroup.of ⟨i,by omega⟩)⁻¹ ∈ relators n from
        Or.inr (Or.inr ⟨⟨i,by omega⟩,⟨j,hj⟩,hij,rfl⟩))
    simpa only [map_mul,map_inv,PresentedGroup.of,mul_inv_eq_one,generator_lt hj,
      generator_lt (show i<n by omega),Commute,SemiconjBy] using h

variable {H : Type u} [Group H]
lemma relators_valid {r : ℕ → H} {n : ℕ} (h : Relations r n) :
    ∀ w ∈ relators n, FreeGroup.lift (fun i : Fin n => r i) w = 1 := by
  rintro w (⟨i,rfl⟩ | ⟨i,j,hij,rfl⟩ | ⟨i,j,hij,rfl⟩)
  · simpa only [map_mul,FreeGroup.lift_apply_of] using h.square i i.isLt
  · simp only [map_mul,map_inv,FreeGroup.lift_apply_of,mul_inv_eq_one]
    simpa only [hij] using h.braid i (by omega)
  · simp only [map_mul,map_inv,FreeGroup.lift_apply_of,mul_inv_eq_one]
    exact (h.distant i j hij j.isLt).eq

noncomputable def lift {r : ℕ → H} {n : ℕ} (h : Relations r n) : Presentation n →* H :=
  PresentedGroup.toGroup (relators_valid h)

@[simp] lemma lift_of {r : ℕ → H} {n : ℕ} (h : Relations r n) (i : Fin n) :
    lift h (PresentedGroup.of i) = r i := PresentedGroup.toGroup.of _
@[simp] lemma lift_generator {r : ℕ → H} {n i : ℕ} (h : Relations r n) (hi : i < n) :
    lift h (generator n i) = r i := by rw [generator_lt hi,lift_of]

lemma closure_first (n : ℕ) : Subgroup.closure (first (generator n) n) = ⊤ := by
  rw [show first (generator n) n = Set.range (PresentedGroup.of (rels:=relators n)) by
    ext g
    constructor
    · rintro ⟨i,hi,rfl⟩; exact ⟨⟨i,hi⟩,(generator_lt hi).symm⟩
    · rintro ⟨i,rfl⟩; exact ⟨i,i.isLt,generator_lt i.isLt⟩]
  exact PresentedGroup.closure_range_of _

noncomputable def inclusion (n : ℕ) : Presentation n →* Presentation (n+1) :=
  lift ((generator_relations (n+1)).mono (Nat.le_succ n))

@[simp] lemma inclusion_of (n : ℕ) (i : Fin n) :
    inclusion n (PresentedGroup.of i) = generator (n+1) i := lift_of _ i

lemma presentation_normal (n : ℕ) (g : Presentation (n+1)) :
    ∃ i, i ≤ n+1 ∧ ∃ k : Presentation n,
      g = inclusion n k * descending (generator (n+1)) i (n+1) := by
  have hg : g ∈ Subgroup.closure (first (generator (n+1)) (n+1)) := by
    rw [closure_first]; trivial
  obtain ⟨i,hi,k,hk,hg⟩ := normal_form (generator_relations (n+1)) hg
  have hm : Subgroup.closure (first (generator (n+1)) n) ≤ (inclusion n).range := by
    rw [Subgroup.closure_le]
    rintro z ⟨j,hj,rfl⟩
    exact ⟨PresentedGroup.of ⟨j,hj⟩,inclusion_of n ⟨j,hj⟩⟩
  obtain ⟨k,rfl⟩ := hm hk
  exact ⟨i,hi,k,hg⟩

end

universe u

lemma map_descending {H K : Type*} [Group H] [Group K] (f : H →* K)
    (r : ℕ → H) (i n : ℕ) : f (descending r i n) = descending (fun j => f (r j)) i n := by
  induction n with
  | zero => exact map_one f
  | succ n ih => simp only [descending]; split_ifs <;> simp [ih]

def natSwap (i : ℕ) : Equiv.Perm ℕ := Equiv.swap i (i+1)

lemma natSwap_relations (n : ℕ) : Relations natSwap n := by
  constructor
  · intro i _; exact Equiv.swap_mul_self _ _
  · intro i _
    ext a
    simp only [natSwap,Equiv.Perm.mul_apply,Equiv.swap_apply_def]
    split_ifs <;> omega
  · intro i j hij _
    apply Equiv.Perm.Disjoint.commute
    apply Equiv.Perm.disjoint_swap_swap
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,
      not_false_eq_true,List.nodup_nil,and_true,not_or]
    omega

noncomputable def natEvaluation (n : ℕ) : Presentation n →* Equiv.Perm ℕ :=
  lift (natSwap_relations n)

@[simp] lemma natEvaluation_of (n : ℕ) (i : Fin n) :
    natEvaluation n (PresentedGroup.of i) = natSwap i := lift_of _ _
@[simp] lemma natEvaluation_generator {n i : ℕ} (hi : i < n) :
    natEvaluation n (generator n i) = natSwap i := lift_generator _ hi

lemma natEvaluation_inclusion (n : ℕ) :
    (natEvaluation (n+1)).comp (inclusion n) = natEvaluation n := by
  apply PresentedGroup.ext
  intro i
  simp [show (i:ℕ)<n+1 by omega]

lemma natEvaluation_fixes {n : ℕ} (g : Presentation n) {k : ℕ} (hk : n < k) :
    natEvaluation n g k = k := by
  have hg : g ∈ Subgroup.closure (first (generator n) n) := by rw [closure_first]; trivial
  induction hg using Subgroup.closure_induction_right with
  | one => simp
  | mul_right g hg a ha ih =>
    obtain ⟨i,hi,rfl⟩ := ha
    rw [map_mul,Equiv.Perm.mul_apply,natEvaluation_generator hi]
    simpa [natSwap,Equiv.swap_apply_def,show k≠i by omega,show k≠i+1 by omega] using ih
  | mul_inv_cancel g hg a ha ih =>
    obtain ⟨i,hi,rfl⟩ := ha
    rw [inv_eq_of_mul_eq_one_right ((generator_relations n).square i hi)]
    rw [map_mul,Equiv.Perm.mul_apply,natEvaluation_generator hi]
    simpa [natSwap,Equiv.swap_apply_def,show k≠i by omega,show k≠i+1 by omega] using ih

lemma descending_nat_apply {i n : ℕ} (hi : i ≤ n) : descending natSwap i n i = n := by
  induction n with
  | zero =>
    have : i=0 := by omega
    subst i
    rfl
  | succ n ih =>
    by_cases hin : i ≤ n
    · rw [descending_step natSwap hin,Equiv.Perm.mul_apply,ih hin]
      exact Equiv.swap_apply_left _ _
    · have : i=n+1 := by omega
      subst i
      rw [descending_empty natSwap le_rfl]; rfl

lemma natEvaluation_descending {n i : ℕ} (hi : i ≤ n) :
    natEvaluation n (descending (generator n) i n) i = n := by
  have hmap (m : ℕ) (hm : m ≤ n) :
      natEvaluation n (descending (generator n) i m) = descending natSwap i m := by
    induction m with
    | zero => simp
    | succ m ih =>
      simp only [descending]
      split_ifs <;> simp [show m<n by omega,ih (by omega)]
  rw [hmap n le_rfl]
  exact descending_nat_apply hi

lemma natEvaluation_injective (n : ℕ) : Function.Injective (natEvaluation n) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro g hg
  change natEvaluation n g = 1 at hg
  change g = 1
  induction n with
  | zero =>
    have hc := closure_first 0
    have he : first (generator 0) 0 = ∅ := by ext g; simp [first]
    rw [he,Subgroup.closure_empty] at hc
    have : g ∈ (⊥ : Subgroup (Presentation 0)) := by rw [hc]; trivial
    exact this
  | succ n ih =>
    obtain ⟨i,hi,k,rfl⟩ := presentation_normal n g
    have he : natEvaluation (n+1) (inclusion n k) = natEvaluation n k :=
      DFunLike.congr_fun (natEvaluation_inclusion n) k
    have ha := congrArg (fun f : Equiv.Perm ℕ => f i) hg
    rw [map_mul,Equiv.Perm.mul_apply,he,natEvaluation_descending hi,
      natEvaluation_fixes k (Nat.lt_succ_self n)] at ha
    change n+1=i at ha
    subst i
    rw [descending_empty _ le_rfl,mul_one] at hg ⊢
    rw [he] at hg
    rw [ih hg,map_one]

noncomputable def natExtend (n : ℕ) : Equiv.Perm (Fin n) →* Equiv.Perm ℕ :=
  Equiv.Perm.ofSubtype.comp (Equiv.permCongrHom Fin.equivSubtype).toMonoidHom

lemma natExtend_injective (n : ℕ) : Function.Injective (natExtend n) :=
  Equiv.Perm.ofSubtype_injective.comp (Equiv.permCongrHom Fin.equivSubtype).injective

@[simp] lemma natExtend_swap (n : ℕ) (i j : Fin n) :
    natExtend n (Equiv.swap i j) = Equiv.swap (i:ℕ) (j:ℕ) := by
  have hc : (Equiv.permCongrHom Fin.equivSubtype) (Equiv.swap i j) =
      Equiv.swap (Fin.equivSubtype i) (Fin.equivSubtype j) :=
    Equiv.symm_trans_swap_trans i j Fin.equivSubtype
  rw [natExtend,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,hc,Equiv.Perm.ofSubtype_swap_eq]
  rfl

noncomputable def finSwap (n i : ℕ) : Equiv.Perm (Fin (n+1)) :=
  if hi : i < n then Equiv.swap ⟨i,by omega⟩ ⟨i+1,by omega⟩ else 1

lemma finSwap_lt {n i : ℕ} (hi : i < n) :
    finSwap n i = Equiv.swap ⟨i,by omega⟩ ⟨i+1,by omega⟩ := dite_eq_left hi

lemma natExtend_finSwap {n i : ℕ} (hi : i < n) :
    natExtend (n+1) (finSwap n i) = natSwap i := by
  rw [finSwap_lt hi,natExtend_swap]; rfl

lemma finSwap_relations (n : ℕ) : Relations (finSwap n) n := by
  constructor
  · intro i hi
    apply natExtend_injective (n+1)
    simpa only [map_mul,natExtend_finSwap hi,map_one] using (natSwap_relations n).square i hi
  · intro i hi
    apply natExtend_injective (n+1)
    simpa only [map_mul,natExtend_finSwap hi,natExtend_finSwap (show i<n by omega)] using
      (natSwap_relations n).braid i hi
  · intro i j hij hj
    apply (natExtend_injective (n+1))
    simpa only [map_mul,natExtend_finSwap hj,natExtend_finSwap (show i<n by omega)] using
      ((natSwap_relations n).distant i j hij hj).eq

noncomputable def finEvaluation (n : ℕ) : Presentation n →* Equiv.Perm (Fin (n+1)) :=
  lift (finSwap_relations n)

@[simp] lemma finEvaluation_of (n : ℕ) (i : Fin n) :
    finEvaluation n (PresentedGroup.of i) = Equiv.swap i.castSucc i.succ := by
  rw [finEvaluation,lift_of,finSwap_lt i.isLt]; rfl

lemma natExtend_finEvaluation (n : ℕ) :
    (natExtend (n+1)).comp (finEvaluation n) = natEvaluation n := by
  apply PresentedGroup.ext
  intro i
  simp only [MonoidHom.comp_apply,finEvaluation_of,natExtend_swap,natEvaluation_of]
  rfl

lemma finEvaluation_bijective (n : ℕ) : Function.Bijective (finEvaluation n) := by
  constructor
  · exact Function.Injective.of_comp (f:=natExtend (n+1))
      (show Function.Injective ((natExtend (n+1)) ∘ finEvaluation n) from
        by
          change Function.Injective (((natExtend (n+1)).comp (finEvaluation n)) : _ → _)
          rw [natExtend_finEvaluation]
          exact natEvaluation_injective n)
  · have hc : Submonoid.closure (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) ≤
        (finEvaluation n).range.toSubmonoid := by
      rw [Submonoid.closure_le]
      rintro s ⟨i,rfl⟩
      exact ⟨PresentedGroup.of i,finEvaluation_of n i⟩
    intro p
    have hp : p ∈ (finEvaluation n).range := hc (by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial)
    exact hp

noncomputable def permutationEquiv (n : ℕ) : Presentation n ≃* Equiv.Perm (Fin (n+1)) :=
  MulEquiv.ofBijective (finEvaluation n) (finEvaluation_bijective n)

/-- Coxeter's relations are sufficient, not just necessary: any adjacent family
satisfying the three local laws gives a canonical finite permutation action. -/
noncomputable def permutationLift {H : Type u} [Group H] {n : ℕ} {r : ℕ → H}
    (h : Relations r n) : Equiv.Perm (Fin (n+1)) →* H :=
  (lift h).comp (permutationEquiv n).symm.toMonoidHom

@[simp] lemma permutationLift_swap {H : Type u} [Group H] {n : ℕ} {r : ℕ → H}
    (h : Relations r n) (i : Fin n) :
    permutationLift h (Equiv.swap i.castSucc i.succ) = r i := by
  change lift h ((permutationEquiv n).symm _) = r i
  rw [show Equiv.swap i.castSucc i.succ = permutationEquiv n (PresentedGroup.of i) from
    (finEvaluation_of n i).symm,MulEquiv.symm_apply_apply,lift_of]

end FiniteAlgebraicEnvelopes.Adjacent

end OAI
end

section
-- module Solutions.OAIFAE.BinaryCoherence
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Binary combs, folds, permutations, and coherent exchanges.
-/

namespace FiniteAlgebraicEnvelopes
namespace Adjacent
lemma permutation_induction {n : ℕ} {P : Equiv.Perm (Fin (n+1)) → Prop}
    (hone : P 1) (hswap : ∀ i : Fin n, P (Equiv.swap i.castSucc i.succ))
    (hmul : ∀ p q, P p → P q → P (p*q)) (p : Equiv.Perm (Fin (n+1))) : P p := by
  have hp : p ∈ Submonoid.closure (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial
  induction hp using Submonoid.closure_induction with
  | mem p hp => obtain ⟨i,rfl⟩ := hp; exact hswap i
  | one => exact hone
  | mul p q hp hq ihp ihq => exact hmul p q ihp ihq

@[simp] lemma natExtend_apply (n : ℕ) (p : Equiv.Perm (Fin n)) (i : Fin n) :
    natExtend n p i = (p i : ℕ) := by
  change Equiv.Perm.ofSubtype ((Equiv.permCongrHom Fin.equivSubtype) p) (↑(Fin.equivSubtype i)) = _
  rw [Equiv.Perm.ofSubtype_apply_coe]
  rfl

end Adjacent
end FiniteAlgebraicEnvelopes

namespace FiniteAlgebraicEnvelopes
namespace Adjacent
universe u
variable {H : Type u} [Group H]
lemma descending_congr (r s : ℕ → H) (i n : ℕ) (h : ∀ j,j<n → r j=s j) :
    descending r i n=descending s i n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [descending]
    split_ifs
    · rw [h n (by omega),ih (fun j hj=>h j (by omega))]
    · rfl

lemma descending_head (r : ℕ → H) (n : ℕ) :
    descending r 0 (n+1)=descending (fun i=>r (i+1)) 0 n*r 0 := by
  induction n with
  | zero => simp only [descending,Nat.zero_le,↓reduceIte,mul_one,one_mul]
  | succ n ih =>
    rw [descending_step r (Nat.zero_le _),ih,
      descending_step (fun i=>r (i+1)) (Nat.zero_le _),mul_assoc]

lemma descending_nat_zero_apply (n k : ℕ) :
    descending natSwap 0 n k = if k=0 then n else if k≤n then k-1 else k := by
  induction n with
  | zero => simp only [descending_zero,Equiv.Perm.one_apply]; split_ifs <;> omega
  | succ n ih =>
    rw [descending_step natSwap (Nat.zero_le _),Equiv.Perm.mul_apply,ih]
    simp only [natSwap,Equiv.swap_apply_def]
    split_ifs <;> omega

lemma natExtend_descending (n i k : ℕ) (hk : k≤n) :
    natExtend (n+1) (descending (finSwap n) i k)=descending natSwap i k := by
  rw [map_descending]
  apply descending_congr
  intro j hj
  exact natExtend_finSwap (by omega)
end Adjacent
end FiniteAlgebraicEnvelopes

end

end OAI
end


