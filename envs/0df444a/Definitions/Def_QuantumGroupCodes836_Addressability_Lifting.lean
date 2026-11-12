-- Prove2me | Definitions.Def_QuantumGroupCodes836_Addressability_Lifting
-- name    : QuantumGroupCodes836_Addressability_Lifting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T17:11:28.885327+00:00
-- url     : https://prove2.me/theorems/48f9348b-f1b7-4e2c-84e4-204779e3762a
-- title:
--   Constant-changing AG lifts and actual module-freeness predicates
-- statement:
--   A lifting datum contains two actual constant fields, a one-variable extension field, a finite field embedding and an enumeration of rational evaluation places. It contains no distance, freeness or decoder certificates. The group is the subgroup of actual automorphisms fixing both embedded base field and enlarged constants.
--
--   $$\widetilde P=\operatorname{Con}(P),\qquad\widetilde D=\operatorname{Con}(D).$$
--
--   Differential cotrace is Kähler pullback. Freeness means an explicit equivariant linear isomorphism from copies of the regular representation. The lifting conclusions are predicates on these computed objects, to be established by existence theorems. Classical decoding is represented as exact error recovery from the corresponding syndrome, and designed-distance bounds quantify over every nonzero word.
-- source:
--   Virgile Guemard, Jean Gasnier, STOC 2027 submission #836 (October 2026), Theorems 4.1,4.4,4.7 and Corollary 4.5, pp.14–18; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/836.pdf

import Mathlib
import Definitions.Def_QuantumGroupCodes836_Addressability_FunctionFields
import Definitions.Def_QuantumGroupCodes836_Addressability_Decoder

set_option autoImplicit false
noncomputable section

namespace QuantumGroupCodes836.Addressability
open AlgebraicCurve KaehlerDifferential

/-- Kähler pullback is differential cotrace, also when the constant field changes. -/
def cotrace {k l : Type} [Field k] [Field l] [Algebra k l]
    {F : FunctionFieldData k} {E : FunctionFieldData l} (T : FieldExtension F E)
    (ω : Ω[F.carrier⁄k]) : Ω[E.carrier⁄l] := by
  letI : Algebra F.carrier E.carrier := T.inclusion.toAlgebra
  letI : Algebra k E.carrier := ((algebraMap l E.carrier).comp (algebraMap k l)).toAlgebra
  letI : IsScalarTower k F.carrier E.carrier :=
    IsScalarTower.of_algebraMap_eq fun a => (T.constants a).symm
  letI : IsScalarTower k l E.carrier := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact KaehlerDifferential.map k l F.carrier E.carrier ω

def extensionAutomorphisms {k l : Type} [Field k] [Field l] [Algebra k l]
    {F : FunctionFieldData k} {E : FunctionFieldData l} (T : FieldExtension F E) :
    Subgroup (E.carrier ≃ₐ[l] E.carrier) where
  carrier := {σ | ∀ x, σ (T.inclusion x) = T.inclusion x}
  one_mem' := by intro x; rfl
  mul_mem' := by intro σ τ hσ hτ x; change σ (τ (T.inclusion x)) = _; rw [hτ, hσ]
  inv_mem' := by
    intro σ hσ x
    change σ.symm (T.inclusion x) = T.inclusion x
    calc
      σ.symm (T.inclusion x) = σ.symm (σ (T.inclusion x)) := congrArg σ.symm (hσ x).symm
      _ = T.inclusion x := σ.symm_apply_apply _

structure LiftData {k : Type} [Field k] (F : FunctionFieldData k) where
  constants : Type
  field : Field constants
  finiteConstants : Fintype constants
  constantAlgebra : Algebra k constants
  upstairs : FunctionFieldData constants
  extension : FieldExtension F upstairs
  evaluation : EvaluationData upstairs

attribute [instance] LiftData.field LiftData.finiteConstants LiftData.constantAlgebra

abbrev LiftData.group {k : Type} [Field k] {F : FunctionFieldData k} (L : LiftData F) :=
  extensionAutomorphisms L.extension

def IsAbelian {G : Type*} [Group G] : Prop := ∀ σ τ : G, σ * τ = τ * σ

def SeparableExtension {k l : Type} [Field k] [Field l] [Algebra k l]
    {F : FunctionFieldData k} {E : FunctionFieldData l} (T : FieldExtension F E) : Prop :=
  letI := T.inclusion.toAlgebra
  Algebra.IsSeparable F.carrier E.carrier

def RRFree {k : Type} [Field k] {F : FunctionFieldData k}
    (L : LiftData F) (D : Divisors F) (r : ℕ) : Prop :=
  ∃ B : (Fin r × L.group → L.constants) ≃ₗ[L.constants] rrSpace (conorm L.extension D),
    ∀ σ f, (B (fun j => f (j.1, σ⁻¹ * j.2)) : L.upstairs.carrier) =
      (σ.val : L.upstairs.carrier ≃ₐ[L.constants] L.upstairs.carrier) (B f)

def CodeFree {F I G : Type*} [Field F] [Group G] {C : Code F I}
    (A : CodeAction F I G C) (r : ℕ) : Prop :=
  ∃ B : (Fin r × G → F) ≃ₗ[F] C, ∀ σ f,
    (B (fun j => f (j.1, σ⁻¹ * j.2)) : I → F) = permute (A.coordinates σ) (B f)

def AGAssumptions {k : Type} [Field k] {F : FunctionFieldData k}
    (P : EvaluationData F) (D : Divisors F) (m : ℕ) (η : Ω[F.carrier⁄k]) : Prop :=
  (∀ i, D (P.places i) = 0) ∧
  2 * (genus F : ℤ) - 2 < Divisor.degree D ∧ Divisor.degree D < P.n ∧
  0 < m ∧ η ≠ 0 ∧ (∀ i, (P.places i).ordDifferential η = -1) ∧
  (m + 1) • D ≤ evaluationDivisor P + differentialDivisor η

def ClassicalDistanceBound {F I : Type*} [Field F] [Fintype I]
    (C : Code F I) (d : ℤ) : Prop :=
  ∀ c : C, c ≠ 0 → d ≤ weight (c : I → F)

/-- The intermediate constant extension F′ is generated inside the actual lifted field. -/
def GaloisOverConstantSubfield {k : Type} [Field k] {F : FunctionFieldData k}
    (L : LiftData F) : Prop :=
  letI : Algebra F.carrier L.upstairs.carrier := L.extension.inclusion.toAlgebra
  let K := IntermediateField.adjoin F.carrier (Set.range (algebraMap L.constants L.upstairs.carrier))
  IsGalois K L.upstairs.carrier

/-- This predicate contains the six computed conclusions of Corollary 4.5;
it is a conclusion of existence theorems, never a starting-family hypothesis. -/
def LiftCodeProperties {k : Type} [Field k] [Fintype k] {F : FunctionFieldData k}
    (P : EvaluationData F) (D : Divisors F) (m : ℕ) (L : LiftData F) : Prop :=
  Fintype.card L.constants = (Fintype.card k)^2 ∧
  Unramified L.extension ∧ SeparableExtension L.extension ∧ GaloisOverConstantSubfield L ∧ IsAbelian (G := L.group) ∧
  evaluationDivisor L.evaluation = conorm L.extension (evaluationDivisor P) ∧
  L.evaluation.n = P.n * Nat.card L.group ∧
  ∃ A : CodeAction L.constants (Fin L.evaluation.n) L.group
      (agCode L.evaluation (conorm L.extension D)),
    (∀ σ j, L.evaluation.places (A.coordinates σ j) = σ.val • L.evaluation.places j) ∧
    CodeFree A (Module.finrank k (agCode P D)) ∧
    Multiplication (agCode L.evaluation (conorm L.extension D)) m ∧
    Module.finrank L.constants (agCode L.evaluation (conorm L.extension D)) =
      Module.finrank k (agCode P D) * Nat.card L.group ∧
    ClassicalDistanceBound (agCode L.evaluation (conorm L.extension D))
      (((P.n : ℤ) - Divisor.degree D) * Nat.card L.group) ∧
    ∃ B : CodeAction L.constants (Fin L.evaluation.n) L.group
        (dual (agCode L.evaluation (conorm L.extension D))),
      B.coordinates = A.coordinates ∧
      CodeFree B (P.n - Module.finrank k (agCode P D)) ∧
      Module.finrank L.constants (dual (agCode L.evaluation (conorm L.extension D))) =
        (P.n - Module.finrank k (agCode P D)) * Nat.card L.group ∧
      ClassicalDistanceBound (dual (agCode L.evaluation (conorm L.extension D)))
        ((Divisor.degree D - 2 * genus F + 2) * Nat.card L.group)

def ClassicalCSS {F : Type} [Field F] {n : ℕ} (C : Code F (Fin n)) : CSS F :=
  ⟨n, ⊥, C, bot_le⟩

end QuantumGroupCodes836.Addressability


