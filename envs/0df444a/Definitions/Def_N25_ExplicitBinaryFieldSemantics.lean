-- Prove2me | Definitions.Def_N25_ExplicitBinaryFieldSemantics
-- name    : N25_ExplicitBinaryFieldSemantics
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:14:12.651138+00:00
-- url     : https://prove2.me/theorems/0d28dfb5-9fa2-4fd3-8f34-2adcbe7e55d3
-- title:
--   Semantic fields attached to certified binary operation tables
-- statement:
--   Given a finite carrier $R$, a characteristic-two operation table, and a chosen inverse function, the file defines a tagged wrapper carrying exactly those zero, one, addition, multiplication, negation, and inverse operations. A complete table certificate installs a genuine field structure, and the file specializes this construction to semantic copies of $𝔽_4$, $𝔽_8$, and $𝔽_{16}$, with equivalences back to the raw carriers and their normalized curve-point predicates. This technical bridge turns executable table counts into ordinary finite-field statements without changing the computations.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_ExplicitF16Field
import Definitions.Def_N25_NormalizedPointPredicates
/-!
# Field semantics for the executable binary N25 models

The binary point-count files use small operation tables so that Lean can
check the finite enumerations in the kernel.  Those raw types are not yet
coefficient fields: in particular the raw `F4` type is a product whose
ambient product multiplication is not the multiplication of the four-element
field.

This file supplies the semantic bridge without changing the executable
tables.  A wrapper type remembers the certified table in its type, installs
exactly those operations as a field, and identifies its canonical curve
points with the points enumerated by the raw table.  The wrapper avoids any
typeclass diamond with operations already present on a raw carrier.
-/

namespace MazurProof.RationalPointsN25QuotientBinaryFieldSemantics

open RationalPointsN25QuotientF2
open RationalPointsN25QuotientWeil
open RationalPointsN25QuotientSmoothF2
open RationalPointsN25QuotientF16Field

/-! ## A field built from a certified characteristic-two operation table -/

/-- A copy of a raw finite carrier tagged by its binary operation table and
its chosen inverse function.  Keeping the table as a type parameter makes
the induced algebraic operations canonical on the wrapper. -/
structure BinaryFieldModel (R : Type*) (O : BinaryRingOperations R)
    (tableInv : R → R) where
  raw : R
deriving DecidableEq, Fintype

namespace BinaryFieldModel

variable {R : Type*} (O : BinaryRingOperations R) (tableInv : R → R)

/-- The raw zero, viewed in the semantic wrapper. -/
instance : Zero (BinaryFieldModel R O tableInv) := ⟨⟨O.zero⟩⟩

/-- The raw one, viewed in the semantic wrapper. -/
instance : One (BinaryFieldModel R O tableInv) := ⟨⟨O.one⟩⟩

/-- Addition is exactly the certified table addition. -/
instance : Add (BinaryFieldModel R O tableInv) :=
  ⟨fun a b => ⟨O.add a.raw b.raw⟩⟩

/-- Every element is its own additive inverse in characteristic two. -/
instance : Neg (BinaryFieldModel R O tableInv) := ⟨fun a => a⟩

/-- Multiplication is exactly the certified table multiplication. -/
instance : Mul (BinaryFieldModel R O tableInv) :=
  ⟨fun a b => ⟨O.mul a.raw b.raw⟩⟩

/-- The field inverse uses the certified inverse away from zero and sends
zero to zero, as required by Lean's total inverse convention. -/
def inverseValue [DecidableEq R] (a : R) : R :=
  if a = O.zero then O.zero else tableInv a

/-- The total inverse induced by `inverseValue`. -/
instance [DecidableEq R] : Inv (BinaryFieldModel R O tableInv) :=
  ⟨fun a => ⟨inverseValue O tableInv a.raw⟩⟩

/-- Forgetting the wrapper sends semantic zero to the table zero. -/
@[simp] theorem raw_zero :
    (0 : BinaryFieldModel R O tableInv).raw = O.zero := rfl

/-- Forgetting the wrapper sends semantic one to the table one. -/
@[simp] theorem raw_one :
    (1 : BinaryFieldModel R O tableInv).raw = O.one := rfl

/-- Forgetting the wrapper sends semantic addition to table addition. -/
@[simp] theorem raw_add (a b : BinaryFieldModel R O tableInv) :
    (a + b).raw = O.add a.raw b.raw := rfl

/-- Forgetting the wrapper sends semantic multiplication to table
multiplication. -/
@[simp] theorem raw_mul (a b : BinaryFieldModel R O tableInv) :
    (a * b).raw = O.mul a.raw b.raw := rfl

/-- Equality in the wrapper is exactly equality of raw coordinates. -/
@[simp] theorem eq_iff_raw_eq (a b : BinaryFieldModel R O tableInv) :
    a = b ↔ a.raw = b.raw := by
  constructor
  · exact fun hEq => congrArg BinaryFieldModel.raw hEq
  · cases a
    cases b
    simp only [BinaryFieldModel.mk.injEq]
    exact fun hEq => hEq

/-- A certified binary operation table determines a field on its
semantic wrapper.  This theorem uses every algebraic law in
`IsBinaryFieldTable`; no cardinality argument supplies a missing ring law. -/
@[reducible] def field [DecidableEq R]
    (h : IsBinaryFieldTable O tableInv) :
    Field (BinaryFieldModel R O tableInv) := by
  rcases h with
    ⟨hzeroOne, haddAssoc, haddComm, hzeroAdd, haddSelf,
      hmulAssoc, hmulComm, honeMul, hzeroMul, hmulAdd, hmulInv⟩
  apply Field.ofMinimalAxioms (BinaryFieldModel R O tableInv)
  · rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
    exact congrArg BinaryFieldModel.mk (haddAssoc a b c)
  · rintro ⟨a⟩
    exact congrArg BinaryFieldModel.mk (hzeroAdd a)
  · rintro ⟨a⟩
    exact congrArg BinaryFieldModel.mk (haddSelf a)
  · rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
    exact congrArg BinaryFieldModel.mk (hmulAssoc a b c)
  · rintro ⟨a⟩ ⟨b⟩
    exact congrArg BinaryFieldModel.mk (hmulComm a b)
  · rintro ⟨a⟩
    exact congrArg BinaryFieldModel.mk (honeMul a)
  · rintro ⟨a⟩ ha
    have haRaw : a ≠ O.zero := by
      intro hEq
      apply ha
      exact congrArg BinaryFieldModel.mk hEq
    apply congrArg BinaryFieldModel.mk
    change O.mul a (inverseValue O tableInv a) = O.one
    rw [inverseValue, if_neg haRaw]
    exact hmulInv a haRaw
  · exact congrArg BinaryFieldModel.mk (by simp [inverseValue])
  · rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
    exact congrArg BinaryFieldModel.mk (hmulAdd a b c)
  · exact ⟨⟨O.zero⟩, ⟨O.one⟩, fun hEq =>
      hzeroOne (congrArg BinaryFieldModel.raw hEq)⟩

/-- Forgetting the semantic wrapper is an equivalence of finite carriers. -/
def rawEquiv : BinaryFieldModel R O tableInv ≃ R where
  toFun := BinaryFieldModel.raw
  invFun := BinaryFieldModel.mk
  left_inv a := by cases a; rfl
  right_inv _ := rfl

end BinaryFieldModel

/-! ## The three executable extension fields as semantic fields -/

/-- Semantic copy of the executable four-element field. -/
abbrev SemanticF4 := BinaryFieldModel F4 f4Operations f4Inv

/-- Semantic copy of the executable eight-element field. -/
abbrev SemanticF8 := BinaryFieldModel F8 f8Operations f8Inv

/-- Semantic copy of the executable sixteen-element field. -/
abbrev SemanticF16 := BinaryFieldModel F16 f16Operations f16Inv

/-- The complete table certificate installs the field structure on `F4`. -/
instance semanticF4Field : Field SemanticF4 :=
  BinaryFieldModel.field f4Operations f4Inv f4_isBinaryFieldTable

/-- The complete table certificate installs the field structure on `F8`. -/
instance semanticF8Field : Field SemanticF8 :=
  BinaryFieldModel.field f8Operations f8Inv f8_isBinaryFieldTable

/-- The split quartic certificates install the field structure on `F16`. -/
instance semanticF16Field : Field SemanticF16 :=
  BinaryFieldModel.field f16Operations f16Inv f16_isBinaryFieldTable

/-- The semantic four-element field has characteristic two. -/
instance semanticF4CharP : CharP SemanticF4 2 :=
  charP_of_card_eq_prime_pow (by decide : Fintype.card SemanticF4 = 2 ^ 2)

/-- The semantic eight-element field has characteristic two. -/
instance semanticF8CharP : CharP SemanticF8 2 :=
  charP_of_card_eq_prime_pow (by decide : Fintype.card SemanticF8 = 2 ^ 3)

/-- The semantic sixteen-element field has characteristic two. -/
instance semanticF16CharP : CharP SemanticF16 2 :=
  charP_of_card_eq_prime_pow (by decide : Fintype.card SemanticF16 = 2 ^ 4)

/-! ## Pointwise compatibility with the executable predicates -/

/-- The binary operation record lifted from a raw table to its semantic
wrapper. -/
def liftedOperations {R : Type*} (O : BinaryRingOperations R)
    (tableInv : R → R) :
    BinaryRingOperations (BinaryFieldModel R O tableInv) where
  zero := ⟨O.zero⟩
  one := ⟨O.one⟩
  add := fun a b => ⟨O.add a.raw b.raw⟩
  mul := fun a b => ⟨O.mul a.raw b.raw⟩

/-- The operation record obtained from the certified field structure is
definitionally the lifted executable table. -/
theorem fieldBinaryOperations_model_eq
    {R : Type*} [DecidableEq R] {O : BinaryRingOperations R}
    {tableInv : R → R} (h : IsBinaryFieldTable O tableInv) :
    @fieldBinaryOperations (BinaryFieldModel R O tableInv)
      (BinaryFieldModel.field O tableInv h) =
        liftedOperations O tableInv := by
  rcases h with
    ⟨hzeroOne, haddAssoc, haddComm, hzeroAdd, haddSelf,
      hmulAssoc, hmulComm, honeMul, hzeroMul, hmulAdd, hmulInv⟩
  rfl

/-- Apply the raw-carrier equivalence coordinatewise to normalized
projective charts.  No ring structure is needed for this chart equivalence. -/
def normalizedRawEquiv {R : Type*} {O : BinaryRingOperations R}
    {tableInv : R → R} :
    NormalizedProjective4 (BinaryFieldModel R O tableInv) ≃
      NormalizedProjective4 R where
  toFun
    | .xChart y z w => .xChart y.raw z.raw w.raw
    | .yChart z w => .yChart z.raw w.raw
    | .zChart w => .zChart w.raw
    | .wChart => .wChart
  invFun
    | .xChart y z w => .xChart ⟨y⟩ ⟨z⟩ ⟨w⟩
    | .yChart z w => .yChart ⟨z⟩ ⟨w⟩
    | .zChart w => .zChart ⟨w⟩
    | .wChart => .wChart
  left_inv P := by cases P <;> rfl
  right_inv P := by cases P <;> rfl

/-- The standard field equations on the semantic wrapper are exactly the
raw executable equations after forgetting the wrapper. -/
theorem isCanonicalNormalizedTwo_iff_table
    {R : Type*} [DecidableEq R] {O : BinaryRingOperations R}
    {tableInv : R → R} (h : IsBinaryFieldTable O tableInv)
    (P : NormalizedProjective4 (BinaryFieldModel R O tableInv)) :
    @IsCanonicalNormalizedTwo (BinaryFieldModel R O tableInv)
        (BinaryFieldModel.field O tableInv h) P ↔
      IsCanonicalNormalized25 O (normalizedRawEquiv P) := by
  let : Field (BinaryFieldModel R O tableInv) :=
    BinaryFieldModel.field O tableInv h
  change IsCanonicalNormalizedTwo P ↔
    IsCanonicalNormalized25 O (normalizedRawEquiv P)
  rw [IsCanonicalNormalizedTwo, fieldBinaryOperations_model_eq h]
  cases P with
  | xChart y z w =>
      simp [normalizedCoordinates25, fieldBinaryOperations_model_eq h,
        liftedOperations, IsCanonicalNormalized25,
        NormalizedProjective4.coordinates, canonicalQuadric25Binary,
        canonicalCubic25Binary, normalizedRawEquiv,
        BinaryFieldModel.eq_iff_raw_eq]
  | yChart z w =>
      simp [normalizedCoordinates25, fieldBinaryOperations_model_eq h,
        liftedOperations, IsCanonicalNormalized25,
        NormalizedProjective4.coordinates, canonicalQuadric25Binary,
        canonicalCubic25Binary, normalizedRawEquiv,
        BinaryFieldModel.eq_iff_raw_eq]
  | zChart w =>
      simp [normalizedCoordinates25, fieldBinaryOperations_model_eq h,
        liftedOperations, IsCanonicalNormalized25,
        NormalizedProjective4.coordinates, canonicalQuadric25Binary,
        canonicalCubic25Binary, normalizedRawEquiv,
        BinaryFieldModel.eq_iff_raw_eq]
  | wChart =>
      simp [normalizedCoordinates25, fieldBinaryOperations_model_eq h,
        liftedOperations, IsCanonicalNormalized25,
        NormalizedProjective4.coordinates, canonicalQuadric25Binary,
        canonicalCubic25Binary, normalizedRawEquiv,
        BinaryFieldModel.eq_iff_raw_eq]

/-- Executable normalized curve points are equivalent to standard semantic
curve points on the field wrapper.  This is an equation-preserving
equivalence, not a consequence of equal point counts. -/
noncomputable def canonicalPointEquivRaw
    {R : Type*} [Fintype R] [DecidableEq R]
    {O : BinaryRingOperations R} {tableInv : R → R}
    (h : IsBinaryFieldTable O tableInv) :
    {P : NormalizedProjective4 R // IsCanonicalNormalized25 O P} ≃
      {P : NormalizedProjective4 (BinaryFieldModel R O tableInv) //
        @IsCanonicalNormalizedTwo (BinaryFieldModel R O tableInv)
          (BinaryFieldModel.field O tableInv h) P} where
  toFun P := ⟨normalizedRawEquiv.symm P.1,
    (isCanonicalNormalizedTwo_iff_table h _).2 (by simpa using P.2)⟩
  invFun P := ⟨normalizedRawEquiv P.1,
    (isCanonicalNormalizedTwo_iff_table h P.1).1 P.2⟩
  left_inv P := by
    apply Subtype.ext
    exact normalizedRawEquiv.apply_symm_apply P.1
  right_inv P := by
    apply Subtype.ext
    exact normalizedRawEquiv.symm_apply_apply P.1

/-! ## Structural transfer of the executable point counts -/

/-- The four disjoint normalized-projective charts, with the canonical
equations retained on each chart.  This type mirrors the fibre decompositions
used by the existing `F8` and `F16` kernel certificates. -/
def CanonicalNormalizedPieces (R : Type*) [DecidableEq R]
    (O : BinaryRingOperations R) :=
  (Σ y : R, {zw : R × R //
      IsCanonicalNormalized25 O (.xChart y zw.1 zw.2)}) ⊕
    ({zw : R × R // IsCanonicalNormalized25 O (.yChart zw.1 zw.2)} ⊕
      ({w : R // IsCanonicalNormalized25 O (.zChart w)} ⊕
        {_u : Unit // IsCanonicalNormalized25 O
          (NormalizedProjective4.wChart : NormalizedProjective4 R)}))

/-- A canonical normalized point belongs to exactly one of the four chart
pieces.  The equivalence is purely structural and does not inspect the curve
equations or enumerate the coefficient field. -/
def canonicalNormalizedEquivPieces
    {R : Type*} [DecidableEq R] (O : BinaryRingOperations R) :
    {P : NormalizedProjective4 R // IsCanonicalNormalized25 O P} ≃
      CanonicalNormalizedPieces R O where
  toFun P := by
    rcases P with ⟨P, hP⟩
    cases P with
    | xChart y z w => exact Sum.inl ⟨y, ⟨(z, w), hP⟩⟩
    | yChart z w => exact Sum.inr (Sum.inl ⟨(z, w), hP⟩)
    | zChart w => exact Sum.inr (Sum.inr (Sum.inl ⟨w, hP⟩))
    | wChart => exact Sum.inr (Sum.inr (Sum.inr ⟨(), hP⟩))
  invFun S := by
    rcases S with X | YZW
    · rcases X with ⟨y, ⟨⟨z, w⟩, hP⟩⟩
      exact ⟨.xChart y z w, hP⟩
    · rcases YZW with Y | ZW
      · rcases Y with ⟨⟨z, w⟩, hP⟩
        exact ⟨.yChart z w, hP⟩
      · rcases ZW with Z | W
        · rcases Z with ⟨w, hP⟩
          exact ⟨.zChart w, hP⟩
        · rcases W with ⟨⟨⟩, hP⟩
          exact ⟨.wChart, hP⟩
  left_inv P := by
    rcases P with ⟨P, hP⟩
    cases P <;> rfl
  right_inv S := by
    rcases S with X | YZW
    · rcases X with ⟨y, ⟨⟨z, w⟩, hP⟩⟩
      rfl
    · rcases YZW with Y | ZW
      · rcases Y with ⟨⟨z, w⟩, hP⟩
        rfl
      · rcases ZW with Z | W
        · rcases Z with ⟨w, hP⟩
          rfl
        · rcases W with ⟨⟨⟩, hP⟩
          rfl

end MazurProof.RationalPointsN25QuotientBinaryFieldSemantics


