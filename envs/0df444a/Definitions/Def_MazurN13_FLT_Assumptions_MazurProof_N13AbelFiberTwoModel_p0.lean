-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13AbelFiberTwoModel_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13AbelFiberTwoModel_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T21:55:14.997903+00:00
-- url     : https://prove2.me/theorems/2714aab4-754a-4231-bf49-ec8cc0197c3f
-- title:
--   FLT.Assumptions.MazurProof.N13AbelFiberTwoModel source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13AbelFiberTwoModel

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13AbelFiberTwoModel
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SymmetricSquareTwo_p0

set_option autoImplicit false




/-!
# A finite set model for the N13 Abel fibres at two

The six points of the good characteristic-two model form three
hyperelliptic pairs.  On `Sym²(C)(F₂)`, collapse the three corresponding
canonical divisors to one class and leave every other divisor unchanged.
The resulting quotient has nineteen elements.

This quotient is only a set-level model of the expected Abel fibres.  It is
not asserted to be the geometric Picard group.  The structure
`GeometricAbelCriterion` records exactly the geometric statements required
to transfer the same fibre calculation to a genuine Picard target.
-/

namespace MazurProof.N13AbelFiberTwoModel

noncomputable section

open N13GoodModelTwo
open N13SymmetricSquareTwo

abbrev K := F2
abbrev CurvePoint := CompletedPoint K

/-- The three rational points of the hyperelliptic base. -/
abbrev BasePoint := K ⊕ Unit

/-- The six curve points are the three base points times two sheets. -/
def curvePointEquiv : CurvePoint ≃ BasePoint × K where
  toFun
    | Sum.inl P => (Sum.inl P.1.1, P.1.2)
    | Sum.inr P => (Sum.inr (), P.1)
  invFun
    | (Sum.inl x, y) =>
        Sum.inl ⟨(x, y), (affineEquation_iff_fixed f2_fourth_eq x y).2
          ⟨ZMod.pow_card x, ZMod.pow_card y⟩⟩
    | (Sum.inr _, v) =>
        Sum.inr ⟨v, (infinityChartEquation_zero_iff_fixed v).2
          (ZMod.pow_card v)⟩
  left_inv P := by
    rcases P with P | P
    · rfl
    · rfl
  right_inv P := by
    rcases P with ⟨b, z⟩
    rcases b with x | u
    · rfl
    · cases u
      rfl

theorem basePoint_card : Nat.card BasePoint = 3 := by
  rw [Nat.card_sum]
  norm_num [BasePoint, K, F2]

/-- The hyperelliptic fibre over `b`, as an effective divisor of degree two. -/
def canonicalDivisor (b : BasePoint) : EffectiveDivisorTwo :=
  s(curvePointEquiv.symm (b, 0), curvePointEquiv.symm (b, 1))

theorem canonicalDivisor_injective :
    Function.Injective canonicalDivisor := by
  intro b c h
  change
    s(curvePointEquiv.symm (b, 0), curvePointEquiv.symm (b, 1)) =
      s(curvePointEquiv.symm (c, 0), curvePointEquiv.symm (c, 1)) at h
  rw [Sym2.eq_iff] at h
  rcases h with h | h
  · exact congrArg Prod.fst (curvePointEquiv.symm.injective h.1)
  · have hz : (0 : K) = 1 :=
      congrArg Prod.snd (curvePointEquiv.symm.injective h.1)
    exact (zero_ne_one hz).elim

/-- The three divisors in the canonical pencil over `F₂`. -/
def IsCanonical (D : EffectiveDivisorTwo) : Prop :=
  D ∈ Set.range canonicalDivisor

theorem canonicalDivisor_isCanonical (b : BasePoint) :
    IsCanonical (canonicalDivisor b) :=
  Set.mem_range_self b

/-- Equality except that all three canonical divisors are identified. -/
def AbelRel (D E : EffectiveDivisorTwo) : Prop :=
  D = E ∨ IsCanonical D ∧ IsCanonical E

theorem abelRel_equivalence : Equivalence AbelRel where
  refl D := Or.inl rfl
  symm := by
    intro D E h
    rcases h with rfl | ⟨hD, hE⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨hE, hD⟩
  trans := by
    intro D E F hDE hEF
    rcases hDE with rfl | ⟨hD, hE⟩
    · exact hEF
    rcases hEF with rfl | ⟨_, hF⟩
    · exact Or.inr ⟨hD, hE⟩
    · exact Or.inr ⟨hD, hF⟩

def abelSetoid : Setoid EffectiveDivisorTwo :=
  ⟨AbelRel, abelRel_equivalence⟩

/-- Set-level quotient obtained by collapsing the canonical pencil. -/
abbrev PicTwoSetModel := Quotient abelSetoid

def abel : EffectiveDivisorTwo → PicTwoSetModel :=
  Quotient.mk''

theorem abel_eq_iff (D E : EffectiveDivisorTwo) :
    abel D = abel E ↔ AbelRel D E :=
  Quotient.eq''

def baseAtInfinity : BasePoint := Sum.inr ()

def canonicalClass : PicTwoSetModel :=
  abel (canonicalDivisor baseAtInfinity)

theorem abel_eq_canonicalClass_iff (D : EffectiveDivisorTwo) :
    abel D = canonicalClass ↔ IsCanonical D := by
  change abel D = abel (canonicalDivisor baseAtInfinity) ↔ IsCanonical D
  rw [abel_eq_iff]
  constructor
  · rintro (rfl | ⟨hD, _⟩)
    · exact canonicalDivisor_isCanonical baseAtInfinity
    · exact hD
  · intro hD
    exact Or.inr ⟨hD, canonicalDivisor_isCanonical baseAtInfinity⟩

def exceptionalFiberEquivCanonical :
    {D : EffectiveDivisorTwo // abel D = canonicalClass} ≃
      {D : EffectiveDivisorTwo // IsCanonical D} :=
  Equiv.subtypeEquivRight (fun D => abel_eq_canonicalClass_iff D)

theorem canonical_fiber_card :
    Nat.card {D : EffectiveDivisorTwo // abel D = canonicalClass} = 3 := by
  calc
    Nat.card {D : EffectiveDivisorTwo // abel D = canonicalClass} =
        Nat.card {D : EffectiveDivisorTwo // IsCanonical D} :=
      Nat.card_congr exceptionalFiberEquivCanonical
    _ = Nat.card BasePoint :=
      (Nat.card_congr
        (Equiv.ofInjective canonicalDivisor canonicalDivisor_injective)).symm
    _ = 3 := basePoint_card

theorem regular_fiber_subsingleton
    (c : PicTwoSetModel) (hc : c ≠ canonicalClass) :
    Subsingleton {D : EffectiveDivisorTwo // abel D = c} := by
  constructor
  intro D E
  apply Subtype.ext
  have hDE : abel D.1 = abel E.1 := D.2.trans E.2.symm
  rw [abel_eq_iff] at hDE
  rcases hDE with h | ⟨hD, hE⟩
  · exact h
  · have hregularD : ¬IsCanonical D.1 := by
      intro hcanonical
      apply hc
      calc
        c = abel D.1 := D.2.symm
        _ = canonicalClass :=
          (abel_eq_canonicalClass_iff D.1).2 hcanonical
    exact (hregularD hD).elim

theorem regular_fiber_nonempty (c : PicTwoSetModel) :
    Nonempty {D : EffectiveDivisorTwo // abel D = c} :=
  ⟨Quotient.out c, Quotient.out_eq c⟩

theorem regular_fiber_card
    (c : PicTwoSetModel) (hc : c ≠ canonicalClass) :
    Nat.card {D : EffectiveDivisorTwo // abel D = c} = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨regular_fiber_subsingleton c hc, regular_fiber_nonempty c⟩

/-- The set quotient has the expected Abel fibre sizes. -/
def abelFiberData : AbelFiberData PicTwoSetModel where
  abel := abel
  canonicalClass := canonicalClass
  canonical_fiber := canonical_fiber_card
  regular_fiber := regular_fiber_card

theorem picTwoSetModel_card : Nat.card PicTwoSetModel = 19 :=
  jacobian_card_eq_nineteen abelFiberData

/-! ## Interface to a genuine geometric Picard target -/

/-- The geometric facts needed to transfer the set-level fibre calculation.
Surjectivity is the genus-two Riemann--Roch input; `eq_iff` is the
degree-two linear-equivalence theorem. -/
structure GeometricAbelCriterion (J : Type*) where
  abel : EffectiveDivisorTwo → J
  canonicalClass : J
  canonical_eq :
    ∀ b : BasePoint, abel (canonicalDivisor b) = canonicalClass
  surjective : Function.Surjective abel
  eq_iff :
    ∀ D E : EffectiveDivisorTwo,
      abel D = abel E ↔ AbelRel D E

/-- The intrinsic nineteen-element quotient itself satisfies the geometric
Abel-fibre interface.  This lets later arguments use Abel rigidity without
postulating a separate special Picard-group implementation. -/
def picTwoSetModelCriterion :
    GeometricAbelCriterion PicTwoSetModel where
  abel := abel
  canonicalClass := canonicalClass
  canonical_eq := by
    intro b
    change
      abel (canonicalDivisor b) =
        abel (canonicalDivisor baseAtInfinity)
    rw [abel_eq_iff]
    exact Or.inr
      ⟨canonicalDivisor_isCanonical b,
        canonicalDivisor_isCanonical baseAtInfinity⟩
  surjective := Quotient.mk_surjective
  eq_iff := abel_eq_iff

namespace GeometricAbelCriterion

variable {J : Type*} (G : GeometricAbelCriterion J)

theorem abel_eq_canonical_iff (D : EffectiveDivisorTwo) :
    G.abel D = G.canonicalClass ↔ IsCanonical D := by
  constructor
  · intro hD
    have hpair :
        G.abel D = G.abel (canonicalDivisor baseAtInfinity) := by
      rw [G.canonical_eq]
      exact hD
    rcases (G.eq_iff D (canonicalDivisor baseAtInfinity)).1 hpair with
      hEq | ⟨hcanonical, _⟩
    · exact hEq ▸ canonicalDivisor_isCanonical baseAtInfinity
    · exact hcanonical
  · rintro ⟨b, rfl⟩
    exact G.canonical_eq b

theorem canonical_fiber_card :
    Nat.card {D : EffectiveDivisorTwo //
      G.abel D = G.canonicalClass} = 3 := by
  calc
    Nat.card {D : EffectiveDivisorTwo //
        G.abel D = G.canonicalClass} =
        Nat.card {D : EffectiveDivisorTwo // IsCanonical D} :=
      Nat.card_congr
        (Equiv.subtypeEquivRight (fun D => G.abel_eq_canonical_iff D))
    _ = Nat.card BasePoint :=
      (Nat.card_congr
        (Equiv.ofInjective canonicalDivisor canonicalDivisor_injective)).symm
    _ = 3 := basePoint_card

theorem regular_fiber_card
    (c : J) (hc : c ≠ G.canonicalClass) :
    Nat.card {D : EffectiveDivisorTwo // G.abel D = c} = 1 := by
  obtain ⟨E, hE⟩ := G.surjective c
  rw [Nat.card_eq_one_iff_unique]
  constructor
  · constructor
    intro D D'
    apply Subtype.ext
    have hDD' : G.abel D.1 = G.abel D'.1 := D.2.trans D'.2.symm
    rcases (G.eq_iff D.1 D'.1).1 hDD' with h | ⟨hcanonical, _⟩
    · exact h
    · have : G.abel D.1 = G.canonicalClass :=
        (G.abel_eq_canonical_iff D.1).2 hcanonical
      exact (hc (D.2 ▸ this)).elim
  · exact ⟨⟨E, hE⟩⟩

def toAbelFiberData [Finite J] : AbelFiberData J where
  abel := G.abel
  canonicalClass := G.canonicalClass
  canonical_fiber := G.canonical_fiber_card
  regular_fiber := G.regular_fiber_card

end GeometricAbelCriterion

end

end MazurProof.N13AbelFiberTwoModel


