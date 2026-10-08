-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialAbelCodeQuotient_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13SpecialAbelCodeQuotient_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:35:37.873611+00:00
-- url     : https://prove2.me/theorems/ada062b9-a726-4015-86e7-8d3735315d52
-- title:
--   FLT.Assumptions.MazurProof.N13SpecialAbelCodeQuotient source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13SpecialAbelCodeQuotient

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13SpecialAbelCodeQuotient
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialAbelCode_p0

set_option autoImplicit false




/-!
# The explicit `ZMod 19` code of the special Abel quotient (plan Q8717, A03–A07)

`divisorCode` (A01/A02, `N13SpecialAbelCode`) separates the 21 effective degree-two divisors
exactly up to `AbelRel`: equal codes force equal divisors or two canonical divisors (A03/A04).
Hence it descends to an injective, and by counting bijective, map
`PicTwoSetModel → ZMod 19` (A05/A06), and every `r : ZMod 19` transports to a translation of
`PicTwoSetModel` (A07).  The separation fact is a finite check on
`Sym2 (BasePoint × K)`, done by `decide` after transport along `curvePointEquiv`.
-/

open scoped Sym2

open MazurProof.N13AbelFiberTwoModel
open MazurProof.N13SymmetricSquareTwo

namespace MazurProof.N13SpecialAbelCode

noncomputable section

/-- Point code read in the explicit `(base point, sheet)` coordinates. -/
def codeBP (p : BasePoint × K) : Code :=
  if p.2 = 0 then baseAmplitude p.1 else -(baseAmplitude p.1)

theorem pointCode_eq_codeBP (P : N13AbelFiberTwoModel.CurvePoint) :
    pointCode P = codeBP (curvePointEquiv P) := by
  rfl

/-- Divisor code read in the explicit coordinates. -/
def dcodeBP : Sym2 (BasePoint × K) → Code :=
  Sym2.lift ⟨fun p q => codeBP p + codeBP q, fun p q => by simp [add_comm]⟩

theorem divisorCode_eq_dcodeBP (D : EffectiveDivisorTwo) :
    divisorCode D = dcodeBP (D.map curvePointEquiv) := by
  induction D using Sym2.ind with
  | h P Q => rfl

/-- The canonical pencil in the explicit coordinates. -/
def CanonBP (S : Sym2 (BasePoint × K)) : Prop :=
  ∃ b : BasePoint, S = s((b, 0), (b, 1))

instance instDecidablePredSym2ProdBasePointKCanonBP : DecidablePred CanonBP := fun S => by
  unfold CanonBP; infer_instance

theorem map_curvePointEquiv_injective :
    Function.Injective (fun D : EffectiveDivisorTwo => D.map curvePointEquiv) :=
  Sym2.map.injective curvePointEquiv.injective

theorem map_canonicalDivisor (b : BasePoint) :
    (canonicalDivisor b).map curvePointEquiv = s((b, 0), (b, 1)) := by
  simp [canonicalDivisor]

theorem isCanonical_iff_canonBP (D : EffectiveDivisorTwo) :
    IsCanonical D ↔ CanonBP (D.map curvePointEquiv) := by
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b, map_canonicalDivisor b⟩
  · rintro ⟨b, hb⟩
    refine ⟨b, map_curvePointEquiv_injective ?_⟩
    simp only
    rw [map_canonicalDivisor, hb]

/-- The finite separation fact behind A04 (checked by `decide`). -/
theorem dcodeBP_separates :
    ∀ S T : Sym2 (BasePoint × K),
      dcodeBP S = dcodeBP T → S = T ∨ (CanonBP S ∧ CanonBP T) := by
  decide

/-- A04: the code is a complete invariant of `AbelRel`. -/
theorem divisorCode_eq_iff_abelRel (D E : EffectiveDivisorTwo) :
    divisorCode D = divisorCode E ↔ AbelRel D E := by
  constructor
  · intro h
    rw [divisorCode_eq_dcodeBP, divisorCode_eq_dcodeBP] at h
    rcases dcodeBP_separates _ _ h with h | ⟨hD, hE⟩
    · exact Or.inl (map_curvePointEquiv_injective h)
    · exact Or.inr ⟨(isCanonical_iff_canonBP D).2 hD, (isCanonical_iff_canonBP E).2 hE⟩
  · exact divisorCode_eq_of_abelRel

/-- A05: the code on the special Abel quotient. -/
def picCode : PicTwoSetModel → Code :=
  Quotient.lift divisorCode (fun _ _ h => divisorCode_eq_of_abelRel h)

@[simp] theorem picCode_abel (D : EffectiveDivisorTwo) :
    picCode (abel D) = divisorCode D :=
  rfl

theorem picCode_canonicalClass : picCode canonicalClass = 0 := by
  unfold canonicalClass
  exact divisorCode_canonicalDivisor _

/-- A06 (injectivity). -/
theorem picCode_injective : Function.Injective picCode := by
  intro x y
  induction x using Quotient.inductionOn
  induction y using Quotient.inductionOn
  intro h
  exact (abel_eq_iff _ _).2 ((divisorCode_eq_iff_abelRel _ _).1 h)

/-- A06: the code is a bijection onto `ZMod 19`. -/
theorem picCode_bijective : Function.Bijective picCode := by
  rw [Nat.bijective_iff_injective_and_card]
  exact ⟨picCode_injective, by rw [picTwoSetModel_card, Nat.card_zmod]⟩

/-- The special Abel quotient identified with `ZMod 19`. -/
def picEquiv : PicTwoSetModel ≃ Code :=
  Equiv.ofBijective picCode picCode_bijective

@[simp] theorem picEquiv_apply (c : PicTwoSetModel) : picEquiv c = picCode c :=
  rfl

/-- A07: translation by `r` on the coded special target. -/
def specialTranslateCode (r : Code) : PicTwoSetModel ≃ PicTwoSetModel :=
  (picEquiv.trans (Equiv.addRight r)).trans picEquiv.symm

@[simp] theorem picCode_specialTranslateCode (r : Code) (c : PicTwoSetModel) :
    picCode (specialTranslateCode r c) = picCode c + r := by
  change picEquiv (picEquiv.symm (picCode c + r)) = picCode c + r
  exact picEquiv.apply_symm_apply _

theorem specialTranslateCode_zero : specialTranslateCode 0 = Equiv.refl _ := by
  ext c
  apply picCode_injective
  simp

theorem specialTranslateCode_add (r s : Code) :
    specialTranslateCode (r + s) = (specialTranslateCode r).trans (specialTranslateCode s) := by
  ext c
  apply picCode_injective
  simp [add_assoc]

end

end MazurProof.N13SpecialAbelCode


