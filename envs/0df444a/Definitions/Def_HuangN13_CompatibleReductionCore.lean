-- Prove2me | Definitions.Def_HuangN13_CompatibleReductionCore
-- name    : HuangN13_CompatibleReductionCore
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-30T16:25:30.795735+00:00
-- url     : https://prove2.me/theorems/39eb9277-b900-4f40-8710-2bfc48c89920
-- title:
--   Exact original statement data for quotient_kernel_separated, actual_kernel_separated
-- statement:
--   Exactly the original definitions (and the lemmas their bodies need) that the statements of the listed N13 nodes refer to; no new mathematics.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_SeparationDataCore
import Theorems.Thm_HuangN13_N13ConstructedSpecialization_chosen_point_specialClass
import Theorems.Thm_HuangN13_N13ConstructedSpecialization_specialCode_add
import Theorems.Thm_MazurProof_N13GoodModelTwo_affineEquation_iff_fixed
import Theorems.Thm_MazurProof_N13ProperCurveReduction_reduceCurve_cusp

set_option autoImplicit false

namespace MazurProof.N13SpecialDegreeFourCode
end MazurProof.N13SpecialDegreeFourCode
section
section
set_option autoImplicit false
open scoped Sym2
open MazurProof.N13AbelFiberTwoModel
open MazurProof.N13SymmetricSquareTwo
namespace MazurProof.N13SpecialAbelCode
noncomputable section
/-- First lemma: every member of the canonical hyperelliptic pencil has
code zero. The two sheets have opposite point codes. -/
@[simp] theorem divisorCode_canonicalDivisor
    (B : BasePoint) :
    divisorCode (canonicalDivisor B) = 0 := by
  simp [divisorCode, pointCode, N13AbelFiberTwoModel.curvePointEquiv, canonicalDivisor]
  cases B <;> simp [baseAmplitude]
end
end MazurProof.N13SpecialAbelCode
end
end

section
section
set_option autoImplicit false
open scoped Sym2
open MazurProof.N13AbelFiberTwoModel
open MazurProof.N13SymmetricSquareTwo
namespace MazurProof.N13SpecialAbelCode
noncomputable section
/-- Second lemma: the explicit code is constant on every AbelRel class. -/
theorem divisorCode_eq_of_abelRel
    {D E : EffectiveDivisorTwo}
    (h : AbelRel D E) :
    divisorCode D = divisorCode E := by
  -- The AbelRel is D = E or both are canonical
  rcases h with rfl | ⟨hD, hE⟩
  · rfl
  · -- Both D and E are canonical divisors, so both have code 0
    have hD0 : divisorCode D = 0 := by
      obtain ⟨bD, rfl⟩ := hD
      exact divisorCode_canonicalDivisor bD
    have hE0 : divisorCode E = 0 := by
      obtain ⟨bE, rfl⟩ := hE
      exact divisorCode_canonicalDivisor bE
    rw [hD0, hE0]
end
end MazurProof.N13SpecialAbelCode
end
end

section
section
set_option autoImplicit false
open scoped Sym2
open MazurProof.N13AbelFiberTwoModel
open MazurProof.N13SymmetricSquareTwo
namespace MazurProof.N13SpecialAbelCode
noncomputable section
/-- Point code read in the explicit `(base point, sheet)` coordinates. -/
def codeBP (p : BasePoint × K) : Code :=
  if p.2 = 0 then baseAmplitude p.1 else -(baseAmplitude p.1)
end
end MazurProof.N13SpecialAbelCode
end
end

section
section
set_option autoImplicit false
open scoped Sym2
open MazurProof.N13AbelFiberTwoModel
open MazurProof.N13SymmetricSquareTwo
namespace MazurProof.N13SpecialAbelCode
noncomputable section
/-- Divisor code read in the explicit coordinates. -/
def dcodeBP : Sym2 (BasePoint × K) → Code :=
  Sym2.lift ⟨fun p q => codeBP p + codeBP q, fun p q => by simp [add_comm]⟩
end
end MazurProof.N13SpecialAbelCode
end
end

section
section
set_option autoImplicit false
open scoped Sym2
open MazurProof.N13AbelFiberTwoModel
open MazurProof.N13SymmetricSquareTwo
namespace MazurProof.N13SpecialAbelCode
noncomputable section
theorem divisorCode_eq_dcodeBP (D : EffectiveDivisorTwo) :
    divisorCode D = dcodeBP (D.map curvePointEquiv) := by
  induction D using Sym2.ind with
  | h P Q => rfl
end
end MazurProof.N13SpecialAbelCode
end
end

section
section
set_option autoImplicit false
open scoped Sym2
open MazurProof.N13AbelFiberTwoModel
open MazurProof.N13SymmetricSquareTwo
namespace MazurProof.N13SpecialAbelCode
noncomputable section
theorem map_curvePointEquiv_injective :
    Function.Injective (fun D : EffectiveDivisorTwo => D.map curvePointEquiv) :=
  Sym2.map.injective curvePointEquiv.injective
end
end MazurProof.N13SpecialAbelCode
end
end

section
section
set_option autoImplicit false
open scoped Sym2
open MazurProof.N13AbelFiberTwoModel
open MazurProof.N13SymmetricSquareTwo
namespace MazurProof.N13SpecialAbelCode
noncomputable section
theorem isCanonical_iff_canonBP (D : EffectiveDivisorTwo) :
    IsCanonical D ↔ CanonBP (D.map curvePointEquiv) := by
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b, map_canonicalDivisor b⟩
  · rintro ⟨b, hb⟩
    refine ⟨b, map_curvePointEquiv_injective ?_⟩
    simp only
    rw [map_canonicalDivisor, hb]
end
end MazurProof.N13SpecialAbelCode
end
end

section
section
set_option autoImplicit false
open scoped Sym2
open MazurProof.N13AbelFiberTwoModel
open MazurProof.N13SymmetricSquareTwo
namespace MazurProof.N13SpecialAbelCode
noncomputable section
/-- The finite separation fact behind A04 (checked by `decide`). -/
theorem dcodeBP_separates :
    ∀ S T : Sym2 (BasePoint × K),
      dcodeBP S = dcodeBP T → S = T ∨ (CanonBP S ∧ CanonBP T) := by
  decide
end
end MazurProof.N13SpecialAbelCode
end
end

section
section
set_option autoImplicit false
open scoped Sym2
open MazurProof.N13AbelFiberTwoModel
open MazurProof.N13SymmetricSquareTwo
namespace MazurProof.N13SpecialAbelCode
noncomputable section
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
end
end MazurProof.N13SpecialAbelCode
end
end

section
section
set_option autoImplicit false
open scoped Sym2
open MazurProof.N13AbelFiberTwoModel
open MazurProof.N13SymmetricSquareTwo
namespace MazurProof.N13SpecialAbelCode
noncomputable section
/-- A05: the code on the special Abel quotient. -/
def picCode : PicTwoSetModel → Code :=
  Quotient.lift divisorCode (fun _ _ h => divisorCode_eq_of_abelRel h)
end
end MazurProof.N13SpecialAbelCode
end
end

section
section
set_option autoImplicit false
open scoped Sym2
open MazurProof.N13AbelFiberTwoModel
open MazurProof.N13SymmetricSquareTwo
namespace MazurProof.N13SpecialAbelCode
noncomputable section
/-- A06 (injectivity). -/
theorem picCode_injective : Function.Injective picCode := by
  intro x y
  induction x using Quotient.inductionOn
  induction y using Quotient.inductionOn
  intro h
  exact (abel_eq_iff _ _).2 ((divisorCode_eq_iff_abelRel _ _).1 h)
end
end MazurProof.N13SpecialAbelCode
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13ConstructedSpecialization
noncomputable section
open N13SpecialDivisorCharts N13CoherentChartComparison
open N13SpecialAbelCode hiding EffectiveDivisorTwo
open N13SpecialDegreeFourCode
@[simp] theorem specialCode_zero : specialCode 0 = 0 := by simp [specialCode]
end
end MazurProof.N13ConstructedSpecialization
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13ConstructedSpecialization
noncomputable section
open N13SpecialDivisorCharts N13CoherentChartComparison
open N13SpecialAbelCode hiding EffectiveDivisorTwo
open N13SpecialDegreeFourCode
/-- The additive specialization code, built without an additivity input. -/
def specialization : G →+ ZMod 19 where
  toFun := specialCode
  map_zero' := specialCode_zero
  map_add' := HuangN13.N13ConstructedSpecialization.specialCode_add
end
end MazurProof.N13ConstructedSpecialization
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13ConstructedReductionClassifier
noncomputable section
open N13ConstructedSpecialization N13SpecialAbelCode
def classifier : N13ReductionClassifier.Data G N13RationalPointEndgame.SpecialSet where
  kernel := specialization.ker
  classify P := (N13CalibratedChooser.choose P).toSpecialPic
  exact P Q := by
    constructor
    · intro h
      change specialization (P - Q) = 0
      rw [map_sub]
      apply sub_eq_zero.mpr
      have hc := congrArg picCode h
      change divisorCode (chosenDivisor P) = divisorCode (chosenDivisor Q) at hc
      change divisorCode (chosenDivisor P) - divisorCode (chosenDivisor 0) =
        divisorCode (chosenDivisor Q) - divisorCode (chosenDivisor 0)
      rw [hc]
    · intro h
      change specialization (P - Q) = 0 at h
      rw [map_sub] at h
      have he := sub_eq_zero.mp h
      apply picCode_injective
      change divisorCode (chosenDivisor P) = divisorCode (chosenDivisor Q)
      change divisorCode (chosenDivisor P) - divisorCode (chosenDivisor 0) =
        divisorCode (chosenDivisor Q) - divisorCode (chosenDivisor 0) at he
      linear_combination he
end
end MazurProof.N13ConstructedReductionClassifier
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13ConstructedReductionClassifier
noncomputable section
open N13ConstructedSpecialization N13SpecialAbelCode
/-- The actual existing rational-point endpoint structure is constructed,
with no classifier exactness or point-compatibility input. -/
def compatibleReduction : N13RationalPointEndgame.CompatibleReduction where
  classifier := classifier
  reduceCurve := N13ProperCurveReduction.reduceCurve
  classify_abel := HuangN13.N13ConstructedSpecialization.chosen_point_specialClass
  reduce_cusp := N13ProperCurveReduction.reduceCurve_cusp
end
end MazurProof.N13ConstructedReductionClassifier
end
end


