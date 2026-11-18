-- Prove2me | Definitions.Def_OAIQ368Chrom013
-- name    : OAIQ368Chrom013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:05:58.759102+00:00
-- url     : https://prove2.me/theorems/f71b7be9-c767-4204-861e-b54d873abb50
-- title:
--   Definitions bundle OAIQ368Chrom013 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 35 declarations of OpenAI's Lean: 28 definitions and 7 theorems. The definitions and types are `OAI.ElementaryPositivity.LaurentPositive.NatCoeff`, `OAI.ElementaryPositivity.LaurentPositive.Positive`, `OAI.ElementaryPositivity.LaurentPrecision.Agrees`, `OAI.ElementaryPositivity.LaurentPrecision.Converges`, `OAI.ElementaryPositivity.LaurentPrecision.LowerBound`, `OAI.ElementaryPositivity.LaurentPrecision.Series`, `OAI.ElementaryPositivity.QuantumTorus.InPrecisionClosure`, `OAI.ElementaryPositivity.QuantumTorus.IntegralPositive`, `OAI.ElementaryPositivity.QuantumTorus.PositiveIncomingPrescription`, `OAI.ElementaryPositivity.QuantumTorus.PrecisionTest`, `OAI.ElementaryPositivity.QuantumTorus.RootClosedThrough`, `OAI.ElementaryPositivity.QuantumTorus.SeriesConverges`, `OAI.ElementaryPositivity.QuantumTorus.ShiftGraded`, `OAI.ElementaryPositivity.QuantumTorus.TestAgreement`, `OAI.ElementaryPositivity.QuantumTorus.TorusConverges`, `OAI.ElementaryPositivity.QuantumTorus.TorusPositive`, `OAI.ElementaryPositivity.QuantumTorus.WallsPositiveThrough`, `OAI.ElementaryPositivity.QuantumTorus.chargeGrade`, `OAI.ElementaryPositivity.QuantumTorus.chargeGradeAddCommGroup`, `OAI.ElementaryPositivity.QuantumTorus.chargeGradeAddGroup`, `OAI.ElementaryPositivity.QuantumTorus.positiveRayWithZero`, `OAI.ElementaryPositivity.QuantumTorus.rootApprox`, `OAI.ElementaryPositivity.QuantumTorus.sectionIncoming`, `OAI.ElementaryPositivity.QuantumTorus.sectionValue`, `OAI.ElementaryPositivity.QuantumTorus.shiftRootGrade`, `OAI.ElementaryPositivity.QuantumTorus.shiftRootGradeAddCommGroup`, `OAI.ElementaryPositivity.QuantumTorus.shiftRootGradeAddGroup`, `OAI.ElementaryPositivity.QuantumTorus.sumSupport`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_GradedAlgebra_LaurentContinuity`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/GradedAlgebra/LaurentContinuity.lean), [`Chromatic_GradedAlgebra_SeriesApproximation`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/GradedAlgebra/SeriesApproximation.lean), [`Chromatic_GradedAlgebra_SplitContinuity`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/GradedAlgebra/SplitContinuity.lean), [`Chromatic_GradedAlgebra_TruncatedPrecisionClosure`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/GradedAlgebra/TruncatedPrecisionClosure.lean), [`Chromatic_QuantumTorus_TorusContinuity`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/QuantumTorus/TorusContinuity.lean), [`Chromatic_Walls_GlobalWallPositive`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/GlobalWallPositive.lean), [`Chromatic_Walls_IsotropicLiteralPositive`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/IsotropicLiteralPositive.lean), [`Chromatic_Walls_PlanarRefinement`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/PlanarRefinement.lean), [`Chromatic_Walls_RootProducts`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/RootProducts.lean), [`Chromatic_Walls_SectionIncoming`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/SectionIncoming.lean), [`Chromatic_Walls_TorusPositive`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/TorusPositive.lean), [`Chromatic_Walls_TranslatedCompletion`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/TranslatedCompletion.lean).
--
--   **Imports.** It imports the bundle `OAIQ368Chrom001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ368Chrom015` and `OAIQ368Chrom016`; the statements `OAI.ElementaryPositivity.QuantumTorus.literal_isotropic_adjoint`, `OAI.ElementaryPositivity.QuantumTorus.positive_sections`, `OAI.ElementaryPositivity.QuantumTorus.wall_joint_induction` and `OAI.ElementaryPositivity.RawShuffle.finiteInput_zero_rootClosure`; the proofs of `OAI.ElementaryPositivity.QuantumTorus.polynomialSectionIncoming_mutation`, `OAI.ElementaryPositivity.QuantumTorus.positive_sections`, `OAI.ElementaryPositivity.QuantumTorus.wall_joint_induction`, `OAI.ElementaryPositivity.RawShuffle.finiteInput_zero_rootClosure` and `OAI.ElementaryPositivity.TriangularDynamics.genuine_history_cut_deficit`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom001

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_LaurentContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LaurentPrecision
open Filter
open scoped LaurentSeries

abbrev Series := LaurentSeries ℚ

def LowerBound (b : ℤ) (f : Series) : Prop := ∀j<b,f.coeff j=0
def Agrees (b : ℤ) (f g : Series) : Prop := ∀j<b,f.coeff j=g.coeff j

variable {ι : Type*} (l : Filter ι)

def Converges (f : ι → Series) (F : Series) : Prop :=
  ∀N : ℤ,∀ᶠ i in l,Agrees N (f i) F

end ElementaryPositivity.LaurentPrecision

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_TorusContinuity
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries LaurentPrecision ElementaryPositivity.PowerSeriesSplit
noncomputable section
variable {M I ι : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ)
variable (C : (I → ℤ) →+ M) (l : Filter ι)
attribute [local instance] Classical.propDecidable

local instance instAddGroupTorusLaurentSeriesRat_rc1f27b_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instSubTorusLaurentSeriesRat_rc1f27b_1 : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
def TorusConverges (f : ι → Torus v Ω) (F : Torus v Ω) : Prop :=
  ∀m,Converges l (fun i=>f i m) (F m)

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_SplitContinuity
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries LaurentPrecision ElementaryPositivity.PowerSeriesSplit
noncomputable section
variable {M I ι : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ)
variable (C : (I → ℤ) →+ M) (l : Filter ι)
attribute [local instance] Classical.propDecidable

local instance instAddGroupTorusLaurentSeriesRat_1_rc1f27b_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instSubTorusLaurentSeriesRat_1_rc1f27b_1 : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
def SeriesConverges (f : ι → PowerSeries (Torus v Ω)) (F : PowerSeries (Torus v Ω)) : Prop :=
  ∀n,TorusConverges v Ω l (fun i=>coeff n (f i)) (coeff n F)

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_SeriesApproximation
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries LaurentPrecision Filter
noncomputable section
variable {M ι : Type*} [AddCommGroup M]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M→+M→+ℤ)

abbrev PrecisionTest := ℕ×M×ℤ

def TestAgreement (T : Finset (PrecisionTest (M:=M)))
    (F G : PowerSeries (Torus v Ω)) : Prop :=
  ∀t∈T,Agrees t.2.2 ((coeff t.1 F) t.2.1) ((coeff t.1 G) t.2.1)

def InPrecisionClosure (A : Set (PowerSeries (Torus v Ω)))
    (F : PowerSeries (Torus v Ω)) : Prop :=
  ∀T : Finset (PrecisionTest (M:=M)),∃G∈A,TestAgreement v Ω T G F

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RootProducts
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LaurentPositive
open LaurentPrecision
noncomputable section

def NatCoeff (r : ℚ) : Prop := ∃n : ℕ,r=n

def Positive (f : LaurentSeries ℚ) : Prop := ∀j,NatCoeff (f.coeff j)

lemma natCoeff_zero : NatCoeff 0 := ⟨0,rfl⟩
lemma NatCoeff.add {r s : ℚ} (hr : NatCoeff r) (hs : NatCoeff s) : NatCoeff (r+s) := by
  obtain ⟨n,rfl⟩:=hr
  obtain ⟨m,rfl⟩:=hs
  exact ⟨n+m,(Nat.cast_add n m).symm⟩
lemma NatCoeff.mul {r s : ℚ} (hr : NatCoeff r) (hs : NatCoeff s) : NatCoeff (r*s) := by
  obtain ⟨n,rfl⟩:=hr
  obtain ⟨m,rfl⟩:=hs
  exact ⟨n*m,(Nat.cast_mul n m).symm⟩
lemma NatCoeff.sum {A : Type*} (s : Finset A) (f : A → ℚ)
    (h : ∀a∈s,NatCoeff (f a)) : NatCoeff (∑a∈s,f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact natCoeff_zero
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih (fun b hb=>h b (Finset.mem_insert_of_mem hb)))

lemma Positive.mul {f g : LaurentSeries ℚ} (hf : Positive f) (hg : Positive g) : Positive (f*g) := by
  intro j
  rw [HahnSeries.coeff_mul]
  apply NatCoeff.sum
  intro p hp
  exact (hf p.1).mul (hg p.2)

end
end ElementaryPositivity.LaurentPositive

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_TruncatedPrecisionClosure
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries RootTruncation LaurentPrecision Filter WallUnits
noncomputable section
variable {M I J : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M→+M→+ℤ)
abbrev RootClosedThrough (N : ℕ) (A : Set (PowerSeries (Torus v Ω)))
    (F : PowerSeries (Torus v Ω)) : Prop :=
  InPrecisionClosure v Ω (RootTruncation.cut N '' A) (RootTruncation.cut N F)
variable {N : ℕ} {A : Set (PowerSeries (Torus v Ω))} {F : PowerSeries (Torus v Ω)}
lemma rootClosedThrough_approx_exists (hF : RootClosedThrough v Ω N A F)
    (T : Finset (PrecisionTest (M:=M))) :
    ∃G∈A,TestAgreement v Ω T (RootTruncation.cut N G) (RootTruncation.cut N F) := by
  obtain ⟨G,⟨G',hG,rfl⟩,H⟩:=hF T
  exact ⟨G',hG,H⟩
def rootApprox (hF : RootClosedThrough v Ω N A F)
    (T : Finset (PrecisionTest (M:=M))) : PowerSeries (Torus v Ω) :=
  Classical.choose (rootClosedThrough_approx_exists v Ω hF T)
end

end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TorusPositive
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open LaurentPositive WallUnits PowerSeries
noncomputable section
variable {M : Type*} [AddCommGroup M]
variable (Ω : M →+ M →+ ℤ)

local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_rc1f27b_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_rc1f27b_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
def TorusPositive (f : Torus LaurentRay.vUnit Ω) : Prop := ∀m,Positive (f m)
def IntegralPositive (F : PowerSeries (Torus LaurentRay.vUnit Ω)) : Prop := ∀n,TorusPositive Ω (coeff n F)

end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries LaurentPrecision
noncomputable section
variable {M I ι : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ)
variable (C : (I→ℤ) →+ M) (l : Filter ι)
attribute [local instance] Classical.propDecidable

def sumSupport (S T : Finset M) : Finset M := (S×ˢT).image (fun p=>p.1+p.2)

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_PlanarRefinement
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry RootTruncation WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M) (e : M →+ E)
def WallsPositiveThrough (N : ℕ) (F : CompletedPositive LaurentRay.vUnit Ω C) : Prop :=
  ∀r d,0 < d → HasRootDegree C d r → ∀h : Module.Dual ℝ E,
    RayGeneric C N r (h.toAddMonoidHom.comp e) →
      RootClosedThrough LaurentRay.vUnit Ω N (literalRootProducts Ω C (OnPositiveRay r))
        (chartZero LaurentRay.vUnit Ω C (h.toAddMonoidHom.comp e) F).val
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_GlobalWallPositive
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry FiniteEventTraversal WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)

def PositiveIncomingPrescription (F : CompletedPositive LaurentRay.vUnit Ω C) : Prop :=
  ∀r d,0 < d → HasRootDegree C d r → ∃D : CompletedPositive LaurentRay.vUnit Ω C,
    (∀n m,coeff (n+1) D.val m≠0 → OnPositiveRay r m) ∧
    InPrecisionClosure LaurentRay.vUnit Ω (literalRootProducts Ω C (OnPositiveRay r)) D.val ∧
    ∀n m,OnPositiveRay r m →
      coeff n (FormalLog.log (chartZero LaurentRay.vUnit Ω C (incomingCovector Ω m) F).val) m=
        coeff n (FormalLog.log D.val) m
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_IsotropicLiteralPositive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits LaurentPrecision
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]

def positiveRayWithZero (r : M) : AddSubmonoid M where
  carrier:={m | m=0 ∨ OnPositiveRay r m}
  zero_mem':=Or.inl rfl
  add_mem':=by
    intro a b ha hb
    rcases ha with rfl|ha
    · simpa using hb
    rcases hb with rfl|hb
    · simpa using Or.inr ha
    · exact Or.inr (ha.add hb)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TranslatedCompletion
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
local instance shiftRootGradeAddCommGroup : AddCommGroup (Torus v Ω) := (Torus.instRing v Ω).toAddCommGroup
local instance shiftRootGradeSub_rc1f27b_1 : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
local instance shiftRootGradeAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup

def shiftRootGrade (b : M) (n : ℕ) : AddSubgroup (Torus v Ω) where
  carrier:={f | ∀m,¬HasRootDegree C n (m-b) → f m=0}
  zero_mem':=by intro m hm; rfl
  add_mem':=by intro f g hf hg m hm; change f m+g m=0; rw [hf m hm,hg m hm,add_zero]
  neg_mem':=by intro f hf m hm; change -f m=0; rw [hf m hm,neg_zero]
def ShiftGraded (b : M) (X : PowerSeries (Torus v Ω)) : Prop :=
  ∀n,coeff n X∈shiftRootGrade v Ω C b n
lemma shiftRootGrade_finite (b : M) (n : ℕ) : {m | HasRootDegree C n (m-b)}.Finite := by
  apply ((rootDegree_finite C n).image (fun r=>r+b)).subset
  intro m hm
  exact ⟨m-b,hm,sub_add_cancel m b⟩

def sectionValue (F : CompletedPositive v Ω C) (h : M →+ ℝ)
    (X : PowerSeries (Torus v Ω)) : PowerSeries (Torus v Ω) :=
  adjoint (chartNegative v Ω C h F).val X
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint
noncomputable section
variable {M : Type*} [AddCommGroup M]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ) (q : M →+ ℤ)
local instance chargeGradeAddCommGroup : AddCommGroup (Torus v Ω) := (Torus.instRing v Ω).toAddCommGroup
local instance chargeGradeAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup

local instance chargeGradeSub_rc1f27b_1 : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
def chargeGrade (z : ℤ) : AddSubgroup (Torus v Ω) where
  carrier:={f | ∀m,q m≠z → f m=0}
  zero_mem':=by intro m hm; rfl
  add_mem':=by intro f g hf hg m hm; change f m+g m=0; rw [hf m hm,hg m hm,add_zero]
  neg_mem':=by intro f hf m hm; change -f m=0; rw [hf m hm,neg_zero]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_SectionIncoming
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
attribute [local instance] Classical.propDecidable
variable (F : CompletedPositive v Ω C) (b : M)

local instance sectionIncomingAddCommGroup_rc1f27b_1 : AddCommGroup (Torus v Ω) := (Torus.instRing v Ω).toAddCommGroup
local instance sectionIncomingAddGroup_rc1f27b_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance sectionIncomingSub_rc1f27b_1 : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
def sectionIncoming (n : ℕ) (X : PowerSeries (Torus v Ω)) : Torus v Ω :=
  Finsupp.onFinset (shiftRootGrade_finite C b n).toFinset
    (fun m => if HasRootDegree C n (m-b) then
      (coeff n (sectionValue v Ω C F (incomingCovector Ω m) X)) m else 0)
    (by intro m hm; rw [Set.Finite.mem_toFinset]; by_contra hn; exact hm (ite_eq_right hn))
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end


