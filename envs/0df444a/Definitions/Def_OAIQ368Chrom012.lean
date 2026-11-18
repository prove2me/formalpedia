-- Prove2me | Definitions.Def_OAIQ368Chrom012
-- name    : OAIQ368Chrom012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:19:34.541297+00:00
-- url     : https://prove2.me/theorems/fd9c36ff-58ee-4c12-a4a7-679bc18e8282
-- title:
--   Definitions bundle OAIQ368Chrom012 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 24 declarations of OpenAI's Lean: 21 definitions and 3 theorems. The definitions and types are `OAI.ElementaryPositivity.AffineCut.oldFactor`, `OAI.ElementaryPositivity.AffineCut.oldGauge`, `OAI.ElementaryPositivity.PowerSeriesAdjoint.hahnAction`, `OAI.ElementaryPositivity.QuantumTorus.NearCut`, `OAI.ElementaryPositivity.QuantumTorus.PureInitialRelation`, `OAI.ElementaryPositivity.QuantumTorus.halfspacePolynomialCoefficientsCoeffRing`, `OAI.ElementaryPositivity.QuantumTorus.latticeHahn`, `OAI.ElementaryPositivity.QuantumTorus.latticeHahnNonUnitalNonAssocSemiring`, `OAI.ElementaryPositivity.QuantumTorus.latticeHahnNonUnitalSemiring`, `OAI.ElementaryPositivity.QuantumTorus.latticeHahnRing`, `OAI.ElementaryPositivity.QuantumTorus.laurentHomogenizeNonUnitalNonAssocSemiring`, `OAI.ElementaryPositivity.QuantumTorus.nearCutProbes`, `OAI.ElementaryPositivity.QuantumTorus.nearCutSectionChartsRing`, `OAI.ElementaryPositivity.QuantumTorus.polynomialSectionCoefficient`, `OAI.ElementaryPositivity.QuantumTorus.pureActualCoefficientsRing`, `OAI.ElementaryPositivity.QuantumTorus.pureActualScalarCoefficientsNonUnitalNonAssocSemiring`, `OAI.ElementaryPositivity.QuantumTorus.pureActualScalarCoefficientsRing`, `OAI.ElementaryPositivity.QuantumTorus.purePolynomialCoefficientsRing`, `OAI.ElementaryPositivity.QuantumTorus.rootSectionChart`, `OAI.ElementaryPositivity.RationalFiber.centeredRatio`, `OAI.ElementaryPositivity.RationalFiber.readFiber`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_GradedAlgebra_HalfspacePolynomialCoefficients`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/GradedAlgebra/HalfspacePolynomialCoefficients.lean), [`Chromatic_GradedAlgebra_HomogeneousElementaryExpressions`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/GradedAlgebra/HomogeneousElementaryExpressions.lean), [`Chromatic_GradedAlgebra_LaurentHomogenize`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/GradedAlgebra/LaurentHomogenize.lean), [`Chromatic_GradedAlgebra_PurePolynomialCoefficients`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/GradedAlgebra/PurePolynomialCoefficients.lean), [`Chromatic_GradedAlgebra_RationalPureCoefficients`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/GradedAlgebra/RationalPureCoefficients.lean), [`Chromatic_QuantumTorus_LatticeHahn`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/QuantumTorus/LatticeHahn.lean), [`Chromatic_QuantumTorus_NearCutGeometry`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/QuantumTorus/NearCutGeometry.lean), [`Chromatic_QuantumTorus_NearCutPolynomialSeeds`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/QuantumTorus/NearCutPolynomialSeeds.lean), [`Chromatic_QuantumTorus_NearCutSectionCharts`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/QuantumTorus/NearCutSectionCharts.lean), [`Chromatic_QuantumTorus_RationalTorusFaithful`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/QuantumTorus/RationalTorusFaithful.lean), [`Chromatic_Walls_PureActualCoefficients`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/PureActualCoefficients.lean), [`Chromatic_Walls_PureCutGroup`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/PureCutGroup.lean).
--
--   **Imports.** It imports the bundle `OAIQ368Chrom008` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ368Chrom057`; the statements `OAI.ElementaryPositivity.QuantumTorus.nearCut_old_positive_seed` and `OAI.ElementaryPositivity.QuantumTorus.pure_mutated_inverse_finite`; the proofs of `OAI.ElementaryPositivity.QuantumTorus.nearCut_old_positive_seed`, `OAI.ElementaryPositivity.QuantumTorus.pure_mutated_inverse_finite` and `OAI.ElementaryPositivity.RationalFiber.finite_refinement_import`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom008

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_RationalTorusFaithful
attribute [-simp] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.gaugeAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.gauge_monomial _root_.OAI.ElementaryPositivity.RationalFiber.pureAction_monomial _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)

def readFiber (m : M) : FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω) →+ K where
  toFun f:=(expandZero (f (off k p hp m))).coeff (k m)*
    (↑(v^(k m*complementAlpha k p Ω (off k p hp m))):K)
  map_zero':=by simp
  map_add' f g:=by simp [add_mul]
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RationalPureCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus WallUnits PowerSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ)
def centeredRatio (t : ℤ) : PowerSeries K :=
  rescale (↑(v^(-t)):K)
    (rescale (↑(v^(2*t)):K) (elementary (↑(v^(-2:ℤ)):K) (↑(v⁻¹):K))*
      (elementary (↑(v^(-2:ℤ)):K) (↑(v⁻¹):K))⁻¹)
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_LaurentHomogenize
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_raySeries _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries HahnSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ κ : M →+ ℤ)
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.laurentHomogenizeRing
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.laurentHomogenizeAddCommMonoid
local instance laurentHomogenizeAddGroup_r20b525_1 : AddGroup (Torus v Ω) :=
  (Torus.instRing v Ω).toAddGroup
local instance laurentHomogenizeNonUnitalSemiring_r20b525_1 : NonUnitalSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalSemiring
local instance laurentHomogenizeNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring

lemma laurentHomogenize_monomial_mul (m n : M) (a b : R)
    (hm : 0 ≤ δ m) (hn : 0 ≤ δ n) :
    laurentHomogenize v Ω δ κ (Torus.monomial v Ω m a * Torus.monomial v Ω n b) =
      laurentHomogenize v Ω δ κ (Torus.monomial v Ω m a) *
        laurentHomogenize v Ω δ κ (Torus.monomial v Ω n b) := by
  rw [Torus.monomial_mul_monomial, laurentHomogenize_monomial,
    laurentHomogenize_monomial, laurentHomogenize_monomial, monomial_mul_monomial,
    HahnSeries.single_mul_single, Torus.monomial_mul_monomial, map_add, map_add,
    Int.toNat_add hm hn]

lemma laurentHomogenize_mul (f g : Torus v Ω)
    (hf : ∀ m, f m ≠ 0 → 0 ≤ δ m) (hg : ∀ m, g m ≠ 0 → 0 ≤ δ m) :
    laurentHomogenize v Ω δ κ (f*g) =
      laurentHomogenize v Ω δ κ f * laurentHomogenize v Ω δ κ g := by
  classical
  calc
    _ = ∑ m ∈ f.support, ∑ n ∈ g.support,
        laurentHomogenize v Ω δ κ (Torus.monomial v Ω m (f m)*Torus.monomial v Ω n (g n)) := by
      have H (s : Finset M) (a : M → Torus v Ω) :
          laurentHomogenize v Ω δ κ (∑m∈s,a m)=∑m∈s,laurentHomogenize v Ω δ κ (a m) :=
        _root_.map_sum (laurentHomogenize v Ω δ κ) a s
      simp_rw [←H]
      congr 1
      simp_rw [←homo_mul_sum]
      rw [torus_sum_monomial, ←homo_sum_mul, torus_sum_monomial]
    _ = ∑ m ∈ f.support, ∑ n ∈ g.support,
        laurentHomogenize v Ω δ κ (Torus.monomial v Ω m (f m))*
        laurentHomogenize v Ω δ κ (Torus.monomial v Ω n (g n)) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      exact laurentHomogenize_monomial_mul v Ω δ κ m n _ _
        (hf m (Finsupp.mem_support_iff.mp hm)) (hg n (Finsupp.mem_support_iff.mp hn))
    _ = _ := by
      simp_rw [←Finset.mul_sum]
      rw [←Finset.sum_mul]
      congr 1 <;> rw [←_root_.map_sum, torus_sum_monomial]

lemma laurentHomogenize_one : laurentHomogenize v Ω δ κ 1 = 1 := by
  change laurentHomogenize v Ω δ κ (Torus.monomial v Ω 0 1) = _
  rw [laurentHomogenize_monomial, _root_.map_zero, _root_.map_zero, Int.toNat_zero,
    monomial_zero_eq_C_apply]
  change C (HahnSeries.single 0 (1 : Torus v Ω)) = 1
  simp
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_LatticeHahn
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_raySeries _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries HahnSeries PowerSeriesAdjoint
noncomputable section
variable {R M:Type*} [CommRing R] [AddCommGroup M]
variable (v:Rˣ) (Ω:M →+ M →+ ℤ) (τ:M →+ ℤ)
local instance latticeHahnRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance latticeHahnAddCommMonoid_r20b525_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance latticeHahnAddGroup_r20b525_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance latticeHahnNonUnitalSemiring : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance latticeHahnNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalNonAssocSemiring

def latticeHahn : Torus v Ω →+* HahnSeries ℤ (Torus v Ω) where
  toFun F:=constantCoeff (laurentHomogenize v Ω 0 τ F)
  map_zero':=by simp
  map_add' F G:=by rw [_root_.map_add,_root_.map_add]
  map_one':=by rw [laurentHomogenize_one,map_one]
  map_mul' F G:=by rw [laurentHomogenize_mul v Ω 0 τ F G (by simp) (by simp),map_mul]

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_PureActualCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits RationalFiber
noncomputable section
variable {M:Type*} [AddCommGroup M]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (τ:M →+ ℤ)
local instance pureActualCoefficientsRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.PowerSeriesAdjoint
open PowerSeries HahnSeries
noncomputable section
variable {A:Type*} [Ring A]
def hahnAction (f:PowerSeries A) (x:HahnSeries ℤ A) : HahnSeries ℤ A :=
  ofPowerSeries ℤ A f*x*ofPowerSeries ℤ A (invOfUnit f 1)
end
end ElementaryPositivity.PowerSeriesAdjoint
namespace ElementaryPositivity.QuantumTorus
open PowerSeries HahnSeries PowerSeriesAdjoint WallUnits
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0) (τ:M →+ ℤ)
local instance pureActualScalarCoefficientsRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance pureActualScalarCoefficientsAddCommMonoid_r20b525_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance pureActualScalarCoefficientsAddGroup_r20b525_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance pureActualScalarCoefficientsNonUnitalSemiring_r20b525_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
local instance pureActualScalarCoefficientsNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalNonAssocSemiring

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_HalfspacePolynomialCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits HahnSeries
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d)
local instance halfspacePolynomialCoefficientsCoeffRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω

local instance halfspacePolynomialCoefficientsCoeffAddCommMonoid_r20b525_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance halfspacePolynomialCoefficientsCoeffAddGroup_r20b525_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance halfspacePolynomialCoefficientsCoeffNonUnitalSemiring_r20b525_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
local instance halfspacePolynomialCoefficientsCoeffNonUnitalNonAssocSemiring_r20b525_1 : NonUnitalNonAssocSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalNonAssocSemiring
def rootSectionChart (h:M →+ ℝ) : CompletedPositive LaurentRay.vUnit Ω C :=
  ⟨(chartNegative LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C)).val*
      invOfUnit (simpleTotalTransport Ω C).val 1,
    by simp only [map_mul,(chartNegative LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C)).property.1,
      constantCoeff_invOfUnit,inv_one,Units.val_one,mul_one],
    SeriesGraded.mul LaurentRay.vUnit Ω C
      (chartNegative LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C)).property.2
      (SeriesGraded.inverse LaurentRay.vUnit Ω C (simpleTotalTransport Ω C).property.2)⟩

def polynomialSectionCoefficient (h:M →+ ℝ) (F:Torus LaurentRay.vUnit Ω) (m:M) : LaurentSeries ℚ :=
  actualPolynomialAdjointCoefficient Ω (rootOrder coord) (rootSectionChart Ω C h).val F m

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_HomogeneousElementaryExpressions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M)
variable (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d) (pc:I)
variable (e:M →+ E)

def NearCut (h:Module.Dual ℝ E) : Prop :=
  |h (e (simpleRoot C pc))|<1/((mutationSize Ω C pc:ℝ)+1) ∧
    ∀i,i≠pc → h (e (simpleRoot C i))< -1

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_PurePolynomialCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits RationalFiber
noncomputable section
variable {M:Type*} [AddCommGroup M]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0) (τ:M →+ ℤ)
local instance purePolynomialCoefficientsRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_NearCutGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open FiniteRayGeometry
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M) (pc:I) (e:M →+ E)

def nearCutProbes : Finset (ℝ×E) := by
  classical
  exact (Finset.univ.erase pc).image (fun i=>(1,e (simpleRoot C i))) ∪
    {(-1/((mutationSize Ω C pc:ℝ)+1),e (simpleRoot C pc)),
     (1/((mutationSize Ω C pc:ℝ)+1),e (simpleRoot C pc))}

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_PureCutGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.AffineCut
noncomputable section
variable {G:Type*} [Group G]
def oldGauge (g:G) (side:Bool) : G := if side then g⁻¹ else 1
def oldFactor (g:G) (u v t:ℝ) : G := if u+t*v=0 then if v<0 then g else g⁻¹ else 1
end
end ElementaryPositivity.AffineCut

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_NearCutSectionCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits RationalFiber FiniteRayGeometry
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d) (pc:I)
variable (e:M →+ E) (he:Function.Injective e)
variable (S:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS:∀x,S x x=0)
variable (hcomp:∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L:Module.Dual ℝ E) (hdeg:∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
local instance nearCutSectionChartsRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_NearCutPolynomialSeeds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits RationalFiber FiniteRayGeometry
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d) (pc:I)
variable (e:M →+ E) (he:Function.Injective e)
variable (S:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS:∀x,S x x=0)
variable (hcomp:∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L:Module.Dual ℝ E) (hdeg:∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))

local instance nearCutPolynomialSeedsRing_r20b525_1 : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance nearCutPolynomialSeedsAddCommMonoid_r20b525_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance nearCutPolynomialSeedsAddGroup_r20b525_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
def PureInitialRelation (F F':Torus LaurentRay.vUnit Ω) : Prop :=
  embed LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc) F=
    pureAction LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω)
        (embed LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc) F')

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end


