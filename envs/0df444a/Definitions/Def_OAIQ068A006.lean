-- Prove2me | Definitions.Def_OAIQ068A006
-- name    : OAIQ068A006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T07:39:59.418221+00:00
-- url     : https://prove2.me/theorems/905aef74-86a5-4073-a2ed-8da4564043f4
-- title:
--   Definitions bundle OAIQ068A006 of the split of OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 159 declarations of OpenAI's Lean: 78 definitions, 3 instances and 78 theorems. The definitions and types are `OAI.PiExponent.AffineJetSupport.restrictionSectionsIso`, `OAI.PiExponent.AffineJetSupport.sectionsIso`, `OAI.PiExponent.AnalyticCollision.exponentialMonomial`, `OAI.PiExponent.AnalyticCollision.normalizedTaylorCoeff`, `OAI.PiExponent.AnalyticCollision.rowTest`, `OAI.PiExponent.ApproximationExponents`, `OAI.PiExponent.BranchContactIdeal.powerIdeal`, `OAI.PiExponent.CoherentCokernels.presentationOfIso`, `OAI.PiExponent.CoherentCokernels.specCokernelIso`, `OAI.PiExponent.Collision.collisionRatio`, `OAI.PiExponent.Collision.collisionRemainder`, `OAI.PiExponent.Collision.multiplicity`, `OAI.PiExponent.CommutingTaylor.iter`, `OAI.PiExponent.CommutingTaylor.mixedIter`, `OAI.PiExponent.CommutingTaylor.residueTaylorFin`, `OAI.PiExponent.CommutingTaylor.taylorHom`, `OAI.PiExponent.CommutingTaylor.taylorHomFin`, `OAI.PiExponent.CommutingTaylor.taylorSeries`, `OAI.PiExponent.CoordinateFiniteSlice.coordinateEquiv`, `OAI.PiExponent.CoordinateFiniteSlice.coordinateRenaming`, `OAI.PiExponent.CoordinateFiniteSlice.residueCoordinates`, `OAI.PiExponent.CoordinateFiniteSlice.residueEquiv`, `OAI.PiExponent.CoordinateFiniteSlice.slicePoint`, `OAI.PiExponent.CoordinateFiniteSlice.splitPrime`, `OAI.PiExponent.CoordinateSliceComparison.primeLength`, `OAI.PiExponent.CoordinateSliceLength.localizedLength`, `OAI.PiExponent.CoordinateSliceLength.residueSlice`, `OAI.PiExponent.DeterminantContradiction.collisionConstant`, `OAI.PiExponent.ExceptionalAffineChart.affineGammaEquiv`, `OAI.PiExponent.ExceptionalAffineChart.chartFunctionsEquiv`, `OAI.PiExponent.ExceptionalAffineChart.chartOpen`, `OAI.PiExponent.ExceptionalAffineChart.functionsOnOpenEquiv`, `OAI.PiExponent.ExceptionalAffineChart.idealMapAddEquiv`, `OAI.PiExponent.FormalBranchContact.composedLogTails`, `OAI.PiExponent.FormalBranchContact.truncatedBranchCoordinates`, `OAI.PiExponent.FormalLogJet.formalLog`, `OAI.PiExponent.FormalLogJet.liftSeries`, `OAI.PiExponent.FormalLogTruncation.logTail`, `OAI.PiExponent.GeneratorsSectionCover.schemeFree`, `OAI.PiExponent.GoodRationalApproximations` and 38 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `PiExponent_Ampleness_ExceptionalAffineChart`, `PiExponent_Ampleness_ExceptionalAffineChartRestriction`, `PiExponent_Ampleness_ExceptionalPowerSections`, `PiExponent_Analysis_AnalyticCollision`, `PiExponent_Analysis_CollisionCombinatorics`, `PiExponent_Analysis_CollisionExponential`, `PiExponent_Analysis_FormalLogTailOrder`, `PiExponent_Analysis_FormalLogTruncation`, `PiExponent_Analysis_LogarithmicContactIdeal`, `PiExponent_Approximation_CoherentCokernels`, `PiExponent_Approximation_CoordinateSliceComparison`, `PiExponent_Approximation_DeterminantContradiction`, `PiExponent_Approximation_GeneratorsSectionCover`, `PiExponent_Approximation_WeightedSliceDegree`, `PiExponent_Cohomology_FiniteZeroEuler`, `PiExponent_Geometry_CartierPowerFrames`, `PiExponent_Geometry_CurveEffectiveTwist`, `PiExponent_Geometry_ProjectiveSerreTransfer`, `PiExponent_Geometry_SectionZeroStalk`, `PiExponent_Jets_AffineJetQuotient`, `PiExponent_Jets_AffineJetSupport`, `PiExponent_Jets_BranchContact`, `PiExponent_Jets_BranchContactIdeal`, `PiExponent_Jets_CommutingTaylor`, `PiExponent_Jets_CompactJetIdeal`, `PiExponent_Jets_FormalBranchCoordinates`, `PiExponent_Jets_FormalLogJet`, `PiExponent_Jets_JetGeometry`, `PiExponent_Jets_OrdinaryAuxiliaryJet`, `PiExponent_Jets_TransverseMultiplicity`, `PiExponent_LocalAlgebra_CoordinateContactBound`, `PiExponent_LocalAlgebra_CoordinateFiniteSlice`, `PiExponent_LocalAlgebra_CoordinateSliceLength`, `PiExponent_LocalAlgebra_IdealPowerAnnihilator`, `PiExponent_LocalAlgebra_LocalizationQuotientParameters`, `PiExponent_LocalAlgebra_LocalizedLengthEquivalence`, `PiExponent_LocalAlgebra_PrimeResidueAlgebraEquiv`, `PiExponent_LocalAlgebra_SplitCoordinateClosedPoint`, `PiExponent_LocalAlgebra_TensorIdealInclusion`, `PiExponent_Polynomials_PolynomialCoefficientLocalization`, `PiExponent_Polynomials_PolynomialFrame`, `PiExponent_Polynomials_PolynomialPoleBound`, `PiExponent_Polynomials_RationalResidueCoefficientField`, `PiExponent_Statement`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ068A016`, `OAIQ068A017`, `OAIQ068A018` and `OAIQ068A019`; the statements `OAI_PiExponent_AnalyticCollision_translated_row_determinant_exp_bound`, `OAI.PiExponent.AnalyticCollision.translated_row_determinant_exp_bound_q68`, `OAI_PiExponent_CoordinateSliceComparison_length_eq_sliceFamily_of_normalBasis`, `OAI.PiExponent.CoordinateSliceComparison.length_eq_sliceFamily_of_normalBasis_q68`, `OAI_PiExponent_CoordinateSliceComparison_sliceFamily_mem_minimalPrimes_of_normalBasis`, `OAI.PiExponent.CoordinateSliceComparison.sliceFamily_mem_minimalPrimes_of_normalBasis_q68`, `OAI_PiExponent_NumericalAmpleness_isAmple_of_lower_ampleness_of_euler_growth`, `OAI_PiExponent_PrimeWeightedBezout_weighted_prime_length_bound` and `OAI.PiExponent.PrimeWeightedBezout.weighted_prime_length_bound_q68`; the proofs of `OAI_PiExponentJets_W22_localized_onecut_parent_recurrence`, `OAI.PiExponentJets.W22.localized_onecut_parent_recurrence_q68`, `OAI_PiExponent_AnalyticCollision_translated_row_determinant_exp_bound`, `OAI.PiExponent.AnalyticCollision.translated_row_determinant_exp_bound_q68` and `OAI_PiExponent_CurveInequality_excess_implies_fibre_coordinate_constant`.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 1581d4c

import Mathlib

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_TensorIdealInclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X : Scheme.{0}}

lemma frame_square {C : Type*} [Category C]
    {A B A' B' T O : C} (r : A ≅ A') (r' : B ≅ B')
    (e : A' ≅ T) (e' : B' ≅ T) (u : T ≅ O)
    (m : A ⟶ B) (p : A' ⟶ B') (a : O ⟶ O)
    (hn : m ≫ r'.hom = r.hom ≫ p)
    (hs : e.inv ≫ p ≫ e'.hom ≫ u.hom = u.hom ≫ a) :
    (r ≪≫ e ≪≫ u).inv ≫ m ≫ (r' ≪≫ e' ≪≫ u).hom = a := by
  simp only [Iso.trans_inv, Iso.trans_hom, Category.assoc]
  rw [← Category.assoc m r'.hom, hn]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [hs]
  simp

lemma frame_inclusion {C : Type*} [Category C]
    {A B D O : C} (e : A ≅ O) (e' : B ≅ O) (h : B ≅ D) (f : D ≅ O)
    (m : A ⟶ B) (a : O ⟶ O) (ha : e.inv ≫ m ≫ e'.hom = a) :
    e.inv ≫ (m ≫ h.hom) ≫ f.hom = a ≫ (f.symm ≪≫ h.symm ≪≫ e').inv := by
  rw [← ha]
  simp

lemma mono_iso_sandwich {C : Type*} [Category C]
    {A B D E F : C} (e : A ≅ B) (m : B ⟶ D) (u : D ≅ E) (v : E ≅ F)
    [Mono m] : Mono ((e.hom ≫ m ≫ u.hom) ≫ v.hom) := inferInstance

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ExceptionalPowerSections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry
namespace PiExponentSeshadri.Geometry
variable {X Y : Scheme}

def powerChartIdeal (f : Y ⟶ X) (I : X.IdealSheafData) (n : ℕ)
    (U : Y.affineOpens) (V : X.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    Ideal Γ(U.1.toScheme, ⊤) :=
  (((I.ideal V)^n).map (f.appLE V.1 U.1 hUV).hom).map U.1.topIso.inv.hom

end PiExponentSeshadri.Geometry
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ExceptionalAffineChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry
namespace PiExponent.ExceptionalAffineChart
variable {R A : Type} [CommRing R] [CommRing A] {Y : Scheme}
variable (I : Ideal R) (f : Y ⟶ Spec (CommRingCat.of R))
  (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
  (φ : R →+* A) (hf : j ≫ f = Spec.map (CommRingCat.ofHom φ))

def chartOpen : Y.affineOpens :=
  ⟨j.opensRange, isAffineOpen_opensRange _⟩

def affineGammaEquiv {Y : Scheme} {A : CommRingCat} (g : Y ≅ Spec A) :
    Γ(Y,⊤) ≃+* A :=
  (Scheme.Γ.mapIso g.symm.op ≪≫ Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv

def chartFunctionsEquiv : Γ((chartOpen j).1.toScheme, ⊤) ≃+* A :=
  affineGammaEquiv (j.isoOpensRange.symm)

def idealMapAddEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (J : Ideal A) : J ≃+ J.map e.toRingHom :=
  AddEquiv.ofBijective
    (show J →+ J.map e.toRingHom from
      { toFun := fun x => ⟨e x, Ideal.mem_map_of_mem _ x.property⟩
        map_zero' := by ext; exact e.map_zero
        map_add' := by intro x y; ext; exact e.map_add x y })
    ⟨by intro x y h; exact Subtype.ext (e.injective (congrArg Subtype.val h)), by
      intro y
      obtain ⟨x, hx, he⟩ := (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).mp y.property
      exact ⟨⟨x, hx⟩, Subtype.ext he⟩⟩

end PiExponent.ExceptionalAffineChart
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ExceptionalAffineChartRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ExceptionalAffineChart
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry

section Functions
variable {A B : Type} [CommRing A] [CommRing B] {Y : Scheme}
variable (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
  (j' : Spec (CommRingCat.of B) ⟶ Y) [IsOpenImmersion j']
  (θ : A →+* B) (h : Spec.map (CommRingCat.ofHom θ) ≫ j = j')

def functionsOnOpenEquiv : Γ(Y,j.opensRange) ≃+* A :=
  j.opensRange.topIso.symm.commRingCatIsoToRingEquiv.trans (chartFunctionsEquiv j)

end Functions

end
end PiExponent.ExceptionalAffineChart

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Analysis_AnalyticCollision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Complex Finset

namespace PiExponent.AnalyticCollision

noncomputable def exponentialMonomial (b h : ℂ) (d : ℕ) (z : ℂ) : ℂ :=
  b * Complex.exp (h * z) * z ^ d

noncomputable def normalizedTaylorCoeff (f : ℂ → ℂ) (R : ℝ) (d : ℕ) : ℂ :=
  cauchyPowerSeries f 0 R d (fun _ => (R : ℂ))

noncomputable def rowTest (ell : ℕ) (f : ℂ → ℂ) : ℂ :=
  cauchyPowerSeries f 0 (1 / 2) ell (fun _ => 1)

end PiExponent.AnalyticCollision

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Analysis_CollisionCombinatorics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace PiExponent.Collision

def multiplicity {ι κ : Type*} [DecidableEq κ]
    (rows : Finset ι) (group : ι → κ) (a : κ) : ℕ :=
  (rows.filter fun i => group i = a).card

end PiExponent.Collision

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Analysis_CollisionExponential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace PiExponent.Collision

noncomputable def collisionRatio : ℝ := Real.exp (-Real.log 2 / 2)

noncomputable def collisionRemainder (M : ℕ) (H : ℝ) : ℝ :=
  (Real.log M + Real.log 2 / 4 - Real.log (1 - collisionRatio)) / H

end PiExponent.Collision

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_JetGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.JetGeometry

noncomputable section

open MvPowerSeries

variable {σ R : Type*} [CommRing R]

def RationalCoefficientPacket (v : σ → ℚ) (H : ℚ) :=
  {d : σ →₀ ℕ // Finsupp.weight v d < H} → R

def rationalCoefficientPacket (v : σ → ℚ) (H : ℚ) (f : MvPowerSeries σ R) :
    RationalCoefficientPacket (R := R) v H := fun d => coeff d.val f

end

end PiExponent.JetGeometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_PolynomialFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentApprox

noncomputable section

abbrev FramePolynomial (m : ℕ) := MvPolynomial (Fin (m + 1)) ℂ

def logarithmicDerivation (m : ℕ) :
    Derivation ℂ (FramePolynomial m) (FramePolynomial m) :=
  (MvPolynomial.X (0 : Fin (m + 1)) : FramePolynomial m) •
    MvPolynomial.pderiv (R := ℂ) (0 : Fin (m + 1)) +
    ∑ i : Fin m, MvPolynomial.pderiv (R := ℂ) i.succ

def polynomialFrame (m : ℕ) (i : Fin (m + 1)) :
    Derivation ℂ (FramePolynomial m) (FramePolynomial m) :=
  if i = 0 then logarithmicDerivation m else MvPolynomial.pderiv i

@[simp] theorem polynomialFrame_zero (m : ℕ) :
    polynomialFrame m 0 = logarithmicDerivation m := by
  simp only [polynomialFrame, ite_true]

end
end PiExponentApprox

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_FormalLogJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.FormalLogJet
open MvPowerSeries

variable {R : Type*} [CommRing R]

def liftSeries (m : ℕ) : PowerSeries R →+* MvPowerSeries (Fin (m + 1)) R :=
  (finSuccEquiv R m).symm.toRingHom.comp (PowerSeries.map MvPowerSeries.C)

@[simp] theorem coeff_liftSeries (m : ℕ) (f : PowerSeries R)
    (d : Fin (m + 1) →₀ ℕ) :
    coeff d (liftSeries m f) = if d.tail = 0 then PowerSeries.coeff (d 0) f else 0 := by
  have h := coeff_coeff_finSuccEquiv (liftSeries m f) (k := d 0) (x := d.tail)
  rw [Finsupp.cons_tail] at h
  rw [← h]
  simp [liftSeries, PowerSeries.coeff_map, coeff_C]

@[simp] theorem liftSeries_X (m : ℕ) : liftSeries (R := R) m PowerSeries.X = X 0 := by
  apply (finSuccEquiv R m).injective
  simp [liftSeries]

@[simp] theorem liftSeries_C (m : ℕ) (r : R) :
    liftSeries m (PowerSeries.C r) = C r := by
  apply (finSuccEquiv R m).injective
  simp [liftSeries]

def formalLog (m : ℕ) : MvPowerSeries (Fin (m+1)) ℂ :=
  liftSeries m (PowerSeries.log ℂ)

end PiExponent.FormalLogJet

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Analysis_FormalLogTruncation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.FormalLogTruncation

open MvPowerSeries
open scoped BigOperators

variable {R : Type*} [CommRing R]

open JetGeometry

noncomputable def logTail (T : ℕ) : PowerSeries ℂ :=
  PowerSeries.log ℂ - (PowerSeries.trunc T (PowerSeries.log ℂ) : PowerSeries ℂ)

@[simp] theorem logTail_constantCoeff (T : ℕ) : PowerSeries.constantCoeff (logTail T) = 0 := by
  simp [logTail, Polynomial.constantCoeff_coe, PowerSeries.coeff_trunc,
    PowerSeries.coeff_log]

theorem coeff_logTail_eq_zero (T n : ℕ) (hn : n < T) :
    PowerSeries.coeff n (logTail T) = 0 := by
  simp [logTail, Polynomial.coeff_coe, PowerSeries.coeff_trunc, hn]

end PiExponent.FormalLogTruncation

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_BranchContact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.BranchContact

variable {ι : Type*} [Fintype ι]

theorem order_add_lower (B : ℚ) (f g : PowerSeries ℂ)
    (hf : ∀ k : ℕ, f.order = (k : ℕ∞) → B ≤ (k : ℚ))
    (hg : ∀ k : ℕ, g.order = (k : ℕ∞) → B ≤ (k : ℚ))
    (k : ℕ) (hk : (f + g).order = (k : ℕ∞)) : B ≤ (k : ℚ) := by
  have hmin : min f.order g.order ≤ (k : ℕ∞) :=
    (PowerSeries.min_order_le_order_add f g).trans hk.le
  rcases min_le_iff.mp hmin with h | h
  · have hn : f.order ≠ ⊤ := ne_top_of_le_ne_top (by simp) h
    have he := ENat.natCast_toNat hn
    have hb := hf f.order.toNat he.symm
    have hnat : f.order.toNat ≤ k := by
      exact_mod_cast he.symm ▸ h
    exact hb.trans (by exact_mod_cast hnat)
  · have hn : g.order ≠ ⊤ := ne_top_of_le_ne_top (by simp) h
    have he := ENat.natCast_toNat hn
    have hb := hg g.order.toNat he.symm
    have hnat : g.order.toNat ≤ k := by
      exact_mod_cast he.symm ▸ h
    exact hb.trans (by exact_mod_cast hnat)

end PiExponent.BranchContact

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Analysis_FormalLogTailOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.FormalBranchContact

open FormalLogTruncation

theorem logTail_order_ge (T : ℕ) : (T : ℕ∞) ≤ (logTail T).order :=
  PowerSeries.nat_le_order (logTail T) T (coeff_logTail_eq_zero T)

theorem composed_logTail_order_ge (T : ℕ) (t : PowerSeries ℂ)
    (ht : PowerSeries.constantCoeff t = 0) :
    (T : ℕ∞) * t.order ≤ PowerSeries.order (PowerSeries.subst t (logTail T)) := by
  calc
    (T : ℕ∞) * t.order = MvPowerSeries.order t * T := by
      rw [PowerSeries.order_eq_order, mul_comm]
    _ ≤ MvPowerSeries.order t * (logTail T).order :=
      mul_le_mul_right (logTail_order_ge T) _
    _ ≤ MvPowerSeries.order (PowerSeries.subst t (logTail T)) :=
      PowerSeries.le_order_subst t (PowerSeries.HasSubst.of_constantCoeff_zero' ht) _
    _ = PowerSeries.order (PowerSeries.subst t (logTail T)) := PowerSeries.order_eq_order.symm

end PiExponent.FormalBranchContact

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_BranchContactIdeal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.BranchContactIdeal
open IsDiscreteValuationRing

variable {A ι : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

def powerIdeal (z : ι → A) (e : ι → ℕ) : Ideal A :=
  Ideal.span (Set.range (fun i => z i ^ e i))

theorem powerIdeal_eq_singleton (z : ι → A) (e : ι → ℕ) (i : ι)
    (hmin : ∀ j, addVal A (z i ^ e i) ≤ addVal A (z j ^ e j)) :
    powerIdeal z e = Ideal.span {z i ^ e i} := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro a ⟨j,rfl⟩
    exact Ideal.mem_span_singleton.mpr (addVal_le_iff_dvd.mp (hmin j))
  · rw [Ideal.span_le]
    intro b hb
    obtain rfl := Set.mem_singleton_iff.mp hb
    exact Ideal.subset_span (Set.mem_range_self i)

theorem addVal_pow_toNat {a : A} (ha : a ≠ 0) (n : ℕ) :
    (addVal A (a ^ n)).toNat = n * (addVal A a).toNat := by
  have ht : addVal A a ≠ ⊤ := addVal_eq_top_iff.not.mpr ha
  rw [(addVal A).map_pow, ← ENat.natCast_toNat ht]
  simp [nsmul_eq_mul]

end PiExponent.BranchContactIdeal

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_FormalBranchCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.FormalBranchContact

open FormalLogTruncation

def composedLogTails {m : ℕ} (a : Fin (m+1) → PowerSeries ℂ) (T : Fin m → ℕ) :
    Fin (m+1) → PowerSeries ℂ :=
  Fin.cases 0 (fun i => PowerSeries.subst (a 0) (logTail (T i)))

def truncatedBranchCoordinates {m : ℕ} (c : Fin m → ℂ) (y : PowerSeries ℂ)
    (x : Fin m → PowerSeries ℂ) (T : Fin m → ℕ) : Fin (m+1) → PowerSeries ℂ :=
  Fin.cases (y-1) (fun i => x i - PowerSeries.C (c i) -
    PowerSeries.subst (y-1)
      (PowerSeries.trunc (T i) (PowerSeries.log ℂ) : PowerSeries ℂ))

end PiExponent.FormalBranchContact

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Analysis_LogarithmicContactIdeal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.LogarithmicContactIdeal

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra ℂ A] [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]

def truncatedCoordinates {m : ℕ} (c : Fin m → ℂ) (y : A) (x : Fin m → A)
    (T : Fin m → ℕ) : Fin (m+1) → A :=
  Fin.cases (y-1) (fun i => x i - algebraMap ℂ A (c i) -
    Polynomial.aeval (y-1) (PowerSeries.trunc (T i) (PowerSeries.log ℂ)))

def logarithmicIdeal {m : ℕ} (c : Fin m → ℂ) (y : A) (x : Fin m → A)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) : Ideal A :=
  BranchContactIdeal.powerIdeal (truncatedCoordinates c y x T) e

end PiExponent.LogarithmicContactIdeal

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_CoherentCokernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CoherentCokernels
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u

def presentationOfIso (X : Scheme.{u})
    {M N : SheafOfModules.{u} X.ringCatSheaf} (e : M ≅ N)
    (P : M.Presentation) : N.Presentation := by
  let : IsIso e.hom := e.isIso_hom
  exact P.ofIsIso e.hom

def specCokernelIso {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    let g := (tilde.functor R).preimage
      ((asIso M.fromTildeΓ).hom ≫ f ≫ (asIso N.fromTildeΓ).inv)
    (tilde.functor R).obj (cokernel g) ≅ cokernel f := by
  intro g
  let hm := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  let hn := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent N
  let em := @asIso _ _ _ _ M.fromTildeΓ hm
  let en := @asIso _ _ _ _ N.fromTildeΓ hn
  exact PreservesCokernel.iso (tilde.functor R) g ≪≫
    cokernel.mapIso ((tilde.functor R).map g) f em en (by
        change (tilde.functor R).map ((tilde.functor R).preimage _) ≫ _ = _
        erw [Functor.map_preimage]
        exact (Category.assoc em.hom (f ≫ en.inv) en.hom).trans
          (congrArg (fun q => em.hom ≫ q)
            ((Category.assoc f en.inv en.hom).trans
              ((congrArg (fun q => f ≫ q) en.inv_hom_id).trans (Category.comp_id f)))))

end
end PiExponent.CoherentCokernels

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_WeightedSliceDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.WeightedSliceDegree

open scoped BigOperators Pointwise

variable {C E ι σ : Type*} [Field C] [Field E] [Algebra C E]

def SupportBound (ρ : σ → ℝ) (N : ℝ) (p : MvPolynomial σ E) : Prop :=
  ∀ d ∈ p.support, Finsupp.weight ρ d ≤ N

noncomputable def sliceMap (A : Finset ι) (b : ι → E) :
    MvPolynomial ι C →ₐ[C] MvPolynomial A E := by
  classical
  exact MvPolynomial.aeval (fun i => if h : i ∈ A then MvPolynomial.X ⟨i, h⟩ else MvPolynomial.C (b i))

@[simp] theorem sliceMap_X_mem (A : Finset ι) (b : ι → E) (i : ι) (hi : i ∈ A) :
    sliceMap (C := C) A b (MvPolynomial.X i) = MvPolynomial.X ⟨i, hi⟩ := by
  classical
  simp [sliceMap, hi]

@[simp] theorem sliceMap_X_notMem (A : Finset ι) (b : ι → E) (i : ι) (hi : i ∉ A) :
    sliceMap (C := C) A b (MvPolynomial.X i) = MvPolynomial.C (b i) := by
  classical
  simp [sliceMap, hi]

@[simp] theorem sliceMap_C (A : Finset ι) (b : ι → E) (c : C) :
    sliceMap A b (MvPolynomial.C c) = MvPolynomial.C (algebraMap C E c) := by
  classical
  simp [sliceMap]

noncomputable def enumeratedSliceMap (A : Finset ι) (b : ι → E) :
    MvPolynomial ι C →ₐ[C] MvPolynomial (Fin A.card) E :=
  ((MvPolynomial.rename (R := E) A.equivFin).restrictScalars C).comp (sliceMap A b)

end PiExponent.WeightedSliceDegree

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_LocalizedLengthEquivalence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

variable {R S : Type*} [CommRing R] [CommRing S]

theorem primeCompl_map_eq_of_comap
    (e : R ≃+* S) (P : Ideal R) (Q : Ideal S) [P.IsPrime] [Q.IsPrime]
    (hPQ : P = Q.comap e.toRingHom) :
    P.primeCompl.map e.toMonoidHom = Q.primeCompl := by
  ext x
  constructor
  · rintro ⟨r, hr, rfl⟩
    change e r ∉ Q
    intro h
    apply hr
    rw [hPQ]
    exact h
  · intro hx
    change x ∉ Q at hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    change e.symm x ∉ P
    rw [hPQ]
    change e (e.symm x) ∉ Q
    simpa only [e.apply_symm_apply] using hx

noncomputable def primeLocalizationEquiv
    (e : R ≃+* S) (P : Ideal R) (Q : Ideal S) [P.IsPrime] [Q.IsPrime]
    (hPQ : P = Q.comap e.toRingHom) :
    Localization.AtPrime P ≃+* Localization.AtPrime Q :=
  IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime P) (Localization.AtPrime Q)
    e (primeCompl_map_eq_of_comap e P Q hPQ)

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_LocalizationQuotientParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentSiegel.W23

variable {A : Type*} [CommRing A]

def quotientParameterPrime (I m : Ideal A) (_hI : I ≤ m) : Ideal (A ⧸ I) :=
  m.map (Ideal.Quotient.mk I)

instance quotientParameterPrime_isPrime (I m : Ideal A) [m.IsPrime] (hI : I ≤ m) :
    (quotientParameterPrime I m hI).IsPrime :=
  Ideal.map_isPrime_of_surjective (f := Ideal.Quotient.mk I) (I := m)
    Ideal.Quotient.mk_surjective
    (by simpa only [Ideal.mk_ker] using hI)

@[simp] theorem mem_quotientParameterPrime_mk (I m : Ideal A) (hI : I ≤ m) (a : A) :
    Ideal.Quotient.mk I a ∈ quotientParameterPrime I m hI ↔ a ∈ m :=
  Ideal.mem_quotient_iff_mem hI

def parameterLocalizedIdeal (I m : Ideal A) [m.IsPrime] :
    Ideal (Localization.AtPrime m) :=
  I.map (algebraMap A (Localization.AtPrime m))

variable (I m : Ideal A) [m.IsPrime] (hI : I ≤ m)

def parameterLocalizationMap :
    Localization.AtPrime m →+* Localization.AtPrime (quotientParameterPrime I m hI) :=
  IsLocalization.map (Localization.AtPrime (quotientParameterPrime I m hI))
    (Ideal.Quotient.mk I) (M := m.primeCompl)
    (S := Localization.AtPrime m)
    (T := (quotientParameterPrime I m hI).primeCompl) (by
      intro a ha
      change Ideal.Quotient.mk I a ∉ quotientParameterPrime I m hI
      exact fun h => ha ((mem_quotientParameterPrime_mk I m hI a).mp h))

@[simp] theorem parameterLocalizationMap_algebraMap (a : A) :
    parameterLocalizationMap I m hI (algebraMap A (Localization.AtPrime m) a) =
      algebraMap (A ⧸ I) (Localization.AtPrime (quotientParameterPrime I m hI))
        (Ideal.Quotient.mk I a) :=
  IsLocalization.map_eq _ a

theorem parameterLocalizedIdeal_le_ker :
    parameterLocalizedIdeal I m ≤ RingHom.ker (parameterLocalizationMap I m hI) := by
  rw [parameterLocalizedIdeal, Ideal.map_le_iff_le_comap]
  intro a ha
  change parameterLocalizationMap I m hI (algebraMap A (Localization.AtPrime m) a) = 0
  rw [parameterLocalizationMap_algebraMap,
    (Ideal.Quotient.eq_zero_iff_mem).mpr ha, map_zero]

def parameterLocalQuotientForward :
    (Localization.AtPrime m ⧸ parameterLocalizedIdeal I m) →+*
      Localization.AtPrime (quotientParameterPrime I m hI) :=
  Ideal.Quotient.lift _ (parameterLocalizationMap I m hI)
    (fun x hx => (RingHom.mem_ker (f := parameterLocalizationMap I m hI) (r := x)).mp
      (parameterLocalizedIdeal_le_ker I m hI hx))

@[simp] theorem parameterLocalQuotientForward_mk (x : Localization.AtPrime m) :
    parameterLocalQuotientForward I m hI (Ideal.Quotient.mk _ x) =
      parameterLocalizationMap I m hI x := rfl

def parameterQuotientToLocalQuotient :
    (A ⧸ I) →+* (Localization.AtPrime m ⧸ parameterLocalizedIdeal I m) :=
  Ideal.Quotient.lift I
    ((Ideal.Quotient.mk (parameterLocalizedIdeal I m)).comp
      (algebraMap A (Localization.AtPrime m)))
    (fun _ ha => Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ ha))

@[simp] theorem parameterQuotientToLocalQuotient_mk (a : A) :
    parameterQuotientToLocalQuotient I m (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk (parameterLocalizedIdeal I m)
        (algebraMap A (Localization.AtPrime m) a) := rfl

theorem parameterQuotientToLocalQuotient_units
    (s : (quotientParameterPrime I m hI).primeCompl) :
    IsUnit (parameterQuotientToLocalQuotient I m (s : A ⧸ I)) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (s : A ⧸ I)
  have ham : a ∉ m := by
    intro ham
    apply s.property
    change (s : A ⧸ I) ∈ m.map (Ideal.Quotient.mk I)
    rw [← ha]
    exact Ideal.mem_map_of_mem _ ham
  rw [← ha, parameterQuotientToLocalQuotient_mk]
  exact (IsLocalization.map_units (Localization.AtPrime m) (⟨a, ham⟩ : m.primeCompl)).map
    (Ideal.Quotient.mk (parameterLocalizedIdeal I m))

def parameterLocalQuotientReverse :
    Localization.AtPrime (quotientParameterPrime I m hI) →+*
      (Localization.AtPrime m ⧸ parameterLocalizedIdeal I m) :=
  IsLocalization.lift (M := (quotientParameterPrime I m hI).primeCompl)
    (S := Localization.AtPrime (quotientParameterPrime I m hI))
    (parameterQuotientToLocalQuotient_units I m hI)

@[simp] theorem parameterLocalQuotientReverse_algebraMap (x : A ⧸ I) :
    parameterLocalQuotientReverse I m hI
      (algebraMap (A ⧸ I) (Localization.AtPrime (quotientParameterPrime I m hI)) x) =
      parameterQuotientToLocalQuotient I m x :=
  IsLocalization.lift_eq _ x

theorem parameterLocalQuotient_reverse_forward :
    (parameterLocalQuotientReverse I m hI).comp (parameterLocalQuotientForward I m hI) =
      RingHom.id (Localization.AtPrime m ⧸ parameterLocalizedIdeal I m) := by
  apply Ideal.Quotient.ringHom_ext
  apply IsLocalization.ringHom_ext m.primeCompl
  apply RingHom.ext
  intro a
  simp only [RingHom.comp_apply, RingHom.id_apply, parameterLocalQuotientForward_mk,
    parameterLocalizationMap_algebraMap, parameterLocalQuotientReverse_algebraMap,
    parameterQuotientToLocalQuotient_mk]

theorem parameterLocalQuotient_forward_reverse :
    (parameterLocalQuotientForward I m hI).comp (parameterLocalQuotientReverse I m hI) =
      RingHom.id (Localization.AtPrime (quotientParameterPrime I m hI)) := by
  apply IsLocalization.ringHom_ext (quotientParameterPrime I m hI).primeCompl
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro a
  simp only [RingHom.comp_apply, RingHom.id_apply, parameterLocalQuotientReverse_algebraMap,
    parameterQuotientToLocalQuotient_mk, parameterLocalQuotientForward_mk,
    parameterLocalizationMap_algebraMap]

def localizationQuotientParametersEquiv :
    (Localization.AtPrime m ⧸ parameterLocalizedIdeal I m) ≃+*
      Localization.AtPrime (quotientParameterPrime I m hI) where
  toFun := parameterLocalQuotientForward I m hI
  invFun := parameterLocalQuotientReverse I m hI
  left_inv x := RingHom.congr_fun (parameterLocalQuotient_reverse_forward I m hI) x
  right_inv x := RingHom.congr_fun (parameterLocalQuotient_forward_reverse I m hI) x
  map_mul' := (parameterLocalQuotientForward I m hI).map_mul
  map_add' := (parameterLocalQuotientForward I m hI).map_add

@[simp] theorem localizationQuotientParametersEquiv_mk_algebraMap (a : A) :
    localizationQuotientParametersEquiv I m hI
      (Ideal.Quotient.mk _ (algebraMap A (Localization.AtPrime m) a)) =
    algebraMap (A ⧸ I) (Localization.AtPrime (quotientParameterPrime I m hI))
      (Ideal.Quotient.mk I a) :=
  parameterLocalizationMap_algebraMap I m hI a

variable {B : Type*} [CommRing B]

local instance parameterEquivImage_isPrime (e : A ≃+* B) (P : Ideal A) [P.IsPrime] :
    (P.map e.toRingHom).IsPrime :=
  Ideal.map_isPrime_of_equiv e

theorem atPrimeImage_comap (e : A ≃+* B) (P : Ideal A) :
    P = (P.map e.toRingHom).comap e.toRingHom := by
  ext a
  change a ∈ P ↔ e a ∈ P.map e.toRingHom
  exact Ideal.apply_mem_of_equiv_iff.symm

def atPrimeEquivOfRingEquiv (e : A ≃+* B) (P : Ideal A) [P.IsPrime] :
    Localization.AtPrime P ≃+* Localization.AtPrime (P.map e.toRingHom) :=
  PiExponentJets.W22.primeLocalizationEquiv e P (P.map e.toRingHom)
    (atPrimeImage_comap e P)

@[simp] theorem atPrimeEquivOfRingEquiv_algebraMap
    (e : A ≃+* B) (P : Ideal A) [P.IsPrime] (a : A) :
    atPrimeEquivOfRingEquiv e P (algebraMap A (Localization.AtPrime P) a) =
      algebraMap B (Localization.AtPrime (P.map e.toRingHom)) (e a) :=
  IsLocalization.ringEquivOfRingEquiv_eq
    (PiExponentJets.W22.primeCompl_map_eq_of_comap e P (P.map e.toRingHom)
      (atPrimeImage_comap e P)) a

def localizationQuotientParametersEquivTrans (e : (A ⧸ I) ≃+* B) :
    (Localization.AtPrime m ⧸ parameterLocalizedIdeal I m) ≃+*
      Localization.AtPrime ((quotientParameterPrime I m hI).map e.toRingHom) :=
  (localizationQuotientParametersEquiv I m hI).trans
    (atPrimeEquivOfRingEquiv e (quotientParameterPrime I m hI))

@[simp] theorem localizationQuotientParametersEquivTrans_mk_algebraMap
    (e : (A ⧸ I) ≃+* B) (a : A) :
    localizationQuotientParametersEquivTrans I m hI e
      (Ideal.Quotient.mk _ (algebraMap A (Localization.AtPrime m) a)) =
      algebraMap B
        (Localization.AtPrime ((quotientParameterPrime I m hI).map e.toRingHom))
        (e (Ideal.Quotient.mk I a)) := by
  simp only [localizationQuotientParametersEquivTrans, RingEquiv.trans_apply,
    localizationQuotientParametersEquiv_mk_algebraMap, atPrimeEquivOfRingEquiv_algebraMap]

end PiExponentSiegel.W23

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_PrimeResidueAlgebraEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentJets.PolynomialLocalResidueResolution

variable {K R S : Type*} [CommRing K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S]
variable (e : R ≃ₐ[K] S) (P : Ideal R) [P.IsPrime]

instance primeResidueImage_isPrime : (P.map e.toRingHom).IsPrime :=
  Ideal.map_isPrime_of_equiv e

def primeResidueRingEquiv : P.ResidueField ≃+* (P.map e.toRingHom).ResidueField :=
  IsLocalRing.ResidueField.mapEquiv
    (PiExponentSiegel.W23.atPrimeEquivOfRingEquiv e.toRingEquiv P)

@[simp] theorem primeResidueRingEquiv_algebraMap (r : R) :
    primeResidueRingEquiv e P (algebraMap R P.ResidueField r) =
      algebraMap S (P.map e.toRingHom).ResidueField (e r) := by
  change IsLocalRing.residue (Localization.AtPrime (P.map e.toRingHom))
      (PiExponentSiegel.W23.atPrimeEquivOfRingEquiv e.toRingEquiv P
        (algebraMap R (Localization.AtPrime P) r)) =
    IsLocalRing.residue (Localization.AtPrime (P.map e.toRingHom))
      (algebraMap S (Localization.AtPrime (P.map e.toRingHom)) (e r))
  exact congrArg (IsLocalRing.residue (Localization.AtPrime (P.map e.toRingHom)))
    (PiExponentSiegel.W23.atPrimeEquivOfRingEquiv_algebraMap e.toRingEquiv P r)

def primeResidueAlgEquiv : P.ResidueField ≃ₐ[K] (P.map e.toRingHom).ResidueField where
  __ := primeResidueRingEquiv e P
  commutes' a := by
    change primeResidueRingEquiv e P (algebraMap K P.ResidueField a) = _
    rw [IsScalarTower.algebraMap_apply K R P.ResidueField,
      primeResidueRingEquiv_algebraMap, e.commutes]
    exact (IsScalarTower.algebraMap_apply K S (P.map e.toRingHom).ResidueField a).symm

@[simp] theorem primeResidueAlgEquiv_algebraMap (r : R) :
    primeResidueAlgEquiv e P (algebraMap R P.ResidueField r) =
      algebraMap S (P.map e.toRingHom).ResidueField (e r) :=
  primeResidueRingEquiv_algebraMap e P r

end PiExponentJets.PolynomialLocalResidueResolution

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_CoordinateFiniteSlice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CoordinateFiniteSlice

open PiExponentJets.PolynomialLocalResidueResolution

variable {K ι : Type*} [Field K]

def coordinateEquiv (A : Finset ι) :
    Fin A.card ⊕ {i // i ∉ A} ≃ ι := by
  classical
  exact (Equiv.sumCongr A.equivFin.symm (Equiv.refl _)).trans (Equiv.sumCompl (· ∈ A))

@[simp] theorem coordinateEquiv_inl (A : Finset ι) (i : Fin A.card) :
    coordinateEquiv A (Sum.inl i) = (A.equivFin.symm i).val := rfl

@[simp] theorem coordinateEquiv_inr (A : Finset ι) (i : {i // i ∉ A}) :
    coordinateEquiv A (Sum.inr i) = i.val := rfl

def coordinateRenaming (A : Finset ι) :
    MvPolynomial ι K ≃ₐ[K] MvPolynomial (Fin A.card ⊕ {i // i ∉ A}) K :=
  MvPolynomial.renameEquiv K (coordinateEquiv A).symm

@[simp] theorem coordinateRenaming_X_inl (A : Finset ι) (i : Fin A.card) :
    coordinateRenaming (K := K) A (MvPolynomial.X (A.equivFin.symm i).val) =
      MvPolynomial.X (Sum.inl i) := by
  change MvPolynomial.rename (coordinateEquiv A).symm
    (MvPolynomial.X (coordinateEquiv A (Sum.inl i))) = _
  rw [MvPolynomial.rename_X, Equiv.symm_apply_apply]

@[simp] theorem coordinateRenaming_X_inr (A : Finset ι) (i : {i // i ∉ A}) :
    coordinateRenaming (K := K) A (MvPolynomial.X i.val) =
      MvPolynomial.X (Sum.inr i) := by
  change MvPolynomial.rename (coordinateEquiv A).symm
    (MvPolynomial.X (coordinateEquiv A (Sum.inr i))) = _
  rw [MvPolynomial.rename_X, Equiv.symm_apply_apply]

abbrev splitPrime (Q : Ideal (MvPolynomial ι K)) (A : Finset ι) :
    Ideal (MvPolynomial (Fin A.card ⊕ {i // i ∉ A}) K) :=
  Q.map (coordinateRenaming (K := K) A).toRingHom

instance splitPrime_isPrime (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι) :
    (splitPrime Q A).IsPrime := Ideal.map_isPrime_of_equiv (coordinateRenaming A)

def residueEquiv (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι) :
    Q.ResidueField ≃ₐ[K] (splitPrime Q A).ResidueField :=
  primeResidueAlgEquiv (coordinateRenaming A) Q

@[simp] theorem residueEquiv_coordinate_inl
    (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι) (i : Fin A.card) :
    residueEquiv Q A
      (algebraMap (MvPolynomial ι K) Q.ResidueField (MvPolynomial.X (A.equivFin.symm i).val)) =
    algebraMap (MvPolynomial (Fin A.card ⊕ {i // i ∉ A}) K) (splitPrime Q A).ResidueField (MvPolynomial.X (Sum.inl i)) := by
  simpa only [residueEquiv, splitPrime, coordinateRenaming_X_inl] using
    primeResidueAlgEquiv_algebraMap (coordinateRenaming (K := K) A) Q
      (MvPolynomial.X (A.equivFin.symm i).val)

@[simp] theorem residueEquiv_coordinate_inr
    (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι) (i : {i // i ∉ A}) :
    residueEquiv Q A
      (algebraMap (MvPolynomial ι K) Q.ResidueField (MvPolynomial.X i.val)) =
    algebraMap (MvPolynomial (Fin A.card ⊕ {i // i ∉ A}) K) (splitPrime Q A).ResidueField (MvPolynomial.X (Sum.inr i)) := by
  simpa only [residueEquiv, splitPrime, coordinateRenaming_X_inr] using
    primeResidueAlgEquiv_algebraMap (coordinateRenaming (K := K) A) Q (MvPolynomial.X i.val)

def residueCoordinates (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (i : ι) : Q.ResidueField :=
  algebraMap (MvPolynomial ι K) Q.ResidueField (MvPolynomial.X i)

def slicePoint (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι)
    (i : Fin A.card) : Q.ResidueField := residueCoordinates Q (A.equivFin.symm i)

@[simp] theorem enumeratedSliceMap_X_inl
    (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι) (i : Fin A.card) :
    WeightedSliceDegree.enumeratedSliceMap (C := K) A (residueCoordinates Q)
      (MvPolynomial.X (A.equivFin.symm i).val) = MvPolynomial.X i := by
  simp [WeightedSliceDegree.enumeratedSliceMap,
    WeightedSliceDegree.sliceMap_X_mem (C := K) A (residueCoordinates Q)
      (A.equivFin.symm i).val (A.equivFin.symm i).property]

@[simp] theorem enumeratedSliceMap_X_inr
    (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι) (i : {i // i ∉ A}) :
    WeightedSliceDegree.enumeratedSliceMap (C := K) A (residueCoordinates Q)
      (MvPolynomial.X i.val) = MvPolynomial.C (residueCoordinates Q i.val) := by
  simp [WeightedSliceDegree.enumeratedSliceMap,
    WeightedSliceDegree.sliceMap_X_notMem (C := K) A (residueCoordinates Q) i.val i.property]

end PiExponent.CoordinateFiniteSlice

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_PolynomialCoefficientLocalization
attribute [-instance] _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentSiegelAux.W09

variable (K : Type*) [Field K] (α β : Type*)

abbrev SplitPolynomial := MvPolynomial (α ⊕ β) K
abbrev CoefficientPolynomial := MvPolynomial β K
abbrev CoefficientFractionField := FractionRing (CoefficientPolynomial K β)
abbrev FractionCoefficientPolynomial := MvPolynomial α (CoefficientFractionField K β)

def coefficientDenominators : Submonoid (SplitPolynomial K α β) :=
  (nonZeroDivisors (CoefficientPolynomial K β)).map
    (MvPolynomial.rename (Sum.inr : β → α ⊕ β)).toRingHom

abbrev PolynomialCoefficientLocalization := Localization (coefficientDenominators K α β)

@[simp] theorem mem_coefficientDenominators (p : SplitPolynomial K α β) :
    p ∈ coefficientDenominators K α β ↔
      ∃ f : CoefficientPolynomial K β, f ≠ 0 ∧ MvPolynomial.rename Sum.inr f = p := by
  simp [coefficientDenominators, Submonoid.mem_map, mem_nonZeroDivisors_iff_ne_zero]

@[simp] theorem sumAlgEquiv_coefficientRename (f : CoefficientPolynomial K β) :
    MvPolynomial.sumAlgEquiv K α β (MvPolynomial.rename Sum.inr f) = MvPolynomial.C f := by
  exact congrArg (fun g : CoefficientPolynomial K β →ₐ[K]
      MvPolynomial α (CoefficientPolynomial K β) => g f)
    (MvPolynomial.sumAlgEquiv_comp_rename_inr K α β)

theorem sumAlgEquiv_coefficientDenominators :
    (coefficientDenominators K α β).map (MvPolynomial.sumAlgEquiv K α β) =
      (nonZeroDivisors (CoefficientPolynomial K β)).map (MvPolynomial.C (σ := α)) := by
  ext y
  constructor
  · rintro ⟨x, ⟨f, hf, rfl⟩, rfl⟩
    exact ⟨f, hf, (sumAlgEquiv_coefficientRename K α β f).symm⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨MvPolynomial.rename Sum.inr f, ⟨f, hf, rfl⟩,
      sumAlgEquiv_coefficientRename K α β f⟩

attribute [local instance] MvPolynomial.algebraMvPolynomial

local instance coefficientPolynomial_scalarTower :
    IsScalarTower K (MvPolynomial α (CoefficientPolynomial K β))
      (FractionCoefficientPolynomial K α β) :=
  IsScalarTower.of_algebraMap_eq (fun c => by
    change MvPolynomial.C (algebraMap K (CoefficientFractionField K β) c) =
      MvPolynomial.map
        (algebraMap (CoefficientPolynomial K β) (CoefficientFractionField K β))
        (MvPolynomial.C (MvPolynomial.C c))
    rw [MvPolynomial.map_C]
    exact congrArg (MvPolynomial.C (σ := α))
      (IsScalarTower.algebraMap_apply K (CoefficientPolynomial K β)
        (CoefficientFractionField K β) c))

end PiExponentSiegelAux.W09

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_RationalResidueCoefficientField
attribute [-instance] _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentJets.PolynomialLocalResidueResolution
open scoped IntermediateField.algebraAdjoinAdjoin

variable {K R ι : Type*} [Field K] [CommRing R] [IsLocalRing R] [Algebra K R]
variable (x : ι → R)
variable (hx : AlgebraicIndependent K (fun i => IsLocalRing.residue R (x i)))

def rationalResidueEquiv : FractionRing (MvPolynomial ι K) ≃ₐ[K]
    IntermediateField.adjoin K (Set.range (fun i => IsLocalRing.residue R (x i))) :=
  IsFractionRing.algEquivOfAlgEquiv hx.aevalEquiv

@[simp] theorem rationalResidueEquiv_polynomial (f : MvPolynomial ι K) :
    ((rationalResidueEquiv x hx
      (algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K)) f)) :
        IsLocalRing.ResidueField R) =
      MvPolynomial.aeval (fun i => IsLocalRing.residue R (x i)) f := by
  rw [rationalResidueEquiv, IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  rfl

end PiExponentJets.PolynomialLocalResidueResolution

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_SplitCoordinateClosedPoint
attribute [-instance] _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentJets.PolynomialLocalResidueResolution
open scoped IntermediateField

variable (K α β : Type*) [Field K]
variable (Q : Ideal (MvPolynomial (α ⊕ β) K)) [Q.IsPrime]

abbrev SplitLocalRing := Localization.AtPrime Q
abbrev SplitResidue := Q.ResidueField
abbrev SplitCoefficientField := FractionRing (MvPolynomial β K)

def splitLocalBeta (j : β) : SplitLocalRing K α β Q :=
  algebraMap (MvPolynomial (α ⊕ β) K) (SplitLocalRing K α β Q) (MvPolynomial.X (Sum.inr j))

def splitResidueBeta (j : β) : SplitResidue K α β Q :=
  IsLocalRing.residue (SplitLocalRing K α β Q) (splitLocalBeta K α β Q j)

variable (hB : IsTranscendenceBasis K (splitResidueBeta K α β Q))

@[reducible] def splitCoefficientResidueAlgebra :
    Algebra (SplitCoefficientField K β) (SplitResidue K α β Q) :=
  (((IntermediateField.adjoin K (Set.range (splitResidueBeta K α β Q))).val.toRingHom).comp
    (rationalResidueEquiv (splitLocalBeta K α β Q) hB.1).toRingHom).toAlgebra

end PiExponentJets.PolynomialLocalResidueResolution

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_CoordinateSliceLength
attribute [-instance] _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.CoordinateSliceLength

open PiExponentJets.PolynomialLocalResidueResolution

abbrev localizedLength {R : Type*} [CommRing R] (P : Ideal R) [P.IsPrime] (I : Ideal R) : ℕ∞ :=
  Module.length (Localization.AtPrime P)
    (Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P)))

variable (K α β : Type*) [Field K]
variable (Q : Ideal (MvPolynomial (α ⊕ β) K)) [Q.IsPrime]
variable (hB : IsTranscendenceBasis K (splitResidueBeta K α β Q))

def residueSlice :
    MvPolynomial (α ⊕ β) K →+* MvPolynomial α (SplitResidue K α β Q) :=
  (MvPolynomial.aeval (fun i : α ⊕ β => match i with
    | Sum.inl i => MvPolynomial.X i
    | Sum.inr j => MvPolynomial.C (splitResidueBeta K α β Q j))).toRingHom

end PiExponent.CoordinateSliceLength

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_CoordinateSliceComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CoordinateSliceComparison

open PiExponentJets.PolynomialLocalResidueResolution
open CoordinateFiniteSlice

variable {K ι : Type*} [Field K] [Fintype ι]

abbrev primeLength {R : Type*} [CommRing R] (Q : Ideal R) [Q.IsPrime] (I : Ideal R) : ℕ∞ :=
  Module.length (Localization.AtPrime Q)
    (Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q)))

end PiExponent.CoordinateSliceComparison

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Statement
attribute [-instance] _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent

def GoodRationalApproximations (x ν : ℝ) : Set ℚ :=
  {r | 2 ≤ r.den ∧ 0 < |x - (r : ℝ)| ∧ |x - (r : ℝ)| < (r.den : ℝ) ^ (-ν)}

def ApproximationExponents (x : ℝ) : Set ℝ :=
  {ν | 0 < ν ∧ (GoodRationalApproximations x ν).Infinite}

end PiExponent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_DeterminantContradiction
attribute [-instance] _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace PiExponent.DeterminantContradiction

noncomputable def collisionConstant : ℝ := Real.log 2 / 4

end PiExponent.DeterminantContradiction

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_GeneratorsSectionCover
attribute [-instance] _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeneratorsSectionCover
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

abbrev schemeFree (X : Scheme.{0}) (ι : Type) : X.Modules :=
  SheafOfModules.free ι

end
end PiExponent.GeneratorsSectionCover

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_FiniteZeroEuler
attribute [-instance] _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open AlgebraicGeometry PiExponentSeshadri.Geometry

namespace PiExponent.FiniteZeroEuler

theorem finrank_eq_sum_localizations
    (B : Type*) [CommRing B] [IsArtinianRing B]
    (F : Type*) [Field F] [Algebra F B] [Module.Finite F B]
    [Fintype (MaximalSpectrum B)] :
    Module.finrank F B = ∑ m : MaximalSpectrum B,
      Module.finrank F (Localization.AtPrime m.asIdeal) := by
  let : ∀ m : MaximalSpectrum B, Module.Finite F (Localization.AtPrime m.asIdeal) :=
    fun m => Module.Finite.of_surjective (IsScalarTower.toAlgHom F B
      (Localization.AtPrime m.asIdeal)).toLinearMap
      (IsArtinianRing.localization_surjective m.asIdeal.primeCompl _)
  have e := (MaximalSpectrum.toPiLocalizationEquiv B).restrictScalars F
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]

end PiExponent.FiniteZeroEuler

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CartierPowerFrames
attribute [-instance] _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CartierPowerFrames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

lemma frame_section {C : Type*} [Category C] {A B D : C}
    (u : A ≅ B) (s : A ⟶ D) (e : D ≅ B) :
    s ≫ e.hom = u.hom ≫ ((u.inv ≫ s) ≫ e.hom) := by
  simp

lemma framed_multiply {C : Type*} [Category C] {A B D P Q T O : C}
    (g : O ⟶ A) (k : A ⟶ B) (m : B ⟶ D) (r : B ⟶ P) (r' : D ⟶ Q)
    (e : P ⟶ T) (e' : Q ⟶ T) (u : T ⟶ O) (a : O ⟶ O)
    (p : P ⟶ Q) (b : T ⟶ T)
    (hn : m ≫ r' = r ≫ p) (ht : p ≫ e' = e ≫ b) (hs : b ≫ u = u ≫ a) :
    g ≫ (k ≫ m) ≫ (r' ≫ e' ≫ u) = (g ≫ k ≫ r ≫ e ≫ u) ≫ a := by
  simp only [Category.assoc]
  rw [← Category.assoc m r', hn]
  simp only [Category.assoc]
  rw [← Category.assoc p e', ht]
  simp only [Category.assoc]
  rw [hs]

end
end PiExponent.CartierPowerFrames

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveEffectiveTwist
attribute [-instance] _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CurveDegree
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} [IsIntegral X]

theorem id_eq_zero_of_iso {C : Type*} [Category C] [Preadditive C]
    {A B : C} (e : A ≅ B) (h : 𝟙 A = 0) : 𝟙 B = 0 := by
  have he := congrArg (fun f : A ⟶ A => e.inv ≫ f ≫ e.hom) h
  simpa only [Category.id_comp, comp_zero, zero_comp, Iso.inv_hom_id] using he

theorem generators_isZero {T : TopCat.{0}} (R : Sheaf (Opens.grothendieckTopology T) RingCat.{0})
    (M : SheafOfModules.{0} R) (G : M.GeneratingSections)
    (h : ∀ s : SheafOfModules.unit.{0} R ⟶ M, s = 0) : IsZero M := by
  have hπ : G.π = 0 := by
    apply M.freeHomEquiv.injective
    funext i
    apply M.unitHomEquiv.symm.injective
    rw [SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply,
      SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
    simpa only [comp_zero] using h (SheafOfModules.ιFree i ≫ G.π)
  let : Epi G.π := G.epi
  exact IsZero.of_epi_eq_zero G.π hπ

end
end PiExponent.CurveDegree

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveSerreTransfer
attribute [-instance] _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ClosedImmersionSerreTransfer
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open PiExponentSeshadri.Geometry
variable {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f]
local instance instHasExtModules_solutions_3 : HasExt.{1} Y.Modules := HasExt.standard _

end
end PiExponent.ClosedImmersionSerreTransfer

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_SectionZeroStalk
attribute [-instance] _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry

namespace PiExponent.SectionZeroStalk


theorem stalkMap_ker_eq_map_affine_ker
    {X Y : Scheme} (f : Y ⟶ X) [IsClosedImmersion f]
    (U : X.Opens) (hU : IsAffineOpen U) (y : Y) (hy : f y ∈ U) :
    RingHom.ker (f.stalkMap y).hom =
      (RingHom.ker (f.app U).hom).map (X.presheaf.germ U (f y) hy).hom := by
  let V := f ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage f
  let q := hU.primeIdealOf ⟨f y, hy⟩
  let p := hV.primeIdealOf ⟨y, hy⟩
  let φ := (f.app U).hom
  let := X.presheaf.algebra_section_stalk ⟨f y, hy⟩
  let := Y.presheaf.algebra_section_stalk (⟨y, hy⟩ : V)
  let := hU.isLocalization_stalk ⟨f y, hy⟩
  let := hV.isLocalization_stalk ⟨y, hy⟩
  have hqp : p.asIdeal.comap φ = q.asIdeal := by
    have h := IsAffineOpen.comap_primeIdealOf_appLE U hU V hV le_rfl hy (f := f)
    simpa only [V, Scheme.Hom.appLE_eq_app, PrimeSpectrum.comap_asIdeal, φ, p, q] using congrArg PrimeSpectrum.asIdeal h
  have hmon : q.asIdeal.primeCompl.map φ = p.asIdeal.primeCompl := by
    simpa only [hqp] using p.asIdeal.map_primeCompl_comap_of_surjective φ (f.app_surjective U hU)
  have hf : (f.stalkMap y).hom =
      (IsLocalization.map (Y.presheaf.stalk y) φ
        (hmon.symm ▸ q.asIdeal.primeCompl.le_comap_map) : X.presheaf.stalk (f y) →+* Y.presheaf.stalk y) := by
    apply IsLocalization.ringHom_ext q.asIdeal.primeCompl
    ext a
    rw [RingHom.comp_apply, RingHom.comp_apply, IsLocalization.map_eq]
    exact Scheme.Hom.germ_stalkMap_apply f U y hy a
  rw [hf, IsLocalization.ker_map (Y.presheaf.stalk y) φ hmon]
  rfl

variable {X : Scheme.{0}}

theorem intrinsic_length_eq_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) : Module.length A A = Module.length B B := by
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  exact Order.krullDim_eq_of_orderIso e.idealComapOrderIso.symm

end PiExponent.SectionZeroStalk

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_CompactJetIdeal
attribute [-instance] _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace PiExponent.CompactJetIdeal

universe u
variable {U X S : Scheme.{u}}

theorem restrict_eq_top_of_disjoint (I : X.IdealSheafData)
    {V : Scheme.{u}} (f : V ⟶ X)
    (havoid : ∀ v, f v ∉ I.support) : I.comap f = ⊤ := by
  apply (Scheme.IdealSheafData.support_eq_bot_iff (I.comap f)).mp
  rw [Scheme.IdealSheafData.support_comap]
  ext v
  exact ⟨fun h => (havoid v h).elim, False.elim⟩

end PiExponent.CompactJetIdeal
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_AffineJetSupport
attribute [-instance] _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AffineJetSupport
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry
variable {X Y : Scheme}

def restrictionSectionsIso (M : X.Modules) (U : X.Opens) :
    Γ(M.restrict U.ι, ⊤) ≅ Γ(M,U) :=
  M.restrictAppIso U.ι ⊤ ≪≫ M.presheaf.mapIso (eqToIso U.ι_image_top.symm).op

def sectionsIso {M N : X.Modules} (e : M ≅ N) (U : X.Opens) : Γ(M,U) ≅ Γ(N,U) :=
  ((Scheme.Modules.toPresheaf X).mapIso e).app (op U)

end PiExponent.AffineJetSupport
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_AffineJetQuotient
attribute [-instance] _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AffineJetQuotient
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry
open PiExponent.AffineJetSupport
variable {X : Scheme}

@[reassoc] theorem restrictionSectionsIso_natural {M N : X.Modules}
    (f : M ⟶ N) (U : X.Opens) :
    ((Scheme.Modules.restrictFunctor U.ι).map f).app ⊤ ≫
        (restrictionSectionsIso N U).hom =
      (restrictionSectionsIso M U).hom ≫ f.app U := by
  change f.app (U.ι ''ᵁ ⊤) ≫ N.presheaf.map (eqToHom U.ι_image_top.symm).op =
    M.presheaf.map (eqToHom U.ι_image_top.symm).op ≫ f.app U
  exact (f.mapPresheaf.naturality (eqToHom U.ι_image_top.symm).op).symm

end PiExponent.AffineJetQuotient
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_CommutingTaylor
attribute [-instance] _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CommutingTaylor

open Finset Nat
variable {R : Type*} [CommRing R] [Algebra ℚ R]

def iter (D : Derivation ℚ R R) (n : ℕ) : R →ₗ[ℚ] R := D.toLinearMap ^ n

@[simp] theorem iter_zero (D : Derivation ℚ R R) (a : R) : iter D 0 a = a := rfl
@[simp] theorem iter_succ (D : Derivation ℚ R R) (n : ℕ) (a : R) :
    iter D (n+1) a = D (iter D n a) := by
  change (D.toLinearMap ^ (n + 1)) a = D ((D.toLinearMap ^ n) a)
  calc
    (D.toLinearMap ^ (n + 1)) a = (D.toLinearMap * D.toLinearMap ^ n) a :=
      congrArg (fun f : Module.End ℚ R => f a) (_root_.pow_succ' D.toLinearMap n)
    _ = D.toLinearMap ((D.toLinearMap ^ n) a) :=
      Module.End.mul_apply D.toLinearMap (D.toLinearMap ^ n) a
    _ = D ((D.toLinearMap ^ n) a) :=
      congrFun (Derivation.coeFn_coe D) ((D.toLinearMap ^ n) a)

theorem iter_mul (D : Derivation ℚ R R) (n : ℕ) (a b : R) :
    iter D n (a*b) = ∑ ij ∈ antidiagonal n,
      n.choose ij.1 • (iter D ij.1 a * iter D ij.2 b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_antidiagonal_choose_succ_nsmul
      (fun i j => iter D i a * iter D j b) n]
    simp only [iter_succ, ih, map_sum, map_nsmul, Derivation.leibniz,
      smul_eq_mul, nsmul_add, Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro ij hij
    rw [n.choose_symm_of_eq_add (mem_antidiagonal.mp hij).symm]
    rw [mul_comm]

theorem factorial_normalize (i j : ℕ) :
    (1 / ((i+j).factorial : ℚ)) * ((i+j).choose i : ℚ) =
      (1 / (i.factorial : ℚ)) * (1 / (j.factorial : ℚ)) := by
  have h : (((i+j).choose i : ℚ) * (i.factorial : ℚ) * (j.factorial : ℚ)) =
      ((i+j).factorial : ℚ) := by
    exact_mod_cast (by
      simpa using Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right i j) :
        (i+j).choose i * i.factorial * j.factorial = (i+j).factorial)
  have hi : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hj : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hn : ((i+j).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (i+j)
  field_simp
  nlinarith [h]

def taylorSeries (D : Derivation ℚ R R) (a : R) : PowerSeries R :=
  PowerSeries.mk fun n => (1 / (n.factorial : ℚ)) • iter D n a

@[simp] theorem coeff_taylorSeries (D : Derivation ℚ R R) (a : R) (n : ℕ) :
    PowerSeries.coeff n (taylorSeries D a) = (1 / (n.factorial : ℚ)) • iter D n a := by
  exact PowerSeries.coeff_mk n _

theorem taylorSeries_mul (D : Derivation ℚ R R) (a b : R) :
    taylorSeries D (a*b) = taylorSeries D a * taylorSeries D b := by
  ext n
  rw [PowerSeries.coeff_mul, coeff_taylorSeries, iter_mul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  have hn : ij.1 + ij.2 = n := mem_antidiagonal.mp hij
  rw [coeff_taylorSeries, coeff_taylorSeries]
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, smul_mul_smul_comm]
  rw [← hn, factorial_normalize]

def taylorHom (D : Derivation ℚ R R) : R →+* PowerSeries R where
  toFun := taylorSeries D
  map_zero' := by ext n; simp [taylorSeries]
  map_one' := by
    ext n
    cases n with
    | zero => simp [taylorSeries]
    | succ n =>
      have h : iter D (n+1) (1:R) = 0 := by
        induction n with
        | zero => simp
        | succ n ih => simp [ih]
      simp [taylorSeries, h]
  map_add' a b := by ext n; simp [taylorSeries, smul_add]
  map_mul' := taylorSeries_mul D

@[simp] theorem coeff_taylorHom (D : Derivation ℚ R R) (a : R) (n : ℕ) :
    PowerSeries.coeff n (taylorHom D a) = (1 / (n.factorial : ℚ)) • iter D n a := by
  exact coeff_taylorSeries D a n

@[simp] theorem constantCoeff_taylorHom (D : Derivation ℚ R R) (a : R) :
    PowerSeries.constantCoeff (taylorHom D a) = a := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_taylorHom]
  simp

def mixedIter : (m : ℕ) → (Fin m → Derivation ℚ R R) → (Fin m →₀ ℕ) → R →ₗ[ℚ] R
  | 0, _, _ => LinearMap.id
  | m+1, D, α => (mixedIter m (fun i => D i.succ) α.tail).comp (iter (D 0) (α 0))

def taylorHomFin : (m : ℕ) → (Fin m → Derivation ℚ R R) → R →+* MvPowerSeries (Fin m) R
  | 0, _ => MvPowerSeries.C
  | m+1, D => (MvPowerSeries.finSuccEquiv R m).symm.toRingHom.comp
      ((PowerSeries.map (taylorHomFin m (fun i => D i.succ))).comp (taylorHom (D 0)))

theorem coeff_taylorHomFin (m : ℕ) (D : Fin m → Derivation ℚ R R)
    (α : Fin m →₀ ℕ) (a : R) :
    MvPowerSeries.coeff α (taylorHomFin m D a) =
      (∏ i, (1 / ((α i).factorial : ℚ))) • mixedIter m D α a := by
  induction m generalizing a with
  | zero =>
    have hα : α = 0 := Subsingleton.elim _ _
    simp [taylorHomFin, mixedIter, hα]
  | succ m ih =>
    have hcoeff := MvPowerSeries.coeff_coeff_finSuccEquiv
      ((MvPowerSeries.finSuccEquiv R m).symm
        (PowerSeries.map (taylorHomFin m (fun i => D i.succ)) (taylorHom (D 0) a)))
      (k := α 0) (x := α.tail)
    simp only [AlgEquiv.apply_symm_apply] at hcoeff
    rw [show α.tail.cons (α 0) = α by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp] at hcoeff
    rw [taylorHomFin, RingHom.comp_apply, RingHom.comp_apply]
    change MvPowerSeries.coeff α ((MvPowerSeries.finSuccEquiv R m).symm
      (PowerSeries.map (taylorHomFin m (fun i => D i.succ)) (taylorHom (D 0) a))) = _
    rw [← hcoeff, PowerSeries.coeff_map, coeff_taylorHom, ih]
    simp only [map_smul, mixedIter, LinearMap.comp_apply, Fin.prod_univ_succ,
      Finsupp.tail_apply, smul_smul]
    rw [mul_comm]

@[simp] theorem mixedIter_zero (m : ℕ) (D : Fin m → Derivation ℚ R R) (a : R) :
    mixedIter m D 0 a = a := by
  induction m generalizing a with
  | zero => rfl
  | succ m ih =>
    have ht : (0 : Fin (m+1) →₀ ℕ).tail = 0 := by ext i; rfl
    simp [mixedIter, ht, ih]

@[simp] theorem mixedIter_single (m : ℕ) (D : Fin m → Derivation ℚ R R)
    (i : Fin m) (a : R) : mixedIter m D (Finsupp.single i 1) a = D i a := by
  induction m generalizing a with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [← Finsupp.cons_zero_eq_single_zero]
      simp [mixedIter, iter]
    · rw [← Finsupp.cons_zero_single_eq_single_succ]
      simp [mixedIter, ih]

@[simp] theorem coeff_zero_taylorHomFin (m : ℕ) (D : Fin m → Derivation ℚ R R) (a : R) :
    MvPowerSeries.coeff 0 (taylorHomFin m D a) = a := by
  simp [coeff_taylorHomFin]

@[simp] theorem coeff_single_taylorHomFin (m : ℕ) (D : Fin m → Derivation ℚ R R)
    (i : Fin m) (a : R) :
    MvPowerSeries.coeff (Finsupp.single i 1) (taylorHomFin m D a) = D i a := by
  rw [coeff_taylorHomFin, mixedIter_single]
  have h : (∏ j : Fin m, (1 / ((Finsupp.single i 1 j).factorial : ℚ))) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    by_cases he : i = j <;> simp [he]
  rw [h, one_smul]

def residueTaylorFin {K : Type*} [CommRing K]
    (m : ℕ) (D : Fin m → Derivation ℚ R R) (ρ : R →+* K) :
    R →+* MvPowerSeries (Fin m) K :=
  (MvPowerSeries.map ρ).comp (taylorHomFin m D)

@[simp] theorem coeff_zero_residueTaylorFin {K : Type*} [CommRing K]
    (m : ℕ) (D : Fin m → Derivation ℚ R R) (ρ : R →+* K) (a : R) :
    MvPowerSeries.coeff 0 (residueTaylorFin m D ρ a) = ρ a := by
  simp [residueTaylorFin]

@[simp] theorem coeff_single_residueTaylorFin {K : Type*} [CommRing K]
    (m : ℕ) (D : Fin m → Derivation ℚ R R) (ρ : R →+* K) (i : Fin m) (a : R) :
    MvPowerSeries.coeff (Finsupp.single i 1) (residueTaylorFin m D ρ a) = ρ (D i a) := by
  simp [residueTaylorFin]

@[simp] theorem constantCoeff_residueTaylorFin {K : Type*} [CommRing K]
    (m : ℕ) (D : Fin m → Derivation ℚ R R) (ρ : R →+* K) (a : R) :
    MvPowerSeries.constantCoeff (residueTaylorFin m D ρ a) = ρ a := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact coeff_zero_residueTaylorFin m D ρ a

end PiExponent.CommutingTaylor

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_OrdinaryAuxiliaryJet
attribute [-instance] _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Filter Topology
namespace PiExponent.OrdinaryAuxiliaryJet

def formalJet {n : ℕ} (c : Fin n → ℂ) :
    MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPowerSeries (Fin n) ℂ :=
  MvPolynomial.aeval (fun i => MvPowerSeries.C (c i) + MvPowerSeries.X i)

end PiExponent.OrdinaryAuxiliaryJet
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_TransverseMultiplicity
attribute [-instance] _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentApprox.TransverseMultiplicity

noncomputable section

open MvPowerSeries

variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]

def localizedTaylorMap {A L : Type*} [CommRing A] [CommRing L] [Algebra A L]
    (M : Submonoid A) [IsLocalization M L]
    (tau : A →+* MvPowerSeries σ K) (rho : L →+* K)
    (hconstant : ∀ a, constantCoeff (tau a) = rho (algebraMap A L a)) :
    L →+* MvPowerSeries σ K :=
  IsLocalization.lift (M := M) (S := L) (g := tau) (fun s : M => by
    apply MvPowerSeries.isUnit_iff_constantCoeff.mpr
    rw [hconstant]
    exact (IsLocalization.map_units L s).map rho)

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem localizedTaylorMap_algebraMap {A L : Type*}
    [CommRing A] [CommRing L] [Algebra A L]
    (M : Submonoid A) [IsLocalization M L]
    (tau : A →+* MvPowerSeries σ K) (rho : L →+* K)
    (hconstant : ∀ a, constantCoeff (tau a) = rho (algebraMap A L a)) (a : A) :
    localizedTaylorMap M tau rho hconstant (algebraMap A L a) = tau a := by
  simp only [localizedTaylorMap, IsLocalization.lift_eq]

omit [Fintype σ] [DecidableEq σ] in
theorem localizedTaylorMap_constant {A L : Type*}
    [CommRing A] [CommRing L] [Algebra A L]
    (M : Submonoid A) [IsLocalization M L]
    (tau : A →+* MvPowerSeries σ K) (rho : L →+* K)
    (hconstant : ∀ a, constantCoeff (tau a) = rho (algebraMap A L a)) :
    (constantCoeff : MvPowerSeries σ K →+* K).comp
      (localizedTaylorMap M tau rho hconstant) = rho := by
  apply IsLocalization.ringHom_ext M
  ext a
  simp only [RingHom.comp_apply, localizedTaylorMap_algebraMap]
  exact hconstant a

end
end PiExponentApprox.TransverseMultiplicity

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_PolynomialPoleBound
attribute [-instance] _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.PolynomialPoleBound

variable {K C σ : Type*} [Field K] [CommRing C] [Algebra C K]

theorem valuation_prod (v : AddValuation K (WithTop ℝ))
    (s : Finset σ) (f : σ → K) : v (∏ i ∈ s, f i) = ∑ i ∈ s, v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, ih]

end PiExponent.PolynomialPoleBound

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_CoordinateContactBound
attribute [-instance] _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.CoordinateContactBound

open WeightedSliceDegree

@[simp] theorem ordinary_formalJet_X_sub_C {n : ℕ} (c : Fin n → ℂ) (i : Fin n) :
    OrdinaryAuxiliaryJet.formalJet c (MvPolynomial.X i - MvPolynomial.C (c i)) =
      MvPowerSeries.X i := by
  simp only [OrdinaryAuxiliaryJet.formalJet, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
  change MvPowerSeries.C (c i) + MvPowerSeries.X i - MvPowerSeries.C (c i) = MvPowerSeries.X i
  abel

end PiExponent.CoordinateContactBound

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_IdealPowerAnnihilator
attribute [-instance] _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.IdealModule
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem hom_ext_affine {M N : X.Modules} {f g : M ⟶ N}
    (h : ∀ U : X.affineOpens, f.app U.1 = g.app U.1) : f = g := by
  let F := SheafOfModules.toSheaf X.ringCatSheaf
  apply F.map_injective
  apply Sheaf.hom_ext
  apply TopCat.Sheaf.hom_ext _ _ (show Opens.IsBasis
    (Set.range (fun U : X.affineOpens => U.1)) by simpa using X.isBasis_affineOpens)
  intro U
  ext x
  exact ConcreteCategory.congr_hom (h U) x

end
end PiExponentSeshadri.IdealModule

end OAI
end


