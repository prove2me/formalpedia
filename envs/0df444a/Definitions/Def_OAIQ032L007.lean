-- Prove2me | Definitions.Def_OAIQ032L007
-- name    : OAIQ032L007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T19:44:23.216479+00:00
-- url     : https://prove2.me/theorems/ba0870f7-b636-476c-9db6-49bdab4a7d7a
-- title:
--   Definitions bundle OAIQ032L007 of the split of OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 91 declarations of OpenAI's Lean: 42 definitions and 49 theorems. The definitions and types are `OAI.Lech.ProductSourceCover.Chart`, `OAI.Lech.ProductSourceCover.RootPositions`, `OAI.Lech.ProductSourceCover.chartOrder`, `OAI.Lech.ProductSourceCover.endpointDecEq`, `OAI.Lech.ProductSourceCover.endpointRingDecEq`, `OAI.Lech.ProductSourceCover.endpointVertex`, `OAI.Lech.ProductSourceCover.gridSourceDecEq`, `OAI.Lech.ProductSourceCover.highThreshold`, `OAI.Lech.ProductSourceCover.levelTwist`, `OAI.Lech.ProductSourceCover.negativeCount`, `OAI.Lech.ProductSourceCover.permuteWeight`, `OAI.Lech.ProductSourceCover.rootDegree`, `OAI.Lech.ProductSourceCover.rootPrefix`, `OAI.Lech.ProductSourceCover.rootStripPolynomial`, `OAI.Lech.ProductSourceCover.signedChartOrder`, `OAI.Lech.ProductSourceCover.signedRank`, `OAI.Lech.ProductSourceCover.trueFace`, `OAI.Lech.ProductSourceCover.zeroDimChartOrder`, `OAI.Lech.PureCohomology`, `OAI.Lech.PureProjective.homotopyEquiv`, `OAI.Lech.PureProjective.inclusion`, `OAI.Lech.PureProjective.sectionCycles`, `OAI.Lech.ReesRoot.baseTwist`, `OAI.Lech.ReesRoot.proofFinite`, `OAI.Lech.ReesRoot.raise`, `OAI.Lech.ReesRoot.twistSequence`, `OAI.Lech.RootTower.Expanded`, `OAI.Lech.RootTower.FrobeniusExpanded`, `OAI.Lech.SplitPair.left`, `OAI.Lech.SplitPair.right`, `OAI.Lech.StandardFactorCharts.E`, `OAI.Lech.StandardFactorCharts.L`, `OAI.Lech.StandardFactorCharts.chartUnit`, `OAI.Lech.StandardFactorCharts.coordinate`, `OAI.Lech.StandardFactorCharts.embedding`, `OAI.Lech.UniversalSplitting.PowerIndex`, `OAI.Lech.UniversalSplitting.binaryPower`, `OAI.Lech.UniversalSplitting.powerExponent`, `OAI.Lech.UniversalSplitting.powerMonomial`, `OAI.Lech.UniversalSplitting.powerWeight` and 2 more.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory/Multiplicity, in whole or in part: `Multiplicity_AlternatingCechPost`, `Multiplicity_AlternatingCechPrismPrimitive`, `Multiplicity_CechCartierRange`, `Multiplicity_LechFactorizationMap`, `Multiplicity_LechHomogeneousEval`, `Multiplicity_LechSignedUnit`, `Multiplicity_NativeDescentCanonicalAlg`, `Multiplicity_OrderedRootBasis`, `Multiplicity_PrimitiveChartFaithfullyFlat`, `Multiplicity_PrincipalCoverRegularRegularMap`, `Multiplicity_ProductSourceCoverAllowedEmpty`, `Multiplicity_ProductSourceCoverCechNat`, `Multiplicity_ProductSourceCoverHighThreshold`, `Multiplicity_ProductSourceCoverOrdinaryPositive`, `Multiplicity_ProductSourceCoverRootSigned`, `Multiplicity_PureProjective`, `Multiplicity_ReesRootG`, `Multiplicity_ReesRootLayers`, `Multiplicity_ReesRootNilpotence`, `Multiplicity_RootBaseProjective`, `Multiplicity_RootLineEuler`, `Multiplicity_RootPermutation`, `Multiplicity_RootStripComplement`, `Multiplicity_RootTowerRemainderExponent`, `Multiplicity_RootUlrichSpan`, `Multiplicity_StandardFactorChartsL`, `Multiplicity_UniversalFactorMapMapChart`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ032L015` and `OAIQ032L016`; the statement `OAI.Lech.ReesRoot.sum_estimate`; the proof of `OAI.Lech.complex_estimate_allModule`.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory/Multiplicity at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ032_LECH.Multiplicity_AlternatingCechPost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option synthInstance.maxHeartbeats 200000
namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators

open scoped Classical


namespace Lech.ProductLinearChart
open Polynomial
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (σ : Fin n → Bool)

lemma linear_degree {S : Type*} [CommRing S] (x y : S) : (C x*Polynomial.X+C y).natDegree≤1 := by
  apply natDegree_add_le_of_degree_le
  · exact (natDegree_C_mul_le _ _).trans natDegree_X_le
  · simp

end Lech.ProductLinearChart


namespace Lech.ProductLinearChart
open Polynomial
universe u
variable (R : Type u) [CommRing R]
lemma finSucc_rename (n : ℕ) (p : MvPolynomial (Fin n) R) :
    MvPolynomial.finSuccEquiv R n (MvPolynomial.rename Fin.succ p)=Polynomial.C p := by
  have he : (MvPolynomial.finSuccEquiv R n).toRingHom.comp (MvPolynomial.rename Fin.succ).toRingHom=
      (Polynomial.C : MvPolynomial (Fin n) R →+* Polynomial (MvPolynomial (Fin n) R)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change MvPolynomial.finSuccEquiv R n (MvPolynomial.rename Fin.succ (MvPolynomial.C r))=_
      simp [MvPolynomial.finSuccEquiv_apply]
    · intro i
      change MvPolynomial.finSuccEquiv R n (MvPolynomial.rename Fin.succ (MvPolynomial.X i))=_
      rw [MvPolynomial.rename_X,MvPolynomial.finSuccEquiv_X_succ]
  exact RingHom.congr_fun he p
end Lech.ProductLinearChart
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_PrincipalCoverRegularRegularMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical
namespace Lech.PrincipalCoverRegular
universe u v
variable {R : Type u} [CommRing R] {ι : Type v}


theorem regular_of_cover (q : ι → R) (hq : Ideal.span (Set.range q)=⊤) (x : R)
    (h : ∀ i,IsRegular (algebraMap R (Localization.Away (q i)) x)) : IsRegular x := by
  constructor
  · intro y z hyz
    apply Localization.algebraMap_injective_of_span_eq_top (Set.range q) hq
    funext a
    obtain ⟨a,⟨i,rfl⟩⟩ := a
    simp only [Pi.algebraMap_apply]
    exact (h i).left (by simpa only [map_mul] using congrArg (algebraMap R (Localization.Away (q i))) hyz)
  · intro y z hyz
    apply Localization.algebraMap_injective_of_span_eq_top (Set.range q) hq
    funext a
    obtain ⟨a,⟨i,rfl⟩⟩ := a
    simp only [Pi.algebraMap_apply]
    exact (h i).right (by simpa only [map_mul] using congrArg (algebraMap R (Localization.Away (q i))) hyz)
end Lech.PrincipalCoverRegular


namespace Lech.ProductSourceCover
open scoped BigOperators
universe u
abbrev Chart (n : ℕ) := Fin n → Bool
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [LinearOrder (Chart n)]
local instance endpointDecEq : DecidableEq (Chart n) := LinearOrder.toDecidableEq
def endpointVertex (j : Fin n) (b : Bool) (σ : Chart n) : Chart n := Function.update σ j b
omit [LinearOrder (Chart n)] in
lemma endpointVertex_idem (j : Fin n) (b : Bool) (σ : Chart n) :
    endpointVertex n j b (endpointVertex n j b σ)=endpointVertex n j b σ := by
  simp only [endpointVertex,Function.update_idem]
end Lech.ProductSourceCover


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_AlternatingCechPrismPrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option synthInstance.maxHeartbeats 200000
namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.ProductSourceCover
open scoped BigOperators Classical
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
def trueFace (σ : Chart n) : Chart (n+1) := Fin.cons true σ
@[simp] lemma trueFace_zero (σ : Chart n) : trueFace n σ 0=true := rfl
@[simp] lemma trueFace_succ (σ : Chart n) (i : Fin n) : trueFace n σ i.succ=σ i := rfl
end Lech.ProductSourceCover


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProductSourceCoverAllowedEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.ProductSourceCover
open AddMonoidAlgebra CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [LinearOrder (Chart n)]
local instance endpointRingDecEq : DecidableEq (Chart n) := LinearOrder.toDecidableEq
end Lech.ProductSourceCover


namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable (R : Type u) [CommRing R]
 

def PureCohomology (K : CochainComplex (ModuleCat.{u} R) ℕ) (d r : ℕ) : Prop :=
  (∀ i,i≠d → IsZero (K.homology i)) ∧ Nonempty (Module.Basis (Fin r) R (K.homology d))
variable {R}
lemma pureCohomology_acyclic (K : CochainComplex (ModuleCat.{u} R) ℕ) (h : K.Acyclic) (d : ℕ) :
    PureCohomology R K d 0 := by
  refine ⟨fun i _ => (exactAt_iff_isZero_homology _ _).mp (h i),?_⟩
  have hi := (exactAt_iff_isZero_homology _ _).mp (h d)
  have : Subsingleton (K.homology d) := ModuleCat.isZero_iff_subsingleton.mp hi
  exact ⟨Module.Basis.empty _⟩
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ)) (hS : S.ShortExact)
def cohomologyShortComplex (d : ℕ) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (homologyMap S.f d) (homologyMap S.g d) (by
    rw [←homologyMap_comp,S.zero,homologyMap_zero])
include hS in
lemma cohomologyShortComplex_shortExact (d : ℕ) (hd : 0<d)
    (hprev : IsZero (S.X₃.homology (d-1))) (hnext : IsZero (S.X₁.homology (d+1))) :
    (cohomologyShortComplex S d).ShortExact := by
  refine ShortComplex.ShortExact.mk' (hS.homology_exact₂ d) ?_ ?_
  · exact (hS.homology_exact₁ (d-1) d (by change d-1+1=d;omega)).mono_g (hprev.eq_of_src _ _)
  · exact (hS.homology_exact₃ d (d+1) rfl).epi_f (hnext.eq_of_tgt _ _)
include hS in
lemma pureCohomology_middle {d a b : ℕ} (hd : 0<d)
    (h₁ : PureCohomology R S.X₁ d a) (h₃ : PureCohomology R S.X₃ d b) :
    PureCohomology R S.X₂ d (a+b) := by
  refine ⟨fun i hi => (hS.homology_exact₂ i).isZero_X₂
    ((h₁.1 i hi).eq_of_src _ _) ((h₃.1 i hi).eq_of_tgt _ _),?_⟩
  obtain ⟨b₁⟩ := h₁.2
  obtain ⟨b₃⟩ := h₃.2
  let h := cohomologyShortComplex_shortExact S hS d hd (h₃.1 (d-1) (by omega)) (h₁.1 (d+1) (by omega))
  exact ⟨(ModuleCat.Basis.ofShortExact h b₁ b₃).reindex (finSumFinEquiv)⟩
def boundaryShortComplex (d : ℕ) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (hS.δ d (d+1) rfl) (homologyMap S.f (d+1)) (hS.δ_comp d (d+1) rfl)
lemma boundaryShortComplex_shortExact (d : ℕ)
    (h₂ : IsZero (S.X₂.homology d)) (h₃ : IsZero (S.X₃.homology (d+1))) :
    (boundaryShortComplex S hS d).ShortExact := by
  refine ShortComplex.ShortExact.mk' (hS.homology_exact₁ d (d+1) rfl) (hS.mono_δ d (d+1) rfl h₂) ?_
  exact (hS.homology_exact₂ (d+1)).epi_f (h₃.eq_of_tgt _ _)
include hS in
lemma pureCohomology_left {d a b : ℕ}
    (hzero : IsZero (S.X₁.homology 0))
    (h₂ : PureCohomology R S.X₂ (d+1) a) (h₃ : PureCohomology R S.X₃ d b) :
    PureCohomology R S.X₁ (d+1) (b+a) := by
  refine ⟨?_,?_⟩
  · intro i hi
    cases i with
    | zero => exact hzero
    | succ i =>
      exact (hS.homology_exact₁ i (i+1) rfl).isZero_X₂
        ((h₃.1 i (by omega)).eq_of_src _ _) ((h₂.1 (i+1) hi).eq_of_tgt _ _)
  · obtain ⟨b₂⟩ := h₂.2
    obtain ⟨b₃⟩ := h₃.2
    let h := boundaryShortComplex_shortExact S hS d (h₂.1 d (by omega)) (h₃.1 (d+1) (by omega))
    exact ⟨(ModuleCat.Basis.ofShortExact h b₃ b₂).reindex finSumFinEquiv⟩
end Lech
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProductSourceCoverOrdinaryPositive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option synthInstance.maxHeartbeats 200000
namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical
namespace Lech.ProductSourceCover
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators Classical
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
local instance chartOrder (n : ℕ) : LinearOrder (Chart n) :=
  LinearOrder.lift' (Fintype.equivFin (Chart n)) (Fintype.equivFin _).injective


end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open scoped BigOperators
 
def negativeCount {n : ℕ} (m : Fin n → ℤ) : ℕ := ∑ i,if m i < -1 then 1 else 0
 
def signedRank {n : ℕ} (m : Fin n → ℤ) : ℕ := ∏ i,(m i+1).natAbs
lemma negativeCount_cons {n : ℕ} (k : ℤ) (m : Fin n → ℤ) :
    negativeCount (Fin.cons k m)=(if k < -1 then 1 else 0)+negativeCount m := by
  simp only [negativeCount,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
lemma signedRank_cons {n : ℕ} (k : ℤ) (m : Fin n → ℤ) :
    signedRank (Fin.cons k m)=(k+1).natAbs*signedRank m := by
  simp [signedRank,Fin.prod_univ_succ]
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators Classical
universe u
variable (R : Type u) [CommRing R]
local instance zeroDimChartOrder (n : ℕ) : LinearOrder (Chart n) :=
  LinearOrder.lift' (Fintype.equivFin (Chart n)) (Fintype.equivFin _).injective
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators Classical
universe u
variable (R : Type u) [CommRing R]
local instance signedChartOrder (n : ℕ) : LinearOrder (Chart n) :=
  LinearOrder.lift' (Fintype.equivFin (Chart n)) (Fintype.equivFin _).injective


end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open AddMonoidAlgebra
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
def levelTwist (m : Fin n → ℤ) (d N : ℕ) : Fin n → ℤ := fun i => m i+(N:ℤ)*(d:ℤ)
end Lech.ProductSourceCover
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProductSourceCoverHighThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option synthInstance.maxHeartbeats 200000
namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical
namespace Lech.ProductSourceCover
open Set AddMonoidAlgebra CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
def highThreshold (m : Fin n → ℤ) : ℕ := Finset.univ.sup (fun i => (m i).natAbs)
lemma level_high (m : Fin n → ℤ) (d N : ℕ) (hd : 0<d) (hN : highThreshold n m≤N) :
    ∀ i,-1≤levelTwist n m d N i := by
  intro i
  have hm : (m i).natAbs≤N := (Finset.le_sup (f:=fun i : Fin n => (m i).natAbs) (Finset.mem_univ i)).trans hN
  have hm' : |m i|≤(N:ℤ) := by rw [←Int.natCast_natAbs];exact_mod_cast hm
  have hd' : (1:ℤ)≤(d:ℤ) := by exact_mod_cast hd
  have hN' : (0:ℤ)≤(N:ℤ) := Nat.cast_nonneg _
  have hn := neg_le_abs (m i)
  dsimp [levelTwist]
  nlinarith

variable [LinearOrder (Chart n)]
local instance gridSourceDecEq : DecidableEq (Chart n) := LinearOrder.toDecidableEq


end Lech.ProductSourceCover


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProductSourceCoverCechNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech

section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable (R : Type u) [CommRing R]
lemma pureCohomology_of_iso (K L : CochainComplex (ModuleCat.{u} R) ℕ)
    (e : ∀ p,K.homology p ≅ L.homology p) (d r : ℕ)
    (h : PureCohomology R K d r) : PureCohomology R L d r := by
  refine ⟨fun p hp => (h.1 p hp).of_iso (e p).symm,?_⟩
  obtain ⟨b⟩ := h.2
  exact ⟨b.map (e d).toLinearEquiv⟩
end


open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
end Lech


namespace Lech.ProductSourceCover

section


open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators Classical
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [LinearOrder (Chart n)]
 
def RootPositions (s : ℕ) (r : Fin n → ℤ) : Prop :=
  ∀ j, -((j.val:ℤ)+2)*(s:ℤ) < r j ∧ r j < -((j.val:ℤ)+1)*(s:ℤ)
def rootDegree (r : Fin n → ℤ) (a : ℤ) : ℕ :=
  (Finset.univ.filter (fun j => a < r j)).card
end


open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
open scoped BigOperators Classical
universe u
end Lech.ProductSourceCover


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProductSourceCoverRootSigned
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.ProductSourceCover


open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
open scoped BigOperators
universe u
variable {C : Type u}
  [CommRing C]
  (I : Ideal C)
variable (n : ℕ) [LinearOrder (Chart n)]
 
def rootStripPolynomial (r : Fin n → ℤ) (i s : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (i*s),∏ j,((l:ℝ)-(i:ℝ)*(s:ℝ)-(r j:ℝ))
end Lech.ProductSourceCover


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechHomogeneousEval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.ProductSourceCover

section


open Polynomial
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
lemma ratio_rescale {S : Type*} [CommRing S] (u v : Sˣ) (b : S) :
    (↑((u*v)⁻¹):S)*((u:S)*b)=(↑(v⁻¹):S)*b := by
  rw [mul_inv_rev,Units.val_mul]
  calc
    _ = (↑(v⁻¹):S)*((↑(u⁻¹):S)*(u:S))*b := by ring
    _ = _ := by rw [Units.inv_mul,mul_one]


end


universe u
end Lech.ProductSourceCover


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_PrimitiveChartFaithfullyFlat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical
namespace Lech.PrimitiveChart
open Polynomial
universe u
variable {A : Type u} [CommRing A]

 

theorem faithfullyFlat_away (f : A[X])
    (hf : Ideal.span (Set.range f.coeff)=⊤) :
    Module.FaithfullyFlat A (Localization.Away f) := by
  have : Module.Flat A[X] (Localization.Away f) :=
    IsLocalization.flat (Localization.Away f) (Submonoid.powers f)
  have : Module.Flat A (Localization.Away f) :=
    Module.Flat.trans A A[X] (Localization.Away f)
  apply Module.FaithfullyFlat.of_comap_surjective
  intro p
  let I : Ideal A[X] := Ideal.map C p.asIdeal
  have hI : I.IsPrime := Ideal.isPrime_map_C_iff_isPrime _ |>.mpr p.isPrime
  have hnot : f∉I := by
    intro h
    have hcoef : ∀ k, f.coeff k∈p.asIdeal := Ideal.mem_map_C_iff.mp h
    have he : (⊤ : Ideal A)≤p.asIdeal := by
      rw [← hf]
      exact Ideal.span_le.mpr (by rintro _ ⟨k,rfl⟩; exact hcoef k)
    exact p.isPrime.ne_top (top_le_iff.mp he)
  let : I.IsPrime := hI
  have hdis : Disjoint (Submonoid.powers f : Set A[X]) (I : Set A[X]) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hnot
  let J : Ideal (Localization.Away f) := I.map (algebraMap A[X] (Localization.Away f))
  have hJ : J.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers f) (Localization.Away f) I hI hdis
  have hu : J.under A[X]=I := IsLocalization.under_map_of_isPrime_disjoint
    (Submonoid.powers f) (Localization.Away f) hI hdis
  refine ⟨⟨J,hJ⟩,?_⟩
  apply PrimeSpectrum.ext
  ext a
  change algebraMap A (Localization.Away f) a∈J ↔ a∈p.asIdeal
  rw [IsScalarTower.algebraMap_apply A A[X] (Localization.Away f)]
  change C a∈J.under A[X] ↔ a∈p.asIdeal
  rw [hu]
  change C a∈Ideal.map C p.asIdeal ↔ a∈p.asIdeal
  rw [Ideal.mem_map_C_iff]
  constructor
  · intro h
    simpa using h 0
  · intro h k
    by_cases hk : k=0
    · simpa [hk] using h
    · simp [coeff_C,hk]

end Lech.PrimitiveChart


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_StandardFactorChartsL
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical
namespace Lech.StandardFactorCharts
open Polynomial
universe u
variable {A S : Type u} [CommRing A] [CommRing S] [Algebra A S]
variable (D : Subalgebra A S) (n : ℕ) (P : Fin n → Bool → S)
  (v : Sˣ) (c : (Fin n → Bool) → D)
  (hc : ∀ σ,(c σ:S)=(v:S)*∏ i,P i (σ i))

abbrev L (σ : Fin n → Bool) := Localization.Away (c σ)
abbrev E (σ : Fin n → Bool) := Localization.Away (D.val (c σ))

def embedding (σ : Fin n → Bool) : L D n c σ →ₐ[A] E D n c σ :=
  IsLocalization.Away.mapₐ _ _ D.val (c σ)

lemma embedding_injective (σ : Fin n → Bool) : Function.Injective (embedding D n c σ) :=
  IsLocalization.Away.mapₐ_injective_of_injective (f := D.val) (c σ) Subtype.val_injective

lemma embedding_map (σ : Fin n → Bool) (x : D) :
    embedding D n c σ (algebraMap D (L D n c σ) x)=algebraMap S (E D n c σ) (x:S) := by
  change IsLocalization.Away.map (L D n c σ) (E D n c σ) D.val.toRingHom (c σ)
    (algebraMap D (L D n c σ) x)=algebraMap S (E D n c σ) (D.val x)
  dsimp only [IsLocalization.Away.map]
  exact IsLocalization.map_eq _ x

def chartUnit (σ : Fin n → Bool) : (L D n c σ)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (c σ)).unit

lemma chartUnit_val (σ : Fin n → Bool) : (chartUnit D n c σ:L D n c σ)=algebraMap D _ (c σ) :=
  (IsLocalization.Away.algebraMap_isUnit (c σ)).unit_spec

 
def coordinate (σ : Fin n → Bool) (i : Fin n) (b : Bool) : L D n c σ :=
  algebraMap D _ (c (Function.update σ i b))*((chartUnit D n c σ)⁻¹).val

lemma coordinate_selected (σ : Fin n → Bool) (i : Fin n) : coordinate D n c σ i (σ i)=1 := by
  simp only [coordinate,Function.update_eq_self]
  rw [← chartUnit_val,Units.mul_inv]

include hc in
lemma cross_identity (σ : Fin n → Bool) (i : Fin n) (b : Bool) :
    (c σ:S)*P i b=(c (Function.update σ i b):S)*P i (σ i) := by
  classical
  rw [hc,hc]
  have he : (∏ j ∈ Finset.univ.erase i,P j (Function.update σ i b j))=
      ∏ j ∈ Finset.univ.erase i,P j (σ j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ (fun j => P j (Function.update σ i b j)) (Finset.mem_univ i)]
  rw [he,Function.update_self]
  ring

include hc in
lemma coordinate_relation (σ : Fin n → Bool) (i : Fin n) (b : Bool) :
    embedding D n c σ (coordinate D n c σ i b)*algebraMap S (E D n c σ) (P i (σ i))=
      algebraMap S (E D n c σ) (P i b) := by
  have h := congrArg (algebraMap S (E D n c σ)) (cross_identity D n P v c hc σ i b)
  simp only [map_mul] at h
  have hu := congrArg (embedding D n c σ) (Units.mul_inv (chartUnit D n c σ))
  rw [map_mul,chartUnit_val,embedding_map,map_one] at hu
  rw [coordinate,map_mul,embedding_map]
  calc
    algebraMap S _ (c (Function.update σ i b):S)*
        embedding D n c σ ((chartUnit D n c σ)⁻¹).val*algebraMap S _ (P i (σ i)) =
      (algebraMap S _ (c (Function.update σ i b):S)*algebraMap S _ (P i (σ i)))*
        embedding D n c σ ((chartUnit D n c σ)⁻¹).val := by ring
    _ = (algebraMap S _ (c σ:S)*algebraMap S _ (P i b))*
        embedding D n c σ ((chartUnit D n c σ)⁻¹).val := by rw [h]
    _ = algebraMap S _ (P i b)*(algebraMap S _ (c σ:S)*
        embedding D n c σ ((chartUnit D n c σ)⁻¹).val) := by ring
    _ = algebraMap S _ (P i b) := by rw [hu,mul_one]
 
lemma normalize_product {R : Type*} [CommRing R] (m : ℕ)
    (P Q : Fin m → Bool → R) (σ : Fin m → Bool) (r d : R)
    (hd : d=r*∏ i,P i (σ i))
    (hQ : ∀ i b,Q i b*P i (σ i)=P i b) :
    MvPolynomial.C r*∏ i : Fin m,(MvPolynomial.C (P i true)*MvPolynomial.X (0:Fin 2)+
      MvPolynomial.C (P i false)*MvPolynomial.X 1)=
    MvPolynomial.C d*∏ i : Fin m,(MvPolynomial.C (Q i true)*MvPolynomial.X (0:Fin 2)+
      MvPolynomial.C (Q i false)*MvPolynomial.X 1) := by
  rw [hd,map_mul,map_prod,mul_assoc,← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [mul_add,← mul_assoc,← MvPolynomial.C_mul, mul_comm (P i (σ i)),hQ]
  rw [← mul_assoc,← MvPolynomial.C_mul,mul_comm (P i (σ i)),hQ]

include hc in
 

lemma chart_factorization (f : A[X])
    (hf : MvPolynomial.map (algebraMap A S) (f.homogenize n)=
      MvPolynomial.C (v:S)*∏ i : Fin n,(MvPolynomial.C (P i true)*MvPolynomial.X 0+
        MvPolynomial.C (P i false)*MvPolynomial.X 1)) (σ : Fin n → Bool) :
    MvPolynomial.map (algebraMap A (L D n c σ)) (f.homogenize n)=
      MvPolynomial.C (chartUnit D n c σ:L D n c σ)*∏ i : Fin n,
        (MvPolynomial.C (coordinate D n c σ i true)*MvPolynomial.X 0+
          MvPolynomial.C (coordinate D n c σ i false)*MvPolynomial.X 1) := by
  apply MvPolynomial.map_injective (embedding D n c σ).toRingHom (embedding_injective D n c σ)
  simp only [map_mul,map_prod,map_add,MvPolynomial.map_C,MvPolynomial.map_X]
  have hco : (embedding D n c σ).toRingHom.comp (algebraMap A (L D n c σ))=
      (algebraMap S (E D n c σ)).comp (algebraMap A S) := by
    exact (embedding D n c σ).comp_algebraMap.trans
      (IsScalarTower.algebraMap_eq A S (E D n c σ))
  rw [MvPolynomial.map_map,hco,← MvPolynomial.map_map,hf]
  simp only [map_mul,map_prod,map_add,MvPolynomial.map_C,MvPolynomial.map_X]
  refine normalize_product n (fun i b => algebraMap S (E D n c σ) (P i b))
    (fun i b => embedding D n c σ (coordinate D n c σ i b)) σ
    (algebraMap S (E D n c σ) (v:S)) (embedding D n c σ (chartUnit D n c σ)) ?_ ?_
  · rw [chartUnit_val,embedding_map,hc,map_mul,map_prod]
  · exact coordinate_relation D n P v c hc σ

end Lech.StandardFactorCharts


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_NativeDescentCanonicalAlg
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option synthInstance.maxHeartbeats 200000
namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.StandardFactorCharts
open Polynomial
universe u
variable {A S : Type u} [CommRing A] [CommRing S] [Algebra A S]
variable (D : Subalgebra A S) (n : ℕ) (P : Fin n → Bool → S)
  (v : Sˣ) (c : (Fin n → Bool) → D)
  (hc : ∀ σ,(c σ:S)=(v:S)*∏ i,P i (σ i))
variable {T : Type u} [CommRing T] [Algebra A T]

include hc in
lemma map_coordinate_relation (σ : Fin n → Bool) (ψ : L D n c σ →ₐ[A] T) (φ : S →ₐ[A] T)
    (hcompat : ∀ x : D,ψ (algebraMap D (L D n c σ) x)=φ (x:S)) (i : Fin n) (b : Bool) :
    ψ (coordinate D n c σ i b)*φ (P i (σ i))=φ (P i b) := by
  have h := congrArg φ (cross_identity D n P v c hc σ i b)
  simp only [map_mul] at h
  have hu := congrArg ψ (Units.mul_inv (chartUnit D n c σ))
  rw [map_mul,chartUnit_val,hcompat,map_one] at hu
  rw [coordinate,map_mul,hcompat]
  calc
    φ (c (Function.update σ i b):S)*ψ ((chartUnit D n c σ)⁻¹).val*φ (P i (σ i))=
      (φ (c (Function.update σ i b):S)*φ (P i (σ i)))*ψ ((chartUnit D n c σ)⁻¹).val := by ring
    _ = (φ (c σ:S)*φ (P i b))*ψ ((chartUnit D n c σ)⁻¹).val := by rw [h]
    _ = φ (P i b)*(φ (c σ:S)*ψ ((chartUnit D n c σ)⁻¹).val) := by ring
    _ = φ (P i b) := by rw [hu,mul_one]

 

lemma normalized_root {R : Type*} [CommRing R] (x t a b α : R) (μ : Rˣ)
    (hμ : (μ:R)=t*a+b) (ha : a*α= -x) (hb : b*α=1+t*x) :
    x= -a*(μ⁻¹).val := by
  have hm : (μ:R)*α=1 := by
    rw [hμ,add_mul,mul_assoc,ha,hb]
    ring
  have hα : α=(μ⁻¹).val := by
    calc
      α = ((μ⁻¹).val*(μ:R))*α := by rw [Units.inv_mul,one_mul]
      _ = (μ⁻¹).val := by rw [mul_assoc,hm,mul_one]
  rw [←hα,neg_mul,ha,neg_neg]
end Lech.StandardFactorCharts
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_UniversalFactorMapMapChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option synthInstance.maxHeartbeats 200000
namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical
namespace Lech.UniversalFactorMap
open Polynomial
open scoped TensorProduct
universe u
variable {A B T : Type u} [CommRing A] [CommRing B] [CommRing T]
  [Algebra A B] [Algebra A T] [Module.FaithfullyFlat A B]
variable (f : A[X])
  (n : ℕ)
  (hn : f.natDegree≤n)
  (t : B)
  (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
variable (σ : Fin n → Bool) (w : Tˣ) (a b : Fin n → T)
  (hf : (f.map (algebraMap A T)).homogenize n=MvPolynomial.C (w:T)*∏ i,
    (MvPolynomial.C (a i)*MvPolynomial.X 0+MvPolynomial.C (b i)*MvPolynomial.X 1))
  (hs : ∀ i,(if σ i then a i else b i)=1)

include hs in
lemma update_product (i : Fin n) (κ : Bool) :
    (∏ j : Fin n,if Function.update σ i κ j then a j else b j)=if κ then a i else b i := by
  classical
  rw [Finset.prod_eq_single i]
  · rw [Function.update_self]
  · intro j _ hji
    rw [Function.update_of_ne hji]
    exact hs j
  · intro hi
    exact (hi (Finset.mem_univ i)).elim



end Lech.UniversalFactorMap


namespace Lech.UniversalFactorMap
open Polynomial
open scoped TensorProduct
universe u
lemma normalizedRatio_rescale {T : Type u} [CommRing T] (a : T) (c μ : Tˣ) :
    -((c:T)*a)*(↑((c*μ)⁻¹):T)= -a*(↑(μ⁻¹):T) := by
  simp only [mul_inv_rev,Units.val_mul]
  calc
    _ = (-a*↑(μ⁻¹))*((c:T)*↑(c⁻¹)) := by ring
    _ = _ := by rw [Units.mul_inv,mul_one]
end Lech.UniversalFactorMap


namespace Lech.ProductLinearChart
open Polynomial
universe u v
variable (R : Type u) [CommRing R] (n : ℕ) (σ : Fin n → Bool) (k : Fin (n+1))
variable {T : Type v} [CommRing T] [Algebra R T]

lemma dehomogenize_factorization (f : T[X]) (hf : f.natDegree≤n) (w : T)
    (x y : Fin n → T)
    (h : f.homogenize n=MvPolynomial.C w*∏ i,
      (MvPolynomial.C (x i)*MvPolynomial.X 0+MvPolynomial.C (y i)*MvPolynomial.X 1)) :
    f=C w*∏ i,(C (x i)*Polynomial.X+C (y i)) := by
  have hh := congrArg (MvPolynomial.aeval ![Polynomial.X, (1:T[X])]) h
  rw [Polynomial.aeval_homogenize_X_one f hf] at hh
  simpa only [map_mul,map_add,map_prod,MvPolynomial.aeval_C,MvPolynomial.aeval_X,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,mul_one,algebraMap_eq] using hh

end Lech.ProductLinearChart


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechFactorizationMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical
namespace Lech
open Polynomial
universe u
lemma factorization_map {A T U : Type u} [CommRing A] [CommRing T] [CommRing U]
    [Algebra A T] [Algebra A U] (φ : T →ₐ[A] U) (f : A[X]) (n : ℕ)
    (w : Tˣ) (a b : Fin n → T)
    (hf : (f.map (algebraMap A T)).homogenize n=MvPolynomial.C (w:T)*∏ i,
      (MvPolynomial.C (a i)*MvPolynomial.X 0+MvPolynomial.C (b i)*MvPolynomial.X 1)) :
    (f.map (algebraMap A U)).homogenize n=MvPolynomial.C (φ (w:T))*∏ i,
      (MvPolynomial.C (φ (a i))*MvPolynomial.X 0+MvPolynomial.C (φ (b i))*MvPolynomial.X 1) := by
  rw [←φ.comp_algebraMap,←Polynomial.map_map,Polynomial.homogenize_map,hf]
  simp only [map_mul,map_prod,map_add,MvPolynomial.map_C,MvPolynomial.map_X]
  rfl
end Lech


namespace Lech.StandardFactorCharts
open Polynomial
universe u z
variable {A S : Type u} [CommRing A] [CommRing S] [Algebra A S]
variable (D : Subalgebra A S) (n : ℕ) (P : Fin n → Bool → S)
  (v : Sˣ) (c : (Fin n → Bool) → D)
  (hc : ∀ σ,(c σ:S)=(v:S)*∏ i,P i (σ i))
variable {T : Type z} [CommRing T]
include hc in
lemma coordinate_relation_ring (σ : Fin n → Bool) (ψ : L D n c σ →+* T) (φ : S →+* T)
    (hcompat : ∀ x : D,ψ (algebraMap D (L D n c σ) x)=φ (x:S)) (i : Fin n) (b : Bool) :
    ψ (coordinate D n c σ i b)*φ (P i (σ i))=φ (P i b) := by
  have h := congrArg φ (cross_identity D n P v c hc σ i b)
  simp only [map_mul] at h
  have hu := congrArg ψ (Units.mul_inv (chartUnit D n c σ))
  rw [map_mul,chartUnit_val,hcompat,map_one] at hu
  rw [coordinate,map_mul,hcompat]
  calc
    φ (c (Function.update σ i b):S)*ψ ((chartUnit D n c σ)⁻¹).val*φ (P i (σ i))=
      (φ (c (Function.update σ i b):S)*φ (P i (σ i)))*ψ ((chartUnit D n c σ)⁻¹).val := by ring
    _ = (φ (c σ:S)*φ (P i b))*ψ ((chartUnit D n c σ)⁻¹).val := by rw [h]
    _ = φ (P i b)*(φ (c σ:S)*ψ ((chartUnit D n c σ)⁻¹).val) := by ring
    _ = φ (P i b) := by rw [hu,mul_one]

include hc in
lemma selected_unit (σ : Fin n → Bool) (ψ : L D n c σ →+* T) (φ : S →+* T)
    (hcompat : ∀ x : D,ψ (algebraMap D (L D n c σ) x)=φ (x:S)) (i : Fin n) :
    IsUnit (φ (P i (σ i))) := by
  have hu : IsUnit (φ (c σ:S)) := by
    rw [← hcompat]
    exact (IsLocalization.Away.algebraMap_isUnit (c σ)).map ψ
  rw [hc,map_mul,map_prod] at hu
  have hp := isUnit_of_mul_isUnit_right hu
  exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun j => φ (P j (σ j))) (Finset.mem_univ i)) hp
end Lech.StandardFactorCharts


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechSignedUnit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical
namespace Lech
lemma signedUnitProduct {G : Type*} [CommGroup G] {ι : Type*} [Fintype ι]
    (a b : ι → G) (m : ι → ℤ) :
    (∏ i,a i^m i)*(∏i,b i^m i)⁻¹=∏i,(a i*(b i)⁻¹)^m i := by
  simp only [mul_zpow,inv_zpow,Finset.prod_mul_distrib,Finset.prod_inv_distrib]
end Lech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootLayers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j, z j ∈ I)
attribute [local instance] MvPolynomial.gradedAlgebra

variable (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ)



def raise (m : Fin n → ℤ) : ℕ → Fin n → ℤ
  | 0 => m
  | N+1 => raise (fun i => m i+1) N

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CechCartierRange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (m : Fin n → ℤ)
attribute [local instance] MvPolynomial.gradedAlgebra
local instance proofFinite (s : Finset (Fin (n+1))) : Fintype (PLift s.Nonempty) := Fintype.ofFinite _

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_OrderedRootBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.UniversalSplitting
open Polynomial
universe u

abbrev PowerIndex : ℕ → Type
  | 0 => Unit
  | n+1 => Fin (n+1) × PowerIndex n

def powerMonomial {S : Type*} [CommMonoid S] :
    (n : ℕ) → (Fin n → S) → PowerIndex n → S
  | 0,_,_ => 1
  | n+1,rs,e => rs 0 ^ e.1.val * powerMonomial n (fun i => rs i.succ) e.2

lemma map_powerMonomial {S T : Type*} [CommMonoid S] [CommMonoid T]
    (φ : S →* T) (n : ℕ) (rs : Fin n → S) (e : PowerIndex n) :
    φ (powerMonomial n rs e)=powerMonomial n (fun i => φ (rs i)) e := by
  induction n with
  | zero => exact map_one φ
  | succ n ih =>
      simp only [powerMonomial,map_mul,map_pow]
      rw [ih]

end Lech.UniversalSplitting

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_PureProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.PureProjective
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]
variable (K : CochainComplex C ℤ) (d : ℤ) [Projective (K.homology d)]

def sectionCycles : K.homology d ⟶ K.cycles d :=
  Projective.factorThru (𝟙 (K.homology d)) (K.homologyπ d)

lemma sectionCycles_π : sectionCycles K d ≫ K.homologyπ d = 𝟙 _ :=
  Projective.factorThru_comp _ _

def inclusion : (single C (.up ℤ) d).obj (K.homology d) ⟶ K :=
  mkHomFromSingle (sectionCycles K d ≫ K.iCycles d)
    (by intro k _; simp only [Category.assoc, iCycles_d, comp_zero])

lemma cycles_inclusion : cyclesMap (inclusion K d) d =
    (singleObjCyclesSelfIso (.up ℤ) d (K.homology d)).hom ≫ sectionCycles K d := by
  rw [←cancel_mono (K.iCycles d), cyclesMap_i]
  simp only [inclusion, mkHomFromSingle_f, Category.assoc, singleObjCyclesSelfIso_hom]

lemma homology_inclusion : homologyMap (inclusion K d) d =
    (singleObjHomologySelfIso (.up ℤ) d (K.homology d)).hom := by
  rw [←cancel_epi (((single C (.up ℤ) d).obj (K.homology d)).homologyπ d),
    homologyπ_naturality, cycles_inclusion, Category.assoc, sectionCycles_π,
    Category.comp_id, homologyπ_singleObjHomologySelfIso_hom]

lemma inclusion_quasiIso (hpure : ∀ j, j≠d → IsZero (K.homology j)) :
    QuasiIso (inclusion K d) := by
  rw [quasiIso_iff]
  intro j
  rw [quasiIsoAt_iff_isIso_homologyMap]
  by_cases hj : j=d
  · subst j
    rw [homology_inclusion]
    infer_instance
  · exact (isZero_single_obj_homology (.up ℤ) d (K.homology d) j hj).isIso
      (hpure j hj) _

 

def homotopyEquiv (N : ℤ) [K.IsStrictlyLE N] [∀ j, Projective (K.X j)]
    (hpure : ∀ j, j≠d → IsZero (K.homology j)) :
    HomotopyEquiv ((single C (.up ℤ) d).obj (K.homology d)) K := by
  let S : CochainComplex C ℤ := (single C (.up ℤ) d).obj (K.homology d)
  have : S.IsStrictlyLE d := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro j hj
    exact isZero_single_obj_X (.up ℤ) d (K.homology d) j (by omega)
  letI := CochainComplex.isKProjective_of_projective S d
  letI := CochainComplex.isKProjective_of_projective K N
  exact Classical.choose ((CochainComplex.IsKProjective.quasiIso_iff (inclusion K d)).mp
    (inclusion_quasiIso K d hpure))
end Lech.PureProjective

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootG
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j, z j ∈ I)
attribute [local instance] MvPolynomial.gradedAlgebra

variable (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (m : Fin n → ℤ)

 

def baseTwist : Fin n → ℤ := fun j => m j-(h*s:ℕ)

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootNilpotence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j, z j ∈ I)
attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable (F : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℕ)
  (H : ∀ k, Homotopy (z k^a • 𝟙 F) 0)

variable (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))



def twistSequence (m : Fin n → ℤ) (a : ℕ) : ℕ → (Fin n → ℤ)
  | 0 => m
  | N+1 => raise (twistSequence m a N) a

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootBaseProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ProjectiveScalar
universe u v w
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

lemma trans [Module.Projective R S] [Module.Projective S M] : Module.Projective R M := by
  classical
  obtain ⟨i,hi⟩ := (inferInstance : Module.Projective S M).out
  have hp : Module.Projective R (M →₀ S) :=
    Module.Projective.of_equiv (finsuppLequivDFinsupp R).symm
  apply Module.Projective.of_split (i.restrictScalars R)
    ((Finsupp.linearCombination S id).restrictScalars R)
  ext x
  exact hi x
end Lech.ProjectiveScalar

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootUlrichSpan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.UniversalSplitting
open Polynomial
universe u v
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

 

lemma degree_fill (t : R) (a b c : S) (hab : b+algebraMap R S t*a=1)
    (Q : Submodule R S) (d : ℕ)
    (hh : ∀ e : ℕ,e≤d → a^e*b^(d-e)*c∈Q) (extra : ℕ) :
    ∀ e k : ℕ,e+k+extra=d → a^e*b^k*c∈Q := by
  induction extra with
  | zero =>
      intro e k he
      have hk : k=d-e := by omega
      rw [hk]
      exact hh e (by omega)
  | succ extra ih =>
      intro e k he
      have h₁ := ih e (k+1) (by omega)
      have h₂ := ih (e+1) k (by omega)
      have hl := Q.add_mem h₁ (Q.smul_mem t h₂)
      convert hl using 1
      all_goals try with_reducible_and_instances rfl
      rw [Algebra.smul_def,pow_succ,pow_succ]
      calc
        a^e*b^k*c = a^e*b^k*c*(b+algebraMap R S t*a) := by rw [hab,mul_one]
        _ = _ := by ring

lemma power_in_homogeneous_span (t : R) (x c : S) (Q : Submodule R S) (d e : ℕ) (he : e≤d)
    (hh : ∀ j : ℕ,j≤d → (-x)^j*(1+algebraMap R S t*x)^(d-j)*c∈Q) : x^e*c∈Q := by
  have ha := degree_fill t (-x) (1+algebraMap R S t*x) c (by ring) Q d hh (d-e) e 0 (by omega)
  simp only [pow_zero,mul_one] at ha
  have hb := Q.smul_mem ((-1:R)^e) ha
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Algebra.smul_def,map_pow,map_neg,map_one,←mul_assoc,←mul_pow,neg_mul,one_mul,neg_neg]

 
def binaryPower (t : R) : (n : ℕ) → (Fin n → S) → PowerIndex n → S
  | 0,_,_ => 1
  | n+1,rs,e => (-rs 0)^e.1.val * (1+algebraMap R S t*rs 0)^(n-e.1.val) *
      binaryPower t n (fun i => rs i.succ) e.2

lemma powerMonomial_mem_binary_span (t : R) (n : ℕ) (rs : Fin n → S) (e : PowerIndex n) :
    powerMonomial n rs e ∈ Submodule.span R (Set.range (binaryPower t n rs)) := by
  induction n with
  | zero => exact Submodule.subset_span ⟨e,rfl⟩
  | succ n ih =>
      let Q := Submodule.span R (Set.range (binaryPower t (n+1) rs))
      apply power_in_homogeneous_span t (rs 0) (powerMonomial n (fun i => rs i.succ) e.2) Q n e.1.val
        (by have := e.1.isLt; omega)
      intro j hj
      let a := (-rs 0)^j*(1+algebraMap R S t*rs 0)^(n-j)
      have ht := ih (fun i => rs i.succ) e.2
      have hs : Submodule.span R (Set.range (binaryPower t n (fun i => rs i.succ))) ≤
          Q.comap (LinearMap.mulLeft R a) := by
        apply Submodule.span_le.mpr
        rintro x ⟨e',rfl⟩
        exact Submodule.subset_span ⟨(⟨j,by omega⟩,e'),rfl⟩
      exact hs ht

variable {n : ℕ} {f : R[X]}

def powerWeight (n : ℕ) (i : Fin n) : ℕ := n-(i.val+1)

def powerExponent : (n : ℕ) → PowerIndex n → Fin n → ℕ
  | 0,_ => Fin.elim0
  | n+1,e => Fin.cons e.1.val (powerExponent n e.2)

lemma powerWeight_succ (n : ℕ) (i : Fin n) : powerWeight (n+1) i.succ=powerWeight n i := by
  simp [powerWeight,Fin.val_succ,Nat.add_sub_add_right]

lemma powerExponent_bound (n : ℕ) (e : PowerIndex n) (i : Fin n) :
    powerExponent n e i≤powerWeight n i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.cases ?_ (fun i => ?_) i
      · change e.1.val≤n+1-(0+1)
        have := e.1.isLt
        omega
      · change powerExponent n e.2 i≤powerWeight (n+1) i.succ
        rw [powerWeight_succ]
        exact ih e.2 i

lemma binaryPower_prod (t : R) (n : ℕ) (rs : Fin n → S) (e : PowerIndex n) :
    binaryPower t n rs e = ∏ i,(-rs i)^(powerExponent n e i)*
      (1+algebraMap R S t*rs i)^(powerWeight n i-powerExponent n e i) := by
  induction n with
  | zero => simp [binaryPower]
  | succ n ih =>
      rw [Fin.prod_univ_succ]
      simp only [powerExponent,Fin.cons_zero,Fin.cons_succ,powerWeight_succ]
      change _ = (-rs 0)^e.1.val*(1+algebraMap R S t*rs 0)^(n-e.1.val)*_
      rw [←ih]
      rfl

end Lech.UniversalSplitting

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootLineEuler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
namespace Lech.SplitPair
universe u v
variable (B : Type u) [CommRing B] {S : Type v} [CommRing S] [Algebra B S]

def left (x y : S) : S →ₗ[B] S × S where
  toFun c := (y*c,-(x*c))
  map_add' a b := by
    change (y*(a+b),-(x*(a+b)))=(y*a+y*b,-(x*a)+(-(x*b)))
    apply Prod.ext <;> dsimp only <;> ring
  map_smul' b c := by
    change (y*(b • c),-(x*(b • c)))=(b • (y*c),b • (-(x*c)))
    apply Prod.ext <;> dsimp only <;> simp only [Algebra.smul_def] <;> ring

def right (x y : S) : S × S →ₗ[B] S where
  toFun c := x*c.1+y*c.2
  map_add' a b := by simp only [Prod.fst_add,Prod.snd_add]; ring
  map_smul' b c := by
    change x*(b • c.1)+y*(b • c.2)=b • (x*c.1+y*c.2)
    simp only [Algebra.smul_def]
    ring

lemma left_injective (x y t : S) (h : y+t*x=1) : Function.Injective (left B x y) := by
  intro a b he
  have hy : y*a=y*b := congrArg Prod.fst he
  have hx : x*a=x*b := neg_injective (congrArg Prod.snd he)
  calc
    a = (y+t*x)*a := by rw [h,one_mul]
    _ = y*b+t*(x*b) := by rw [add_mul,mul_assoc,hy,hx]
    _ = b := by rw [←mul_assoc,←add_mul,h,one_mul]

lemma right_surjective (x y t : S) (h : y+t*x=1) : Function.Surjective (right B x y) := by
  intro c
  refine ⟨(t*c,c),?_⟩
  change x*(t*c)+y*c=c
  calc
    _ = (y+t*x)*c := by ring
    _ = c := by rw [h,one_mul]

lemma exact (x y t : S) (h : y+t*x=1) : Function.Exact (left B x y) (right B x y) := by
  intro c
  constructor
  · intro hc
    change x*c.1+y*c.2=0 at hc
    refine ⟨c.1-t*c.2,?_⟩
    apply Prod.ext
    · change y*(c.1-t*c.2)=c.1
      calc
        _ = (y+t*x)*c.1-t*(x*c.1+y*c.2) := by ring
        _ = c.1 := by rw [h,hc,one_mul,mul_zero,sub_zero]
    · change -(x*(c.1-t*c.2))=c.2
      calc
        _ = (y+t*x)*c.2-(x*c.1+y*c.2) := by ring
        _ = c.2 := by rw [h,hc,one_mul,sub_zero]
  · rintro ⟨a,rfl⟩
    change x*(y*a)+y*(-(x*a))=0
    ring
end Lech.SplitPair

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootPermutation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.ProductSourceCover
open AddMonoidAlgebra
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (σ : Equiv.Perm (Fin n))
def permuteWeight (m : Fin n → ℤ) : Fin n → ℤ := fun i => m (σ.symm i)

end Lech.ProductSourceCover

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootStripComplement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ProductSourceCover
open scoped BigOperators

def rootPrefix (n : ℕ) (r : Fin n → ℤ) (h s N : ℕ) : ℝ :=
  ∑ l∈Finset.range N,∏ j,((l:ℝ)-(h:ℝ)*(s:ℝ)-(r j:ℝ))

end Lech.ProductSourceCover

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootTowerRemainderExponent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPowerSeries
open scoped Classical
namespace Lech.RootTower
variable {σ R : Type*} [Fintype σ] [CommRing R] (q : ℕ) [NeZero q]


def Expanded (_q : ℕ) := MvPowerSeries σ R

end Lech.RootTower

open scoped TensorProduct
open IsLocalRing

open MvPowerSeries IsLocalRing
namespace Lech.RootTower
variable {σ k : Type*} [Fintype σ] [Field k]

variable (p n : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]

def FrobeniusExpanded (_p _n : ℕ) := MvPowerSeries σ k

end Lech.RootTower


end

end OAI
end


