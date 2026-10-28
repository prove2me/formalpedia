-- Prove2me | Definitions.Def_OAIQ032L028
-- name    : OAIQ032L028
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T20:42:04.369629+00:00
-- url     : https://prove2.me/theorems/6d56b423-8da0-40a1-87cb-d26a63bcbc75
-- title:
--   Definitions bundle OAIQ032L028 of the split of OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 148 declarations of OpenAI's Lean: 69 definitions, 2 instances and 77 theorems. The definitions and types are `OAI.Lech.FiniteModuleCech.reductionComplexIso`, `OAI.Lech.FiniteModuleCech.tensorShortComplex`, `OAI.Lech.ProductSourceCover.RationalMember`, `OAI.Lech.ProductSourceCover.cechCohomologyComparison`, `OAI.Lech.ProductSourceCover.cechNatCohomologyComparison`, `OAI.Lech.ProductSourceCover.chartScalar`, `OAI.Lech.ProductSourceCover.denominator`, `OAI.Lech.ProductSourceCover.embed`, `OAI.Lech.ProductSourceCover.fraction`, `OAI.Lech.ProductSourceCover.grid`, `OAI.Lech.ProductSourceCover.gridSourceUnaugmentedIso`, `OAI.Lech.ProductSourceCover.gridTarget`, `OAI.Lech.ProductSourceCover.gridUnaugmentedComparison`, `OAI.Lech.ProductSourceCover.locTarget`, `OAI.Lech.ProductSourceCover.localizedChart`, `OAI.Lech.ProductSourceCover.localizedChartA`, `OAI.Lech.ProductSourceCover.localizedLine`, `OAI.Lech.ProductSourceCover.rootCoordinate`, `OAI.Lech.ProductSourceCover.sectionAlgebra`, `OAI.Lech.ProductSourceCover.sectionModuleBase`, `OAI.Lech.ProductSourceCover.targetCech`, `OAI.Lech.ProductSourceCover.targetUnit`, `OAI.Lech.RootChartAtlas.algebraPoint`, `OAI.Lech.RootChartAtlas.chartRAlgebra`, `OAI.Lech.RootChartAtlas.chartToGrid`, `OAI.Lech.RootChartAtlas.chartToGridD`, `OAI.Lech.RootChartAtlas.equiv`, `OAI.Lech.RootChartAtlas.factorUnit`, `OAI.Lech.RootChartAtlas.fromH`, `OAI.Lech.RootChartAtlas.fromH_R`, `OAI.Lech.RootChartAtlas.globalCoefficient`, `OAI.Lech.RootChartAtlas.globalCoefficientA`, `OAI.Lech.RootChartAtlas.gridBasis`, `OAI.Lech.RootChartAtlas.gridCoefficient`, `OAI.Lech.RootChartAtlas.gridGlobalModule`, `OAI.Lech.RootChartAtlas.gridGlobalRoot`, `OAI.Lech.RootChartAtlas.gridInclusion`, `OAI.Lech.RootChartAtlas.gridLineRoot`, `OAI.Lech.RootChartAtlas.moduleRoot`, `OAI.Lech.RootChartAtlas.moduleTarget` and 29 more.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory/Multiplicity, in whole or in part: `Multiplicity_CechReduction`, `Multiplicity_GradedLineBasisHasBasis`, `Multiplicity_LechFactorizationMap`, `Multiplicity_LechHomogeneousEval`, `Multiplicity_LechSignedUnit`, `Multiplicity_ProductSourceCoverCechNat`, `Multiplicity_ProductSourceCoverHighThreshold`, `Multiplicity_ProductSourceCoverOrdinaryPositive`, `Multiplicity_RootChartAtlasGlobalCoefficient`, `Multiplicity_RootCoefficientEuler`, `Multiplicity_RootInvariantsWeightZero`, `Multiplicity_StandardFactorChartsL`, `Multiplicity_TensorCechEuler`, `Multiplicity_UniversalFactorMapMapChart`.
--
--   **Imports.** It imports the bundles `OAIQ032L024`, `OAIQ032L025` and `OAIQ032L026` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ032L030` and `OAIQ032L031`; the proof of `OAI.Lech.FiniteModuleCech.tensorEuler_copies`.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory/Multiplicity at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ032L024
import Definitions.Def_OAIQ032L025
import Definitions.Def_OAIQ032L026

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProductSourceCoverOrdinaryPositive
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
open AddMonoidAlgebra
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
abbrev denominator (s : Finset (Fin (n+1))) : Ambient R n := AwayCover.denominator (targetCoeff R n) s
def embed : Ambient R n →ₐ[R] GridAmbient R n := IsScalarTower.toAlgHom R (Ambient R n) (GridAmbient R n)
lemma denom_regular (s : Finset (Fin (n+1))) : IsRegular (denominator R n s) :=
  IsRegular.prod (fun i _ => ProductLaurent.binaryForm_coefficient_regular R n i)
lemma embed_injective : Function.Injective (embed R n) := by
  apply IsLocalization.injectiveₛ (M:=Submonoid.powers (denominator R n Finset.univ))
  rintro _ ⟨N,rfl⟩
  exact (denom_regular R n Finset.univ).pow N
lemma denominator_unit (s : Finset (Fin (n+1))) : IsUnit (embed R n (denominator R n s)) :=
  IsLocalization.Away.isUnit_of_dvd (denominator R n Finset.univ)
    (AwayCover.denominator_dvd (targetCoeff R n) (Finset.subset_univ s))


def RationalMember (m : Fin n → ℤ) (s : Finset (Fin (n+1))) (t : Finset (Chart n))
    (x : GridAmbient R n) : Prop :=
  ∃ N : ℕ,∃ h : Ambient R n,h∈ringSections R n (levelTwist n m s.card N) t ∧
    embed R n (denominator R n s)^N*x=embed R n h
lemma raise_witness (m : Fin n → ℤ) (s : Finset (Fin (n+1))) (t : Finset (Chart n))
    (x : GridAmbient R n) (N M : ℕ) (hNM : N≤M) (h : Ambient R n)
    (hh : h∈ringSections R n (levelTwist n m s.card N) t)
    (he : embed R n (denominator R n s)^N*x=embed R n h) :
    ∃ g : Ambient R n,g∈ringSections R n (levelTwist n m s.card M) t ∧
      embed R n (denominator R n s)^M*x=embed R n g := by
  obtain ⟨K,rfl⟩ := Nat.exists_eq_add_of_le hNM
  refine ⟨denominator R n s^K*h,multiply_level R n m s.card N K t _ h (coefficient_product_mem R n s) hh,?_⟩
  rw [map_mul,map_pow,pow_add,mul_right_comm,he]
  exact mul_comm _ _
def grid (m : Fin n → ℤ) (s : Finset (Fin (n+1))) (t : Finset (Chart n)) :
    Submodule R (GridAmbient R n) where
  carrier := RationalMember R n m s t
  zero_mem' := ⟨0,0,(ringSections R n _ _).zero_mem,by simp⟩
  add_mem' := by
    rintro x y ⟨N,h,hh,he⟩ ⟨M,k,hk,hke⟩
    obtain ⟨h',hh',he'⟩ := raise_witness R n m s t x N (N+M) (by omega) h hh he
    obtain ⟨k',hk',hke'⟩ := raise_witness R n m s t y M (N+M) (by omega) k hk hke
    exact ⟨N+M,h'+k',(ringSections R n _ _).add_mem hh' hk',by rw [mul_add,he',hke',map_add]⟩
  smul_mem' := by
    rintro r x ⟨N,h,hh,he⟩
    refine ⟨N,r • h,(ringSections R n _ _).smul_mem r hh,?_⟩
    rw [map_smul,mul_smul_comm,he]
lemma grid_source_mono (m : Fin n → ℤ) (s : Finset (Fin (n+1))) : Monotone (grid R n m s) := by
  intro t v htv x hx
  obtain ⟨N,h,hh,he⟩ := hx
  exact ⟨N,h,ringSections_mono R n _ htv hh,he⟩
lemma grid_target_mono (m : Fin n → ℤ) (t : Finset (Chart n)) : Monotone (fun s => grid R n m s t) := by
  intro s v hsv x hx
  obtain ⟨N,h,hh,he⟩ := hx
  let r := denominator R n (v\s)
  have hv : denominator R n v=r*denominator R n s := (Finset.prod_sdiff hsv).symm
  refine ⟨N,r^N*h,?_,?_⟩
  · have hr : r∈ringSections R n (fun _ => ((v\s).card:ℤ)) t :=
      ringSections_mono R n _ (Finset.empty_subset t) (coefficient_product_mem R n (v\s))
    have hp := mul_mem R n (N • fun _ => ((v\s).card:ℤ)) (levelTwist n m s.card N) t
      (r^N) h (pow_mem R n _ t r hr N) hh
    have hc : (v\s).card+s.card=v.card := Finset.card_sdiff_add_card_eq_card hsv
    have hc' : ((v\s).card:ℤ)+(s.card:ℤ)=(v.card:ℤ) := by exact_mod_cast hc
    have ht : (N • fun _ : Fin n => ((v\s).card:ℤ))+levelTwist n m s.card N=levelTwist n m v.card N := by
      ext i
      change (N • ((v\s).card:ℤ))+(m i+(N:ℤ)*(s.card:ℤ))=m i+(N:ℤ)*(v.card:ℤ)
      rw [nsmul_eq_mul,←hc']
      ring
    rwa [ht] at hp
  · rw [hv,map_mul,mul_pow,map_mul,map_pow,mul_assoc,he]
end Lech.ProductSourceCover
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProductSourceCoverHighThreshold
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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

def fraction (s : Finset (Fin (n+1))) (N : ℕ) : Ambient R n →ₗ[R] GridAmbient R n :=
  (LinearMap.mulLeft R ((↑((denominator_unit R n s).unit⁻¹):GridAmbient R n)^N)).comp (embed R n).toLinearMap
lemma fraction_spec (s : Finset (Fin (n+1))) (N : ℕ) (h : Ambient R n) :
    embed R n (denominator R n s)^N*fraction R n s N h=embed R n h := by
  change embed R n (denominator R n s)^N*((↑((denominator_unit R n s).unit⁻¹):GridAmbient R n)^N*embed R n h)=_
  have hu : embed R n (denominator R n s)*(↑((denominator_unit R n s).unit⁻¹):GridAmbient R n)=1 := by
    simpa only [IsUnit.unit_spec] using Units.mul_inv (denominator_unit R n s).unit
  rw [←mul_assoc,←mul_pow,hu,one_pow,one_mul]
lemma uniform_witness (m : Fin n → ℤ) (s : Finset (Fin (n+1))) (p : ℕ)
    (f : AlternatingCech.sorted R (GridAmbient R n) (grid R n m s) p) :
    ∃ N : ℕ,highThreshold n m≤N ∧
      ∃ h : AlternatingCech.sorted R (Ambient R n) (ringSections R n (levelTwist n m s.card N)) p,
      ∀ t,embed R n (denominator R n s)^N*(f t:GridAmbient R n)=embed R n (h t) := by
  have hf : ∀ t : powersetCard (Chart n) p,∃ N : ℕ,∃ h : Ambient R n,
      h∈ringSections R n (levelTwist n m s.card N) t.val ∧
      embed R n (denominator R n s)^N*(f t:GridAmbient R n)=embed R n h := fun t => (f t).property
  choose N h hh he using hf
  let M := max (highThreshold n m) (Finset.univ.sup N)
  have hNM (t : powersetCard (Chart n) p) : N t≤M :=
    (Finset.le_sup (f:=N) (Finset.mem_univ t)).trans (le_max_right _ _)
  have hraise (t : powersetCard (Chart n) p) := raise_witness R n m s t.val (f t) (N t) M (hNM t) (h t) (hh t) (he t)
  choose H hH heH using hraise
  exact ⟨M,le_max_left _ _,fun t => ⟨H t,hH t⟩,heH⟩
variable [LinearOrder (Chart n)]


attribute [local instance] OAI.Lech.ProductSourceCover.gridSourceDecEq
lemma grid_source_exact (m : Fin n → ℤ) (s : Finset (Fin (n+1))) (hs : s.Nonempty)
    (p : ℕ) (f : AlternatingCech.sorted R (GridAmbient R n) (grid R n m s) (p+1))
    (hf : AlternatingCech.sortedDelta R (GridAmbient R n) (grid R n m s) (grid_source_mono R n m s) (p+1) f=0) :
    ∃ g : AlternatingCech.sorted R (GridAmbient R n) (grid R n m s) p,
      AlternatingCech.sortedDelta R (GridAmbient R n) (grid R n m s) (grid_source_mono R n m s) p g=f := by
  obtain ⟨N,hN,h,he⟩ := uniform_witness R n m s (p+1) f
  let T := levelTwist n m s.card N
  let Q := embed R n (denominator R n s)^N
  have hT : ∀ i,-1≤T i := level_high n m s.card N (Finset.card_pos.mpr hs) hN
  have hcycled : AlternatingCech.sortedDelta R (Ambient R n) (ringSections R n T) (ringSections_mono R n T) (p+1) h=0 := by
    have he' : (fun t => (embed R n).toLinearMap (h t))=(fun t => (LinearMap.mulLeft R Q) (f t:GridAmbient R n)) :=
      funext (fun t => (he t).symm)
    have hd := congrArg (AlternatingCech.rawDelta R (GridAmbient R n) (p+1)) he'
    rw [AlternatingCech.rawDelta_post,AlternatingCech.rawDelta_post,
      AlternatingCech.rawDelta_sorted R (Ambient R n) (ringSections R n T) (ringSections_mono R n T),
      AlternatingCech.rawDelta_sorted R (GridAmbient R n) (grid R n m s) (grid_source_mono R n m s),hf] at hd
    funext t
    apply Subtype.ext
    apply embed_injective R n
    simpa only [Pi.zero_apply,Submodule.coe_zero,map_zero,AlgHom.toLinearMap_apply] using congrFun hd t
  let C := AlternatingCech.sortedComplex R (Ambient R n) (ringSections R n T) (ringSections_mono R n T)
  have hc := (C.exactAt_iff' (i:=p) (j:=p+1) (k:=p+2) (by simp) (by simp)).mp (ring_sorted_acyclic R n T hT (p+1))
  rw [ShortComplex.moduleCat_exact_iff] at hc
  obtain ⟨g,hg⟩ := hc h (by
    change (C.d (p+1) (p+2)).hom h=0
    rw [AlternatingCech.sortedComplex_d]
    exact hcycled)
  change (C.d p (p+1)).hom g=h at hg
  rw [AlternatingCech.sortedComplex_d] at hg
  change AlternatingCech.sorted R (Ambient R n) (ringSections R n T) p at g
  change AlternatingCech.sortedDelta R (Ambient R n) (ringSections R n T) (ringSections_mono R n T) p g=h at hg
  let G : AlternatingCech.sorted R (GridAmbient R n) (grid R n m s) p := fun t =>
    ⟨fraction R n s N (g t),N,(g t:Ambient R n),(g t).property,fraction_spec R n s N (g t)⟩
  refine ⟨G,?_⟩
  have hd : (fun t => (AlternatingCech.sortedDelta R (GridAmbient R n) (grid R n m s) (grid_source_mono R n m s) p G t:GridAmbient R n))=
      (fun t => fraction R n s N (h t)) := by
    rw [←AlternatingCech.rawDelta_sorted]
    change AlternatingCech.rawDelta R (GridAmbient R n) p (fun t => fraction R n s N (g t))=_
    rw [AlternatingCech.rawDelta_post,AlternatingCech.rawDelta_sorted R (Ambient R n) (ringSections R n T) (ringSections_mono R n T),hg]
  funext t
  apply Subtype.ext
  apply ((denominator_unit R n s).pow N).isRegular.left
  change embed R n (denominator R n s)^N*_ = embed R n (denominator R n s)^N*_
  rw [congrFun hd t,fraction_spec,he t]

 

theorem grid_source_acyclic (m : Fin n → ℤ) (s : Finset (Fin (n+1))) (hs : s.Nonempty) :
    (AlternatingCech.sortedComplex R (GridAmbient R n) (grid R n m s) (grid_source_mono R n m s)).Acyclic := by
  intro p
  cases p with
  | zero =>
    apply (AlternatingCech.complex_exactAt_zero_of_nonempty R (GridAmbient R n) (grid R n m s) (grid_source_mono R n m s)).of_iso
    convert AlternatingCech.cochainsSortedIso R (GridAmbient R n) (grid R n m s) (grid_source_mono R n m s) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
  | succ p =>
    apply ((AlternatingCech.sortedComplex R (GridAmbient R n) (grid R n m s) (grid_source_mono R n m s)).exactAt_iff'
      (i:=p) (j:=p+1) (k:=p+2) (by simp) (by simp)).mpr
    rw [ShortComplex.moduleCat_exact_iff]
    intro f hf
    change ((AlternatingCech.sortedComplex R (GridAmbient R n) (grid R n m s) (grid_source_mono R n m s)).d (p+1) (p+2)).hom f=0 at hf
    rw [AlternatingCech.sortedComplex_d] at hf
    obtain ⟨g,hg⟩ := grid_source_exact R n m s hs p f hf
    refine ⟨g,?_⟩
    change ((AlternatingCech.sortedComplex R (GridAmbient R n) (grid R n m s) (grid_source_mono R n m s)).d p (p+1)).hom g=f
    rw [AlternatingCech.sortedComplex_d]
    exact hg
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open AddMonoidAlgebra CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (n : ℕ)

def chartScalar (σ : Chart n) : ProductLinearChart.Ring R n →ₐ[R] GridAmbient R n :=
  (embed R n).comp (ProductLaurent.chartMap R n σ)
lemma grid_chart_stable (m : Fin n → ℤ) (t : Finset (Chart n)) (σ : Chart n) (hσ : σ∈t)
    (s : Finset (Fin (n+1))) (a : ProductLinearChart.Ring R n) (x : GridAmbient R n)
    (hx : x∈grid R n m s t) : chartScalar R n σ a*x∈grid R n m s t := by
  obtain ⟨N,h,hh,he⟩ := hx
  refine ⟨N,ProductLaurent.chartMap R n σ a*h,?_,?_⟩
  · have ha := ringSections_mono R n 0 (Finset.singleton_subset_iff.mpr hσ) (chartMap_zero_section R n σ a)
    simpa only [zero_add] using mul_mem R n 0 (levelTwist n m s.card N) t _ h ha hh
  · change embed R n (denominator R n s)^N*(embed R n (ProductLaurent.chartMap R n σ a)*x)=_
    rw [mul_left_comm,he,map_mul]
lemma grid_target_clear (m : Fin n → ℤ) (t : Finset (Chart n)) (σ : Chart n) (hσ : σ∈t)
    (s : Finset (Fin (n+1))) (k : Fin (n+1)) (x : GridAmbient R n)
    (hx : x∈grid R n m (insert k s) t) :
    ∃ N : ℕ,chartScalar R n σ ((ProductLinearChart.product R n σ).coeff k)^N*x∈grid R n m s t := by
  by_cases hk : k∈s
  · refine ⟨0,?_⟩
    simpa only [pow_zero,one_mul,Finset.insert_eq_of_mem hk] using hx
  obtain ⟨N,h,hh,he⟩ := hx
  let u : Ambient R n := ↑((ProductLaurent.chartUnit R n σ)⁻¹)
  have hu : u^N∈ringSections R n (N • fun _ => (-1:ℤ)) t :=
    pow_mem R n (fun _ => (-1:ℤ)) t u (ringSections_mono R n _ (Finset.singleton_subset_iff.mpr hσ) (chartUnit_inv_section R n σ)) N
  have ht : (N • fun _ : Fin n => (-1:ℤ))+levelTwist n m (insert k s).card N=levelTwist n m s.card N := by
    ext i
    change (N • (-1:ℤ))+(m i+(N:ℤ)*((insert k s).card:ℤ))=m i+(N:ℤ)*(s.card:ℤ)
    rw [Finset.card_insert_of_notMem hk,Nat.cast_add,Nat.cast_one,nsmul_eq_mul]
    ring
  refine ⟨N,N,u^N*h,?_,?_⟩
  · have hb := mul_mem R n (N • fun _ => (-1:ℤ)) (levelTwist n m (insert k s).card N) t (u^N) h hu hh
    rwa [ht] at hb
  · have hc : chartScalar R n σ ((ProductLinearChart.product R n σ).coeff k)=embed R n u*embed R n (targetCoeff R n k) := by
      change embed R n (ProductLaurent.chartMap R n σ ((ProductLinearChart.product R n σ).coeff k))=_
      rw [ProductLaurent.chartMap_coefficient,map_mul]
    have hd : denominator R n (insert k s)=targetCoeff R n k*denominator R n s := Finset.prod_insert hk
    rw [hc,mul_pow,map_mul,map_pow]
    calc
      _ = embed R n u^N*(embed R n (denominator R n (insert k s))^N*x) := by rw [hd,map_mul,mul_pow];ring
      _ = _ := by rw [he]

 

theorem grid_target_acyclic (m : Fin n → ℤ) (t : Finset (Chart n)) (ht : t.Nonempty) :
    (AlternatingCech.sortedComplex R (GridAmbient R n) (fun s => grid R n m s t) (grid_target_mono R n m t)).Acyclic := by
  obtain ⟨σ,hσ⟩ := ht
  intro j
  have h := AlternatingCech.scalar_complex_acyclic R (GridAmbient R n) (fun s => grid R n m s t)
    (ProductLinearChart.Ring R n) (chartScalar R n σ) (grid_chart_stable R n m t σ hσ)
    (fun k : Fin (n+1) => (ProductLinearChart.product R n σ).coeff k)
    (ProductLinearChart.coefficients_span R n σ) (grid_target_clear R n m t σ hσ) (grid_target_mono R n m t) j
  apply h.of_iso
  convert AlternatingCech.cochainsSortedIso R (GridAmbient R n) (fun s => grid R n m s t) (grid_target_mono R n m t) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
lemma grid_empty_target (m : Fin n → ℤ) (t : Finset (Chart n)) :
    (ringSections R n m t).map (embed R n).toLinearMap=grid R n m ∅ t := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    refine ⟨0,x,?_,?_⟩
    · have ht : levelTwist n m (∅ : Finset (Fin (n+1))).card 0=m := by ext i;simp [levelTwist]
      exact ht.symm ▸ hx
    · simp only [pow_zero,one_mul,AlgHom.toLinearMap_apply]
  · rintro x ⟨N,h,hh,he⟩
    simp only [denominator,AwayCover.denominator,Finset.prod_empty,map_one,one_pow,one_mul] at he
    refine ⟨h,?_,?_⟩
    · have ht : levelTwist n m (∅ : Finset (Fin (n+1))).card N=m := by ext i;simp [levelTwist]
      exact ht ▸ hh
    · simpa only [AlgHom.toLinearMap_apply] using he.symm
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [LinearOrder (Chart n)]


def targetCech (m : Fin n → ℤ) : CochainComplex (ModuleCat.{u} R) ℕ :=
  AlternatingCech.unaugmentedComplex R (GridAmbient R n) (fun s => grid R n m s ∅) (grid_target_mono R n m ∅)
def gridSourceUnaugmentedIso (m : Fin n → ℤ) : sourceCech R n m ≅
    AlternatingCech.unaugmentedComplex R (GridAmbient R n) (grid R n m ∅) (grid_source_mono R n m ∅) :=
  AlternatingCech.sortedUnaugmentedFamilyIso R (Ambient R n) (GridAmbient R n)
    (ringSections R n m) (grid R n m ∅) (embed R n).toLinearMap (embed_injective R n)
    (grid_empty_target R n m) (ringSections_mono R n m) (grid_source_mono R n m ∅)
def gridUnaugmentedComparison (m : Fin n → ℤ) (i : ℤ) :
    ((AlternatingCech.unaugmentedComplex R (GridAmbient R n) (grid R n m ∅) (grid_source_mono R n m ∅)).extend ComplexShape.embeddingUpNat).homology i ≅
      ((targetCech R n m).extend ComplexShape.embeddingUpNat).homology i :=
  DoubleCech.unaugmentedCoverComparison R (GridAmbient R n) (grid R n m)
    (grid_target_mono R n m) (grid_source_mono R n m)
    (fun _p hp s => grid_source_acyclic R n m s.val (Finset.card_pos.mp (s.property.symm ▸ hp)))
    (fun _q hq t => grid_target_acyclic R n m t.val (Finset.card_pos.mp (t.property.symm ▸ hq))) i
 

def cechCohomologyComparison (m : Fin n → ℤ) (i : ℤ) :
    ((sourceCech R n m).extend ComplexShape.embeddingUpNat).homology i ≅
      ((targetCech R n m).extend ComplexShape.embeddingUpNat).homology i :=
  (homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).mapIso
    ((ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).mapIso (gridSourceUnaugmentedIso R n m)) ≪≫
    gridUnaugmentedComparison R n m i
end Lech.ProductSourceCover
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProductSourceCoverCechNat
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [LinearOrder (Chart n)]
 

def cechNatCohomologyComparison (m : Fin n → ℤ) (q : ℕ) :
    (sourceCech R n m).homology q ≅ (targetCech R n m).homology q :=
  ((sourceCech R n m).extendHomologyIso ComplexShape.embeddingUpNat (j:=q) (j':=(q:ℤ)) rfl).symm ≪≫
    cechCohomologyComparison R n m (q:ℤ) ≪≫
    (targetCech R n m).extendHomologyIso ComplexShape.embeddingUpNat (j:=q) (j':=(q:ℤ)) rfl


end


open scoped BigOperators Classical
end Lech.ProductSourceCover


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechHomogeneousEval
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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

section
open AddMonoidAlgebra
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
lemma chartScalar_coefficient_unit (σ : Chart n) (k : Fin (n+1)) :
    IsUnit (chartScalar R n σ ((ProductLinearChart.product R n σ).coeff k)) := by
  change IsUnit (embed R n (ProductLaurent.chartMap R n σ _))
  rw [ProductLaurent.chartMap_coefficient,map_mul]
  apply IsUnit.mul
  · exact (Units.isUnit ((ProductLaurent.chartUnit R n σ)⁻¹)).map (embed R n)
  · simpa only [denominator,AwayCover.denominator,Finset.prod_singleton] using denominator_unit R n {k}
 

def localizedChart (σ : Chart n) (k : Fin (n+1)) :
    ProductLinearChart.chart R n σ k →ₐ[R] GridAmbient R n :=
  IsLocalization.Away.liftAlgHom ((ProductLinearChart.product R n σ).coeff k)
    (chartScalar_coefficient_unit R n σ k)
lemma localizedChart_algebraMap (σ : Chart n) (k : Fin (n+1)) (a : ProductLinearChart.Ring R n) :
    localizedChart R n σ k (algebraMap (ProductLinearChart.Ring R n) (ProductLinearChart.chart R n σ k) a)=
      chartScalar R n σ a := IsLocalization.Away.lift_eq _ (chartScalar_coefficient_unit R n σ k) _
lemma chartScalar_injective (σ : Chart n) : Function.Injective (chartScalar R n σ) :=
  (embed_injective R n).comp (ProductLaurent.chartMap_injective R n σ)

def localizedLine (m : Fin n → ℤ) (σ : Chart n) (k : Fin (n+1)) :
    ProductLinearChart.chart R n σ k →ₗ[R] GridAmbient R n :=
  (LinearMap.mulLeft R (embed R n (ProductLaurent.monomialUnit R n (twistExponent n m σ):Ambient R n))).comp
    (localizedChart R n σ k).toLinearMap
lemma localizedLine_apply (m : Fin n → ℤ) (σ : Chart n) (k : Fin (n+1))
    (z : ProductLinearChart.chart R n σ k) :
    localizedLine R n m σ k z=embed R n (ProductLaurent.monomialUnit R n (twistExponent n m σ):Ambient R n)*
      localizedChart R n σ k z := rfl
lemma targetCoeff_chart (σ : Chart n) (k : Fin (n+1)) :
    embed R n (targetCoeff R n k)=embed R n (ProductLaurent.chartUnit R n σ:Ambient R n)*
      chartScalar R n σ ((ProductLinearChart.product R n σ).coeff k) := by
  change _=embed R n _ * embed R n (ProductLaurent.chartMap R n σ _)
  rw [ProductLaurent.chartMap_coefficient,map_mul,←mul_assoc,←map_mul,Units.mul_inv,map_one,one_mul]
lemma localizedLine_mem (m : Fin n → ℤ) (σ : Chart n) (k : Fin (n+1))
    (z : ProductLinearChart.chart R n σ k) : localizedLine R n m σ k z∈grid R n m {k} {σ} := by
  obtain ⟨N,a,ha⟩ := IsLocalization.Away.surj ((ProductLinearChart.product R n σ).coeff k) z
  have ha' := congrArg (localizedChart R n σ k) ha
  simp only [map_mul,map_pow,localizedChart_algebraMap] at ha'
  refine ⟨N,chartLine R n (levelTwist n m 1 N) σ a,?_,?_⟩
  · simpa only [Finset.card_singleton] using chartLine_mem R n (levelTwist n m 1 N) σ a
  · simp only [denominator,AwayCover.denominator,Finset.prod_singleton]
    rw [targetCoeff_chart R n σ k,mul_pow,
      localizedLine_apply,chartLine_level,map_mul,map_pow]
    simp only [chartLine,LinearMap.comp_apply,LinearMap.mulLeft_apply,AlgHom.toLinearMap_apply,map_mul]
    change _=embed R n (ProductLaurent.chartUnit R n σ:Ambient R n)^N*
      (embed R n ((ProductLaurent.monomialUnit R n (twistExponent n m σ)):Ambient R n)*chartScalar R n σ a)
    rw [←ha']
    ring


theorem localizedLine_range (m : Fin n → ℤ) (σ : Chart n) (k : Fin (n+1)) :
    (localizedLine R n m σ k).range=grid R n m {k} {σ} := by
  apply le_antisymm
  · rintro _ ⟨z,rfl⟩;exact localizedLine_mem R n m σ k z
  · intro x hx
    obtain ⟨N,h,hh,he⟩ := hx
    simp only [Finset.card_singleton] at hh
    obtain ⟨a,rfl⟩ := (show h∈(chartLine R n (levelTwist n m 1 N) σ).range from
      (chartLine_range R n (levelTwist n m 1 N) σ).symm ▸ hh)
    let z : ProductLinearChart.chart R n σ k :=
      algebraMap (ProductLinearChart.Ring R n) _ a * (↑((ProductLinearChart.denominator R n σ k)⁻¹))^N
    have hz : z*(algebraMap (ProductLinearChart.Ring R n) (ProductLinearChart.chart R n σ k)
        ((ProductLinearChart.product R n σ).coeff k))^N=algebraMap (ProductLinearChart.Ring R n) _ a := by
      dsimp only [z]
      rw [←ProductLinearChart.denominator_val,mul_assoc,←mul_pow,Units.inv_mul,one_pow,mul_one]
    have hz' := congrArg (localizedChart R n σ k) hz
    simp only [map_mul,map_pow,localizedChart_algebraMap] at hz'
    refine ⟨z,?_⟩
    apply ((denominator_unit R n {k}).pow N).mul_left_cancel
    rw [he]
    simp only [denominator,AwayCover.denominator,Finset.prod_singleton]
    rw [targetCoeff_chart R n σ k,mul_pow,localizedLine_apply,chartLine_level,map_mul,map_pow]
    simp only [chartLine,LinearMap.comp_apply,LinearMap.mulLeft_apply,AlgHom.toLinearMap_apply,map_mul,map_pow]
    change _=embed R n (ProductLaurent.chartUnit R n σ:Ambient R n)^N*
      (embed R n ((ProductLaurent.monomialUnit R n (twistExponent n m σ)):Ambient R n)*chartScalar R n σ a)
    rw [←hz']
    simp only [z,map_mul,map_pow]
    ring

end


open Polynomial
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
def targetUnit (k : Fin (n+1)) : (GridAmbient R n)ˣ := (denominator_unit R n {k}).unit
lemma targetUnit_val (k : Fin (n+1)) :
    (targetUnit R n k:GridAmbient R n)=embed R n (targetCoeff R n k) := by
  simpa only [targetUnit,denominator,AwayCover.denominator,Finset.prod_singleton] using
    (denominator_unit R n {k}).unit_spec
 
def gridTarget (k : Fin (n+1)) : UniversalCoefficientChart.Ring R n k →ₐ[R] GridAmbient R n :=
  UniversalCoefficientChart.eval R n k (fun j => (↑((targetUnit R n k)⁻¹):GridAmbient R n)*embed R n (targetCoeff R n j))
lemma gridTarget_coefficient (k j : Fin (n+1)) :
    gridTarget R n k (UniversalCoefficientChart.coefficient R n k j)=
      (↑((targetUnit R n k)⁻¹):GridAmbient R n)*embed R n (targetCoeff R n j) := by
  apply UniversalCoefficientChart.eval_coefficient
  rw [←targetUnit_val,Units.inv_mul]
lemma targetUnit_chart (σ : Chart n) (k : Fin (n+1)) :
    targetUnit R n k=Units.map (embed R n).toMonoidHom (ProductLaurent.chartUnit R n σ)*
      Units.map (localizedChart R n σ k).toMonoidHom (ProductLinearChart.denominator R n σ k) := by
  apply Units.ext
  change (targetUnit R n k:GridAmbient R n)=embed R n (ProductLaurent.chartUnit R n σ:Ambient R n)*
    localizedChart R n σ k (ProductLinearChart.denominator R n σ k:ProductLinearChart.chart R n σ k)
  rw [targetUnit_val,ProductLinearChart.denominator_val,localizedChart_algebraMap]
  exact targetCoeff_chart R n σ k


theorem localizedChart_target (σ : Chart n) (k : Fin (n+1)) :
    (localizedChart R n σ k).comp (ProductLinearChart.target R n σ k)=gridTarget R n k := by
  apply UniversalCoefficientChart.ext
  intro j
  rw [gridTarget_coefficient,AlgHom.comp_apply]
  change localizedChart R n σ k (UniversalCoefficientChart.eval R n k
    (fun j => (ProductLinearChart.normalized R n σ k).coeff j)
    (UniversalCoefficientChart.coefficient R n k j))=_
  rw [UniversalCoefficientChart.eval_coefficient _ _ _ _ (ProductLinearChart.normalized_self R n σ k),
    ProductLinearChart.normalized,coeff_C_mul,coeff_map,map_mul,localizedChart_algebraMap,
    targetUnit_chart R n σ k,targetCoeff_chart R n σ j]
  exact (ratio_rescale (Units.map (embed R n).toMonoidHom (ProductLaurent.chartUnit R n σ))
    (Units.map (localizedChart R n σ k).toMonoidHom (ProductLinearChart.denominator R n σ k))
    (chartScalar R n σ ((ProductLinearChart.product R n σ).coeff j))).symm
instance gridTargetAlgebra (k : Fin (n+1)) : Algebra (UniversalCoefficientChart.Ring R n k) (GridAmbient R n) :=
  (gridTarget R n k).toRingHom.toAlgebra

def localizedChartA (σ : Chart n) (k : Fin (n+1)) :
    ProductLinearChart.chart R n σ k →ₐ[UniversalCoefficientChart.Ring R n k] GridAmbient R n where
  toRingHom := (localizedChart R n σ k).toRingHom
  commutes' a := AlgHom.congr_fun (localizedChart_target R n σ k) a
end


universe u
variable (R : Type u) [CommRing R] (n : ℕ)
lemma grid_mul_mem (m l : Fin n → ℤ) (s : Finset (Fin (n+1))) (t : Finset (Chart n))
    (x y : GridAmbient R n) (hx : x∈grid R n m s t) (hy : y∈grid R n l s t) :
    x*y∈grid R n (m+l) s t := by
  obtain ⟨N,h,hh,he⟩ := hx
  obtain ⟨M,g,hg,hge⟩ := hy
  refine ⟨N+M,h*g,?_,?_⟩
  · have ht : levelTwist n m s.card N+levelTwist n l s.card M=levelTwist n (m+l) s.card (N+M) := by
      ext i
      simp only [levelTwist,Pi.add_apply,Nat.cast_add]
      ring
    rw [←ht]
    exact mul_mem R n _ _ t h g hh hg
  · rw [map_mul,pow_add]
    calc
      _ = (embed R n (denominator R n s)^N*x)*(embed R n (denominator R n s)^M*y) := by ring
      _ = _ := by rw [he,hge]
end Lech.ProductSourceCover


namespace Lech.UniversalSplitting
open Polynomial
universe u

attribute [instance] Data.ring Data.algebra


end Lech.UniversalSplitting

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootInvariantsWeightZero
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.RootInvariants

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


section
open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))


attribute [local instance] OAI.Lech.RootInvariants.weightZeroOverAlgebra
attribute [local instance] OAI.Lech.RootInvariants.weightZeroOverScalarTower
def lineBaseMap (ms : Fin n → ℤ) :
    d.S ⊗[algebra f n hn t v hv d] overAlgebra f n hn t v hv d ms →ₗ[d.S] d.S :=
  (overAlgebra f n hn t v hv d ms).subtype.liftBaseChange d.S


def lineBaseSourceEquiv [Module.Flat A B] (ms : Fin n → ℤ) :
    d.S ⊗[algebra f n hn t v hv d] overAlgebra f n hn t v hv d ms ≃ₗ[A]
      B ⊗[A] module f n hn t v hv d ms :=
  (((TensorProduct.congr (algebraTensorEquivRight f n hn t v hv d).symm.toLinearEquiv
      (LinearEquiv.refl _ _)) ≪≫ₗ
    (TensorProduct.AlgebraTensorModule.rightComm A (algebra f n hn t v hv d)
      (algebra f n hn t v hv d) (algebra f n hn t v hv d) (overAlgebra f n hn t v hv d ms) B).symm ≪≫ₗ
    TensorProduct.AlgebraTensorModule.congr (TensorProduct.lid _ _) (LinearEquiv.refl A B)).restrictScalars A) ≪≫ₗ
    TensorProduct.comm A _ B ≪≫ₗ
    TensorProduct.congr (LinearEquiv.refl A B) (overAlgebraEquiv f n hn t v hv d ms)

lemma lineBaseSourceEquiv_symm_tmul [Module.Flat A B] (ms : Fin n → ℤ)
    (b : B) (x : module f n hn t v hv d ms) :
    (lineBaseSourceEquiv f n hn t v hv d ms).symm (b ⊗ₜ[A] x)=
      algebraMap B d.S b ⊗ₜ[algebra f n hn t v hv d]
        (overAlgebraEquiv f n hn t v hv d ms).symm x := by
  simp [lineBaseSourceEquiv,algebraTensorEquivRight,algebraBaseMapRight]

lemma lineBaseMap_comp [Module.Flat A B] (ms : Fin n → ℤ) :
    ((lineBaseMap f n hn t v hv d ms).restrictScalars A).comp
      (lineBaseSourceEquiv f n hn t v hv d ms).symm.toLinearMap=
        (tensorEquiv f n hn t v hv d ms).toLinearMap.restrictScalars A := by
  ext b x
  change (lineBaseMap f n hn t v hv d ms)
    ((lineBaseSourceEquiv f n hn t v hv d ms).symm (b ⊗ₜ[A] x))=
      (tensorEquiv f n hn t v hv d ms) (b ⊗ₜ[A] x)
  rw [lineBaseSourceEquiv_symm_tmul]
  change algebraMap B d.S b*(x:d.S)=b • (x:d.S)
  exact (Algebra.smul_def b (x:d.S)).symm

def lineTensorEquiv [Module.Flat A B] (ms : Fin n → ℤ) :
    d.S ⊗[algebra f n hn t v hv d] overAlgebra f n hn t v hv d ms ≃ₗ[d.S] d.S :=
  LinearEquiv.ofBijective (lineBaseMap f n hn t v hv d ms) (by
    have h : (lineBaseMap f n hn t v hv d ms).restrictScalars A=
        ((tensorEquiv f n hn t v hv d ms).toLinearMap.restrictScalars A).comp
          (lineBaseSourceEquiv f n hn t v hv d ms).toLinearMap := by
      have h := congrArg (fun l => l.comp (lineBaseSourceEquiv f n hn t v hv d ms).toLinearMap)
        (lineBaseMap_comp f n hn t v hv d ms)
      simpa only [LinearMap.comp_assoc,LinearEquiv.comp_coe,LinearEquiv.self_trans_symm,
        LinearEquiv.refl_toLinearMap,LinearMap.comp_id] using h
    change Function.Bijective ((lineBaseMap f n hn t v hv d ms).restrictScalars A)
    rw [h]
    exact (tensorEquiv f n hn t v hv d ms).bijective.comp
      (lineBaseSourceEquiv f n hn t v hv d ms).bijective)
end


section
open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))


attribute [local instance] OAI.Lech.RootInvariants.weightZeroDiagonalAlgebra
local instance weightZeroDiagonalScalarTower_r8684fc_1 : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl
def diagonalSection : overAlgebra f n hn t v hv d (fun _ => (1:ℤ)) :=
  ⟨algebraMap B d.S (v⁻¹:Bˣ),by
    change (RootCoaction.weight f n hn t v hv d (fun _ => (1:ℤ)) : RootCoaction.T f n t v d)*
      RootCoaction.hom f n hn t v hv d (algebraMap B d.S (v⁻¹:Bˣ))=
        RootCoaction.right f n t v d (algebraMap B d.S (v⁻¹:Bˣ))
    rw [AlgHom.commutes]
    have hu := leftUnit_eq f n hn t v hv d
    have he : RootCoaction.weight f n hn t v hv d (fun _ => (1:ℤ))*
        (Units.map (algebraMap B (RootCoaction.T f n t v d)).toMonoidHom v)⁻¹=
          (RootCoaction.unit f n t v d)⁻¹ := by
      rw [hu,mul_inv_rev,← mul_assoc,mul_inv_cancel,one_mul]
    have hc := congrArg (fun u : (RootCoaction.T f n t v d)ˣ => (u:RootCoaction.T f n t v d)) he
    exact hc⟩

end


section
open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))


attribute [local instance] OAI.Lech.RootInvariants.weightZeroBinaryFormAlgebra
attribute [local instance] OAI.Lech.RootInvariants.weightZeroBinaryFormScalarTower
lemma sections_binary_form :
    MvPolynomial.C (diagonalSection f n hn t v hv d:d.S)*
      MvPolynomial.map (algebraMap A d.S) (f.homogenize n)=
        ∏ i : Fin n, (MvPolynomial.C (sectionX f n hn t v hv d i:d.S)*MvPolynomial.X 0+
          MvPolynomial.C (sectionY f n hn t v hv d i:d.S)*MvPolynomial.X 1) := by
  have hs : BinaryChange.normalized (f.map (algebraMap A d.S)) n
      (algebraMap B d.S t) (Units.map (algebraMap B d.S).toMonoidHom v)=
        ∏ i, (Polynomial.X-C (d.roots i)) := by
    have hh := RootGluing.mapped_factorization (f.map (algebraMap A B)) n t v d
    have hp : (f.map (algebraMap A B)).map (algebraMap B d.S)=f.map (algebraMap A d.S) := by
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq A B d.S]
    have he := congrArg (fun p : d.S[X] => BinaryChange.normalized p n
      (algebraMap B d.S t) (Units.map (algebraMap B d.S).toMonoidHom v)) hp
    exact he.symm.trans hh
  have he := BinaryChange.binary_factorization (f.map (algebraMap A d.S)) n
    (algebraMap B d.S t) (Units.map (algebraMap B d.S).toMonoidHom v) d.roots hs
  rw [Polynomial.homogenize_map] at he
  rw [he]
  change MvPolynomial.C (algebraMap B d.S (v⁻¹:Bˣ))*
    (MvPolynomial.C (algebraMap B d.S (v:B))*_)=_
  rw [← mul_assoc,← MvPolynomial.C_mul,← map_mul,Units.inv_mul,map_one,map_one,one_mul]
  rfl
end


open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))

attribute [local instance] OAI.Lech.RootInvariants.weightZeroProductSectionAlgebra
lemma chartFunction_val (σ : Fin n → Bool) :
    (chartFunction f n hn t v hv d σ:d.S)=
      algebraMap B d.S (v:B)*∏ i,(selected f n hn t v hv d σ i:d.S) := rfl


end Lech.RootInvariants

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_StandardFactorChartsL
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


namespace Lech.RootInvariants
open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))

attribute [local instance] OAI.Lech.RootInvariants.instAlgebraS_1
def pair (i : Fin n) (b : Bool) : d.S :=
  if b then (sectionX f n hn t v hv d i:d.S) else (sectionY f n hn t v hv d i:d.S)

lemma pair_product (σ : Fin n → Bool) : (chartFunction f n hn t v hv d σ:d.S)=
    (Units.map (algebraMap B d.S).toMonoidHom v:d.S)*∏ i,pair f n hn t v hv d i (σ i) := by
  rw [chartFunction_val]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  cases h : σ i <;> simp only [selected,pair,h,Bool.false_eq_true,↓reduceIte]

lemma chartCoordinate_selected (σ : Fin n → Bool) (i : Fin n) :
    chartCoordinate f n hn t v hv d σ i (σ i)=1 :=
  StandardFactorCharts.coordinate_selected _ _ _ _ _

lemma sections_binary_form_unit : MvPolynomial.map (algebraMap A d.S) (f.homogenize n)=
    MvPolynomial.C (algebraMap B d.S (v:B))*∏ i : Fin n,
      (MvPolynomial.C (pair f n hn t v hv d i true)*MvPolynomial.X 0+
        MvPolynomial.C (pair f n hn t v hv d i false)*MvPolynomial.X 1) := by
  have h := congrArg (fun p : MvPolynomial (Fin 2) d.S => MvPolynomial.C (algebraMap B d.S (v:B))*p)
    (sections_binary_form f n hn t v hv d)
  change MvPolynomial.C (algebraMap B d.S (v:B))*(MvPolynomial.C (algebraMap B d.S (v⁻¹:Bˣ))*_)=_ at h
  rw [←mul_assoc,←MvPolynomial.C_mul,←map_mul,Units.mul_inv,map_one,map_one,one_mul] at h
  exact h


lemma chart_factorization (σ : Fin n → Bool) :
    (f.map (algebraMap A (chartRing f n hn t v hv d σ))).homogenize n=
      MvPolynomial.C (chartUnit f n hn t v hv d σ:chartRing f n hn t v hv d σ)*∏ i : Fin n,
        (MvPolynomial.C (chartCoordinate f n hn t v hv d σ i true)*MvPolynomial.X 0+
          MvPolynomial.C (chartCoordinate f n hn t v hv d σ i false)*MvPolynomial.X 1) := by
  rw [Polynomial.homogenize_map]
  exact StandardFactorCharts.chart_factorization (algebra f n hn t v hv d) n
    (pair f n hn t v hv d) (Units.map (algebraMap B d.S).toMonoidHom v)
    (chartFunction f n hn t v hv d) (pair_product f n hn t v hv d) f
    (sections_binary_form_unit f n hn t v hv d) σ
end Lech.RootInvariants


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_UniversalFactorMapMapChart
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
open Polynomial Lech.FactorDescent
open scoped TensorProduct
universe u
variable {A B T : Type u} [CommRing A] [CommRing B] [CommRing T]
  [Algebra A B] [Algebra A T] [Module.FaithfullyFlat A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
variable (σ : Fin n → Bool) (w : Tˣ) (a b : Fin n → T)
  (hf : (f.map (algebraMap A T)).homogenize n=MvPolynomial.C (w:T)*∏ i,
    (MvPolynomial.C (a i)*MvPolynomial.X 0+MvPolynomial.C (b i)*MvPolynomial.X 1))
  (hs : ∀ i,(if σ i then a i else b i)=1)

attribute [local instance] OAI.Lech.UniversalFactorMap.mapChartUniqueAlgebra
lemma extend_map : extend f n hn t v hv d (map f n hn t v hv d w a b hf)=
    splittingMap f n hn t v hv d w a b hf :=
  extend_descended f n hn t v hv d _ _ _ _ _ _

 

attribute [local instance] OAI.Lech.UniversalFactorMap.mapChartUniqueScalarTower
lemma chartMap_unique (h : RootInvariants.chartRing f n hn t v hv d σ →ₐ[A] T)
    (ha : ∀ i,h (RootInvariants.chartCoordinate f n hn t v hv d σ i true)=a i)
    (hb : ∀ i,h (RootInvariants.chartCoordinate f n hn t v hv d σ i false)=b i) :
    h=chartMap f n hn t v hv d σ w a b hf hs := by
  let D := RootInvariants.algebra f n hn t v hv d
  let L := RootInvariants.chartRing f n hn t v hv d σ
  let g : D →ₐ[A] T := h.comp (IsScalarTower.toAlgHom A D L)
  let φ : d.S →ₐ[B] R (A := A) (B := B) (T := T) := extend f n hn t v hv d g
  let ψ : L →ₐ[A] R (A := A) (B := B) (T := T) := (includeT (A := A) (B := B)).comp h
  have hc (x : D) : ψ (algebraMap D L x)=φ (x:d.S) := by
    change includeT (h (algebraMap D L x))=extend f n hn t v hv d g (x:d.S)
    rw [extend_subtype]
    rfl
  have hr (i : Fin n) : φ (d.roots i)=
      -includeT (a i)*((denominator f n hn t v hv w a b hf i)⁻¹).val := by
    have hq (κ : Bool) := StandardFactorCharts.map_coordinate_relation D n
      (RootInvariants.pair f n hn t v hv d) (Units.map (algebraMap B d.S).toMonoidHom v)
      (RootInvariants.chartFunction f n hn t v hv d) (RootInvariants.pair_product f n hn t v hv d)
      σ ψ (φ.restrictScalars A) hc i κ
    have hx := hq true
    change includeT (h (RootInvariants.chartCoordinate f n hn t v hv d σ i true))*
      φ (RootInvariants.pair f n hn t v hv d i (σ i))=φ (-d.roots i) at hx
    rw [ha,map_neg] at hx
    have hy := hq false
    change includeT (h (RootInvariants.chartCoordinate f n hn t v hv d σ i false))*
      φ (RootInvariants.pair f n hn t v hv d i (σ i))=φ (1+algebraMap B d.S t*d.roots i) at hy
    rw [hb,map_add,map_one,map_mul,AlgHom.commutes] at hy
    exact StandardFactorCharts.normalized_root (φ (d.roots i)) (algebraMap B _ t)
      (includeT (a i)) (includeT (b i)) (φ (RootInvariants.pair f n hn t v hv d i (σ i)))
      (denominator f n hn t v hv w a b hf i) (denominator_val f n hn t v hv w a b hf i) hx hy
  have hg : g=map f n hn t v hv d w a b hf := by
    apply point_ext f n hn t v hv d
    intro i
    rw [extend_map,splittingMap_root]
    exact hr i
  have hh : h.toRingHom=(chartMap f n hn t v hv d σ w a b hf hs).toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (RootInvariants.chartFunction f n hn t v hv d σ))
    ext x
    change g x=chartMap f n hn t v hv d σ w a b hf hs (algebraMap D L x)
    rw [chartMap_from,hg]
  exact AlgHom.ext (RingHom.congr_fun hh)

end Lech.UniversalFactorMap


namespace Lech.UniversalFactorMap
open Polynomial Lech.FactorDescent
open scoped TensorProduct
universe u
variable {A B T : Type u} [CommRing A] [CommRing B] [CommRing T]
  [Algebra A B] [Algebra A T] [Module.FaithfullyFlat A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
variable (w w' : Tˣ) (a b a' b' : Fin n → T)
  (hf : (f.map (algebraMap A T)).homogenize n=MvPolynomial.C (w:T)*∏ i,
    (MvPolynomial.C (a i)*MvPolynomial.X 0+MvPolynomial.C (b i)*MvPolynomial.X 1))
  (hf' : (f.map (algebraMap A T)).homogenize n=MvPolynomial.C (w':T)*∏ i,
    (MvPolynomial.C (a' i)*MvPolynomial.X 0+MvPolynomial.C (b' i)*MvPolynomial.X 1))
variable (c : Fin n → Tˣ) (ha : ∀ i,a' i=(c i:T)*a i) (hb : ∀ i,b' i=(c i:T)*b i)
local instance rescaleAlgebra_r8684fc_1 : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
include ha hb in
 

theorem map_rescale : map f n hn t v hv d w' a' b' hf'=map f n hn t v hv d w a b hf := by
  apply point_ext f n hn t v hv d
  intro i
  rw [extend_map,extend_map,splittingMap_root,splittingMap_root,
    denominator_rescale f n hn t v hv w w' a b a' b' hf hf' c ha hb i,ha,map_mul]
  exact normalizedRatio_rescale (includeT (a i))
    (Units.map (includeT (A:=A) (B:=B)).toMonoidHom (c i)) (denominator f n hn t v hv w a b hf i)
end Lech.UniversalFactorMap


namespace Lech.RootChartAtlas
open Polynomial
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
variable {B : Type u} [CommRing B] [Algebra (A R n k) B]
variable (t : B) (v : Bˣ) (hv : ((f R n k).map (algebraMap (A R n k) B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized ((f R n k).map (algebraMap (A R n k) B)) n t v))
variable (σ : Fin n → Bool)
abbrev w := RootInvariants.chartUnit (f R n k) n (hn R n k) t v hv d σ

local instance chartRAlgebra : Algebra R (L R n k t v hv d σ) :=
  Algebra.compHom (L R n k t v hv d σ) (algebraMap R (A R n k))
local instance chartRTower : IsScalarTower R (A R n k) (L R n k t v hv d σ) :=
  IsScalarTower.of_algebraMap_eq (R := R) (S := A R n k) (A := L R n k t v hv d σ)
    fun _ => rfl

lemma coord_selected (i : Fin n) :
    (if σ i then coordinate R n k t v hv d σ i true else coordinate R n k t v hv d σ i false)=1 := by
  have h := RootInvariants.chartCoordinate_selected (f R n k) n (hn R n k) t v hv d σ i
  cases hi : σ i <;> simpa only [hi,Bool.false_eq_true,↓reduceIte] using h

abbrev fromH_R : H R n k σ →ₐ[R] L R n k t v hv d σ :=
  ProductLinearChart.lift R n σ k
    (fun i => coordinate R n k t v hv d σ i true)
    (fun i => coordinate R n k t v hv d σ i false)
    (coord_selected R n k t v hv d σ)
    (IsScalarTower.toAlgHom R (A R n k) (L R n k t v hv d σ))
    (w R n k t v hv d σ)
    (RootInvariants.chart_factorization (f R n k) n (hn R n k) t v hv d σ)

def fromH : H R n k σ →ₐ[A R n k] L R n k t v hv d σ where
  toRingHom := (fromH_R R n k t v hv d σ).toRingHom
  commutes' a := AlgHom.congr_fun
    (ProductLinearChart.lift_target R n σ k _ _ (coord_selected R n k t v hv d σ)
      (IsScalarTower.toAlgHom R (A R n k) (L R n k t v hv d σ))
      (w R n k t v hv d σ)
      (RootInvariants.chart_factorization (f R n k) n (hn R n k) t v hv d σ)) a

lemma fromH_source (z : ProductLinearChart.Ring R n) :
    fromH R n k t v hv d σ (algebraMap (ProductLinearChart.Ring R n) (H R n k σ) z)=
      ProductLinearChart.eval R n σ
        (fun i => coordinate R n k t v hv d σ i true)
        (fun i => coordinate R n k t v hv d σ i false) z :=
  ProductLinearChart.lift_from R n σ k _ _ (coord_selected R n k t v hv d σ)
    (IsScalarTower.toAlgHom R (A R n k) (L R n k t v hv d σ))
    (w R n k t v hv d σ)
    (RootInvariants.chart_factorization (f R n k) n (hn R n k) t v hv d σ) z

lemma fromH_a (i : Fin n) :
    fromH R n k t v hv d σ (algebraMap (ProductLinearChart.Ring R n) (H R n k σ)
      (ProductLinearChart.a R n σ i))=coordinate R n k t v hv d σ i true := by
  rw [fromH_source,ProductLinearChart.eval_a R n σ _ _ (coord_selected R n k t v hv d σ)]
lemma fromH_b (i : Fin n) :
    fromH R n k t v hv d σ (algebraMap (ProductLinearChart.Ring R n) (H R n k σ)
      (ProductLinearChart.b R n σ i))=coordinate R n k t v hv d σ i false := by
  rw [fromH_source,ProductLinearChart.eval_b R n σ _ _ (coord_selected R n k t v hv d σ)]

variable [Module.FaithfullyFlat (A R n k) B]

lemma fromH_toH : (fromH R n k t v hv d σ).comp (toH R n k t v hv d σ)=AlgHom.id (A R n k) _ := by
  have he (g : L R n k t v hv d σ →ₐ[A R n k] L R n k t v hv d σ)
      (ha : ∀ i,g (coordinate R n k t v hv d σ i true)=coordinate R n k t v hv d σ i true)
      (hb : ∀ i,g (coordinate R n k t v hv d σ i false)=coordinate R n k t v hv d σ i false) :=
    UniversalFactorMap.chartMap_unique (f R n k) n (hn R n k) t v hv d σ
      (w R n k t v hv d σ) _ _
      (RootInvariants.chart_factorization (f R n k) n (hn R n k) t v hv d σ)
      (coord_selected R n k t v hv d σ) g ha hb
  apply (he _ ?_ ?_).trans (he (AlgHom.id (A R n k) _) (fun _ => rfl) (fun _ => rfl)).symm
  · intro i
    rw [AlgHom.comp_apply,toH_coordinate]
    exact fromH_a R n k t v hv d σ i
  · intro i
    rw [AlgHom.comp_apply,toH_coordinate]
    exact fromH_b R n k t v hv d σ i

omit [Module.FaithfullyFlat (A R n k) B] in
lemma fromH_X (i : Fin n) :
    fromH R n k t v hv d σ (algebraMap (ProductLinearChart.Ring R n) (H R n k σ) (MvPolynomial.X i))=
      if σ i then coordinate R n k t v hv d σ i false else coordinate R n k t v hv d σ i true :=
  ProductLinearChart.lift_X R n σ k _ _ (coord_selected R n k t v hv d σ)
    (IsScalarTower.toAlgHom R (A R n k) (L R n k t v hv d σ))
    (w R n k t v hv d σ)
    (RootInvariants.chart_factorization (f R n k) n (hn R n k) t v hv d σ) i

lemma toH_fromH : (toH R n k t v hv d σ).comp (fromH R n k t v hv d σ)=AlgHom.id (A R n k) _ := by
  have h : ((toH R n k t v hv d σ).comp (fromH R n k t v hv d σ)).restrictScalars R=
      (AlgHom.id (A R n k) (H R n k σ)).restrictScalars R := by
    apply ProductLinearChart.hom_ext
    intro i
    change toH R n k t v hv d σ (fromH R n k t v hv d σ
      (algebraMap (ProductLinearChart.Ring R n) (H R n k σ) (MvPolynomial.X i)))=
      algebraMap (ProductLinearChart.Ring R n) (H R n k σ) (MvPolynomial.X i)
    rw [fromH_X]
    cases hi : σ i <;>
      simp only [hi,Bool.false_eq_true,↓reduceIte,toH_coordinate,ProductLinearChart.a,ProductLinearChart.b]
  apply AlgHom.ext
  intro x
  have hh := AlgHom.congr_fun h x
  exact hh

 

def equiv : L R n k t v hv d σ ≃ₐ[A R n k] H R n k σ :=
  AlgEquiv.ofAlgHom (toH R n k t v hv d σ) (fromH R n k t v hv d σ)
    (toH_fromH R n k t v hv d σ) (fromH_toH R n k t v hv d σ)

end Lech.RootChartAtlas
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechFactorizationMap
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


namespace Lech.RootChartAtlas

section
open Polynomial ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
variable {B : Type u} [CommRing B] [Algebra (A R n k) B]
variable (t : B) (v : Bˣ) (hv : ((f R n k).map (algebraMap (A R n k) B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized ((f R n k).map (algebraMap (A R n k) B)) n t v))
variable [Module.FaithfullyFlat (A R n k) B]

def chartToGrid (σ : Chart n) : L R n k t v hv d σ →ₐ[A R n k] GridAmbient R n :=
  (localizedChartA R n σ k).comp (toH R n k t v hv d σ)
lemma chartToGrid_coordinate (σ : Chart n) (i : Fin n) (b : Bool) :
    chartToGrid R n k t v hv d σ (coordinate R n k t v hv d σ i b)=
      if b then chartScalar R n σ (ProductLinearChart.a R n σ i)
      else chartScalar R n σ (ProductLinearChart.b R n σ i) := by
  change localizedChart R n σ k (toH R n k t v hv d σ _)=_
  rw [toH_coordinate]
  cases b <;> simp only [Bool.false_eq_true,↓reduceIte,localizedChart_algebraMap]
def factorUnit (σ : Chart n) : (GridAmbient R n)ˣ :=
  Units.map (localizedChart R n σ k).toMonoidHom (ProductLinearChart.denominator R n σ k)⁻¹
lemma factorization_grid (σ : Chart n) :
    ((f R n k).map (algebraMap (A R n k) (GridAmbient R n))).homogenize n=
      MvPolynomial.C (factorUnit R n k σ:GridAmbient R n)*∏ i,
        (MvPolynomial.C (chartScalar R n σ (ProductLinearChart.a R n σ i))*MvPolynomial.X 0+
          MvPolynomial.C (chartScalar R n σ (ProductLinearChart.b R n σ i))*MvPolynomial.X 1) := by
  have h := factorization_map (localizedChartA R n σ k) (f R n k) n
    ((ProductLinearChart.denominator R n σ k)⁻¹)
    (fun i => algebraMap (ProductLinearChart.Ring R n) (H R n k σ) (ProductLinearChart.a R n σ i))
    (fun i => algebraMap (ProductLinearChart.Ring R n) (H R n k σ) (ProductLinearChart.b R n σ i))
    (ProductLinearChart.target_factorization R n σ k)
  have hc (z : ProductLinearChart.Ring R n) :
      localizedChartA R n σ k (algebraMap (ProductLinearChart.Ring R n) (H R n k σ) z)=chartScalar R n σ z :=
    localizedChart_algebraMap R n σ k z
  simp only [hc] at h
  exact h
lemma factor_selected (σ : Chart n) (i : Fin n) :
    (if σ i then chartScalar R n σ (ProductLinearChart.a R n σ i)
      else chartScalar R n σ (ProductLinearChart.b R n σ i))=1 := by
  have h := congrArg (chartScalar R n σ) (ProductLinearChart.selected R n σ i)
  cases hs : σ i <;> simpa only [hs,Bool.false_eq_true,↓reduceIte,map_one] using h

def algebraPoint (σ : Chart n) : GridD R n k t v hv d →ₐ[A R n k] GridAmbient R n :=
  (chartToGrid R n k t v hv d σ).comp (IsScalarTower.toAlgHom (A R n k) _ _)
lemma algebraPoint_eq_factor (σ : Chart n) :
    algebraPoint R n k t v hv d σ=UniversalFactorMap.map (f R n k) n (hn R n k) t v hv d
      (factorUnit R n k σ) (fun i => chartScalar R n σ (ProductLinearChart.a R n σ i))
      (fun i => chartScalar R n σ (ProductLinearChart.b R n σ i)) (factorization_grid R n k σ) := by
  have h := UniversalFactorMap.chartMap_unique (f R n k) n (hn R n k) t v hv d σ
    (factorUnit R n k σ) _ _ (factorization_grid R n k σ) (factor_selected R n σ)
    (chartToGrid R n k t v hv d σ)
    (fun i => chartToGrid_coordinate R n k t v hv d σ i true)
    (fun i => chartToGrid_coordinate R n k t v hv d σ i false)
  ext x
  change chartToGrid R n k t v hv d σ (algebraMap (GridD R n k t v hv d) (L R n k t v hv d σ) x)=_
  rw [h,UniversalFactorMap.chartMap_from]

def rescaleUnit (σ : Chart n) (i : Fin n) : (GridAmbient R n)ˣ :=
  Units.map (embed R n).toMonoidHom (if σ i then (ProductLaurent.variableUnit R n i)⁻¹ else 1)
lemma gridFactor_a (σ : Chart n) (i : Fin n) :
    chartScalar R n σ (ProductLinearChart.a R n σ i)=
      (rescaleUnit R n σ i:GridAmbient R n)*chartScalar R n (fun _ => false) (ProductLinearChart.a R n (fun _ => false) i) := by
  change embed R n (ProductLaurent.chartMap R n σ _)=
    embed R n (↑(if σ i then (ProductLaurent.variableUnit R n i)⁻¹ else 1):Ambient R n)*
      embed R n (ProductLaurent.chartMap R n (fun _ => false) _)
  rw [ProductLaurent.chartMap_a,ProductLaurent.chartMap_a]
  simp only [Bool.false_eq_true,↓reduceIte,Units.val_one,one_mul,map_mul]
lemma gridFactor_b (σ : Chart n) (i : Fin n) :
    chartScalar R n σ (ProductLinearChart.b R n σ i)=
      (rescaleUnit R n σ i:GridAmbient R n)*chartScalar R n (fun _ => false) (ProductLinearChart.b R n (fun _ => false) i) := by
  change embed R n (ProductLaurent.chartMap R n σ _)=
    embed R n (↑(if σ i then (ProductLaurent.variableUnit R n i)⁻¹ else 1):Ambient R n)*
      embed R n (ProductLaurent.chartMap R n (fun _ => false) _)
  rw [ProductLaurent.chartMap_b,ProductLaurent.chartMap_b]
  simp only [Bool.false_eq_true,↓reduceIte,Units.val_one,map_one,mul_one]
 

theorem algebraPoint_independent (σ : Chart n) :
    algebraPoint R n k t v hv d σ=algebraPoint R n k t v hv d (fun _ => false) := by
  rw [algebraPoint_eq_factor,algebraPoint_eq_factor]
  exact UniversalFactorMap.map_rescale (f R n k) n (hn R n k) t v hv d
    _ _ _ _ _ _ _ _ (rescaleUnit R n σ) (gridFactor_a R n σ) (gridFactor_b R n σ)
end


open Polynomial
universe u
end Lech.RootChartAtlas


namespace Lech.RootInvariants

section
open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))

local instance instAlgebraS_2_r8684fc_1 : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
abbrev chartModule (σ : Fin n → Bool) (ms : Fin n → ℤ) :=
  chartRing f n hn t v hv d σ ⊗[algebra f n hn t v hv d] overAlgebra f n hn t v hv d ms

lemma chart_tensor_compat (σ : Fin n → Bool) (x : algebra f n hn t v hv d) :
    @algebraMap (chartRing f n hn t v hv d σ)
      (chartRing f n hn t v hv d σ ⊗[algebra f n hn t v hv d] d.S)
      inferInstance inferInstance inferInstance
      (algebraMap (algebra f n hn t v hv d) (chartRing f n hn t v hv d σ) x)=
    (Algebra.TensorProduct.includeRight : d.S →ₐ[algebra f n hn t v hv d]
      chartRing f n hn t v hv d σ ⊗[algebra f n hn t v hv d] d.S) (x:d.S) := by
  exact (IsScalarTower.algebraMap_apply (algebra f n hn t v hv d)
    (chartRing f n hn t v hv d σ)
    (chartRing f n hn t v hv d σ ⊗[algebra f n hn t v hv d] d.S) x).symm.trans
      ((Algebra.TensorProduct.includeRight : d.S →ₐ[algebra f n hn t v hv d]
        chartRing f n hn t v hv d σ ⊗[algebra f n hn t v hv d] d.S).commutes x).symm

lemma selected_tensor_unit (σ : Fin n → Bool) (i : Fin n) :
    IsUnit ((1:chartRing f n hn t v hv d σ) ⊗ₜ[algebra f n hn t v hv d]
      (selected f n hn t v hv d σ i:d.S)) := by
  have h := StandardFactorCharts.selected_unit (algebra f n hn t v hv d) n
    (pair f n hn t v hv d) (Units.map (algebraMap B d.S).toMonoidHom v)
    (chartFunction f n hn t v hv d) (pair_product f n hn t v hv d) σ
    (algebraMap (chartRing f n hn t v hv d σ)
      (chartRing f n hn t v hv d σ ⊗[algebra f n hn t v hv d] d.S))
    (Algebra.TensorProduct.includeRight : d.S →ₐ[algebra f n hn t v hv d]
      chartRing f n hn t v hv d σ ⊗[algebra f n hn t v hv d] d.S).toRingHom
    (chart_tensor_compat f n hn t v hv d σ) i
  change IsUnit ((1:chartRing f n hn t v hv d σ) ⊗ₜ[algebra f n hn t v hv d]
    pair f n hn t v hv d i (σ i)) at h
  cases hs : σ i <;> simpa only [pair,selected,hs,Bool.false_eq_true,↓reduceIte] using h

lemma lineTensorEquiv_one [Module.Flat A B] (ms : Fin n → ℤ)
    (x : overAlgebra f n hn t v hv d ms) :
    lineTensorEquiv f n hn t v hv d ms (1 ⊗ₜ[algebra f n hn t v hv d] x)=(x:d.S) := by
  change (1:d.S)*(x:d.S)=(x:d.S)
  exact one_mul _


def chartLineEquiv [Module.FaithfullyFlat A B] (σ : Fin n → Bool) (i : Fin n) :
    chartRing f n hn t v hv d σ ≃ₗ[chartRing f n hn t v hv d σ]
      chartModule f n hn t v hv d σ (Pi.single i (1:ℤ)) := by
  let := algebra_faithfullyFlat f n hn t v hv d
  exact LocalLine.basisEquiv (chartRing f n hn t v hv d σ)
    (lineTensorEquiv f n hn t v hv d (Pi.single i (1:ℤ)))
    (selected f n hn t v hv d σ i) (by
      rw [lineTensorEquiv_one]
      exact selected_tensor_unit f n hn t v hv d σ i)

lemma chartLineEquiv_apply [Module.FaithfullyFlat A B] (σ : Fin n → Bool) (i : Fin n)
    (x : chartRing f n hn t v hv d σ) :
    chartLineEquiv f n hn t v hv d σ i x=
      x ⊗ₜ[algebra f n hn t v hv d] selected f n hn t v hv d σ i := by
  let := algebra_faithfullyFlat f n hn t v hv d
  exact LocalLine.basisEquiv_apply _ _ _ _ _


local instance instIsScalarTowerS_2_r8684fc_1 : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl
lemma chart_section_relation [Module.FaithfullyFlat A B] (σ : Fin n → Bool) (i : Fin n) (b : Bool) :
    chartLineEquiv f n hn t v hv d σ i (chartCoordinate f n hn t v hv d σ i b)=
      (1:chartRing f n hn t v hv d σ) ⊗ₜ[algebra f n hn t v hv d]
        (if b then sectionX f n hn t v hv d i else sectionY f n hn t v hv d i) := by
  let := algebra_faithfullyFlat f n hn t v hv d
  rw [chartLineEquiv_apply]
  apply LocalLine.section_relation (chartRing f n hn t v hv d σ)
    (lineTensorEquiv f n hn t v hv d (Pi.single i (1:ℤ)))
  rw [lineTensorEquiv_one,lineTensorEquiv_one]
  have h := StandardFactorCharts.coordinate_relation_ring (algebra f n hn t v hv d) n
    (pair f n hn t v hv d) (Units.map (algebraMap B d.S).toMonoidHom v)
    (chartFunction f n hn t v hv d) (pair_product f n hn t v hv d) σ
    (algebraMap (chartRing f n hn t v hv d σ)
      (chartRing f n hn t v hv d σ ⊗[algebra f n hn t v hv d] d.S))
    (Algebra.TensorProduct.includeRight : d.S →ₐ[algebra f n hn t v hv d]
      chartRing f n hn t v hv d σ ⊗[algebra f n hn t v hv d] d.S).toRingHom
    (chart_tensor_compat f n hn t v hv d σ) i b
  change algebraMap (chartRing f n hn t v hv d σ)
      (chartRing f n hn t v hv d σ ⊗[algebra f n hn t v hv d] d.S)
      (chartCoordinate f n hn t v hv d σ i b)*
      ((1:chartRing f n hn t v hv d σ) ⊗ₜ[algebra f n hn t v hv d] pair f n hn t v hv d i (σ i))=
    (1:chartRing f n hn t v hv d σ) ⊗ₜ[algebra f n hn t v hv d] pair f n hn t v hv d i b at h
  have hx : ((if b then sectionX f n hn t v hv d i else sectionY f n hn t v hv d i :
      overAlgebra f n hn t v hv d (Pi.single i (1:ℤ))):d.S)=
      pair f n hn t v hv d i b := by cases b <;> rfl
  have hm : ((selected f n hn t v hv d σ i):d.S)=pair f n hn t v hv d i (σ i) := by
    cases hs : σ i <;> simp only [selected,pair,hs,Bool.false_eq_true,↓reduceIte]
  rw [hx,hm]
  exact h
end


open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))

attribute [local instance] OAI.Lech.RootInvariants.tensorWorkAlgebra
local instance tensorWorkTower_r8684fc_1 : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl
lemma mul_mem (ms ns : Fin n → ℤ) (x : overAlgebra f n hn t v hv d ms)
    (y : overAlgebra f n hn t v hv d ns) : (x:d.S)*(y:d.S) ∈ overAlgebra f n hn t v hv d (ms+ns) := by
  change (RootCoaction.weight f n hn t v hv d (ms+ns) : RootCoaction.T f n t v d)*
    RootCoaction.hom f n hn t v hv d ((x:d.S)*(y:d.S))=
      RootCoaction.right f n t v d ((x:d.S)*(y:d.S))
  rw [weight_add,Units.val_mul,map_mul,map_mul]
  have hx := member_eq f n hn t v hv d ms ((overAlgebraEquiv f n hn t v hv d ms) x)
  have hy := member_eq f n hn t v hv d ns ((overAlgebraEquiv f n hn t v hv d ns) y)
  change (RootCoaction.weight f n hn t v hv d ms : RootCoaction.T f n t v d)*
    RootCoaction.hom f n hn t v hv d (x:d.S)=RootCoaction.right f n t v d (x:d.S) at hx
  change (RootCoaction.weight f n hn t v hv d ns : RootCoaction.T f n t v d)*
    RootCoaction.hom f n hn t v hv d (y:d.S)=RootCoaction.right f n t v d (y:d.S) at hy
  calc
    _ = ((RootCoaction.weight f n hn t v hv d ms : RootCoaction.T f n t v d)*
      RootCoaction.hom f n hn t v hv d (x:d.S))*
        ((RootCoaction.weight f n hn t v hv d ns : RootCoaction.T f n t v d)*
          RootCoaction.hom f n hn t v hv d (y:d.S)) := by ring
    _ = _ := by rw [hx,hy]

def mulLinear (ms ns : Fin n → ℤ) :
    overAlgebra f n hn t v hv d ms →ₗ[algebra f n hn t v hv d]
      overAlgebra f n hn t v hv d ns →ₗ[algebra f n hn t v hv d]
        overAlgebra f n hn t v hv d (ms+ns) where
  toFun x := {
    toFun y := ⟨(x:d.S)*(y:d.S),mul_mem f n hn t v hv d ms ns x y⟩
    map_add' y z := Subtype.ext (mul_add _ _ _)
    map_smul' r y := Subtype.ext (by change (x:d.S)*((r:d.S)*(y:d.S))=(r:d.S)*((x:d.S)*(y:d.S));ring) }
  map_add' x y := by ext z;exact add_mul _ _ _
  map_smul' r x := by ext z;exact mul_assoc _ _ _

def mulTensor (ms ns : Fin n → ℤ) :
    overAlgebra f n hn t v hv d ms ⊗[algebra f n hn t v hv d] overAlgebra f n hn t v hv d ns
      →ₗ[algebra f n hn t v hv d] overAlgebra f n hn t v hv d (ms+ns) :=
  TensorProduct.lift (mulLinear f n hn t v hv d ms ns)

def mulBaseSourceEquiv [Module.Flat A B] (ms ns : Fin n → ℤ) :
    d.S ⊗[algebra f n hn t v hv d]
      (overAlgebra f n hn t v hv d ms ⊗[algebra f n hn t v hv d] overAlgebra f n hn t v hv d ns)
        ≃ₗ[d.S] d.S :=
  TensorProduct.AlgebraTensorModule.distribBaseChange _ _ _ _ ≪≫ₗ
    TensorProduct.congr (lineTensorEquiv f n hn t v hv d ms) (lineTensorEquiv f n hn t v hv d ns) ≪≫ₗ
      TensorProduct.lid d.S d.S

lemma mulBase_compat [Module.Flat A B] (ms ns : Fin n → ℤ) :
    (lineTensorEquiv f n hn t v hv d (ms+ns)).toLinearMap.comp
      ((mulTensor f n hn t v hv d ms ns).baseChange d.S)=
        (mulBaseSourceEquiv f n hn t v hv d ms ns).toLinearMap := by
  ext x y
  simp [mulTensor,mulLinear,mulBaseSourceEquiv,lineTensorEquiv,lineBaseMap]

lemma mulTensor_bijective [Module.FaithfullyFlat A B] (ms ns : Fin n → ℤ) :
    Function.Bijective (mulTensor f n hn t v hv d ms ns) := by
  let inst : Module.FaithfullyFlat (algebra f n hn t v hv d) d.S :=
    algebra_faithfullyFlat f n hn t v hv d
  apply FFTensorMaps.bijective (R := algebra f n hn t v hv d)
    (M := overAlgebra f n hn t v hv d ms ⊗[algebra f n hn t v hv d] overAlgebra f n hn t v hv d ns)
    (N := overAlgebra f n hn t v hv d (ms+ns)) (Q := d.S) d.S
    (mulTensor f n hn t v hv d ms ns)
    (mulBaseSourceEquiv f n hn t v hv d ms ns)
    (lineTensorEquiv f n hn t v hv d (ms+ns))
  exact mulBase_compat f n hn t v hv d ms ns


def lineMulEquiv [Module.FaithfullyFlat A B] (ms ns : Fin n → ℤ) :
    overAlgebra f n hn t v hv d ms ⊗[algebra f n hn t v hv d] overAlgebra f n hn t v hv d ns
      ≃ₗ[algebra f n hn t v hv d] overAlgebra f n hn t v hv d (ms+ns) :=
  LinearEquiv.ofBijective (mulTensor f n hn t v hv d ms ns)
    (mulTensor_bijective f n hn t v hv d ms ns)
end Lech.RootInvariants

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_GradedLineBasisHasBasis
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


namespace Lech.RootInvariants
open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
variable (σ : Fin n → Bool)

attribute [local instance] OAI.Lech.RootInvariants.gradedLineBasisAlgebra
def chartValue (ms : Fin n → ℤ) : chartModule f n hn t v hv d σ ms →ₗ[chartRing f n hn t v hv d σ]
    chartExtension f n hn t v hv d σ :=
  (overAlgebra f n hn t v hv d ms).subtype.baseChange (chartRing f n hn t v hv d σ)
lemma chartValue_tmul (ms : Fin n → ℤ) (r : chartRing f n hn t v hv d σ)
    (m : overAlgebra f n hn t v hv d ms) :
    chartValue f n hn t v hv d σ ms (r ⊗ₜ[algebra f n hn t v hv d] m)=
      r ⊗ₜ[algebra f n hn t v hv d] (m:d.S) := rfl

local instance gradedLineBasisTower_r8684fc_1 : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl
def zeroLineEquiv : algebra f n hn t v hv d ≃ₗ[algebra f n hn t v hv d]
    overAlgebra f n hn t v hv d (0:Fin n → ℤ) where
  toFun x := ⟨(x:d.S),by
    change (RootCoaction.weight f n hn t v hv d 0:RootCoaction.T f n t v d)*
      RootCoaction.hom f n hn t v hv d (x:d.S)=RootCoaction.right f n t v d (x:d.S)
    rw [weight_zero,Units.val_one,one_mul]
    exact x.property⟩
  invFun x := ⟨(x:d.S),by
    have h := x.property
    change (RootCoaction.weight f n hn t v hv d 0:RootCoaction.T f n t v d)*
      RootCoaction.hom f n hn t v hv d (x:d.S)=RootCoaction.right f n t v d (x:d.S) at h
    change RootCoaction.hom f n hn t v hv d (x:d.S)=RootCoaction.right f n t v d (x:d.S)
    simpa only [weight_zero,Units.val_one,one_mul] using h⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def chartZeroEquiv : chartRing f n hn t v hv d σ ≃ₗ[chartRing f n hn t v hv d σ]
    chartModule f n hn t v hv d σ (0:Fin n → ℤ) :=
  (TensorProduct.AlgebraTensorModule.rid (algebra f n hn t v hv d)
    (chartRing f n hn t v hv d σ) (chartRing f n hn t v hv d σ)).symm ≪≫ₗ
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (chartRing f n hn t v hv d σ) _)
      (zeroLineEquiv f n hn t v hv d)
lemma chartZero_value : chartValue f n hn t v hv d σ 0 (chartZeroEquiv f n hn t v hv d σ 1)=1 := by
  change (1:chartRing f n hn t v hv d σ) ⊗ₜ[algebra f n hn t v hv d] (1:d.S)=1
  rfl

variable [Module.FaithfullyFlat A B]
def chartMul (ms ns : Fin n → ℤ) :
    chartModule f n hn t v hv d σ ms ⊗[chartRing f n hn t v hv d σ] chartModule f n hn t v hv d σ ns
      ≃ₗ[chartRing f n hn t v hv d σ] chartModule f n hn t v hv d σ (ms+ns) :=
  (TensorProduct.AlgebraTensorModule.distribBaseChange (algebra f n hn t v hv d)
    (chartRing f n hn t v hv d σ) (overAlgebra f n hn t v hv d ms) (overAlgebra f n hn t v hv d ns)).symm ≪≫ₗ
      TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (chartRing f n hn t v hv d σ) _)
        (lineMulEquiv f n hn t v hv d ms ns)
lemma chartMul_tmul (ms ns : Fin n → ℤ) (r s : chartRing f n hn t v hv d σ)
    (m : overAlgebra f n hn t v hv d ms) (p : overAlgebra f n hn t v hv d ns) :
    chartMul f n hn t v hv d σ ms ns
      ((r ⊗ₜ[algebra f n hn t v hv d] m) ⊗ₜ[chartRing f n hn t v hv d σ]
        (s ⊗ₜ[algebra f n hn t v hv d] p))=
      (r*s) ⊗ₜ[algebra f n hn t v hv d] (mulLinear f n hn t v hv d ms ns m p) := by
  simp only [chartMul,LinearEquiv.trans_apply,TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul,
    TensorProduct.AlgebraTensorModule.congr_tmul,LinearEquiv.refl_apply]
  rfl
lemma chartValue_mul_tmul (ms ns : Fin n → ℤ) (r s : chartRing f n hn t v hv d σ)
    (m : overAlgebra f n hn t v hv d ms) (p : overAlgebra f n hn t v hv d ns) :
    chartValue f n hn t v hv d σ (ms+ns)
      (chartMul f n hn t v hv d σ ms ns ((r ⊗ₜ[algebra f n hn t v hv d] m) ⊗ₜ[chartRing f n hn t v hv d σ]
        (s ⊗ₜ[algebra f n hn t v hv d] p)))=
      chartValue f n hn t v hv d σ ms (r ⊗ₜ[algebra f n hn t v hv d] m)*
        chartValue f n hn t v hv d σ ns (s ⊗ₜ[algebra f n hn t v hv d] p) := by
  rw [chartMul_tmul,chartValue_tmul,chartValue_tmul,chartValue_tmul]
  exact (Algebra.TensorProduct.tmul_mul_tmul r s (m:d.S) (p:d.S)).symm
lemma chartValue_mul (ms ns : Fin n → ℤ) (x : chartModule f n hn t v hv d σ ms)
    (y : chartModule f n hn t v hv d σ ns) :
    chartValue f n hn t v hv d σ (ms+ns)
      (chartMul f n hn t v hv d σ ms ns (x ⊗ₜ[chartRing f n hn t v hv d σ] y))=
      chartValue f n hn t v hv d σ ms x*chartValue f n hn t v hv d σ ns y := by
  let : CommRing (chartExtension f n hn t v hv d σ) := Algebra.TensorProduct.instCommRing
  induction x using OAI.tensorInductionOn with
  | tmul scalarLeft elementLeft =>
    induction y using OAI.tensorInductionOn with
    | tmul scalarRight elementRight =>
      exact chartValue_mul_tmul f n hn t v hv d σ ms ns
        scalarLeft scalarRight elementLeft elementRight
    | add first second hfirst hsecond =>
      simp only [TensorProduct.tmul_add,map_add]
      exact (congrArg₂ (·+·) hfirst hsecond).trans (mul_add _ _ _).symm
  | add first second hfirst hsecond =>
    simp only [TensorProduct.add_tmul,map_add]
    exact (congrArg₂ (·+·) hfirst hsecond).trans (add_mul _ _ _).symm

omit [Module.FaithfullyFlat A B] in
def chartSelectedUnit (i : Fin n) : (chartExtension f n hn t v hv d σ)ˣ :=
  (selected_tensor_unit f n hn t v hv d σ i).unit
omit [Module.FaithfullyFlat A B] in
lemma chartSelectedUnit_val (i : Fin n) : (chartSelectedUnit f n hn t v hv d σ i: chartExtension f n hn t v hv d σ)=
    (1:chartRing f n hn t v hv d σ) ⊗ₜ[algebra f n hn t v hv d] (selected f n hn t v hv d σ i:d.S) :=
  (selected_tensor_unit f n hn t v hv d σ i).unit_spec

def chartWeight (ms : Fin n → ℤ) : (chartExtension f n hn t v hv d σ)ˣ := by
  letI : CommRing (chartExtension f n hn t v hv d σ) := Algebra.TensorProduct.instCommRing
  exact ∏ i : Fin n,(chartSelectedUnit f n hn t v hv d σ i)^ms i
omit [Module.FaithfullyFlat A B] in
lemma chartWeight_zero : chartWeight f n hn t v hv d σ (0:Fin n → ℤ)=1 := by
  simp only [chartWeight,Pi.zero_apply,zpow_zero,Finset.prod_const_one]
omit [Module.FaithfullyFlat A B] in
lemma chartWeight_add (ms ns : Fin n → ℤ) : chartWeight f n hn t v hv d σ (ms+ns)=
    chartWeight f n hn t v hv d σ ms*chartWeight f n hn t v hv d σ ns := by
  simp only [chartWeight,Pi.add_apply,zpow_add,Finset.prod_mul_distrib]
omit [Module.FaithfullyFlat A B] in
lemma chartWeight_single (i : Fin n) : chartWeight f n hn t v hv d σ (Pi.single i (1:ℤ))=
    chartSelectedUnit f n hn t v hv d σ i := by
  classical
  simp [chartWeight,Pi.single_apply]

 

lemma chart_all_weights (ms : Fin n → ℤ) :
    GradedLineBasis.HasBasis (R := chartRing f n hn t v hv d σ)
      (S := chartExtension f n hn t v hv d σ) (chartModule f n hn t v hv d σ)
      (chartValue f n hn t v hv d σ) (chartWeight f n hn t v hv d σ) ms := by
  apply GradedLineBasis.all_weights _ _ (chartMul f n hn t v hv d σ)
    (chartValue_mul f n hn t v hv d σ) (chartZeroEquiv f n hn t v hv d σ)
    (chartZero_value f n hn t v hv d σ) _ (chartWeight_zero f n hn t v hv d σ)
    (chartWeight_add f n hn t v hv d σ)
  intro i
  refine ⟨chartLineEquiv f n hn t v hv d σ i,?_⟩
  rw [chartWeight_single,chartSelectedUnit_val,chartLineEquiv_apply,chartValue_tmul]

end Lech.RootInvariants


namespace Lech.RootInvariants
open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
variable [Module.FaithfullyFlat A B]

local instance transitionWorkAlgebra_r8684fc_1 : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
def chartBasis (σ : Fin n → Bool) (ms : Fin n → ℤ) :
    chartRing f n hn t v hv d σ ≃ₗ[chartRing f n hn t v hv d σ] chartModule f n hn t v hv d σ ms :=
  (chart_all_weights f n hn t v hv d σ ms).choose
lemma chartBasis_value (σ : Fin n → Bool) (ms : Fin n → ℤ) :
    chartValue f n hn t v hv d σ ms (chartBasis f n hn t v hv d σ ms 1)=
      (chartWeight f n hn t v hv d σ ms:chartExtension f n hn t v hv d σ) :=
  (chart_all_weights f n hn t v hv d σ ms).choose_spec

variable (C : Type u) [CommRing C] [Algebra (algebra f n hn t v hv d) C]
abbrev commonModule (ms : Fin n → ℤ) := C ⊗[algebra f n hn t v hv d] overAlgebra f n hn t v hv d ms

def commonBasis (σ : Fin n → Bool)
    (φ : chartRing f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] C) (ms : Fin n → ℤ) :
    C ≃ₗ[C] commonModule f n hn t v hv d C ms := by
  letI : Algebra (chartRing f n hn t v hv d σ) C := φ.toRingHom.toAlgebra
  letI : IsScalarTower (algebra f n hn t v hv d) (chartRing f n hn t v hv d σ) C :=
    IsScalarTower.of_algebraMap_eq
      (R := algebra f n hn t v hv d) (S := chartRing f n hn t v hv d σ) (A := C)
      fun a => (φ.commutes a).symm
  exact LineBasisExtension.extend C (chartBasis f n hn t v hv d σ ms)

def commonCoefficients (σ : Fin n → Bool)
    (φ : chartRing f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] C) :
    chartExtension f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] commonExtension f n hn t v hv d C :=
  Algebra.TensorProduct.map φ (AlgHom.id _ _)
def commonWeight (σ : Fin n → Bool)
    (φ : chartRing f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] C) (ms : Fin n → ℤ) :
    (commonExtension f n hn t v hv d C)ˣ :=
  Units.map (commonCoefficients f n hn t v hv d C σ φ).toMonoidHom (chartWeight f n hn t v hv d σ ms)
def commonValue (ms : Fin n → ℤ) : commonModule f n hn t v hv d C ms →ₗ[C] commonExtension f n hn t v hv d C :=
  (overAlgebra f n hn t v hv d ms).subtype.baseChange C
lemma commonBasis_value (σ : Fin n → Bool)
    (φ : chartRing f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] C) (ms : Fin n → ℤ) :
    commonValue f n hn t v hv d C ms (commonBasis f n hn t v hv d C σ φ ms 1)=
      (commonWeight f n hn t v hv d C σ φ ms:commonExtension f n hn t v hv d C) := by
  let : Algebra (chartRing f n hn t v hv d σ) C := φ.toRingHom.toAlgebra
  let : IsScalarTower (algebra f n hn t v hv d) (chartRing f n hn t v hv d σ) C :=
    IsScalarTower.of_algebraMap_eq
      (R := algebra f n hn t v hv d) (S := chartRing f n hn t v hv d σ) (A := C)
      fun a => (φ.commutes a).symm
  have h := LineBasisExtension.value_extend C (overAlgebra f n hn t v hv d ms).subtype
    (chartBasis f n hn t v hv d σ ms)
  change commonValue f n hn t v hv d C ms (commonBasis f n hn t v hv d C σ φ ms 1)=
    commonCoefficients f n hn t v hv d C σ φ (chartValue f n hn t v hv d σ ms (chartBasis f n hn t v hv d σ ms 1)) at h
  rw [chartBasis_value] at h
  exact h

 

def chartTransition (σ τ : Fin n → Bool)
    (φ : chartRing f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] C)
    (ψ : chartRing f n hn t v hv d τ →ₐ[algebra f n hn t v hv d] C) (ms : Fin n → ℤ) : Cˣ :=
  LineBasisExtension.transition (commonBasis f n hn t v hv d C τ ψ ms)
    (commonBasis f n hn t v hv d C σ φ ms)
local instance transitionWorkTower_r8684fc_1 : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl
lemma chartTransition_value (σ τ : Fin n → Bool)
    (φ : chartRing f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] C)
    (ψ : chartRing f n hn t v hv d τ →ₐ[algebra f n hn t v hv d] C) (ms : Fin n → ℤ) :
    algebraMap C (commonExtension f n hn t v hv d C) (chartTransition f n hn t v hv d C σ τ φ ψ ms:C)*
      (commonWeight f n hn t v hv d C τ ψ ms:commonExtension f n hn t v hv d C)=
        (commonWeight f n hn t v hv d C σ φ ms:commonExtension f n hn t v hv d C) := by
  have h := LineBasisExtension.transition_apply (commonBasis f n hn t v hv d C τ ψ ms)
    (commonBasis f n hn t v hv d C σ φ ms) (1:C)
  rw [one_mul] at h
  have hh := congrArg (commonValue f n hn t v hv d C ms) h
  have he (r : C) : commonBasis f n hn t v hv d C τ ψ ms r=
    r • commonBasis f n hn t v hv d C τ ψ ms 1 := by
    simpa only [smul_eq_mul,mul_one] using (commonBasis f n hn t v hv d C τ ψ ms).map_smul r 1
  rw [he,(commonValue f n hn t v hv d C ms).map_smul,commonBasis_value,commonBasis_value] at hh
  rw [Algebra.smul_def (R := C) (A := commonExtension f n hn t v hv d C)] at hh
  exact hh

end Lech.RootInvariants


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechSignedUnit
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


namespace Lech.RootInvariants
open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
variable [Module.FaithfullyFlat A B]
local instance signedWorkAlgebra_r8684fc_1 : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
variable (C : Type u) [CommRing C] [Algebra (algebra f n hn t v hv d) C]


def coordinateTransition (σ τ : Fin n → Bool)
    (φ : chartRing f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] C)
    (ψ : chartRing f n hn t v hv d τ →ₐ[algebra f n hn t v hv d] C) (i : Fin n) : Cˣ :=
  chartTransition f n hn t v hv d C σ τ φ ψ (Pi.single i (1:ℤ))
end Lech.RootInvariants


namespace Lech.RootChartAtlas
open Polynomial ProductSourceCover
open scoped TensorProduct
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
variable {B : Type u} [CommRing B] [Algebra (A R n k) B]
variable (t : B) (v : Bˣ) (hv : ((f R n k).map (algebraMap (A R n k) B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized ((f R n k).map (algebraMap (A R n k) B)) n t v))
variable [Module.FaithfullyFlat (A R n k) B]
instance gridRootAlgebra : Algebra (D R n k t v hv d) (GridAmbient R n) :=
  (algebraPoint R n k t v hv d (fun _ => false)).toRingHom.toAlgebra
lemma chartToGrid_from (σ : Chart n) (x : D R n k t v hv d) :
    chartToGrid R n k t v hv d σ (algebraMap (D R n k t v hv d) (L R n k t v hv d σ) x)=
      algebraMap (D R n k t v hv d) (GridAmbient R n) x := by
  change algebraPoint R n k t v hv d σ x=algebraPoint R n k t v hv d (fun _ => false) x
  rw [algebraPoint_independent]
def chartToGridD (σ : Chart n) : L R n k t v hv d σ →ₐ[D R n k t v hv d] GridAmbient R n :=
  { (chartToGrid R n k t v hv d σ).toRingHom with commutes' := chartToGrid_from R n k t v hv d σ }

def gridBasis (σ : Chart n) (m : Fin n → ℤ) : GridAmbient R n ≃ₗ[GridAmbient R n]
    (GridAmbient R n ⊗[D R n k t v hv d] RootInvariants.overAlgebra (f R n k) n (hn R n k) t v hv d m) :=
  RootInvariants.commonBasis (f R n k) n (hn R n k) t v hv d (GridAmbient R n) σ (chartToGridD R n k t v hv d σ) m
end Lech.RootChartAtlas


namespace Lech.RootInvariants
open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
variable [Module.FaithfullyFlat A B]
local instance basisMapWorkAlgebra_r8684fc_1 : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
variable (C : Type u) [CommRing C] [Algebra (algebra f n hn t v hv d) C]
def commonInclusion (σ : Fin n → Bool)
    (φ : chartRing f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] C) (ms : Fin n → ℤ) :
    chartModule f n hn t v hv d σ ms →ₗ[algebra f n hn t v hv d] commonModule f n hn t v hv d C ms :=
  TensorProduct.map φ.toLinearMap (LinearMap.id : overAlgebra f n hn t v hv d ms →ₗ[algebra f n hn t v hv d] _)
end Lech.RootInvariants


namespace Lech.RootChartAtlas
open Polynomial ProductSourceCover
open scoped TensorProduct
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
variable {B : Type u} [CommRing B] [Algebra (A R n k) B]
variable (t : B) (v : Bˣ) (hv : ((f R n k).map (algebraMap (A R n k) B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized ((f R n k).map (algebraMap (A R n k) B)) n t v))
variable [Module.FaithfullyFlat (A R n k) B]
local instance gridLineRoot : Algebra (D R n k t v hv d) (GridAmbient R n) := gridRootAlgebra R n k t v hv d

def gridInclusion (σ : Chart n) (m : Fin n → ℤ) :=
  RootInvariants.commonInclusion (f R n k) n (hn R n k) t v hv d (GridAmbient R n) σ (chartToGridD R n k t v hv d σ) m

local instance gridLineModule_r8684fc_1 (m : Fin n → ℤ) : Module (D R n k t v hv d) (RootInvariants.overAlgebra (f R n k) n (hn R n k) t v hv d m) :=
  Submodule.module _
def gridCoefficient (σ : Chart n) (m : Fin n → ℤ) :
    RootInvariants.chartModule (f R n k) n (hn R n k) t v hv d σ m →ₗ[D R n k t v hv d] GridAmbient R n :=
  (LineBasisExtension.coordinates (GridAmbient R n) (gridBasis R n k t v hv d (fun _ => false) m)).comp
    (gridInclusion R n k t v hv d σ m)
end Lech.RootChartAtlas


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootChartAtlasGlobalCoefficient
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
namespace Lech.RootChartAtlas
open Polynomial ProductSourceCover
open scoped TensorProduct
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
variable {B : Type u} [CommRing B] [Algebra (A R n k) B]
variable (t : B) (v : Bˣ) (hv : ((f R n k).map (algebraMap (A R n k) B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized ((f R n k).map (algebraMap (A R n k) B)) n t v))
variable [Module.FaithfullyFlat (A R n k) B]
local instance gridGlobalRoot : Algebra (D R n k t v hv d) (GridAmbient R n) := gridRootAlgebra R n k t v hv d
local instance gridGlobalModule (m : Fin n → ℤ) : Module (D R n k t v hv d) (RootInvariants.overAlgebra (f R n k) n (hn R n k) t v hv d m) :=
  Submodule.module _
def globalCoefficient (m : Fin n → ℤ) :
    RootInvariants.overAlgebra (f R n k) n (hn R n k) t v hv d m →ₗ[D R n k t v hv d] GridAmbient R n :=
  (LineBasisExtension.coordinates (GridAmbient R n) (gridBasis R n k t v hv d (fun _ => false) m)).comp
    (TensorProduct.mk (D R n k t v hv d) (GridAmbient R n) _ 1)
lemma gridCoefficient_from (σ : Chart n) (m : Fin n → ℤ)
    (z : RootInvariants.overAlgebra (f R n k) n (hn R n k) t v hv d m) :
    gridCoefficient R n k t v hv d σ m (1 ⊗ₜ[D R n k t v hv d] z)=globalCoefficient R n k t v hv d m z := by
  change (gridBasis R n k t v hv d (fun _ => false) m).symm
    (chartToGridD R n k t v hv d σ 1 ⊗ₜ[D R n k t v hv d] z)=_
  rw [map_one]
  rfl
end Lech.RootChartAtlas


namespace Lech.RootChartAtlas
open Polynomial ProductSourceCover
open scoped TensorProduct
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
variable {B : Type u} [CommRing B] [Algebra (A R n k) B]
variable (t : B) (v : Bˣ) (hv : ((f R n k).map (algebraMap (A R n k) B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized ((f R n k).map (algebraMap (A R n k) B)) n t v))
variable [Module.FaithfullyFlat (A R n k) B]
local instance moduleTarget : Algebra (A R n k) (GridAmbient R n) := gridTargetAlgebra R n k
local instance moduleTargetModule : Module (A R n k) (GridAmbient R n) := Algebra.toModule
local instance moduleRoot : Algebra (D R n k t v hv d) (GridAmbient R n) := gridRootAlgebra R n k t v hv d
local instance gridRootTower : IsScalarTower (A R n k) (D R n k t v hv d) (GridAmbient R n) :=
  IsScalarTower.of_algebraMap_eq fun a => ((algebraPoint R n k t v hv d (fun _ => false)).commutes a).symm
 
attribute [local instance] OAI.Lech.RootChartAtlas.moduleWork
local instance moduleTower_r8684fc_1 : IsScalarTower (A R n k) B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl
local instance moduleLine_r8684fc_1 (m : Fin n → ℤ) : Module (D R n k t v hv d) (RootInvariants.overAlgebra (f R n k) n (hn R n k) t v hv d m) :=
  Submodule.module _
def globalCoefficientA (m : Fin n → ℤ) :
    RootInvariants.module (f R n k) n (hn R n k) t v hv d m →ₗ[A R n k] GridAmbient R n :=
  ((globalCoefficient R n k t v hv d m).restrictScalars (A R n k)).comp
    (RootInvariants.overAlgebraEquiv (f R n k) n (hn R n k) t v hv d m).symm.toLinearMap
end Lech.RootChartAtlas


namespace Lech.ProductSourceCover
open Polynomial
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
local instance sectionAlgebra : Algebra (UniversalCoefficientChart.Ring R n k) (GridAmbient R n) := gridTargetAlgebra R n k
local instance sectionModuleBase : Module (UniversalCoefficientChart.Ring R n k) (GridAmbient R n) := Algebra.toModule


end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
local instance locTarget : Algebra (UniversalCoefficientChart.Ring R n k) (GridAmbient R n) := gridTargetAlgebra R n k
end Lech.ProductSourceCover


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CechReduction
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.FiniteModuleCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] {ι : Type} [Fintype ι] [LinearOrder ι]
variable (D : Diagram R ι) (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R)

variable (I : Ideal R)



def reductionComplexIso :
    ((TensorIdeal.quotientFunctor I).mapHomologicalComplex (.up ℕ)).obj (complex D) ≅
      complex (reduction D I) :=
  Hom.isoOfComponents (fun q => (TensorIdeal.quotientPiEquiv I
    (fun s : Set.powersetCard ι q => D.obj s.val)).toModuleIso) (by
      intro q r h
      obtain rfl : q+1=r := h
      rw [complex_d]
      change _ ≫ ModuleCat.ofHom (d (reduction D I) q) =
        (TensorIdeal.quotientFunctor I).map ((complex D).d q (q+1)) ≫ _
      rw [complex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      induction x using Submodule.Quotient.induction_on with
      | _ x => exact (quotientPiEquiv_d D I q x).symm)


end Lech.FiniteModuleCech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootCoefficientEuler
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
namespace Lech.ProductSourceCover
open AddMonoidAlgebra
universe u
variable (R : Type u) [CommRing R] (n : ℕ)

def rootCoordinate (i : Fin n) (b : Bool) : GridAmbient R n :=
  if b then embed R n (ProductLaurent.variableUnit R n i:ProductLaurent.Ring R n) else 1

lemma rootCoordinate_mem (s : Finset (Fin (n+1))) (i : Fin n) (b : Bool) :
    rootCoordinate R n i b∈grid R n (Pi.single i 1) s ∅ := by
  refine ⟨0,(if b then (ProductLaurent.variableUnit R n i:Ambient R n) else 1),?_,?_⟩
  · have ht : levelTwist n (Pi.single i 1) s.card 0=Pi.single i 1 := by
      funext j
      simp only [levelTwist,Nat.cast_zero,zero_mul,add_zero]
    rw [ht]
    exact coordinate_ringSections R n i b
  · cases b <;> simp only [rootCoordinate,Bool.false_eq_true,↓reduceIte,pow_zero,one_mul,map_one]


end Lech.ProductSourceCover

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TensorCechEuler
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.FiniteModuleCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R] {ι : Type} [Fintype ι] [LinearOrder ι]


variable {D E G : Diagram R ι} (φ : Map D E) (ψ : Map E G)
  (hzero : ∀ s,φ.app s ≫ ψ.app s=0)

 
def tensorShortComplex (F : CochainComplex (ModuleCat.{u} R) ℤ) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  ((positiveShortComplex φ ψ hzero).map
    (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R))).map (TensorTotal.Right.functor F)

end Lech.FiniteModuleCech

end

end OAI
end


