-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsAddFundamentalDomainLatticeDomain
-- name    : Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsAddFundamentalDomainLatticeDomain
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:54:40.327153+00:00
-- url     : https://prove2.me/theorems/abbe350a-04e8-43c9-b2f0-3b1f2e7f8bae
-- title:
--   Is Add Fundamental Domain Lattice Domain
-- statement:
--   Definitions and structural lemmas for Is Add Fundamental Domain Lattice Domain, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsAddFundamentalDomainLatticeDomain.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Submodule Set
namespace GlobalTheory
noncomputable section
section Mean
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
def latticeDomain : Set E :=
  ZSpan.fundamentalDomain ((Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L)
theorem latticeDomain_isBounded : Bornology.IsBounded (latticeDomain L) :=
  ZSpan.fundamentalDomain_isBounded _
section Measure
variable [MeasurableSpace E] [BorelSpace E]
theorem isAddFundamentalDomain_latticeDomain (μ : Measure E) :
    IsAddFundamentalDomain L (latticeDomain L) μ :=
  ZLattice.isAddFundamentalDomain (Free.chooseBasis ℤ L) μ
theorem measure_latticeDomain (μ : Measure E) [μ.IsAddHaarMeasure] :
    μ (latticeDomain L) = ENNReal.ofReal (ZLattice.covolume L μ) := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain L μ (isAddFundamentalDomain_latticeDomain L μ),
    ofReal_measureReal (latticeDomain_isBounded L).measure_lt_top.ne]
def latticeProb : Measure E :=
  (Measure.addHaar (latticeDomain L))⁻¹ • (Measure.addHaar : Measure E).restrict (latticeDomain L)
instance isProbabilityMeasure_latticeProb : IsProbabilityMeasure (latticeProb L) := by
  constructor
  rw [latticeProb, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  refine ENNReal.inv_mul_cancel ?_ (latticeDomain_isBounded L).measure_lt_top.ne
  rw [measure_latticeDomain]
  simpa using ZLattice.covolume_pos L Measure.addHaar
end Measure
def latticeMean (f : E → G) : G :=
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  ∫ x, f x ∂(latticeProb L)
theorem latticeMean_eq_integral [m : MeasurableSpace E] [hm : BorelSpace E] (f : E → G) :
    latticeMean L f = ∫ x, f x ∂(latticeProb L) := by
  obtain ⟨rfl⟩ := hm
  rfl
@[simp] theorem latticeMean_const [CompleteSpace G] (c : G) :
    latticeMean L (fun _ => c) = c := by
  borelize E
  simp [latticeMean_eq_integral]
end Mean
section Pi
variable {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace ℝ (E i)] (L : ∀ i, Submodule ℤ (E i))
instance discreteTopology_submodulePi [∀ i, DiscreteTopology (L i)] :
    DiscreteTopology (Submodule.pi Set.univ L) :=
  DiscreteTopology.of_continuous_injective
    (f := fun (x : Submodule.pi Set.univ L) (i : ι) => (⟨x.1 i, x.2 i trivial⟩ : L i))
    (continuous_pi fun i => ((continuous_apply i).comp continuous_subtype_val).subtype_mk _)
    (fun x y h => Subtype.ext (funext fun i => congrArg Subtype.val (congrFun h i)))
instance isZLattice_submodulePi [∀ i, DiscreteTopology (L i)] [∀ i, IsZLattice ℝ (L i)] :
    IsZLattice ℝ (Submodule.pi Set.univ L) where
  span_top := by
    classical
    rw [eq_top_iff]
    intro x _
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hx : x i ∈ span ℝ (L i : Set (E i)) := by rw [IsZLattice.span_top]; trivial
    refine span_mono ?_ (Submodule.apply_mem_span_image_of_mem_span (LinearMap.single ℝ E i) hx)
    rintro _ ⟨a, ha, rfl⟩ j -
    by_cases h : j = i
    · subst h; simpa using ha
    · simp [Pi.single_eq_of_ne h]
def piLpLattice : Submodule ℤ (PiLp 2 E) :=
  ZLattice.comap ℝ (Submodule.pi Set.univ L) (PiLp.continuousLinearEquiv 2 ℝ E).toLinearMap
@[simp] theorem mem_piLpLattice {x : PiLp 2 E} : x ∈ piLpLattice L ↔ ∀ i, x i ∈ L i :=
  ⟨fun h i => h i trivial, fun h i _ => h i⟩
instance discreteTopology_piLpLattice [∀ i, DiscreteTopology (L i)] :
    DiscreteTopology (piLpLattice L) :=
  inferInstanceAs (DiscreteTopology (ZLattice.comap ℝ (Submodule.pi Set.univ L)
    (PiLp.continuousLinearEquiv 2 ℝ E).toLinearMap))
instance isZLattice_piLpLattice [∀ i, DiscreteTopology (L i)] [∀ i, IsZLattice ℝ (L i)] :
    IsZLattice ℝ (piLpLattice L) :=
  inferInstanceAs (IsZLattice ℝ (ZLattice.comap ℝ (Submodule.pi Set.univ L)
    (PiLp.continuousLinearEquiv 2 ℝ E).toLinearMap))
end Pi
section Prod
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] (L : Submodule ℤ E) (L' : Submodule ℤ E')
instance discreteTopology_submoduleProd [DiscreteTopology L] [DiscreteTopology L'] :
    DiscreteTopology (L.prod L') :=
  DiscreteTopology.of_continuous_injective
    (f := fun x : L.prod L' => ((⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩) : L × L'))
    (((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _))
    (fun x y h => Subtype.ext (Prod.ext (congrArg Subtype.val (congrArg Prod.fst h))
      (congrArg Subtype.val (congrArg Prod.snd h))))
instance isZLattice_submoduleProd [DiscreteTopology L] [DiscreteTopology L'] [IsZLattice ℝ L]
    [IsZLattice ℝ L'] : IsZLattice ℝ (L.prod L') where
  span_top := by
    rw [Submodule.prod_coe, Submodule.span_prod_eq ℝ L.zero_mem L'.zero_mem,
      IsZLattice.span_top, IsZLattice.span_top, Submodule.prod_top]
def prodLpLattice : Submodule ℤ (WithLp 2 (E × E')) :=
  ZLattice.comap ℝ (L.prod L') (WithLp.prodContinuousLinearEquiv 2 ℝ E E').toLinearMap
instance discreteTopology_prodLpLattice [DiscreteTopology L] [DiscreteTopology L'] :
    DiscreteTopology (prodLpLattice L L') :=
  inferInstanceAs (DiscreteTopology (ZLattice.comap ℝ (L.prod L')
    (WithLp.prodContinuousLinearEquiv 2 ℝ E E').toLinearMap))
instance isZLattice_prodLpLattice [DiscreteTopology L] [DiscreteTopology L'] [IsZLattice ℝ L]
    [IsZLattice ℝ L'] : IsZLattice ℝ (prodLpLattice L L') :=
  inferInstanceAs (IsZLattice ℝ (ZLattice.comap ℝ (L.prod L')
    (WithLp.prodContinuousLinearEquiv 2 ℝ E E').toLinearMap))
end Prod
end
end GlobalTheory


