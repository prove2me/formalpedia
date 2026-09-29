-- Prove2me | solution 1 for AutomorphicForm.areMatchingLocal_indicator_semiLocalIntegralSet_of_ramificationIdx_eq_one_of_inert_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/e4236a75-ded6-5f50-b610-58f7d0a60089

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LatticeTreeOrbital
import Theorems.Thm_AutomorphicForm_exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_areMatchingLocal_indicator_semiLocalIntegralSet_of_ramificationIdx_eq_one_of_inert_of_prime
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "HeckePair.IsGelfandInvolution.reindex_mk HeckePair.IsGelfandInvolution.reindexInv_mk LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11 LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open NumberField IsDedekindDomain

private theorem isInteger_of_mem_range_algebraMap {R : Type*} {K : Type*} [CommRing R] [Field K]
    [Algebra R K] {x : K} (hx : x ∈ Set.range (algebraMap R K)) : IsLocalization.IsInteger R x :=
  RingHom.mem_rangeS.mpr (Set.mem_range.mp hx)

private theorem mem_range_algebraMap_of_isInteger {R : Type*} {K : Type*} [CommRing R] [Field K]
    [Algebra R K] {x : K} (hx : IsLocalization.IsInteger R x) : x ∈ Set.range (algebraMap R K) :=
  Set.mem_range.mpr (RingHom.mem_rangeS.mp hx)

private theorem mem_integralUnitsSet_range_iff_mem_range_map {R : Type*} {K : Type*}
    [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    g ∈ AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K)) ↔
      g ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range := by
  rw [AutomorphicForm.mem_integralUnitsSet]
  constructor
  · rintro ⟨hg, hg'⟩
    have hle : LT.LatticeTree.latticeMap g (LT.LatticeTree.stdLattice R K) ≤
        LT.LatticeTree.stdLattice R K :=
      LT.LatticeTree.latticeMap_le_stdLattice_of_isInteger
        (fun i j => isInteger_of_mem_range_algebraMap (hg i j))
    have hle' : LT.LatticeTree.latticeMap g⁻¹ (LT.LatticeTree.stdLattice R K) ≤
        LT.LatticeTree.stdLattice R K :=
      LT.LatticeTree.latticeMap_le_stdLattice_of_isInteger
        (fun i j => isInteger_of_mem_range_algebraMap (hg' i j))
    have hge : LT.LatticeTree.stdLattice R K ≤
        LT.LatticeTree.latticeMap g (LT.LatticeTree.stdLattice R K) := by
      intro v hv
      have hv' : v ∈ LT.LatticeTree.latticeMap g
          (LT.LatticeTree.latticeMap g⁻¹ (LT.LatticeTree.stdLattice R K)) := by
        rw [LT.LatticeTree.latticeMap_latticeMap_inv]
        exact hv
      obtain ⟨w, hw, rfl⟩ := LT.LatticeTree.mem_latticeMap.mp hv'
      exact LT.LatticeTree.mulVec_mem_latticeMap (hle' hw)
    exact (LT.LatticeTree.latticeMap_stdLattice_eq_iff_mem_range (R := R) g).mp
      (le_antisymm hle hge)
  · intro hg
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · exact mem_range_algebraMap_of_isInteger (LT.LatticeTree.isInteger_apply_of_mem_range hg i j)
    · exact mem_range_algebraMap_of_isInteger
        (LT.LatticeTree.isInteger_apply_of_mem_range (Subgroup.inv_mem _ hg) i j)

private noncomputable def powerSums {F : Type*} [Field F] {U : Subgroup (GL (Fin 2) F)}
    (T E : HeckePair.HeckeAlgebra U ℂ) : ℕ → HeckePair.HeckeAlgebra U ℂ
  | 0 => 2
  | 1 => T
  | (k + 2) => T * powerSums T E (k + 1) - E * powerSums T E k

private theorem powerSums_zero {F : Type*} [Field F] {U : Subgroup (GL (Fin 2) F)}
    (T E : HeckePair.HeckeAlgebra U ℂ) : powerSums T E 0 = 2 := rfl

private theorem powerSums_one {F : Type*} [Field F] {U : Subgroup (GL (Fin 2) F)}
    (T E : HeckePair.HeckeAlgebra U ℂ) : powerSums T E 1 = T := rfl

private theorem powerSums_add_two {F : Type*} [Field F] {U : Subgroup (GL (Fin 2) F)}
    (T E : HeckePair.HeckeAlgebra U ℂ) (k : ℕ) :
    powerSums T E (k + 2) = T * powerSums T E (k + 1) - E * powerSums T E k := rfl

private def scalarUnit {F : Type*} [Field F] {c : F} (hc : c ≠ 0) : GL (Fin 2) F :=
  ⟨c • (1 : Matrix (Fin 2) (Fin 2) F), c⁻¹ • (1 : Matrix (Fin 2) (Fin 2) F),
    by simp [smul_smul, hc], by simp [smul_smul, hc]⟩

private theorem coe_scalarUnit {F : Type*} [Field F] {c : F} (hc : c ≠ 0) :
    ((scalarUnit hc : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = c • (1 : Matrix (Fin 2) (Fin 2) F) :=
  rfl

private theorem scalarUnit_mul_comm {F : Type*} [Field F] {c : F} (hc : c ≠ 0) (u : GL (Fin 2) F) :
    u * scalarUnit hc = scalarUnit hc * u := by
  ext1
  simp only [Units.val_mul, coe_scalarUnit, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.one_mul]

private theorem doubleCoset_scalarUnit {F : Type*} [Field F] (U : Subgroup (GL (Fin 2) F)) {c : F}
    (hc : c ≠ 0) :
    HeckePair.doubleCoset U (scalarUnit hc) =
      {x : GL (Fin 2) F | ∃ u ∈ U,
        (x : Matrix (Fin 2) (Fin 2) F) = c • (u : Matrix (Fin 2) (Fin 2) F)} := by
  ext x
  rw [HeckePair.mem_doubleCoset_iff]
  constructor
  · rintro ⟨u, hu, w, hw, rfl⟩
    refine ⟨u * w, U.mul_mem hu hw, ?_⟩
    simp only [Units.val_mul, coe_scalarUnit, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  · rintro ⟨u, hu, hx⟩
    refine ⟨1, U.one_mem, u, hu, ?_⟩
    ext1
    simp only [Units.val_mul, Units.val_one, coe_scalarUnit, Matrix.one_mul, Matrix.smul_mul, hx]

open scoped Pointwise in

private theorem finite_image_mk_mul_scalarUnit {F : Type*} [Field F] (U : Subgroup (GL (Fin 2) F))
    {c : F} (hc : c ≠ 0) :
    ((QuotientGroup.mk : GL (Fin 2) F → GL (Fin 2) F ⧸ U) ''
      ((U : Set (GL (Fin 2) F)) * ({scalarUnit hc} : Set (GL (Fin 2) F)))).Finite := by
  refine (Set.finite_singleton ((QuotientGroup.mk (scalarUnit hc) : GL (Fin 2) F ⧸ U))).subset ?_
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨u, hu, z, hz, rfl⟩ := Set.mem_mul.mp hy
  rw [Set.mem_singleton_iff] at hz
  subst hz
  rw [Set.mem_singleton_iff, scalarUnit_mul_comm]
  exact (QuotientGroup.eq).mpr (by simpa using hu)

open scoped Pointwise in

private theorem exists_scalar_heckeElement {F : Type*} [Field F] (U : Subgroup (GL (Fin 2) F))
    {c : F} (hc : c ≠ 0) (q : ℂ) :
    ∃ E : HeckePair.HeckeAlgebra U ℂ, (E : GL (Fin 2) F → ℂ) =
      q • ({x : GL (Fin 2) F | ∃ u ∈ U,
        (x : Matrix (Fin 2) (Fin 2) F) = c • (u : Matrix (Fin 2) (Fin 2) F)}.indicator
          fun _ => (1 : ℂ)) := by
  refine ⟨q • HeckePair.heckeIndicator ℂ (U := U) (scalarUnit hc) (finite_image_mk_mul_scalarUnit U hc), ?_⟩
  rw [Submodule.coe_smul, ← doubleCoset_scalarUnit U hc]
  rfl

open scoped TensorProduct TensorProduct.RightActions in

private noncomputable def semiLocalEquiv (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) [Unique (v.Extension (𝓞 L))] :
    L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] (default : v.Extension (𝓞 L)).1.adicCompletion L :=
  (AlgEquiv.ofBijective (HeightOneSpectrum.adicCompletion.baseChangeRight K L (𝓞 L) v)
      (HeightOneSpectrum.adicCompletion.baseChange_bijective K L (𝓞 L) v)).trans
    (AlgEquiv.ofRingEquiv (f := RingEquiv.piUnique fun w : v.Extension (𝓞 L) => w.1.adicCompletion L)
      fun _ => rfl)

open scoped TensorProduct TensorProduct.RightActions in
private theorem semiLocalEquiv_apply (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) [Unique (v.Extension (𝓞 L))] (a : L ⊗[K] v.adicCompletion K) :
    semiLocalEquiv K L v a = AutomorphicForm.semiLocalHomeomorph K L v a default :=
  rfl

open scoped Pointwise in
private theorem coe_heckeIndicator {G : Type*} [Group G] {U : Subgroup G} (g : G)
    (hfin : (QuotientGroup.mk '' ((U : Set G) * {g}) : Set (G ⧸ U)).Finite) :
    ((HeckePair.heckeIndicator ℂ (U := U) g hfin : HeckePair.HeckeAlgebra U ℂ) : G → ℂ) =
      (HeckePair.doubleCoset U g).indicator fun _ => (1 : ℂ) :=
  rfl

private theorem toRingHom_apply {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A]
    [Algebra R B] (f : A ≃ₐ[R] B) (a : A) : f.toAlgHom.toRingHom a = f a :=
  rfl

private theorem indicator_one_comp_eq {α β : Type*} (s : Set β) (t : Set α) (f : α → β)
    (h : ∀ x, f x ∈ s ↔ x ∈ t) :
    (fun x => Set.indicator s (1 : β → ℂ) (f x)) = t.indicator fun _ => (1 : ℂ) := by
  funext x
  by_cases hx : x ∈ t
  · simp only [Set.indicator_of_mem ((h x).mpr hx), Set.indicator_of_mem hx, Pi.one_apply]
  · simp only [Set.indicator_of_notMem (fun hs => hx ((h x).mp hs)), Set.indicator_of_notMem hx]

private theorem indicator_one_eq_of_eq {α : Type*} {s t : Set α} (h : s = t) :
    Set.indicator s (1 : α → ℂ) = t.indicator fun _ => (1 : ℂ) := by
  subst h
  rfl

open AutomorphicForm in
open scoped Pointwise TensorProduct TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime)
    (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (hinert : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = v → HeightOneSpectrum.under (𝓞 K) w' = v → w = w') :
    AreMatchingLocal K L v σ ((semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
      ((localIntegralSet K v).indicator fun _ => (1 : ℂ)) := by
  classical

  haveI := v.isPrime
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 L) v.asIdeal
    (by rw [RingOfIntegers.ker_algebraMap_eq_bot K L]; exact bot_le)
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    exact v.ne_bot (hQv.symm.trans (RingOfIntegers.ker_algebraMap_eq_bot K L))
  obtain ⟨w₀, hw₀⟩ : ∃ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v :=
    ⟨⟨Q, hQ, hQ0⟩, HeightOneSpectrum.ext hQv⟩
  haveI hu : Unique (v.Extension (𝓞 L)) :=
    ⟨⟨⟨w₀, hw₀⟩⟩, fun w => Subtype.ext (hinert w.1 w₀ w.2 hw₀)⟩

  obtain ⟨e, he⟩ : ∃ e : (L ⊗[K] v.adicCompletion K) ≃ₐ[v.adicCompletion K]
      (default : v.Extension (𝓞 L)).1.adicCompletion L,
      ∀ a, e a = AutomorphicForm.semiLocalHomeomorph K L v a default :=
    ⟨semiLocalEquiv K L v, semiLocalEquiv_apply K L v⟩

  obtain ⟨ϖK, hϖK⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  obtain ⟨ϖL, hϖL⟩ :=
    IsDiscreteValuationRing.exists_irreducible ((default : v.Extension (𝓞 L)).1.adicCompletionIntegers L)
  have hϖK0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK ≠ 0 := fun h =>
    hϖK.ne_zero ((injective_iff_map_eq_zero _).mp
      (IsFractionRing.injective (v.adicCompletionIntegers K) (v.adicCompletion K)) _ h)
  have hϖL0 : algebraMap ((default : v.Extension (𝓞 L)).1.adicCompletionIntegers L)
      ((default : v.Extension (𝓞 L)).1.adicCompletion L) ϖL ≠ 0 := fun h =>
    hϖL.ne_zero ((injective_iff_map_eq_zero _).mp
      (IsFractionRing.injective ((default : v.Extension (𝓞 L)).1.adicCompletionIntegers L)
        ((default : v.Extension (𝓞 L)).1.adicCompletion L)) _ h)
  haveI : Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖK}) := by
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖK).1 hϖK]
    exact inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)))
  haveI : Finite ((default : v.Extension (𝓞 L)).1.adicCompletionIntegers L ⧸ Ideal.span {ϖL}) := by
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖL).1 hϖL]
    exact inferInstanceAs
      (Finite (IsLocalRing.ResidueField ((default : v.Extension (𝓞 L)).1.adicCompletionIntegers L)))

  obtain ⟨UK, hUK⟩ : ∃ U : Subgroup (GL (Fin 2) (v.adicCompletion K)),
      U = LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) := ⟨_, rfl⟩
  obtain ⟨UL, hUL⟩ : ∃ U : Subgroup (GL (Fin 2) ((default : v.Extension (𝓞 L)).1.adicCompletion L)),
      U = LocalGL2.integralSubgroup ((default : v.Extension (𝓞 L)).1.adicCompletionIntegers L)
        ((default : v.Extension (𝓞 L)).1.adicCompletion L) := ⟨_, rfl⟩
  have hfinK : (QuotientGroup.mk '' ((UK : Set (GL (Fin 2) (v.adicCompletion K))) * {LocalGL2.diagPi ϖK hϖK0}) :
      Set (GL (Fin 2) (v.adicCompletion K) ⧸ UK)).Finite := by
    rw [hUK]
    exact LocalGL2.finite_image_mul_diagPi ϖK hϖK0 hϖK
  have hfinL : (QuotientGroup.mk '' ((UL : Set (GL (Fin 2) ((default : v.Extension (𝓞 L)).1.adicCompletion L))) *
      {LocalGL2.diagPi ϖL hϖL0}) :
      Set (GL (Fin 2) ((default : v.Extension (𝓞 L)).1.adicCompletion L) ⧸ UL)).Finite := by
    rw [hUL]
    exact LocalGL2.finite_image_mul_diagPi ϖL hϖL0 hϖL

  obtain ⟨TK, hTK⟩ : ∃ TK : HeckePair.HeckeAlgebra UK ℂ, (TK : GL (Fin 2) (v.adicCompletion K) → ℂ) =
      (HeckePair.doubleCoset UK (LocalGL2.diagPi ϖK hϖK0)).indicator fun _ => (1 : ℂ) :=
    ⟨HeckePair.heckeIndicator ℂ (LocalGL2.diagPi ϖK hϖK0) hfinK, coe_heckeIndicator _ hfinK⟩
  obtain ⟨TL, hTL⟩ : ∃ TL : HeckePair.HeckeAlgebra UL ℂ,
      (TL : GL (Fin 2) ((default : v.Extension (𝓞 L)).1.adicCompletion L) → ℂ) =
        (HeckePair.doubleCoset UL (LocalGL2.diagPi ϖL hϖL0)).indicator fun _ => (1 : ℂ) :=
    ⟨HeckePair.heckeIndicator ℂ (LocalGL2.diagPi ϖL hϖL0) hfinL, coe_heckeIndicator _ hfinL⟩
  obtain ⟨EK, hEK⟩ := exists_scalar_heckeElement UK hϖK0 (Ideal.absNorm v.asIdeal : ℂ)
  obtain ⟨EL, hEL⟩ :=
    exists_scalar_heckeElement UL hϖL0 (Ideal.absNorm (default : v.Extension (𝓞 L)).1.asIdeal : ℂ)

  have hIN :=
    AutomorphicForm.exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime K L hdeg σ hσ v default
      (hv _ (default : v.Extension (𝓞 L)).2) e ϖK hϖK hϖK0 ϖL hϖL hϖL0 UK hUK UL hUL TK EK hTK hEK TL EL hTL hEL
      (powerSums TK EK) (powerSums_zero TK EK) (powerSums_one TK EK) (powerSums_add_two TK EK)
  obtain ⟨b, -, -, hb⟩ := hIN
  have h := hb 1
  rw [map_one, HeckePair.coe_one, HeckePair.coe_one] at h

  have hrangeK : Set.range (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) =
      (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    ext x
    exact ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  have hrangeL : Set.range (algebraMap ((default : v.Extension (𝓞 L)).1.adicCompletionIntegers L)
      ((default : v.Extension (𝓞 L)).1.adicCompletion L)) =
      ((default : v.Extension (𝓞 L)).1.adicCompletionIntegers L :
        Set ((default : v.Extension (𝓞 L)).1.adicCompletion L)) := by
    ext x
    exact ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  have hsetK : (UK : Set (GL (Fin 2) (v.adicCompletion K))) = AutomorphicForm.localIntegralSet K v := by
    rw [hUK]
    ext g
    rw [SetLike.mem_coe, AutomorphicForm.localIntegralSet, ← hrangeK]
    exact (mem_integralUnitsSet_range_iff_mem_range_map g).symm
  have hint : ∀ a : L ⊗[K] v.adicCompletion K,
      e.toAlgHom.toRingHom a ∈ ((default : v.Extension (𝓞 L)).1.adicCompletionIntegers L :
        Set ((default : v.Extension (𝓞 L)).1.adicCompletion L)) ↔
      a ∈ AutomorphicForm.semiLocalIntegers K L v := by
    intro a
    rw [toRingHom_apply, he, AutomorphicForm.semiLocalIntegers_eq_preimage, Set.mem_preimage,
      AutomorphicForm.piIntegers, Set.mem_univ_pi, Unique.forall_iff]
  have hmem : ∀ g : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      Matrix.GeneralLinearGroup.map e.toAlgHom.toRingHom g ∈
          (UL : Set (GL (Fin 2) ((default : v.Extension (𝓞 L)).1.adicCompletion L))) ↔
        g ∈ AutomorphicForm.semiLocalIntegralSet K L v := by
    intro g
    rw [hUL, SetLike.mem_coe]
    refine Iff.trans
      (mem_integralUnitsSet_range_iff_mem_range_map (Matrix.GeneralLinearGroup.map e.toAlgHom.toRingHom g)).symm ?_
    rw [hrangeL, AutomorphicForm.semiLocalIntegralSet, AutomorphicForm.mem_integralUnitsSet,
      AutomorphicForm.mem_integralUnitsSet, ← map_inv]
    simp only [Matrix.GeneralLinearGroup.map_apply, hint]

  rw [indicator_one_comp_eq (UL : Set (GL (Fin 2) ((default : v.Extension (𝓞 L)).1.adicCompletion L)))
      (AutomorphicForm.semiLocalIntegralSet K L v) _ hmem, indicator_one_eq_of_eq hsetK] at h
  exact h

end S_AutomorphicForm_areMatchingLocal_indicator_semiLocalIntegralSet_of_ramificationIdx_eq_one_of_inert_of_prime
end P2MW
export P2MW.S_AutomorphicForm_areMatchingLocal_indicator_semiLocalIntegralSet_of_ramificationIdx_eq_one_of_inert_of_prime (solution)
