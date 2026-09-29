-- Prove2me | solution 1 for AutomorphicForm.map_mulVec_sum_map_tmul_eq_measure_pi_adelicBox_smul_pi_of_linearIndependent_of_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/7c28bb20-7180-5efc-8050-a78592c08fe8

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_map_mulVec_sum_map_tmul_eq_measure_pi_adelicBox_smul_pi_of_linearIndependent_of_span_eq_top
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicBox IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace Ws46
namespace Mu1

section Setup

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

local notation "AK" => AdeleRing (𝓞 K) K
local notation "AL" => AdeleRing (𝓞 L) L

def algAL : Algebra (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) := (M4aHerbrand.Bridge.genuineβ K L).toAlgebra

attribute [local instance] algAL

theorem smul_def' (a : AK) (y : AL) : a • y = M4aHerbrand.Bridge.genuineβ K L a * y := rfl

theorem genuineRingEquiv_tmul (a : AK) (l : L) :
    M4aHerbrand.Bridge.genuineRingEquiv K L (a ⊗ₜ[K] l) =
      M4aHerbrand.Bridge.genuineβ K L a * algebraMap L (AdeleRing (𝓞 L) L) l := by
  rw [show a ⊗ₜ[K] l = (a ⊗ₜ[K] (1 : L)) * ((1 : AK) ⊗ₜ[K] l) by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul],
    map_mul, M4aHerbrand.Bridge.genuineRingEquiv_tmul_one, M4aHerbrand.Bridge.genuineRingEquiv_one_tmul]

variable {ι : Type} [Fintype ι] (b : ι → Matrix (Fin 2) (Fin 2) L) (v : Fin 2 → L)

def Xi (a : ι → AK) : Fin 2 → AL :=
  ((∑ i, (b i).map fun l : L => l ⊗ₜ[K] a i).map
      (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
        (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)).mulVec
    fun j => algebraMap L (AdeleRing (𝓞 L) L) (v j)

theorem Xi_apply (a : ι → AK) (j : Fin 2) :
    Xi K L b v a j = ∑ i, a i • algebraMap L (AdeleRing (𝓞 L) L) (((b i).mulVec v) j) := by
  classical
  set E := ((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
        (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom with hE
  have hEt : ∀ (l : L) (x : AK), E (l ⊗ₜ[K] x) = M4aHerbrand.Bridge.genuineβ K L x * algebraMap L AL l := by
    intro l x
    rw [hE]
    show M4aHerbrand.Bridge.genuineRingEquiv K L ((Algebra.TensorProduct.comm K L AK) (l ⊗ₜ[K] x)) = _
    rw [Algebra.TensorProduct.comm_tmul, genuineRingEquiv_tmul]
  have hv : ∀ k, algebraMap L AL (v k) = E (v k ⊗ₜ[K] (1 : AK)) := by
    intro k; rw [hEt, map_one, one_mul]
  unfold Xi
  rw [← hE]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.sum_apply]
  simp_rw [hv, ← map_mul, ← map_sum]
  rw [show (∑ k : Fin 2, (∑ i, (b i j k) ⊗ₜ[K] a i) * (v k ⊗ₜ[K] (1 : AK))) = ∑ i, ((b i).mulVec v j) ⊗ₜ[K] a i by
    simp only [Finset.sum_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, Matrix.mulVec, dotProduct,
      TensorProduct.sum_tmul]
    rw [Finset.sum_comm]]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hEt, smul_def']
  rfl

end Setup

section Equiv

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

local notation "AK" => AdeleRing (𝓞 K) K
local notation "AL" => AdeleRing (𝓞 L) L

attribute [local instance] algAL

variable {ι : Type} [Fintype ι] (b : ι → Matrix (Fin 2) (Fin 2) L) (v : Fin 2 → L)
  (hli : LinearIndependent K fun i => (b i).mulVec v)
  (hsp : Submodule.span K (Set.range fun i => (b i).mulVec v) = ⊤)

def wBasis : Module.Basis ι K (Fin 2 → L) := Module.Basis.mk hli (by rw [hsp])

@[scoped simp] theorem wBasis_apply (i : ι) : wBasis K L b v hli hsp i = (b i).mulVec v := by
  simp [wBasis]

def T : (ι → K) ≃ₗ[K] (Fin 2 → L) := (wBasis K L b v hli hsp).equivFun.symm

theorem T_apply (k : ι → K) : T K L b v hli hsp k = ∑ i, k i • (b i).mulVec v := by
  simp [T, Module.Basis.equivFun_symm_apply]

def XiEquiv : (ι → AK) ≃ₗ[AK] (Fin 2 → AL) :=
  (Algebra.TensorProduct.basis AK (Pi.basisFun K ι)).equivFun.symm ≪≫ₗ
    (LinearEquiv.baseChange K AK (ι → K) (Fin 2 → L) (T K L b v hli hsp)) ≪≫ₗ
    (TensorProduct.piRight K AK AK (fun _ : Fin 2 => L)) ≪≫ₗ
    (LinearEquiv.piCongrRight fun _ : Fin 2 => (M4aHerbrand.Bridge.genuineTensorEquiv K L).toLinearEquiv)

theorem XiEquiv_apply (a : ι → AK) (j : Fin 2) :
    XiEquiv K L b v hli hsp a j = ∑ i, a i • algebraMap L (AdeleRing (𝓞 L) L) (((b i).mulVec v) j) := by
  classical
  have h1 : (Algebra.TensorProduct.basis AK (Pi.basisFun K ι)).equivFun.symm a =
      ∑ i, a i ⊗ₜ[K] (Pi.basisFun K ι i : ι → K) := by
    rw [Module.Basis.equivFun_symm_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  simp only [XiEquiv, LinearEquiv.trans_apply, h1, map_sum, LinearEquiv.baseChange_tmul,
    LinearEquiv.piCongrRight_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
  show M4aHerbrand.Bridge.genuineTensorEquiv K L (a i ⊗ₜ[K] (T K L b v hli hsp (Pi.basisFun K ι i)) j) = _
  rw [M4aHerbrand.Bridge.genuineTensorEquiv_apply, genuineRingEquiv_tmul, smul_def']
  congr 2
  rw [T_apply]
  simp [Pi.basisFun_apply, Finset.sum_apply, Pi.single_apply]
  simp only [Finset.sum_apply, ite_apply, Pi.zero_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_ite_eq']; simp

theorem XiEquiv_eq_Xi (a : ι → AK) : XiEquiv K L b v hli hsp a = Xi K L b v a := by
  funext j; rw [XiEquiv_apply, Xi_apply]

end Equiv

section TopologyPart

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

local notation "AK" => AdeleRing (𝓞 K) K
local notation "AL" => AdeleRing (𝓞 L) L

attribute [local instance] algAL

variable {ι : Type} [Fintype ι] (b : ι → Matrix (Fin 2) (Fin 2) L) (v : Fin 2 → L)
  (hli : LinearIndependent K fun i => (b i).mulVec v)
  (hsp : Submodule.span K (Set.range fun i => (b i).mulVec v) = ⊤)

theorem isModuleTopology_AL : IsModuleTopology (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) :=
  AutomorphicForm.isModuleTopology_adeleRing K L

attribute [local instance] isModuleTopology_AL

scoped instance continuousSMul_AL : ContinuousSMul (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) :=
  ⟨((M4aHerbrand.Bridge.continuous_genuineβ K L).comp continuous_fst).mul continuous_snd⟩

theorem continuous_XiEquiv : Continuous (XiEquiv K L b v hli hsp) :=
  IsModuleTopology.continuous_of_linearMap (XiEquiv K L b v hli hsp).toLinearMap

theorem continuous_XiEquiv_symm : Continuous (XiEquiv K L b v hli hsp).symm :=
  IsModuleTopology.continuous_of_linearMap (XiEquiv K L b v hli hsp).symm.toLinearMap

def XiCAE : (ι → AK) ≃ₜ+ (Fin 2 → AL) :=
  { (XiEquiv K L b v hli hsp).toAddEquiv with
    continuous_toFun := continuous_XiEquiv K L b v hli hsp
    continuous_invFun := continuous_XiEquiv_symm K L b v hli hsp }

@[scoped simp] theorem XiCAE_apply (a : ι → AK) : XiCAE K L b v hli hsp a = Xi K L b v a :=
  XiEquiv_eq_Xi K L b v hli hsp a

theorem coe_XiCAE : ⇑(XiCAE K L b v hli hsp) = Xi K L b v := funext (XiCAE_apply K L b v hli hsp)

theorem genuineβ_algebraMap (k : K) :
    M4aHerbrand.Bridge.genuineβ K L (algebraMap K AK k) = algebraMap L AL (algebraMap K L k) := by
  rw [← M4aHerbrand.Bridge.genuineRingEquiv_tmul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
    ← Algebra.algebraMap_eq_smul_one, M4aHerbrand.Bridge.genuineRingEquiv_one_tmul]

theorem Xi_algebraMap (k : ι → K) :
    Xi K L b v (fun i => algebraMap K AK (k i)) = fun j => algebraMap L AL (T K L b v hli hsp k j) := by
  funext j
  rw [Xi_apply, T_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_def', genuineβ_algebraMap, Algebra.smul_def, map_mul]

include hli hsp in

theorem Xi_image_range_algebraMap :
    Xi K L b v '' Set.range (fun k : ι → K => fun i => algebraMap K AK (k i)) =
      Set.range (fun m : Fin 2 → L => fun j => algebraMap L AL (m j)) := by
  ext y
  constructor
  · rintro ⟨a, ⟨k, rfl⟩, rfl⟩
    exact ⟨fun j => T K L b v hli hsp k j, (Xi_algebraMap K L b v hli hsp k).symm⟩
  · rintro ⟨m, rfl⟩
    refine ⟨fun i => algebraMap K AK ((T K L b v hli hsp).symm m i), ⟨_, rfl⟩, ?_⟩
    rw [Xi_algebraMap K L b v hli hsp, LinearEquiv.apply_symm_apply]

end TopologyPart

section MeasurePart

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

local notation "AK" => AdeleRing (𝓞 K) K
local notation "AL" => AdeleRing (𝓞 L) L

attribute [local instance] algAL

theorem countable_numberField : Countable K := by
  haveI : Countable (Fin (Module.finrank ℚ K) → ℚ) := inferInstance
  have hinj : Function.Injective ((Module.finBasis ℚ K).equivFun : K → (Fin (Module.finrank ℚ K) → ℚ)) :=
    (Module.finBasis ℚ K).equivFun.injective
  exact hinj.countable

omit [NumberField K] [Field L] [NumberField L] [Algebra K L] in

theorem measurableSet_adelicBox' (F : Type) [Field F] [NumberField F] [m : MeasurableSpace (AdeleRing (𝓞 F) F)]
    [BorelSpace (AdeleRing (𝓞 F) F)] : MeasurableSet (adelicBox F) := by
  rw [show m = NumberField.AdelicHaar.adeleBorel (𝓞 F) F from BorelSpace.measurable_eq]
  exact measurableSet_adelicBox F

variable {ι : Type} [Fintype ι] (b : ι → Matrix (Fin 2) (Fin 2) L) (v : Fin 2 → L)
  (hli : LinearIndependent K fun i => (b i).mulVec v)
  (hsp : Submodule.span K (Set.range fun i => (b i).mulVec v) = ⊤)

def Gam : AddSubgroup (ι → AK) := AddSubgroup.pi Set.univ fun _ => AdeleRing.principalSubgroup (𝓞 K) K

theorem mem_Gam_iff (g : ι → AK) : g ∈ Gam K (ι := ι) ↔ ∃ k : ι → K, g = fun i => algebraMap K AK (k i) := by
  constructor
  · intro hg
    have h : ∀ i, ∃ k : K, algebraMap K AK k = g i := fun i => by
      obtain ⟨k, hk⟩ := (AddSubgroup.mem_pi _).1 hg i (Set.mem_univ i)
      exact ⟨k, hk⟩
    choose k hk using h
    exact ⟨k, funext fun i => (hk i).symm⟩
  · rintro ⟨k, rfl⟩
    exact (AddSubgroup.mem_pi _).2 fun i _ => ⟨k i, rfl⟩

scoped instance countable_Gam : Countable (Gam K (ι := ι)) := by
  haveI := countable_numberField K
  have : (Gam K (ι := ι) : Set (ι → AK)) ⊆ Set.range (fun k : ι → K => fun i => algebraMap K AK (k i)) := by
    intro g hg
    obtain ⟨k, rfl⟩ := (mem_Gam_iff K g).1 hg
    exact ⟨k, rfl⟩
  exact ((Set.countable_range _).mono this).to_subtype

variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  [MeasurableSpace (AdeleRing (𝓞 L) L)] [BorelSpace (AdeleRing (𝓞 L) L)]

include hli hsp

omit hli hsp in

theorem isAddFundamentalDomain_boxPi (ρ : Measure (ι → AK)) :
    IsAddFundamentalDomain (Gam K (ι := ι)) {a : ι → AK | ∀ i, a i ∈ adelicBox K} ρ := by
  haveI : SecondCountableTopology AK := NumberField.AdeleRing.secondCountableTopology K
  refine IsAddFundamentalDomain.mk' ?_ fun a => ?_
  · have : {a : ι → AK | ∀ i, a i ∈ adelicBox K} = Set.univ.pi fun _ => adelicBox K := by
      ext a; simp
    rw [this]
    exact (MeasurableSet.univ_pi fun _ => measurableSet_adelicBox' K).nullMeasurableSet
  · have h := fun i => existsUnique_algebraMap_add_mem_adelicBox K (a i)
    choose k hk huniq using h
    refine ⟨⟨fun i => algebraMap K AK (k i), (mem_Gam_iff K _).2 ⟨k, rfl⟩⟩, fun i => hk i, ?_⟩
    rintro ⟨g, hg⟩ hg'
    obtain ⟨k', rfl⟩ := (mem_Gam_iff K g).1 hg
    have : k' = k := funext fun i => huniq i (k' i) (hg' i)
    subst this; rfl

theorem isAddFundamentalDomain_preimage_boxPi (ρ : Measure (ι → AK)) :
    IsAddFundamentalDomain (Gam K (ι := ι))
      ((Xi K L b v) ⁻¹' {y : Fin 2 → AL | ∀ j, y j ∈ adelicBox L}) ρ := by
  haveI : SecondCountableTopology AK := NumberField.AdeleRing.secondCountableTopology K
  haveI : SecondCountableTopology AL := NumberField.AdeleRing.secondCountableTopology L
  haveI := isModuleTopology_AL K L
  refine IsAddFundamentalDomain.mk' ?_ fun a => ?_
  · have : {y : Fin 2 → AL | ∀ j, y j ∈ adelicBox L} = Set.univ.pi fun _ => adelicBox L := by
      ext y; simp
    rw [this, ← coe_XiCAE K L b v hli hsp]
    exact ((MeasurableSet.univ_pi fun _ => measurableSet_adelicBox' L).preimage
      (XiCAE K L b v hli hsp).continuous.measurable).nullMeasurableSet
  · have h := fun j => existsUnique_algebraMap_add_mem_adelicBox L (Xi K L b v a j)
    choose m hm huniq using h
    set k : ι → K := (T K L b v hli hsp).symm m with hk
    have hadd : ∀ (g : ι → AK), Xi K L b v (g + a) = Xi K L b v g + Xi K L b v a := by
      intro g; rw [← coe_XiCAE K L b v hli hsp, map_add]
    refine ⟨⟨fun i => algebraMap K AK (k i), (mem_Gam_iff K _).2 ⟨k, rfl⟩⟩, ?_, ?_⟩
    · show Xi K L b v ((fun i => algebraMap K AK (k i)) + a) ∈ {y : Fin 2 → AL | ∀ j, y j ∈ adelicBox L}
      intro j
      rw [hadd, Xi_algebraMap K L b v hli hsp, hk, LinearEquiv.apply_symm_apply]
      exact hm j
    · rintro ⟨g, hg⟩ hg'
      obtain ⟨k', rfl⟩ := (mem_Gam_iff K g).1 hg
      have hg'' : ∀ j, algebraMap L AL (T K L b v hli hsp k' j) + Xi K L b v a j ∈ adelicBox L := by
        intro j
        have := hg' j
        change Xi K L b v ((fun i => algebraMap K AK (k' i)) + a) j ∈ adelicBox L at this
        rwa [hadd, Xi_algebraMap K L b v hli hsp] at this
      have hT : T K L b v hli hsp k' = m := funext fun j => huniq j _ (hg'' j)
      have : k' = k := by rw [hk, ← hT, LinearEquiv.symm_apply_apply]
      subst this; rfl

omit hli hsp in
scoped instance measurableConstVAdd_Gam : MeasurableConstVAdd (Gam K (ι := ι)) (ι → AK) := by
  haveI : SecondCountableTopology AK := NumberField.AdeleRing.secondCountableTopology K
  exact ⟨fun g => measurable_const_add (g : ι → AK)⟩

theorem measure_preimage_boxPi_eq (ρ : Measure (ι → AK)) [ρ.IsAddLeftInvariant] :
    ρ ((Xi K L b v) ⁻¹' {y : Fin 2 → AL | ∀ j, y j ∈ adelicBox L}) = ρ {a : ι → AK | ∀ i, a i ∈ adelicBox K} := by
  haveI : SecondCountableTopology AK := NumberField.AdeleRing.secondCountableTopology K
  haveI : VAddInvariantMeasure (Gam K (ι := ι)) (ι → AK) ρ :=
    ⟨fun g s hs => by have h__af := (measure_preimage_add ρ (g : ι → AK) s); simp [Set.preimage, vadd_eq_add] at h__af; exact h__af⟩
  exact (isAddFundamentalDomain_preimage_boxPi K L b v hli hsp ρ).measure_eq (isAddFundamentalDomain_boxPi K ρ)

omit hli hsp in

theorem boxPi_ne_zero_ne_top (ρ : Measure (ι → AK)) [ρ.IsAddHaarMeasure] :
    ρ {a : ι → AK | ∀ i, a i ∈ adelicBox K} ≠ 0 ∧ ρ {a : ι → AK | ∀ i, a i ∈ adelicBox K} ≠ ⊤ := by
  have hpi : {a : ι → AK | ∀ i, a i ∈ adelicBox K} = Set.univ.pi fun _ => adelicBox K := by ext a; simp
  constructor
  · obtain ⟨U, hU, hne, hsub⟩ := exists_isOpen_subset_adelicBox K
    have hUo : IsOpen (Set.univ.pi fun _ : ι => U) := isOpen_set_pi Set.finite_univ fun _ _ => hU
    have hUn : (Set.univ.pi fun _ : ι => U).Nonempty := Set.univ_pi_nonempty_iff.2 fun _ => hne
    rw [hpi]
    exact ((hUo.measure_pos ρ hUn).trans_le (measure_mono (Set.pi_mono fun _ _ => hsub))).ne'
  · obtain ⟨C, hC, hsub⟩ := exists_isCompact_adelicBox_subset K
    rw [hpi]
    exact ((measure_mono (Set.pi_mono fun _ _ => hsub)).trans_lt
      ((isCompact_univ_pi fun _ => hC).measure_lt_top)).ne

theorem map_Xi_eq (ρ : Measure (ι → AK)) [ρ.IsAddHaarMeasure]
    (μ₁ : Measure AL) [μ₁.IsAddHaarMeasure] (hμ₁ : μ₁ (adelicBox L) = 1) :
    Measure.map (Xi K L b v) ρ = ρ {a : ι → AK | ∀ i, a i ∈ adelicBox K} • Measure.pi fun _ : Fin 2 => μ₁ := by
  haveI : SecondCountableTopology AK := NumberField.AdeleRing.secondCountableTopology K
  haveI : SecondCountableTopology AL := NumberField.AdeleRing.secondCountableTopology L
  haveI := isModuleTopology_AL K L
  set ν := Measure.map (Xi K L b v) ρ with hν
  haveI : ν.IsAddHaarMeasure := by
    rw [hν, ← coe_XiCAE K L b v hli hsp]; exact ContinuousAddEquiv.isAddHaarMeasure_map ρ (XiCAE K L b v hli hsp)
  have huniq := Measure.isAddLeftInvariant_eq_smul ν (Measure.pi fun _ : Fin 2 => μ₁)
  set c := ν.addHaarScalarFactor (Measure.pi fun _ : Fin 2 => μ₁) with hc

  have hboxL : {y : Fin 2 → AL | ∀ j, y j ∈ adelicBox L} = Set.univ.pi fun _ => adelicBox L := by ext y; simp
  have h1 : ν {y : Fin 2 → AL | ∀ j, y j ∈ adelicBox L} = (c : ENNReal) := by
    rw [huniq, Measure.smul_apply, hboxL, Measure.pi_pi]
    simp [hμ₁]
  have h2 : ν {y : Fin 2 → AL | ∀ j, y j ∈ adelicBox L} = ρ {a : ι → AK | ∀ i, a i ∈ adelicBox K} := by
    have hmeas : Measurable (Xi K L b v) := by
      rw [← coe_XiCAE K L b v hli hsp]; exact (XiCAE K L b v hli hsp).continuous.measurable
    have hset : MeasurableSet {y : Fin 2 → AL | ∀ j, y j ∈ adelicBox L} := by
      rw [hboxL]; exact MeasurableSet.univ_pi fun _ => measurableSet_adelicBox' L
    rw [hν, Measure.map_apply hmeas hset, measure_preimage_boxPi_eq K L b v hli hsp ρ]
  rw [huniq, ← h2, h1]
  rfl

end MeasurePart

end Ws46.Mu1
p2m_reactivate "P2MW.S_AutomorphicForm_map_mulVec_sum_map_tmul_eq_measure_pi_adelicBox_smul_pi_of_linearIndependent_of_span_eq_top.Ws46 P2MW.S_AutomorphicForm_map_mulVec_sum_map_tmul_eq_measure_pi_adelicBox_smul_pi_of_linearIndependent_of_span_eq_top.Ws46.Mu1"
p2m_reactivate "P2MW.S_AutomorphicForm_map_mulVec_sum_map_tmul_eq_measure_pi_adelicBox_smul_pi_of_linearIndependent_of_span_eq_top.Ws46"

section Final

attribute [local instance] Ws46.Mu1.algAL

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (ι : Type) [Fintype ι] (b : ι → Matrix (Fin 2) (Fin 2) L) (v : Fin 2 → L)
    (hli : LinearIndependent K fun i => (b i).mulVec v)
    (hsp : Submodule.span K (Set.range fun i => (b i).mulVec v) = ⊤)
    [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
    [MeasurableSpace (AdeleRing (𝓞 L) L)] [BorelSpace (AdeleRing (𝓞 L) L)]
    (ρ : Measure (ι → AdeleRing (𝓞 K) K)) [ρ.IsAddHaarMeasure]
    (μ₁ : Measure (AdeleRing (𝓞 L) L)) [μ₁.IsAddHaarMeasure] (hμ₁ : μ₁ (adelicBox L) = 1) :
    ρ {a | ∀ i, a i ∈ adelicBox K} ≠ 0 ∧ ρ {a | ∀ i, a i ∈ adelicBox K} ≠ ⊤ ∧
    Measure.map (fun a : ι → AdeleRing (𝓞 K) K =>
        ((∑ i, (b i).map fun l : L => l ⊗ₜ[K] a i).map
            (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
              (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)).mulVec
          fun j => algebraMap L (AdeleRing (𝓞 L) L) (v j)) ρ =
      ρ {a | ∀ i, a i ∈ adelicBox K} • Measure.pi fun _ : Fin 2 => μ₁  := by
  obtain ⟨h0, htop⟩ := Ws46.Mu1.boxPi_ne_zero_ne_top K ρ
  refine ⟨h0, htop, ?_⟩
  have h := Ws46.Mu1.map_Xi_eq K L b v hli hsp ρ μ₁ hμ₁
  exact h

end Final
p2m_reactivate "P2MW.S_AutomorphicForm_map_mulVec_sum_map_tmul_eq_measure_pi_adelicBox_smul_pi_of_linearIndependent_of_span_eq_top.Ws46 P2MW.S_AutomorphicForm_map_mulVec_sum_map_tmul_eq_measure_pi_adelicBox_smul_pi_of_linearIndependent_of_span_eq_top.Ws46.Mu1"

namespace Ws46
namespace Mu1

end Ws46.Mu1
p2m_reactivate "P2MW.S_AutomorphicForm_map_mulVec_sum_map_tmul_eq_measure_pi_adelicBox_smul_pi_of_linearIndependent_of_span_eq_top.Ws46 P2MW.S_AutomorphicForm_map_mulVec_sum_map_tmul_eq_measure_pi_adelicBox_smul_pi_of_linearIndependent_of_span_eq_top.Ws46.Mu1"
p2m_reactivate "P2MW.S_AutomorphicForm_map_mulVec_sum_map_tmul_eq_measure_pi_adelicBox_smul_pi_of_linearIndependent_of_span_eq_top.Ws46 P2MW.S_AutomorphicForm_map_mulVec_sum_map_tmul_eq_measure_pi_adelicBox_smul_pi_of_linearIndependent_of_span_eq_top.Ws46.Mu1"

end
p2m_reactivate "P2MW.S_AutomorphicForm_map_mulVec_sum_map_tmul_eq_measure_pi_adelicBox_smul_pi_of_linearIndependent_of_span_eq_top.Ws46 P2MW.S_AutomorphicForm_map_mulVec_sum_map_tmul_eq_measure_pi_adelicBox_smul_pi_of_linearIndependent_of_span_eq_top.Ws46.Mu1"

end S_AutomorphicForm_map_mulVec_sum_map_tmul_eq_measure_pi_adelicBox_smul_pi_of_linearIndependent_of_span_eq_top
end P2MW
export P2MW.S_AutomorphicForm_map_mulVec_sum_map_tmul_eq_measure_pi_adelicBox_smul_pi_of_linearIndependent_of_span_eq_top (solution)
