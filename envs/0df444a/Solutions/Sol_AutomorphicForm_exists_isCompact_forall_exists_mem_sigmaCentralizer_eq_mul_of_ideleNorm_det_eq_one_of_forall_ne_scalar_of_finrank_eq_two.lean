-- Prove2me | solution 1 for AutomorphicForm.exists_isCompact_forall_exists_mem_sigmaCentralizer_eq_mul_of_ideleNorm_det_eq_one_of_forall_ne_scalar_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/1f909998-b4e8-5f7c-bafb-5cb92bb0b4ce

import Definitions.Def_AutomorphicForm_TwistedCommutant
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_AutomorphicForm_map_mul_addHaar_twistedCommutant_eq_inv_distribHaarChar_det_smul_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two
import Theorems.Thm_MeasureTheory_exists_isCompact_forall_exists_eq_mul_of_map_mul_eq_of_isAddFundamentalDomain
import Theorems.Thm_AutomorphicForm_exists_homeomorph_twistedCommutant_map_mul_scalar_forall_coe_eq_sum_map_tmul_of_linearIndependent
import Theorems.Thm_AutomorphicForm_existsUnique_mul_eq_mul_map_and_mulVec_eq_of_forall_ne_scalar_of_finrank_eq_two
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isCompact_forall_exists_mem_sigmaCentralizer_eq_mul_of_ideleNorm_det_eq_one_of_forall_ne_scalar_of_finrank_eq_two
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply AutomorphicForm.cpowChar_apply_val ContinuousAddEquiv.preimage_mulLeft_smul"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory NumberField Matrix
open scoped TensorProduct TensorProduct.RightActions NNReal ENNReal Pointwise

noncomputable section

namespace P2mFujisakiD

open AutomorphicForm

section OverK

variable (K L : Type) [Field K] [Field L] [Algebra K L] (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L)

def DK : Submodule K (Matrix (Fin 2) (Fin 2) L) where
  carrier := {x | x * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * x.map σ}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [add_mul, Matrix.map_add _ (map_add σ), mul_add, hx, hy]
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    rw [zero_mul, Matrix.map_zero _ (map_zero σ), mul_zero]
  smul_mem' := by
    intro k x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    have hm : (k • x).map σ = k • x.map σ := by
      ext i j; simp [Matrix.map_apply]
    rw [hm, Matrix.smul_mul, Matrix.mul_smul, hx]

variable {K L σ δ₀}

theorem mem_DK_iff (x : Matrix (Fin 2) (Fin 2) L) :
    x ∈ DK K L σ δ₀ ↔
      x * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * x.map σ :=
  Iff.rfl

theorem one_mem_DK : (1 : Matrix (Fin 2) (Fin 2) L) ∈ DK K L σ δ₀ := by
  rw [mem_DK_iff, Matrix.map_one _ (map_zero σ) (map_one σ), one_mul, mul_one]

theorem mul_mem_DK {x y : Matrix (Fin 2) (Fin 2) L} (hx : x ∈ DK K L σ δ₀) (hy : y ∈ DK K L σ δ₀) :
    x * y ∈ DK K L σ δ₀ := by
  rw [mem_DK_iff] at hx hy ⊢
  have hm : (x * y).map σ = x.map σ * y.map σ := by
    ext i j; simp [Matrix.mul_apply]
  rw [hm, mul_assoc, hy, ← mul_assoc, hx, mul_assoc]

theorem exists_inv_mem_DK [CharZero K] (h2 : Module.finrank K L = 2)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hNL : ∃ z : Lˣ, δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ =
      Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
        Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    {d : Matrix (Fin 2) (Fin 2) L} (hd : d ∈ DK K L σ δ₀) (hd0 : d ≠ 0) :
    ∃ d' : Matrix (Fin 2) (Fin 2) L, d' ∈ DK K L σ δ₀ ∧ d * d' = 1 ∧ d' * d = 1 := by
  classical

  obtain ⟨j, hj⟩ : ∃ j : Fin 2, d.mulVec (Pi.single j 1) ≠ 0 := by
    by_contra h
    push Not at h
    apply hd0
    ext i j
    have := congrFun (h j) i
    rw [Matrix.mulVec_single_one] at this
    simpa using this
  set v : Fin 2 → L := d.mulVec (Pi.single j 1) with hv

  obtain ⟨y, ⟨hy, hyv⟩, -⟩ :=
    AutomorphicForm.existsUnique_mul_eq_mul_map_and_mulVec_eq_of_forall_ne_scalar_of_finrank_eq_two
      K L h2 σ hgen δ₀ hNL hns v hj (Pi.single j 1)

  obtain ⟨z, -, huniq⟩ :=
    AutomorphicForm.existsUnique_mul_eq_mul_map_and_mulVec_eq_of_forall_ne_scalar_of_finrank_eq_two
      K L h2 σ hgen δ₀ hNL hns v hj v
  have h1 : (1 : Matrix (Fin 2) (Fin 2) L) = z := huniq 1 ⟨one_mem_DK, Matrix.one_mulVec v⟩
  have h2' : d * y = z := huniq (d * y) ⟨mul_mem_DK hd hy, by rw [← Matrix.mulVec_mulVec, hyv]⟩
  have hdy : d * y = 1 := h2'.trans h1.symm
  exact ⟨y, hy, hdy, mul_eq_one_comm.1 hdy⟩

end OverK

section Adelic

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

local notation "AK" => AdeleRing (𝓞 K) K
local notation "AL" => AdeleRing (𝓞 L) L

scoped instance secondCountableTopology_adeleRing (F : Type) [Field F] [NumberField F] :
    SecondCountableTopology (AdeleRing (𝓞 F) F) :=
  NumberField.AdeleRing.secondCountableTopology F

abbrev MK : Type := Matrix (Fin 2) (Fin 2) (L ⊗[K] AK)

abbrev inclA : L →+* L ⊗[K] AK := Algebra.TensorProduct.includeLeftRingHom

abbrev δA (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AK)ˣ) : GL (Fin 2) (L ⊗[K] AK) :=
  Matrix.GeneralLinearGroup.map (inclA K L) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) c

variable (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)

abbrev RK : Type := ↥(twistedCommutant K L AK σ (δA K L δ₀ c))

scoped instance isTopologicalRing_MK : IsTopologicalRing (MK K L) := by
  haveI := isTopologicalRing_tensor K L AK
  infer_instance

scoped instance isTopologicalRing_RK : IsTopologicalRing (RK K L σ δ₀ c) := by
  haveI := isTopologicalRing_tensor K L AK
  exact inferInstanceAs (IsTopologicalRing (twistedCommutant K L AK σ (δA K L δ₀ c)).toSubring)

scoped instance isTopologicalAddGroup_RK : IsTopologicalAddGroup (RK K L σ δ₀ c) :=
  @IsTopologicalRing.to_topologicalAddGroup (RK K L σ δ₀ c) _ _ (isTopologicalRing_RK K L σ δ₀ c)

scoped instance t2Space_MK : T2Space (MK K L) := by
  haveI := t2Space_tensor K L AK
  exact inferInstanceAs (T2Space (Fin 2 → Fin 2 → L ⊗[K] AK))

scoped instance t2Space_RK : T2Space (RK K L σ δ₀ c) :=
  inferInstanceAs (T2Space {x // x ∈ twistedCommutant K L AK σ (δA K L δ₀ c)})

scoped instance locallyCompactSpace_RK : LocallyCompactSpace (RK K L σ δ₀ c) :=
  locallyCompactSpace_twistedCommutant K L AK σ _

scoped instance secondCountableTopology_tensor : SecondCountableTopology (L ⊗[K] AK) := by
  haveI := isTopologicalRing_tensor K L AK
  exact Module.Finite.secondCountabletopology AK (L ⊗[K] AK)

scoped instance secondCountableTopology_MK : SecondCountableTopology (MK K L) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → L ⊗[K] AK))

scoped instance secondCountableTopology_RK : SecondCountableTopology (RK K L σ δ₀ c) :=
  TopologicalSpace.Subtype.secondCountableTopology _

omit [FiniteDimensional K L] in
theorem baseChangeEquiv_inclA (l : L) : baseChangeEquiv K L (inclA K L l) = algebraMap L AL l :=
  baseChangeEquiv_tmul_one K L l

omit [FiniteDimensional K L] in
theorem inclA_injective : Function.Injective (inclA K L) := by
  intro l l' h
  have := congrArg (baseChangeEquiv K L) h
  rw [baseChangeEquiv_inclA, baseChangeEquiv_inclA] at this
  exact NumberField.AdeleRing.algebraMap_injective (𝓞 L) L this

abbrev jM : Matrix (Fin 2) (Fin 2) L →+* MK K L := (inclA K L).mapMatrix

omit [NumberField L] [FiniteDimensional K L] in
theorem jM_apply (x : Matrix (Fin 2) (Fin 2) L) : jM K L x = x.map (inclA K L) := rfl

omit [FiniteDimensional K L] in
theorem jM_injective : Function.Injective (jM K L) := fun x y h => by
  ext i j
  exact inclA_injective K L (by simpa [Matrix.map_apply] using congrFun (congrFun h i) j)

omit [NumberField L] [FiniteDimensional K L] in
theorem coe_map_δ₀ :
    ((Matrix.GeneralLinearGroup.map (inclA K L) δ₀ : GL (Fin 2) (L ⊗[K] AK)) : MK K L) =
      jM K L (δ₀ : Matrix (Fin 2) (Fin 2) L) := rfl

omit [NumberField L] [FiniteDimensional K L] in
theorem sigmaTensor_inclA (l : L) : sigmaTensor K L AK σ (inclA K L l) = inclA K L (σ l) := by
  simp [sigmaTensor, Algebra.TensorProduct.map_tmul]

omit [NumberField L] [FiniteDimensional K L] in
theorem map_sigmaTensor_jM (x : Matrix (Fin 2) (Fin 2) L) :
    (jM K L x).map (sigmaTensor K L AK σ) = jM K L (x.map σ) := by
  ext i j
  simp only [jM_apply, Matrix.map_apply, sigmaTensor_inclA]

omit [NumberField L] [FiniteDimensional K L] in
theorem coe_scalarGL :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) (L ⊗[K] AK)) : MK K L) =
      Matrix.scalar (Fin 2) (c : L ⊗[K] AK) := rfl

omit [NumberField L] [FiniteDimensional K L] in

theorem map_sigmaTensor_scalar (r : L ⊗[K] AK) :
    (Matrix.scalar (Fin 2) r : MK K L).map (sigmaTensor K L AK σ) =
      Matrix.scalar (Fin 2) (sigmaTensor K L AK σ r) := by
  rw [Matrix.scalar_apply, Matrix.diagonal_map (map_zero _)]; rfl

omit [NumberField L] [FiniteDimensional K L] in
theorem scalar_comm (r : L ⊗[K] AK) (X : MK K L) :
    Matrix.scalar (Fin 2) r * X = X * Matrix.scalar (Fin 2) r :=
  (Matrix.scalar_commute r (fun r' => mul_comm r r') X).eq

theorem coe_δA : ((δA K L δ₀ c : GL (Fin 2) (L ⊗[K] AK)) : MK K L) =
    jM K L (δ₀ : Matrix (Fin 2) (Fin 2) L) * Matrix.scalar (Fin 2) (c : L ⊗[K] AK) := by
  rw [Matrix.GeneralLinearGroup.coe_mul, coe_map_δ₀, coe_scalarGL]

variable {K L σ δ₀ c}

theorem jM_mem {x : Matrix (Fin 2) (Fin 2) L} (hx : x ∈ DK K L σ δ₀) :
    jM K L x ∈ twistedCommutant K L AK σ (δA K L δ₀ c) := by
  rw [mem_twistedCommutant_iff, coe_δA, map_sigmaTensor_jM, ← mul_assoc, ← map_mul,
    (mem_DK_iff x).1 hx, map_mul, mul_assoc, mul_assoc, scalar_comm]

variable (K L σ δ₀ c)

def jR : DK K L σ δ₀ →+ RK K L σ δ₀ c where
  toFun x := ⟨jM K L (x : Matrix (Fin 2) (Fin 2) L), jM_mem x.2⟩
  map_zero' := Subtype.ext (jM K L).map_zero
  map_add' _ _ := Subtype.ext ((jM K L).map_add _ _)

@[scoped simp] theorem coe_jR (x : DK K L σ δ₀) :
    ((jR K L σ δ₀ c x : RK K L σ δ₀ c) : MK K L) = jM K L (x : Matrix (Fin 2) (Fin 2) L) := rfl

theorem jR_injective : Function.Injective (jR K L σ δ₀ c) := fun _ _ h =>
  Subtype.ext (jM_injective K L (congrArg (fun r : RK K L σ δ₀ c => (r : MK K L)) h))

def Λ : AddSubgroup (RK K L σ δ₀ c) := (jR K L σ δ₀ c).range

theorem mem_Λ_iff (r : RK K L σ δ₀ c) : r ∈ Λ K L σ δ₀ c ↔ ∃ x : DK K L σ δ₀, jR K L σ δ₀ c x = r :=
  Iff.rfl

theorem Λ_mul {r s : RK K L σ δ₀ c} (hr : r ∈ Λ K L σ δ₀ c) (hs : s ∈ Λ K L σ δ₀ c) :
    r * s ∈ Λ K L σ δ₀ c := by
  obtain ⟨x, rfl⟩ := hr
  obtain ⟨y, rfl⟩ := hs
  refine ⟨⟨(x : Matrix (Fin 2) (Fin 2) L) * y, mul_mem_DK x.2 y.2⟩, Subtype.ext ?_⟩
  simp [Subalgebra.coe_mul]

theorem exists_norm_eq_scalar (h2 : Module.finrank K L = 2) (u : AKˣ)
    (hN : normString K L AK σ (δA K L δ₀ c) = toTensorGL K L AK (centralScalar (𝓞 K) K u)) :
    ∃ z : Lˣ, δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ =
      Matrix.GeneralLinearGroup.scalar (Fin 2) z := by
  classical

  have hNS : normString K L AK σ (δA K L δ₀ c) = δA K L δ₀ c * sigmaGL K L AK σ (δA K L δ₀ c) := by
    rw [normString, h2]; simp [List.range_succ]
  rw [hNS] at hN

  set M : Matrix (Fin 2) (Fin 2) L :=
    (δ₀ : Matrix (Fin 2) (Fin 2) L) * ((δ₀ : Matrix (Fin 2) (Fin 2) L).map σ) with hM
  set w : L ⊗[K] AK := (c : L ⊗[K] AK) * sigmaTensor K L AK σ c with hw
  have hw_unit : IsUnit w := (c.isUnit).mul ((c.isUnit).map _)
  have hcoe : ((δA K L δ₀ c * sigmaGL K L AK σ (δA K L δ₀ c) : GL (Fin 2) (L ⊗[K] AK)) : MK K L) =
      jM K L M * Matrix.scalar (Fin 2) w := by
    rw [Matrix.GeneralLinearGroup.coe_mul, coe_sigmaGL, coe_δA, Matrix.map_mul, map_sigmaTensor_jM,
      map_sigmaTensor_scalar, hM, map_mul, hw, map_mul]
    rw [mul_assoc, ← mul_assoc (Matrix.scalar (Fin 2) (c : L ⊗[K] AK)), scalar_comm, mul_assoc,
      mul_assoc]
  have hrhs : ((toTensorGL K L AK (centralScalar (𝓞 K) K u) : GL (Fin 2) (L ⊗[K] AK)) : MK K L) =
      Matrix.scalar (Fin 2) ((1 : L) ⊗ₜ[K] (u : AK)) := by
    change ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) AK) : Matrix (Fin 2) (Fin 2) AK).map
      (Algebra.TensorProduct.includeRight : AK →ₐ[K] L ⊗[K] AK) = _
    change (Matrix.scalar (Fin 2) (u : AK)).map _ = _
    rw [Matrix.scalar_apply, Matrix.diagonal_map (map_zero _)]
    rfl
  have hmat := congrArg (fun g : GL (Fin 2) (L ⊗[K] AK) => (g : MK K L)) hN
  beta_reduce at hmat
  rw [hcoe, hrhs] at hmat

  obtain ⟨wu, hwu⟩ := hw_unit
  have hjM : jM K L M =
      Matrix.scalar (Fin 2) (((1 : L) ⊗ₜ[K] (u : AK)) * ((wu⁻¹ : (L ⊗[K] AK)ˣ) : L ⊗[K] AK)) := by
    have := congrArg (fun X : MK K L => X * Matrix.scalar (Fin 2) ((wu⁻¹ : (L ⊗[K] AK)ˣ) : L ⊗[K] AK)) hmat
    beta_reduce at this
    rwa [mul_assoc, ← map_mul, ← map_mul, ← hwu, Units.mul_inv, map_one, mul_one] at this

  have hent : ∀ i k : Fin 2, inclA K L (M i k) = if i = k then
      ((1 : L) ⊗ₜ[K] (u : AK)) * ((wu⁻¹ : (L ⊗[K] AK)ˣ) : L ⊗[K] AK) else 0 := by
    intro i k
    have := congrFun (congrFun hjM i) k
    rw [jM_apply, Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply] at this
    exact this
  have h01 : M 0 1 = 0 := inclA_injective K L (by rw [hent, if_neg (by decide), map_zero])
  have h10 : M 1 0 = 0 := inclA_injective K L (by rw [hent, if_neg (by decide), map_zero])
  have h0011 : M 0 0 = M 1 1 := inclA_injective K L (by rw [hent, hent, if_pos rfl, if_pos rfl])

  have hMdet : IsUnit M.det := by
    have : M = ((δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ : GL (Fin 2) L) :
        Matrix (Fin 2) (Fin 2) L) := by
      rw [Matrix.GeneralLinearGroup.coe_mul]; rfl
    rw [this]
    exact Matrix.isUnits_det_units _
  have hz : M 0 0 ≠ 0 := by
    intro h0
    rw [Matrix.det_fin_two, h0, h01, zero_mul, zero_mul, sub_zero] at hMdet
    exact not_isUnit_zero hMdet
  refine ⟨Units.mk0 (M 0 0) hz, Units.ext ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_mul]
  change M = ((Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (M 0 0) hz) : GL (Fin 2) L) :
    Matrix (Fin 2) (Fin 2) L)
  ext i k
  simp only [Matrix.GeneralLinearGroup.scalar, Units.coe_map, MonoidHom.coe_coe,
    RingHom.toMonoidHom_eq_coe, Matrix.scalar_apply, Matrix.diagonal_apply, Units.val_mk0]
  fin_cases i <;> fin_cases k <;> simp [h01, h10, h0011]

theorem finite_inter_of_isCompact {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [T2Space G] (Γ : AddSubgroup G) {V : Set G} (hV : IsOpen V)
    (h0 : (0 : G) ∈ V) (hΓV : ∀ x ∈ Γ, x ∈ V → x = 0) {C : Set G} (hC : IsCompact C) :
    (C ∩ (Γ : Set G)).Finite := by
  by_contra hinf
  obtain ⟨p, -, hp⟩ :=
    (Set.not_finite.1 hinf).exists_accPt_of_subset_isCompact hC Set.inter_subset_left

  have hV' : (fun q : G × G => q.1 - q.2) ⁻¹' V ∈ nhds (p, p) := by
    refine continuous_sub.continuousAt.preimage_mem_nhds ?_
    rw [sub_self]
    exact hV.mem_nhds h0
  obtain ⟨W₁, hW₁, W₂, hW₂, hW⟩ := mem_nhds_prod_iff.1 hV'
  have hWp : W₁ ∩ W₂ ∈ nhds p := Filter.inter_mem hW₁ hW₂

  rw [accPt_iff_nhds] at hp
  obtain ⟨q₁, ⟨hq₁W, hq₁⟩, hq₁p⟩ := hp _ hWp
  have hW' : (W₁ ∩ W₂) ∩ {q₁}ᶜ ∈ nhds p :=
    Filter.inter_mem hWp (isOpen_compl_singleton.mem_nhds fun h => hq₁p h.symm)
  obtain ⟨q₂, ⟨⟨hq₂W, hq₂ne⟩, hq₂⟩, -⟩ := hp _ hW'
  have hmem : q₁ - q₂ ∈ V := hW (Set.mk_mem_prod hq₁W.1 hq₂W.2)
  have hΓ : q₁ - q₂ ∈ Γ := Γ.sub_mem hq₁.2 hq₂.2
  have h0' := hΓV _ hΓ hmem
  exact hq₂ne (sub_eq_zero.1 h0').symm

scoped instance moduleFinite_matrix : Module.Finite K (Matrix (Fin 2) (Fin 2) L) :=
  Module.Finite.matrix

abbrev ιD : Type := Fin (Module.finrank K (DK K L σ δ₀))

def bD : Module.Basis (ιD K L σ δ₀) K (DK K L σ δ₀) := Module.finBasis K _

def bM (i : ιD K L σ δ₀) : Matrix (Fin 2) (Fin 2) L := (bD K L σ δ₀ i : Matrix (Fin 2) (Fin 2) L)

omit [NumberField L] in
theorem bM_linearIndependent : LinearIndependent K (bM K L σ δ₀) :=
  (bD K L σ δ₀).linearIndependent.map' (DK K L σ δ₀).subtype (Submodule.ker_subtype _)

omit [NumberField L] in
theorem span_bM : Submodule.span K (Set.range (bM K L σ δ₀)) = DK K L σ δ₀ := by
  have : Set.range (bM K L σ δ₀) = (DK K L σ δ₀).subtype '' Set.range (bD K L σ δ₀) := by
    rw [← Set.range_comp]; rfl
  rw [this, Submodule.span_image, (bD K L σ δ₀).span_eq, Submodule.map_top, Submodule.range_subtype]

omit [NumberField L] in
theorem bM_span (x : Matrix (Fin 2) (Fin 2) L) :
    x * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * x.map σ ↔
      x ∈ Submodule.span K (Set.range (bM K L σ δ₀)) := by
  rw [span_bM]; rfl

omit [NumberField L] in
theorem exists_eA : ∃ e : (ιD K L σ δ₀ → AK) ≃ₜ+ RK K L σ δ₀ c,
    ∀ a : ιD K L σ δ₀ → AK, ((e a : RK K L σ δ₀ c) : MK K L) =
      ∑ i, (bM K L σ δ₀ i).map fun l : L => l ⊗ₜ[K] a i := by
  obtain ⟨e, he⟩ :=
    AutomorphicForm.exists_homeomorph_twistedCommutant_map_mul_scalar_forall_coe_eq_sum_map_tmul_of_linearIndependent
      K L AK σ δ₀ c (ιD K L σ δ₀) (bM K L σ δ₀) (bM_linearIndependent K L σ δ₀) (bM_span K L σ δ₀)
  refine ⟨{ e.toEquiv with
      map_add' := fun a a' => ?_
      continuous_toFun := e.continuous
      continuous_invFun := e.symm.continuous }, he⟩
  refine Subtype.ext ?_
  show ((e (a + a') : RK K L σ δ₀ c) : MK K L) = ((e a : RK K L σ δ₀ c) : MK K L) + ((e a' : RK K L σ δ₀ c) : MK K L)
  rw [he, he, he, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ext j k
  simp [Matrix.map_apply, TensorProduct.tmul_add]

def eA : (ιD K L σ δ₀ → AK) ≃ₜ+ RK K L σ δ₀ c := Classical.choose (exists_eA K L σ δ₀ c)

theorem coe_eA (a : ιD K L σ δ₀ → AK) :
    ((eA K L σ δ₀ c a : RK K L σ δ₀ c) : MK K L) = ∑ i, (bM K L σ δ₀ i).map fun l : L => l ⊗ₜ[K] a i :=
  Classical.choose_spec (exists_eA K L σ δ₀ c) a

theorem eA_symm_add (x y : RK K L σ δ₀ c) :
    (eA K L σ δ₀ c).symm (x + y) = (eA K L σ δ₀ c).symm x + (eA K L σ δ₀ c).symm y :=
  (eA K L σ δ₀ c).symm.toAddEquiv.map_add x y

theorem eA_symm_apply_apply (a : ιD K L σ δ₀ → AK) : (eA K L σ δ₀ c).symm (eA K L σ δ₀ c a) = a :=
  (eA K L σ δ₀ c).toEquiv.symm_apply_apply a

theorem eA_apply_symm_apply (r : RK K L σ δ₀ c) : eA K L σ δ₀ c ((eA K L σ δ₀ c).symm r) = r :=
  (eA K L σ δ₀ c).toEquiv.apply_symm_apply r

def algK (k : ιD K L σ δ₀ → K) : ιD K L σ δ₀ → AK := fun i => algebraMap K AK (k i)

omit [NumberField L] [FiniteDimensional K L] in
theorem algK_zero : algK K L σ δ₀ 0 = 0 := by
  funext i; simp [algK]

omit [NumberField L] [FiniteDimensional K L] in
theorem algK_injective : Function.Injective (algK K L σ δ₀) := fun _ _ h =>
  funext fun i => NumberField.AdeleRing.algebraMap_injective (𝓞 K) K (congrFun h i)

theorem eA_algK (k : ιD K L σ δ₀ → K) :
    eA K L σ δ₀ c (algK K L σ δ₀ k) = jR K L σ δ₀ c (∑ i, k i • bD K L σ δ₀ i) := by
  refine Subtype.ext ?_
  rw [coe_eA, coe_jR, Submodule.coe_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Submodule.coe_smul, jM_apply]
  ext j m
  simp only [Matrix.map_apply, Matrix.smul_apply, algK]
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  rfl

theorem mem_Λ_iff_exists_algK (r : RK K L σ δ₀ c) :
    r ∈ Λ K L σ δ₀ c ↔ ∃ k : ιD K L σ δ₀ → K, eA K L σ δ₀ c (algK K L σ δ₀ k) = r := by
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨fun i => (bD K L σ δ₀).repr x i, ?_⟩
    rw [eA_algK, (bD K L σ δ₀).sum_repr x]
  · rintro ⟨k, rfl⟩
    rw [eA_algK]
    exact ⟨_, rfl⟩

theorem exists_isOpen_algebraMap_mem_imp :
    ∃ V : Set AK, IsOpen V ∧ (0 : AK) ∈ V ∧ ∀ k : K, algebraMap K AK k ∈ V → k = 0 := by
  obtain ⟨U, hU, ⟨u₀, hu₀⟩, hUsub⟩ := NumberField.AdelicBox.exists_isOpen_subset_adelicBox K
  refine ⟨(fun x => x + u₀) ⁻¹' U, hU.preimage (continuous_id.add continuous_const), ?_, ?_⟩
  · show (0 : AK) + u₀ ∈ U
    rwa [zero_add]
  · intro k hk
    obtain ⟨k₀, -, huniq⟩ := NumberField.AdelicBox.existsUnique_algebraMap_add_mem_adelicBox K u₀
    have h1 : k = k₀ := huniq k (hUsub hk)
    have h2 : (0 : K) = k₀ :=
      huniq 0 (show algebraMap K AK 0 + u₀ ∈ _ by rw [map_zero, zero_add]; exact hUsub hu₀)
    rw [h1, ← h2]

theorem finite_inter_Λ (C : Set (RK K L σ δ₀ c)) (hC : IsCompact C) :
    (C ∩ (Λ K L σ δ₀ c : Set (RK K L σ δ₀ c))).Finite := by
  obtain ⟨V, hV, h0V, hVK⟩ := exists_isOpen_algebraMap_mem_imp K
  set W : Set (RK K L σ δ₀ c) := eA K L σ δ₀ c '' Set.pi Set.univ (fun _ : ιD K L σ δ₀ => V) with hW
  refine finite_inter_of_isCompact (Λ K L σ δ₀ c) (V := W) ?_ ?_ ?_ hC
  · exact (eA K L σ δ₀ c).toHomeomorph.isOpenMap _ (isOpen_set_pi Set.finite_univ fun _ _ => hV)
  · exact ⟨0, fun i _ => h0V, map_zero _⟩
  · intro x hx hxW
    obtain ⟨k, rfl⟩ := (mem_Λ_iff_exists_algK K L σ δ₀ c x).1 hx
    obtain ⟨a, ha, hax⟩ := hxW
    have hka : algK K L σ δ₀ k = a := ((eA K L σ δ₀ c).injective hax).symm
    have hk : k = 0 := by
      funext i
      apply hVK
      have hai : a i ∈ V := ha i (Set.mem_univ i)
      rw [← hka] at hai
      exact hai
    rw [hk, algK_zero, map_zero]

def boxK : Set (ιD K L σ δ₀ → AK) := Set.pi Set.univ fun _ => NumberField.AdelicBox.adelicBox K

def F : Set (RK K L σ δ₀ c) := (eA K L σ δ₀ c).symm ⁻¹' boxK K L σ δ₀

omit [NumberField L] [FiniteDimensional K L] in
theorem existsUnique_algK_add_mem_boxK (a : ιD K L σ δ₀ → AK) :
    ∃! k : ιD K L σ δ₀ → K, algK K L σ δ₀ k + a ∈ boxK K L σ δ₀ := by
  have h := fun i => NumberField.AdelicBox.existsUnique_algebraMap_add_mem_adelicBox K (a i)
  refine ⟨fun i => Classical.choose (h i).exists, fun i _ => Classical.choose_spec (h i).exists, ?_⟩
  intro k hk
  funext i
  exact (h i).unique (hk i (Set.mem_univ i)) (Classical.choose_spec (h i).exists)

theorem eA_algK_mem_Λ (k : ιD K L σ δ₀ → K) : eA K L σ δ₀ c (algK K L σ δ₀ k) ∈ Λ K L σ δ₀ c :=
  (mem_Λ_iff_exists_algK K L σ δ₀ c _).2 ⟨k, rfl⟩

theorem measurableSet_F [MeasurableSpace (RK K L σ δ₀ c)] [BorelSpace (RK K L σ δ₀ c)] :
    MeasurableSet (F K L σ δ₀ c) := by
  letI : MeasurableSpace AK := NumberField.AdelicHaar.adeleBorel (𝓞 K) K
  haveI : BorelSpace AK := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 K) K
  refine MeasurableSet.preimage ?_ (eA K L σ δ₀ c).symm.continuous.measurable
  exact MeasurableSet.univ_pi fun _ => NumberField.AdelicBox.measurableSet_adelicBox K

theorem isAddFundamentalDomain_F [MeasurableSpace (RK K L σ δ₀ c)] [BorelSpace (RK K L σ δ₀ c)]
    (μ : Measure (RK K L σ δ₀ c)) :
    IsAddFundamentalDomain (Λ K L σ δ₀ c) (F K L σ δ₀ c) μ := by
  refine IsAddFundamentalDomain.mk' (measurableSet_F K L σ δ₀ c).nullMeasurableSet fun r => ?_
  · obtain ⟨k, hk, huniq⟩ := existsUnique_algK_add_mem_boxK K L σ δ₀ ((eA K L σ δ₀ c).symm r)
    refine ⟨⟨eA K L σ δ₀ c (algK K L σ δ₀ k), eA_algK_mem_Λ K L σ δ₀ c k⟩, ?_, ?_⟩
    · show (eA K L σ δ₀ c).symm (eA K L σ δ₀ c (algK K L σ δ₀ k) + r) ∈ boxK K L σ δ₀
      rwa [eA_symm_add, eA_symm_apply_apply]
    · rintro ⟨r', hr'⟩ hr'F
      obtain ⟨k', rfl⟩ := (mem_Λ_iff_exists_algK K L σ δ₀ c r').1 hr'
      have hk'F : (eA K L σ δ₀ c).symm (eA K L σ δ₀ c (algK K L σ δ₀ k') + r) ∈ boxK K L σ δ₀ := hr'F
      rw [eA_symm_add, eA_symm_apply_apply] at hk'F
      have := huniq k' hk'F
      subst this
      rfl

theorem F_subset_image : ∃ C : Set (ιD K L σ δ₀ → AK), IsCompact C ∧
    F K L σ δ₀ c ⊆ eA K L σ δ₀ c '' C := by
  obtain ⟨C₁, hC₁, hsub⟩ := NumberField.AdelicBox.exists_isCompact_adelicBox_subset K
  refine ⟨Set.pi Set.univ fun _ => C₁, isCompact_univ_pi fun _ => hC₁, fun r hr => ?_⟩
  exact ⟨(eA K L σ δ₀ c).symm r, fun i _ => hsub (hr i (Set.mem_univ i)), eA_apply_symm_apply K L σ δ₀ c r⟩

theorem image_subset_F : ∃ U : Set (ιD K L σ δ₀ → AK), IsOpen U ∧ U.Nonempty ∧
    eA K L σ δ₀ c '' U ⊆ F K L σ δ₀ c := by
  obtain ⟨U₁, hU₁, ⟨u₁, hu₁⟩, hsub⟩ := NumberField.AdelicBox.exists_isOpen_subset_adelicBox K
  refine ⟨Set.pi Set.univ fun _ => U₁, isOpen_set_pi Set.finite_univ fun _ _ => hU₁,
    ⟨fun _ => u₁, fun _ _ => hu₁⟩, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  show (eA K L σ δ₀ c).symm (eA K L σ δ₀ c a) ∈ boxK K L σ δ₀
  rw [eA_symm_apply_apply]
  exact fun i _ => hsub (ha i (Set.mem_univ i))

theorem nontrivial_tensor : Nontrivial (L ⊗[K] AK) :=
  ⟨⟨inclA K L 1, inclA K L 0, fun h => one_ne_zero (inclA_injective K L h)⟩⟩

theorem one_ne_zero_RK : (1 : RK K L σ δ₀ c) ≠ 0 := by
  haveI := nontrivial_tensor K L
  intro h
  have := congrArg (fun r : RK K L σ δ₀ c => (r : MK K L) 0 0) h
  simp at this

theorem one_mem_Λ : (1 : RK K L σ δ₀ c) ∈ Λ K L σ δ₀ c :=
  ⟨⟨1, one_mem_DK⟩, Subtype.ext (jM K L).map_one⟩

theorem exists_unit_of_mem_Λ (h2 : Module.finrank K L = 2) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hNL : ∃ z : Lˣ, δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ =
      Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
        Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    (x : RK K L σ δ₀ c) (hx : x ∈ Λ K L σ δ₀ c) (hx0 : x ≠ 0) :
    ∃ v : (RK K L σ δ₀ c)ˣ, (v : RK K L σ δ₀ c) = x ∧ ((v⁻¹ : (RK K L σ δ₀ c)ˣ) : RK K L σ δ₀ c) ∈ Λ K L σ δ₀ c := by
  obtain ⟨d, rfl⟩ := hx
  have hd0 : (d : Matrix (Fin 2) (Fin 2) L) ≠ 0 := fun h => hx0 (by
    have : d = 0 := Subtype.ext h
    rw [this, map_zero])
  obtain ⟨d', hd', h1, h1'⟩ := exists_inv_mem_DK h2 hgen hNL hns d.2 hd0
  refine ⟨⟨jR K L σ δ₀ c d, jR K L σ δ₀ c ⟨d', hd'⟩, ?_, ?_⟩, rfl, ⟨⟨d', hd'⟩, rfl⟩⟩
  · refine Subtype.ext ?_
    rw [Subalgebra.coe_mul, coe_jR, coe_jR, ← map_mul, Subalgebra.coe_one]
    change jM K L ((d : Matrix (Fin 2) (Fin 2) L) * d') = 1
    rw [h1, map_one]
  · refine Subtype.ext ?_
    rw [Subalgebra.coe_mul, coe_jR, coe_jR, ← map_mul, Subalgebra.coe_one]
    change jM K L (d' * (d : Matrix (Fin 2) (Fin 2) L)) = 1
    rw [h1', map_one]

def F' : Set (RK K L σ δ₀ c) := (fun r : RK K L σ δ₀ c => -1 + r) ⁻¹' F K L σ δ₀ c

theorem vadd_F_eq_F' :
    ((⟨1, one_mem_Λ K L σ δ₀ c⟩ : Λ K L σ δ₀ c) +ᵥ F K L σ δ₀ c : Set (RK K L σ δ₀ c)) = F' K L σ δ₀ c := by
  ext r
  rw [Set.mem_vadd_set]
  constructor
  · rintro ⟨f, hf, rfl⟩
    show -1 + ((1 : RK K L σ δ₀ c) + f) ∈ F K L σ δ₀ c
    convert hf using 1
    all_goals try rfl
    exact neg_add_cancel_left (1 : RK K L σ δ₀ c) f
  · intro hr
    refine ⟨-1 + r, hr, ?_⟩
    show (1 : RK K L σ δ₀ c) + (-1 + r) = r
    exact add_neg_cancel_left (1 : RK K L σ δ₀ c) r

theorem exists_isCompact_measure_F_lt [MeasurableSpace (RK K L σ δ₀ c)] [BorelSpace (RK K L σ δ₀ c)]
    (α : Measure (RK K L σ δ₀ c)) [α.IsAddHaarMeasure] :
    ∃ C₀ : Set (RK K L σ δ₀ c), IsCompact C₀ ∧ α (F K L σ δ₀ c) < α C₀ := by
  have hF := isAddFundamentalDomain_F K L σ δ₀ c α
  obtain ⟨Cb, hCb, hFsub⟩ := F_subset_image K L σ δ₀ c
  have hcont : Continuous (eA K L σ δ₀ c) := (eA K L σ δ₀ c).continuous
  have hFlt : α (F K L σ δ₀ c) < ⊤ :=
    (measure_mono hFsub).trans_lt (hCb.image hcont).measure_lt_top
  obtain ⟨U, hU, hUne, hUsub⟩ := image_subset_F K L σ δ₀ c
  have hFpos : 0 < α (F K L σ δ₀ c) :=
    (IsOpen.measure_pos α ((eA K L σ δ₀ c).toHomeomorph.isOpenMap _ hU) (hUne.image _)).trans_le
      (measure_mono hUsub)

  set l₁ : Λ K L σ δ₀ c := ⟨1, one_mem_Λ K L σ δ₀ c⟩ with hl₁
  have hl₁0 : l₁ ≠ 0 := fun h => one_ne_zero_RK K L σ δ₀ c (congrArg Subtype.val h)
  have hdisj : AEDisjoint α (F K L σ δ₀ c) (F' K L σ δ₀ c) := by
    have h := hF.aedisjoint hl₁0.symm
    change AEDisjoint α ((0 : Λ K L σ δ₀ c) +ᵥ F K L σ δ₀ c) (l₁ +ᵥ F K L σ δ₀ c) at h
    rwa [zero_vadd, vadd_F_eq_F'] at h
  have hF'meas : MeasurableSet (F' K L σ δ₀ c) :=
    (measurableSet_F K L σ δ₀ c).preimage (measurable_const_add (-1 : RK K L σ δ₀ c))
  have hF'eq : α (F' K L σ δ₀ c) = α (F K L σ δ₀ c) := measure_preimage_add α _ _

  set C₀ : Set (RK K L σ δ₀ c) :=
    eA K L σ δ₀ c '' Cb ∪ (fun r : RK K L σ δ₀ c => 1 + r) '' (eA K L σ δ₀ c '' Cb) with hC₀
  refine ⟨C₀, (hCb.image hcont).union ((hCb.image hcont).image (continuous_const.add continuous_id)), ?_⟩
  have hsub : F K L σ δ₀ c ∪ F' K L σ δ₀ c ⊆ C₀ := by
    refine Set.union_subset_union hFsub fun r hr => ?_
    exact ⟨-1 + r, hFsub hr, add_neg_cancel_left 1 r⟩
  calc α (F K L σ δ₀ c) < α (F K L σ δ₀ c) + α (F' K L σ δ₀ c) := by
        rw [hF'eq]; exact ENNReal.lt_add_right hFlt.ne hFpos.ne'
    _ = α (F K L σ δ₀ c ∪ F' K L σ δ₀ c) := (measure_union₀ hF'meas.nullMeasurableSet hdisj).symm
    _ ≤ α C₀ := measure_mono hsub

def ψT (v : (RK K L σ δ₀ c)ˣ) : twistedCentralizer K L AK σ (δA K L δ₀ c) :=
  (twistedCentralizerEquivUnits (δA K L δ₀ c)).symm v

omit [NumberField L] [FiniteDimensional K L] in
theorem coe_ψT (v : (RK K L σ δ₀ c)ˣ) :
    ((ψT K L σ δ₀ c v : twistedCentralizer K L AK σ (δA K L δ₀ c)) : GL (Fin 2) (L ⊗[K] AK)) =
      Units.map ((twistedCommutant K L AK σ (δA K L δ₀ c)).val : RK K L σ δ₀ c →* MK K L) v :=
  Units.ext rfl

theorem continuous_ψT : Continuous (ψT K L σ δ₀ c) := by
  have h1 : Continuous fun v : (RK K L σ δ₀ c)ˣ =>
      ((ψT K L σ δ₀ c v : twistedCentralizer K L AK σ (δA K L δ₀ c)) : GL (Fin 2) (L ⊗[K] AK)) := by
    have : (fun v : (RK K L σ δ₀ c)ˣ =>
        ((ψT K L σ δ₀ c v : twistedCentralizer K L AK σ (δA K L δ₀ c)) : GL (Fin 2) (L ⊗[K] AK))) =
        Units.map ((twistedCommutant K L AK σ (δA K L δ₀ c)).val : RK K L σ δ₀ c →* MK K L) :=
      funext (coe_ψT K L σ δ₀ c)
    rw [this]
    exact Continuous.units_map _ continuous_subtype_val
  exact continuous_induced_rng.2 h1

theorem main [IsGalois K L] (h2 : Module.finrank K L = 2)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (u : AKˣ)
    (hN : normString K L AK σ (δA K L δ₀ c) = toTensorGL K L AK (centralScalar (𝓞 K) K u))
    (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
        Matrix.GeneralLinearGroup.scalar (Fin 2) z) :
    ∃ C : Set (twistedCentralizer K L AK σ (δA K L δ₀ c)), IsCompact C ∧
      ∀ t : twistedCentralizer K L AK σ (δA K L δ₀ c),
        NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det
          (baseChangeGL K L (t : GL (Fin 2) (L ⊗[K] AK)))) = 1 →
        ∃ γ ∈ sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀, ∃ k ∈ C,
          (t : GL (Fin 2) (L ⊗[K] AK)) =
            Matrix.GeneralLinearGroup.map (inclA K L) γ * (k : GL (Fin 2) (L ⊗[K] AK)) := by
  classical
  letI : MeasurableSpace (RK K L σ δ₀ c) := borel _
  haveI : BorelSpace (RK K L σ δ₀ c) := ⟨rfl⟩
  set α : Measure (RK K L σ δ₀ c) := Measure.addHaar with hα
  have hNL := exists_norm_eq_scalar K L σ δ₀ c h2 u hN

  have hmul : ∀ x ∈ Λ K L σ δ₀ c, ∀ y ∈ Λ K L σ δ₀ c, x * y ∈ Λ K L σ δ₀ c :=
    fun x hx y hy => Λ_mul K L σ δ₀ c hx hy
  have hF := isAddFundamentalDomain_F K L σ δ₀ c α
  obtain ⟨C₀, hC₀, hlt⟩ := exists_isCompact_measure_F_lt K L σ δ₀ c α
  haveI : Countable (DK K L σ δ₀) := by
    haveI : Countable L := (Module.Free.chooseBasis ℚ L).equivFun.toEquiv.countable_iff.2 inferInstance
    haveI : Countable (Matrix (Fin 2) (Fin 2) L) := inferInstanceAs (Countable (Fin 2 → Fin 2 → L))
    infer_instance
  haveI : Countable (Λ K L σ δ₀ c) := by
    change Countable (Set.range (jR K L σ δ₀ c))
    exact Set.countable_range _ |>.to_subtype
  obtain ⟨C, hC, hall⟩ :=
    MeasureTheory.exists_isCompact_forall_exists_eq_mul_of_map_mul_eq_of_isAddFundamentalDomain
      α (Λ K L σ δ₀ c) hmul (finite_inter_Λ K L σ δ₀ c) (exists_unit_of_mem_Λ K L σ δ₀ c h2 hgen hNL hns)
      (F K L σ δ₀ c) hF C₀ hC₀ hlt
  refine ⟨ψT K L σ δ₀ c '' C, hC.image (continuous_ψT K L σ δ₀ c), fun t ht => ?_⟩

  have hn : distribHaarChar AL (Matrix.GeneralLinearGroup.det
      (baseChangeGL K L (t : GL (Fin 2) (L ⊗[K] AK)))) = 1 := by
    have h := ht
    simp only [NumberField.TateGlobal.ideleNorm] at h
    exact_mod_cast h
  have hM :=
    AutomorphicForm.map_mul_addHaar_twistedCommutant_eq_inv_distribHaarChar_det_smul_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two
      K L h2 σ hgen δ₀ c u hN α t
  change Measure.map _ α = (distribHaarChar AL (Matrix.GeneralLinearGroup.det
      (baseChangeGL K L (t : GL (Fin 2) (L ⊗[K] AK)))))⁻¹ • α ∧
    Measure.map _ α = (distribHaarChar AL (Matrix.GeneralLinearGroup.det
      (baseChangeGL K L (t : GL (Fin 2) (L ⊗[K] AK)))))⁻¹ • α at hM
  rw [hn, inv_one, one_smul] at hM
  set uR : (RK K L σ δ₀ c)ˣ := twistedCentralizerEquivUnits (δA K L δ₀ c) t with huR
  obtain ⟨l, hlΛ, hlinvΛ, k, hkC, hulk⟩ := hall uR hM.1 hM.2
  obtain ⟨d, hd⟩ := hlΛ
  obtain ⟨d', hd'⟩ := hlinvΛ
  have hdd' : (d : Matrix (Fin 2) (Fin 2) L) * (d' : Matrix (Fin 2) (Fin 2) L) = 1 := by
    apply jM_injective K L
    have h := congrArg (fun r : RK K L σ δ₀ c => (r : MK K L)) l.mul_inv
    simp only [Subalgebra.coe_mul, Subalgebra.coe_one] at h
    rw [← hd, ← hd', coe_jR, coe_jR, ← map_mul] at h
    rw [h, map_one]
  have hd'd : (d' : Matrix (Fin 2) (Fin 2) L) * (d : Matrix (Fin 2) (Fin 2) L) = 1 := by
    apply jM_injective K L
    have h := congrArg (fun r : RK K L σ δ₀ c => (r : MK K L)) l.inv_mul
    simp only [Subalgebra.coe_mul, Subalgebra.coe_one] at h
    rw [← hd, ← hd', coe_jR, coe_jR, ← map_mul] at h
    rw [h, map_one]
  let γ : GL (Fin 2) L := ⟨d, d', hdd', hd'd⟩
  refine ⟨γ, ?_, ψT K L σ δ₀ c k, ⟨k, hkC, rfl⟩, ?_⟩
  · rw [mem_sigmaCentralizer_iff, mul_inv_eq_iff_eq_mul]
    exact Units.ext d.2
  · refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.coe_mul]
    change (((uR : (RK K L σ δ₀ c)ˣ) : RK K L σ δ₀ c) : MK K L) =
      jM K L (d : Matrix (Fin 2) (Fin 2) L) * (((k : (RK K L σ δ₀ c)ˣ) : RK K L σ δ₀ c) : MK K L)
    rw [hulk, Units.val_mul, Subalgebra.coe_mul, ← hd, coe_jR]

end Adelic

end P2mFujisakiD
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isCompact_forall_exists_mem_sigmaCentralizer_eq_mul_of_ideleNorm_det_eq_one_of_forall_ne_scalar_of_finrank_eq_two.P2mFujisakiD"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isCompact_forall_exists_mem_sigmaCentralizer_eq_mul_of_ideleNorm_det_eq_one_of_forall_ne_scalar_of_finrank_eq_two.P2mFujisakiD"

open NumberField
open scoped TensorProduct TensorProduct.RightActions

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hN : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ
        (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K u))
    (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
        Matrix.GeneralLinearGroup.scalar (Fin 2) z) :
    ∃ C : Set (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
        (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)),
      IsCompact C ∧
        ∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
            (Matrix.GeneralLinearGroup.map
                (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
              Matrix.GeneralLinearGroup.scalar (Fin 2) c),
          NumberField.TateGlobal.ideleNorm L
            (Matrix.GeneralLinearGroup.det
              (Matrix.GeneralLinearGroup.map
                (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                  (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
                (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) = 1 →
          ∃ γ ∈ AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀,
            ∃ k ∈ C,
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) =
                Matrix.GeneralLinearGroup.map
                    (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) γ *
                  (k : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :=
  P2mFujisakiD.main K L σ δ₀ c h2 hgen u hN hns

end S_AutomorphicForm_exists_isCompact_forall_exists_mem_sigmaCentralizer_eq_mul_of_ideleNorm_det_eq_one_of_forall_ne_scalar_of_finrank_eq_two
end P2MW
export P2MW.S_AutomorphicForm_exists_isCompact_forall_exists_mem_sigmaCentralizer_eq_mul_of_ideleNorm_det_eq_one_of_forall_ne_scalar_of_finrank_eq_two (solution)
