-- Prove2me | solution 1 for AutomorphicForm.exists_measure_fundamentalDomain_op_twistedCentralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_eq_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/b7326746-7005-58dc-870c-dd5f69808f28

import Theorems.Thm_AutomorphicForm_exists_measure_fundamentalDomain_op_centralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_mem_center
import Theorems.Thm_AutomorphicForm_exists_continuousMulEquiv_centralizer_twistedCentralizer_of_eq_scalar
import Theorems.Thm_AutomorphicForm_map_genuineRingEquiv_sigmaGL_and_toTensorGL_and_includeLeft
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_idelesBaseChange
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_measure_fundamentalDomain_op_twistedCentralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_eq_scalar
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11 ContinuousAddEquiv.preimage_mulLeft_smul"

set_option autoImplicit false

open MeasureTheory NumberField AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions ENNReal NNReal

noncomputable section

namespace P2mCentralCovolTw

section Algebra

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (B : Type) [CommRing B] [Algebra K B]

local notation "incl" => (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] B)

theorem sigmaTensor_includeLeft (σ : L ≃ₐ[K] L) (l : L) :
    sigmaTensor K L B σ (l ⊗ₜ[K] (1 : B)) = σ l ⊗ₜ[K] (1 : B) := by
  simp [sigmaTensor, Algebra.TensorProduct.map_tmul]

theorem sigmaGL_map_includeLeft (σ : L ≃ₐ[K] L) (g : GL (Fin 2) L) :
    sigmaGL K L B σ (Matrix.GeneralLinearGroup.map incl g) =
      Matrix.GeneralLinearGroup.map incl (Matrix.GeneralLinearGroup.map (σ : L →+* L) g) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show sigmaTensor K L B σ (Algebra.TensorProduct.includeLeftRingHom (g i j)) =
    Algebra.TensorProduct.includeLeftRingHom ((σ : L →+* L) (g i j))
  rw [Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.includeLeftRingHom_apply,
    sigmaTensor_includeLeft]
  rfl

theorem map_includeLeft_scalar (d : Lˣ) :
    Matrix.GeneralLinearGroup.map incl (Matrix.GeneralLinearGroup.scalar (Fin 2) d) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (incl : L →* L ⊗[K] B) d) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [Matrix.GeneralLinearGroup.map_apply]
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply, Units.coe_map,
    MonoidHom.coe_coe]
  split_ifs <;> simp

variable {K L B} in
theorem scalar_mul_comm {R : Type*} [CommRing R] (c : Rˣ) (g : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) c * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  refine Units.ext ?_
  show Matrix.scalar (Fin 2) (c : R) * (g : Matrix (Fin 2) (Fin 2) R) =
    (g : Matrix (Fin 2) (Fin 2) R) * Matrix.scalar (Fin 2) (c : R)
  exact (Matrix.scalar_commute (c : R) (fun r => Commute.all _ r) _).eq

theorem conj_eq_scalar (σ : L ≃ₐ[K] L) (δ₀ h : GL (Fin 2) L) (d : Lˣ)
    (hd : h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h =
      Matrix.GeneralLinearGroup.scalar (Fin 2) d)
    (c : (L ⊗[K] B)ˣ) :
    (Matrix.GeneralLinearGroup.map incl h)⁻¹ *
        (Matrix.GeneralLinearGroup.map incl δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) c) *
        sigmaGL K L B σ (Matrix.GeneralLinearGroup.map incl h) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (incl : L →* L ⊗[K] B) d * c) := by
  rw [sigmaGL_map_includeLeft, map_mul, ← map_includeLeft_scalar K L B d, ← hd, map_mul, map_mul,
    map_inv]
  simp only [mul_assoc]
  rw [scalar_mul_comm]

theorem toTensorGL_map_algebraMap (s₀ : GL (Fin 2) K) :
    toTensorGL K L B (Matrix.GeneralLinearGroup.map (algebraMap K B) s₀) =
      Matrix.GeneralLinearGroup.map incl (Matrix.GeneralLinearGroup.map (algebraMap K L) s₀) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show (Algebra.TensorProduct.includeRight : B →ₐ[K] L ⊗[K] B) (algebraMap K B (s₀ i j)) =
    Algebra.TensorProduct.includeLeftRingHom (algebraMap K L (s₀ i j))
  rw [Algebra.TensorProduct.includeLeftRingHom_apply, AlgHom.commutes,
    Algebra.TensorProduct.algebraMap_apply]

theorem map_sigma_map_algebraMap (σ : L ≃ₐ[K] L) (s₀ : GL (Fin 2) K) :
    Matrix.GeneralLinearGroup.map (σ : L →+* L) (Matrix.GeneralLinearGroup.map (algebraMap K L) s₀) =
      Matrix.GeneralLinearGroup.map (algebraMap K L) s₀ := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show (σ : L →+* L) (algebraMap K L (s₀ i j)) = algebraMap K L (s₀ i j)
  exact σ.commutes _

theorem conj_mem_sigmaCentralizer (σ : L ≃ₐ[K] L) (δ₀ h : GL (Fin 2) L) (d : Lˣ)
    (hd : h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h =
      Matrix.GeneralLinearGroup.scalar (Fin 2) d)
    (s₀ : GL (Fin 2) K) :
    h * Matrix.GeneralLinearGroup.map (algebraMap K L) s₀ * h⁻¹ ∈
      sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀ := by
  rw [mem_sigmaCentralizer_iff]
  set sL := Matrix.GeneralLinearGroup.map (algebraMap K L) s₀ with hsL
  set θ := Matrix.GeneralLinearGroup.map (n := Fin 2) (σ : L →+* L) with hθ
  have hδ₀ : δ₀ = h * Matrix.GeneralLinearGroup.scalar (Fin 2) d * (θ h)⁻¹ := by
    rw [← hd]; group
  have hσs : θ sL = sL := map_sigma_map_algebraMap K L σ s₀
  have hcomm : Matrix.GeneralLinearGroup.scalar (Fin 2) d * sL =
      sL * Matrix.GeneralLinearGroup.scalar (Fin 2) d := scalar_mul_comm d sL
  rw [hδ₀, map_mul, map_mul, map_inv, hσs]
  calc h * sL * h⁻¹ * (h * Matrix.GeneralLinearGroup.scalar (Fin 2) d * (θ h)⁻¹) * (θ h * sL * (θ h)⁻¹)⁻¹
      = h * (sL * Matrix.GeneralLinearGroup.scalar (Fin 2) d) * sL⁻¹ * (θ h)⁻¹ := by group
    _ = h * (Matrix.GeneralLinearGroup.scalar (Fin 2) d * sL) * sL⁻¹ * (θ h)⁻¹ := by rw [hcomm]
    _ = h * Matrix.GeneralLinearGroup.scalar (Fin 2) d * (θ h)⁻¹ := by group

end Algebra

section Descent

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [CharZero K]
  (B : Type) [CommRing B] [Algebra K B]

theorem exists_eq_algebraMap_of_tmul_eq (l : L) (a : B)
    (h : l ⊗ₜ[K] (1 : B) = (1 : L) ⊗ₜ[K] a) : ∃ k : K, a = algebraMap K B k := by
  have h1 := congrArg (fun z => TensorProduct.lid K B
    (LinearMap.rTensor B (Algebra.trace K L) z)) h
  simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul] at h1
  have htr1 : Algebra.trace K L (1 : L) = (Module.finrank K L : K) := by
    rw [← map_one (algebraMap K L), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one]
  rw [htr1] at h1
  have hn : (Module.finrank K L : K) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  refine ⟨(Module.finrank K L : K)⁻¹ * Algebra.trace K L l, ?_⟩
  rw [Algebra.algebraMap_eq_smul_one, mul_smul, h1, smul_smul, inv_mul_cancel₀ hn, one_smul]

theorem exists_eq_map_algebraMap_of_toTensorGL_eq (hinj : Function.Injective (algebraMap K B))
    (s : GL (Fin 2) B) (g : GL (Fin 2) L)
    (h : toTensorGL K L B s =
      Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] B) g) :
    ∃ s₀ : GL (Fin 2) K, s = Matrix.GeneralLinearGroup.map (algebraMap K B) s₀ := by
  haveI : Nontrivial B := hinj.nontrivial
  have hent : ∀ i j : Fin 2, ∃ k : K, (s : Matrix (Fin 2) (Fin 2) B) i j = algebraMap K B k := by
    intro i j
    have hij := congrArg (fun x : GL (Fin 2) (L ⊗[K] B) => (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] B)) i j) h
    refine exists_eq_algebraMap_of_tmul_eq K L B (g i j) (s i j) ?_
    change (Algebra.TensorProduct.includeRight : B →ₐ[K] L ⊗[K] B) (s i j) =
      Algebra.TensorProduct.includeLeftRingHom (g i j) at hij
    rw [Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.includeRight_apply] at hij
    exact hij.symm
  choose k hk using hent
  set M : Matrix (Fin 2) (Fin 2) K := Matrix.of fun i j => k i j with hM
  have hMs : (algebraMap K B).mapMatrix M = (s : Matrix (Fin 2) (Fin 2) B) := by
    ext i j
    simp [hM, hk]
  have hdet : M.det ≠ 0 := by
    intro h0
    have h1 : (s : Matrix (Fin 2) (Fin 2) B).det = 0 := by
      rw [← hMs, ← RingHom.map_det, h0, map_zero]
    exact (Matrix.isUnits_det_units s).ne_zero h1
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet, Units.ext ?_⟩
  rw [← hMs]
  rfl

end Descent

section Band

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

omit [FiniteDimensional K L] [IsGalois K L] in

theorem det_map_baseChange (s : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    Matrix.GeneralLinearGroup.det
        (Matrix.GeneralLinearGroup.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β s) =
      AutomorphicForm.TransversalMeasure.idelesBaseChange K L (Matrix.GeneralLinearGroup.det s) := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, AutomorphicForm.TransversalMeasure.idelesBaseChange,
    M4aHerbrand.GenuineDescent.genuineBaseChange_β, RingHom.map_det]

theorem ideleNorm_det_conj_toTensorGL (y : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (s : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.map
        (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
          (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
        (y * toTensorGL K L (AdeleRing (𝓞 K) K) s * y⁻¹))) =
      NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det s) ^ Module.finrank K L := by
  have hTS := (AutomorphicForm.map_genuineRingEquiv_sigmaGL_and_toTensorGL_and_includeLeft K L
    (M4aHerbrand.GenuineDescent.genuineDescentDatum K L)).2.1 s
  rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, mul_inv_cancel_comm, hTS,
    det_map_baseChange, NumberField.TateGlobal.ideleNorm_idelesBaseChange]

theorem pow_mem_Icc_iff {N a b : ℝ} (hN : 0 < N) (ha : 0 < a) (hab : a ≤ b) {n : ℕ} (hn : 0 < n) :
    N ^ n ∈ Set.Icc a b ↔ N ∈ Set.Icc (a ^ (n : ℝ)⁻¹) (b ^ (n : ℝ)⁻¹) := by
  have hb : 0 ≤ b := (ha.trans_le hab).le
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  rw [Set.mem_Icc, Set.mem_Icc, ← Real.rpow_natCast,
    Real.rpow_inv_le_iff_of_pos ha.le hN.le hn', Real.le_rpow_inv_iff_of_pos hN.le hb hn']

end Band

section Main

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

abbrev inclA : L →+* L ⊗[K] AdeleRing (𝓞 K) K := Algebra.TensorProduct.includeLeftRingHom

abbrev Emap : L ⊗[K] AdeleRing (𝓞 K) K →+* AdeleRing (𝓞 L) L :=
  ((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
    (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom

abbrev δA (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) :
    GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) :=
  Matrix.GeneralLinearGroup.map (inclA K L) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) c

abbrev Tw (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) :
    Subgroup (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :=
  AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (δA K L δ₀ c)

abbrev ΓTw (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) :
    Subgroup (Tw K L σ δ₀ c) :=
  ((AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀).map
    (Matrix.GeneralLinearGroup.map (inclA K L))).subgroupOf (Tw K L σ δ₀ c)

abbrev Z1 : Subgroup (AdelicGL2 (𝓞 K) K) :=
  Subgroup.centralizer ({(1 : AdelicGL2 (𝓞 K) K)} : Set (AdelicGL2 (𝓞 K) K))

abbrev ΓK1 : Subgroup (Z1 K) := ((globalPoints (𝓞 K) K).range).subgroupOf (Z1 K)

theorem main
    (σ : L ≃ₐ[K] L) (hσ : ∀ θ : L ≃ₐ[K] L, θ ∈ Subgroup.zpowers σ)
    (δ₀ h : GL (Fin 2) L) (d : Lˣ)
    (hd : h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h =
      Matrix.GeneralLinearGroup.scalar (Fin 2) d)
    (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)
    (τ' : Measure (Tw K L σ δ₀ c)) [τ'.IsHaarMeasure] :
    ∃ C : ENNReal, C ≠ 0 ∧ C ≠ ⊤ ∧
      ∀ D' : Set (Tw K L σ δ₀ c), IsFundamentalDomain (ΓTw K L σ δ₀ c).op D' τ' →
        ∀ a b : ℝ, 0 < a → a ≤ b →
          τ' (D' ∩ {t | NumberField.TateGlobal.ideleNorm L
            (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (Emap K L)
                (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ∈ Set.Icc a b}) =
            C * ENNReal.ofReal (Real.log (b / a)) := by

  haveI := isTopologicalRing_tensor K L (AdeleRing (𝓞 K) K)
  haveI := isTopologicalGroup_tensorGL K L (AdeleRing (𝓞 K) K)
  haveI : BorelSpace (Tw K L σ δ₀ c) := ⟨rfl⟩
  haveI : BorelSpace (Z1 K) := ⟨rfl⟩

  have hζ : (Matrix.GeneralLinearGroup.map (inclA K L) h)⁻¹ * δA K L δ₀ c *
      sigmaGL K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map (inclA K L) h) =
      Matrix.GeneralLinearGroup.scalar (Fin 2)
        (Units.map ((inclA K L) : L →* L ⊗[K] AdeleRing (𝓞 K) K) d * c) :=
    conj_eq_scalar K L (AdeleRing (𝓞 K) K) σ δ₀ h d hd c

  obtain ⟨e₀, he₀⟩ :=
    AutomorphicForm.exists_continuousMulEquiv_centralizer_twistedCentralizer_of_eq_scalar
      K L σ hσ (AdeleRing (𝓞 K) K) 1 ⟨1, (map_one _).symm⟩ (δA K L δ₀ c)
      (Matrix.GeneralLinearGroup.map (inclA K L) h) _ hζ
  set τ₀ : Measure (Z1 K) := Measure.map e₀.symm τ' with hτ₀
  haveI : τ₀.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map τ' e₀.symm

  obtain ⟨CK, hCK0, hCKt, hCK⟩ :=
    AutomorphicForm.exists_measure_fundamentalDomain_op_centralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_mem_center
      K 1 (Subgroup.one_mem _) τ₀
  have hn : 0 < Module.finrank K L := Module.finrank_pos
  have hnR : (0 : ℝ) < Module.finrank K L := Nat.cast_pos.2 hn
  refine ⟨CK * ENNReal.ofReal ((Module.finrank K L : ℝ)⁻¹), ?_, ?_, fun D' hD' a b ha hab => ?_⟩
  · refine mul_ne_zero hCK0 ?_
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact inv_pos.2 hnR
  · exact ENNReal.mul_ne_top hCKt ENNReal.ofReal_ne_top

  have hinj : Function.Injective (algebraMap K (AdeleRing (𝓞 K) K)) :=
    NumberField.AdeleRing.algebraMap_injective (𝓞 K) K
  have hmemK : ∀ t : Tw K L σ δ₀ c, t ∈ ΓTw K L σ δ₀ c → e₀.symm t ∈ ΓK1 K := by
    intro t ht
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at ht
    obtain ⟨g₁, -, hg₁⟩ := ht
    have hts : ((e₀ (e₀.symm t) : Tw K L σ δ₀ c) : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) =
        Matrix.GeneralLinearGroup.map (inclA K L) h *
          toTensorGL K L (AdeleRing (𝓞 K) K) ((e₀.symm t : Z1 K) : GL (Fin 2) (AdeleRing (𝓞 K) K)) *
          (Matrix.GeneralLinearGroup.map (inclA K L) h)⁻¹ := he₀ _
    rw [ContinuousMulEquiv.apply_symm_apply] at hts
    have htens : toTensorGL K L (AdeleRing (𝓞 K) K)
        ((e₀.symm t : Z1 K) : GL (Fin 2) (AdeleRing (𝓞 K) K)) =
        Matrix.GeneralLinearGroup.map (inclA K L) (h⁻¹ * g₁ * h) := by
      rw [map_mul, map_mul, map_inv, hg₁, hts]
      group
    obtain ⟨s₀, hs₀⟩ := exists_eq_map_algebraMap_of_toTensorGL_eq K L (AdeleRing (𝓞 K) K) hinj
      ((e₀.symm t : Z1 K) : GL (Fin 2) (AdeleRing (𝓞 K) K)) (h⁻¹ * g₁ * h) htens
    rw [Subgroup.mem_subgroupOf]
    exact ⟨s₀, hs₀.symm⟩
  have hmemL : ∀ s : Z1 K, s ∈ ΓK1 K → e₀ s ∈ ΓTw K L σ δ₀ c := by
    intro s hs
    rw [Subgroup.mem_subgroupOf] at hs
    obtain ⟨s₀, hs₀⟩ := hs
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    refine ⟨h * Matrix.GeneralLinearGroup.map (algebraMap K L) s₀ * h⁻¹,
      conj_mem_sigmaCentralizer K L σ δ₀ h d hd s₀, ?_⟩
    rw [he₀ s, ← hs₀]
    show _ = Matrix.GeneralLinearGroup.map (inclA K L) h * toTensorGL K L (AdeleRing (𝓞 K) K)
      (Matrix.GeneralLinearGroup.map (algebraMap K (AdeleRing (𝓞 K) K)) s₀) *
        (Matrix.GeneralLinearGroup.map (inclA K L) h)⁻¹
    rw [toTensorGL_map_algebraMap, map_mul, map_mul, map_inv]

  let eΓ : (ΓTw K L σ δ₀ c).op → (ΓK1 K).op := fun g =>
    ⟨MulOpposite.op (e₀.symm (MulOpposite.unop (g : (Tw K L σ δ₀ c)ᵐᵒᵖ))),
      Subgroup.mem_op.2 (hmemK _ (Subgroup.mem_op.1 g.2))⟩
  have heΓ : ∀ g : (ΓTw K L σ δ₀ c).op, ((eΓ g : (ΓK1 K).op) : (Z1 K)ᵐᵒᵖ) =
      MulOpposite.op (e₀.symm (MulOpposite.unop (g : (Tw K L σ δ₀ c)ᵐᵒᵖ))) := fun _ => rfl
  have hbij : Function.Bijective eΓ := by
    constructor
    · intro g₁ g₂ hg
      have hg' := congrArg (fun x : (ΓK1 K).op => MulOpposite.unop (x : (Z1 K)ᵐᵒᵖ)) hg
      simp only [heΓ, MulOpposite.unop_op] at hg'
      exact Subtype.ext (MulOpposite.unop_injective (e₀.symm.injective hg'))
    · intro q
      refine ⟨⟨MulOpposite.op (e₀ (MulOpposite.unop (q : (Z1 K)ᵐᵒᵖ))),
        Subgroup.mem_op.2 (hmemL _ (Subgroup.mem_op.1 q.2))⟩, ?_⟩
      apply Subtype.ext
      rw [heΓ]
      simp only [MulOpposite.unop_op, ContinuousMulEquiv.symm_apply_apply, MulOpposite.op_unop]
  have hsemi : ∀ (g : (ΓTw K L σ δ₀ c).op) (x : Z1 K), e₀ (eΓ g • x) = g • e₀ x := by
    intro g x
    rw [Subgroup.smul_def, Subgroup.smul_def, MulOpposite.smul_eq_mul_unop,
      MulOpposite.smul_eq_mul_unop, heΓ, MulOpposite.unop_op, map_mul,
      ContinuousMulEquiv.apply_symm_apply]

  let em : Z1 K ≃ᵐ Tw K L σ δ₀ c := e₀.toHomeomorph.toMeasurableEquiv
  have hems : ∀ t : Tw K L σ δ₀ c, em.symm t = e₀.symm t := fun _ => rfl
  have hqmp : Measure.QuasiMeasurePreserving e₀ τ₀ τ' := by
    refine ⟨e₀.continuous.measurable, ?_⟩
    have hmm : Measure.map e₀ τ₀ = τ' := by
      show Measure.map em (Measure.map em.symm τ') = τ'
      exact em.map_map_symm
    rw [hmm]
  have hΩ : IsFundamentalDomain (ΓK1 K).op (e₀ ⁻¹' D') τ₀ :=
    hD'.preimage_of_equiv hqmp hbij (fun g x => hsemi g x)

  have hb : 0 < b := ha.trans_le hab
  have ha' : 0 < a ^ (Module.finrank K L : ℝ)⁻¹ := Real.rpow_pos_of_pos ha _
  have hab' : a ^ (Module.finrank K L : ℝ)⁻¹ ≤ b ^ (Module.finrank K L : ℝ)⁻¹ :=
    Real.rpow_le_rpow ha.le hab (inv_nonneg.2 hnR.le)
  have key := hCK (e₀ ⁻¹' D') hΩ _ _ ha' hab'
  have hset : D' ∩ {t : Tw K L σ δ₀ c | NumberField.TateGlobal.ideleNorm L
      (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (Emap K L)
        (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ∈ Set.Icc a b} =
      em.symm ⁻¹' (e₀ ⁻¹' D' ∩ {s : Z1 K | NumberField.TateGlobal.ideleNorm K
        (Matrix.GeneralLinearGroup.det (s : AdelicGL2 (𝓞 K) K)) ∈
          Set.Icc (a ^ (Module.finrank K L : ℝ)⁻¹) (b ^ (Module.finrank K L : ℝ)⁻¹)}) := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, hems,
      ContinuousMulEquiv.apply_symm_apply]
    refine and_congr Iff.rfl ?_
    have ht : ((t : Tw K L σ δ₀ c) : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) =
        Matrix.GeneralLinearGroup.map (inclA K L) h * toTensorGL K L (AdeleRing (𝓞 K) K)
          ((e₀.symm t : Z1 K) : GL (Fin 2) (AdeleRing (𝓞 K) K)) *
          (Matrix.GeneralLinearGroup.map (inclA K L) h)⁻¹ := by
      rw [← he₀ (e₀.symm t), ContinuousMulEquiv.apply_symm_apply]
    rw [ht, ideleNorm_det_conj_toTensorGL K L]
    exact pow_mem_Icc_iff (NumberField.TateGlobal.ideleNorm_pos (F := K) _) ha hab hn
  rw [hset, ← MeasurableEquiv.map_apply]
  show τ₀ _ = _
  rw [key]
  have hlog : Real.log (b ^ (Module.finrank K L : ℝ)⁻¹ / a ^ (Module.finrank K L : ℝ)⁻¹) =
      (Module.finrank K L : ℝ)⁻¹ * Real.log (b / a) := by
    rw [← Real.div_rpow hb.le ha.le, Real.log_rpow (div_pos hb ha)]
  rw [hlog, ENNReal.ofReal_mul (inv_nonneg.2 hnR.le), mul_assoc]

end Main

end P2mCentralCovolTw

end

open MeasureTheory NumberField
open scoped TensorProduct

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hσ : ∀ θ : L ≃ₐ[K] L, θ ∈ Subgroup.zpowers σ)
    (δ₀ h : GL (Fin 2) L) (d : Lˣ)
    (hd : h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h =
      Matrix.GeneralLinearGroup.scalar (Fin 2) d)
    (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)
    (τ' : Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
      (Matrix.GeneralLinearGroup.map
          (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
        Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    [τ'.IsHaarMeasure] :
    ∃ C : ENNReal, C ≠ 0 ∧ C ≠ ⊤ ∧
      ∀ D' : Set (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
          (Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
            Matrix.GeneralLinearGroup.scalar (Fin 2) c)),
        IsFundamentalDomain
          (((AutomorphicForm.sigmaCentralizer
              (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀).map
              (Matrix.GeneralLinearGroup.map
                (Algebra.TensorProduct.includeLeftRingHom :
                  L →+* L ⊗[K] AdeleRing (𝓞 K) K))).subgroupOf
            (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
              (Matrix.GeneralLinearGroup.map
                  (Algebra.TensorProduct.includeLeftRingHom :
                    L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
                Matrix.GeneralLinearGroup.scalar (Fin 2) c))).op D' τ' →
        ∀ a b : ℝ, 0 < a → a ≤ b →
          τ' (D' ∩ {t | NumberField.TateGlobal.ideleNorm L
            (Matrix.GeneralLinearGroup.det
              (Matrix.GeneralLinearGroup.map
                (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                  (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
                (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ∈ Set.Icc a b}) =
            C * ENNReal.ofReal (Real.log (b / a)) :=
  P2mCentralCovolTw.main K L σ hσ δ₀ h d hd c τ'

end S_AutomorphicForm_exists_measure_fundamentalDomain_op_twistedCentralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_eq_scalar
end P2MW
export P2MW.S_AutomorphicForm_exists_measure_fundamentalDomain_op_twistedCentralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_eq_scalar (solution)
