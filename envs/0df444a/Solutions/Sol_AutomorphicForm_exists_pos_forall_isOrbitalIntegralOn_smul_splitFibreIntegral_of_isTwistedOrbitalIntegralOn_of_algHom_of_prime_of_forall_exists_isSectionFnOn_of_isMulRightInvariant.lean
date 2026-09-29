-- Prove2me | solution 1 for AutomorphicForm.exists_pos_forall_isOrbitalIntegralOn_smul_splitFibreIntegral_of_isTwistedOrbitalIntegralOn_of_algHom_of_prime_of_forall_exists_isSectionFnOn_of_isMulRightInvariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/893f2475-04fe-5c2d-9a57-c84f871d6e16

import Definitions.Def_AutomorphicForm_SplitFibreIntegral
import Theorems.Thm_AutomorphicForm_SplitPlace_continuous_coords_and_coords_sigmaGL_and_coords_normString_and_exists_pos_map_coords_eq_smul_pi
import Theorems.Thm_AutomorphicForm_integral_twistedConj_mul_eq_integral_conj_fibreIntegral_mul
import Theorems.Thm_AutomorphicForm_integral_mul_eq_integral_mul_of_forall_integral_subgroup_mul_eq_one
import Theorems.Thm_MeasureTheory_Measure_isInvInvariant_of_isMulRightInvariant
import Theorems.Thm_AutomorphicForm_isInvInvariant_of_coupled_of_isInvInvariant
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_smul_splitFibreIntegral_of_isTwistedOrbitalIntegralOn_of_algHom_of_prime_of_forall_exists_isSectionFnOn_of_isMulRightInvariant

set_option autoImplicit false

open MeasureTheory
open scoped TensorProduct TensorProduct.RightActions NNReal

open MeasureTheory
open scoped TensorProduct TensorProduct.RightActions NNReal

namespace AutomorphicForm
p2m_export "AutomorphicForm" "SplitPlace.coords SplitPlace.listProd SplitPlace.string splitFibreIntegral isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL glBorelOf borelSpace_glBorelOf centralizerBorel toTensorGL sigmaTensor sigmaGL normString IsNormConjugator twistedCentralizer twistedCentralizerBorel IsSectionFnOn IsOrbitalIntegralOn IsTwistedOrbitalIntegralOn Coupled IsRegularSemisimple mem_sigmaCentralizer_iff mem_sigmaCentralizer_iff_inv SplitPlace.continuous_coords_and_coords_sigmaGL_and_coords_normString_and_exists_pos_map_coords_eq_smul_pi integral_twistedConj_mul_eq_integral_conj_fibreIntegral_mul integral_mul_eq_integral_mul_of_forall_integral_subgroup_mul_eq_one isInvInvariant_of_coupled_of_isInvInvariant"
namespace SplitTransfer
p2m_open "AutomorphicForm"

section CentralizerRing

p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_smul_splitFibreIntegral_of_isTwistedOrbitalIntegralOn_of_algHom_of_prime_of_forall_exists_isSectionFnOn_of_isMulRightInvariant.AutomorphicForm"

namespace RegularCentralizer

section Ring

variable {A : Type*} [CommRing A]

theorem exists_eq_smul_one_add_smul_of_mul_eq_mul {G X : Matrix (Fin 2) (Fin 2) A}
    (hd : IsUnit (Matrix.trace G ^ 2 - 4 * Matrix.det G)) (hX : X * G = G * X) :
    ∃ l m : A, X = l • (1 : Matrix (Fin 2) (Fin 2) A) + m • G := by
  rw [Matrix.trace_fin_two, Matrix.det_fin_two] at hd
  obtain ⟨u, hu⟩ := hd
  have hu1 : (↑u⁻¹ : A) * ↑u = 1 := u.inv_mul
  have h00 : (X * G) 0 0 = (G * X) 0 0 := by rw [hX]
  have h01 : (X * G) 0 1 = (G * X) 0 1 := by rw [hX]
  have h10 : (X * G) 1 0 = (G * X) 1 0 := by rw [hX]
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10
  obtain ⟨Z, hZ⟩ : ∃ Z : A,
      Z = (G 0 0 - G 1 1) * (X 0 0 - X 1 1) + 2 * (G 1 0 * X 0 1 + G 0 1 * X 1 0) := ⟨_, rfl⟩
  refine ⟨X 0 0 - (↑u⁻¹ : A) * Z * G 0 0, (↑u⁻¹ : A) * Z, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  · simp
  · simp
    linear_combination (-(X 0 1)) * hu1 + (X 0 1 * (↑u⁻¹ : A)) * hu -
      ((↑u⁻¹ : A) * (G 0 0 - G 1 1)) * h01 + (2 * (↑u⁻¹ : A) * G 0 1) * h00 -
      ((↑u⁻¹ : A) * G 0 1) * hZ
  · simp
    linear_combination (-(X 1 0)) * hu1 + (X 1 0 * (↑u⁻¹ : A)) * hu +
      ((↑u⁻¹ : A) * (G 0 0 - G 1 1)) * h10 - (2 * (↑u⁻¹ : A) * G 1 0) * h00 -
      ((↑u⁻¹ : A) * G 1 0) * hZ
  · simp
    linear_combination (X 0 0 - X 1 1) * hu1 - ((X 0 0 - X 1 1) * (↑u⁻¹ : A)) * hu -
      (2 * (↑u⁻¹ : A) * G 1 0) * h01 + (2 * (↑u⁻¹ : A) * G 0 1) * h10 +
      ((↑u⁻¹ : A) * (G 0 0 - G 1 1)) * hZ

theorem commute_of_mul_eq_mul_of_mul_eq_mul {G X Y : Matrix (Fin 2) (Fin 2) A}
    (hd : IsUnit (Matrix.trace G ^ 2 - 4 * Matrix.det G)) (hX : X * G = G * X)
    (hY : Y * G = G * Y) :
    Commute X Y := by
  obtain ⟨l, m, rfl⟩ := exists_eq_smul_one_add_smul_of_mul_eq_mul hd hX
  obtain ⟨l', m', rfl⟩ := exists_eq_smul_one_add_smul_of_mul_eq_mul hd hY
  have c1 : Commute (1 : Matrix (Fin 2) (Fin 2) A) (l' • (1 : Matrix (Fin 2) (Fin 2) A) + m' • G) :=
    ((Commute.one_left _).smul_right l').add_right ((Commute.one_left G).smul_right m')
  have c2 : Commute G (l' • (1 : Matrix (Fin 2) (Fin 2) A) + m' • G) :=
    ((Commute.one_right G).smul_right l').add_right ((Commute.refl G).smul_right m')
  exact (c1.smul_left l).add_left (c2.smul_left m)

theorem commute_of_mem_centralizer_of_isRegularSemisimple {g : GL (Fin 2) A}
    (hg : IsRegularSemisimple g) {x y : GL (Fin 2) A}
    (hx : x ∈ Subgroup.centralizer ({g} : Set (GL (Fin 2) A)))
    (hy : y ∈ Subgroup.centralizer ({g} : Set (GL (Fin 2) A))) : Commute x y := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hx hy
  have hx' : (x : Matrix (Fin 2) (Fin 2) A) * g = g * x := congrArg Units.val hx
  have hy' : (y : Matrix (Fin 2) (Fin 2) A) * g = g * y := congrArg Units.val hy
  exact Units.ext (commute_of_mul_eq_mul_of_mul_eq_mul hg hx' hy').eq

theorem isMulCommutative_centralizer_of_isRegularSemisimple {g : GL (Fin 2) A}
    (hg : IsRegularSemisimple g) :
    IsMulCommutative (Subgroup.centralizer ({g} : Set (GL (Fin 2) A))) :=
  ⟨⟨fun x y => Subtype.ext (commute_of_mem_centralizer_of_isRegularSemisimple hg x.2 y.2).eq⟩⟩

end Ring

end RegularCentralizer

end CentralizerRing

section CentralizerCommutative

p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_smul_splitFibreIntegral_of_isTwistedOrbitalIntegralOn_of_algHom_of_prime_of_forall_exists_isSectionFnOn_of_isMulRightInvariant.AutomorphicForm"
open scoped TensorProduct

namespace RegularCentralizer

section Generic

variable {G : Type*} [Group G]

theorem mul_prod_range_iterate (f : G →* G) {t δ : G} (h : t * δ = δ * f t) (n : ℕ) :
    t * ((List.range n).map fun i => (⇑f)^[i] δ).prod =
      ((List.range n).map fun i => (⇑f)^[i] δ).prod * (⇑f)^[n] t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, List.prod_append, List.prod_cons,
      List.prod_nil, mul_one, ← mul_assoc, ih, mul_assoc, mul_assoc, Function.iterate_succ_apply]
    congr 1
    have h' := congrArg ((⇑f)^[n]) h
    rwa [iterate_map_mul, iterate_map_mul] at h'

end Generic

section Twisted

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]

theorem twistedCentralizer_le_centralizer_normString_of_iterate (σ : L ≃ₐ[K] L)
    (hσ : ∀ t : GL (Fin 2) (L ⊗[K] A), (⇑(sigmaGL K L A σ))^[Module.finrank K L] t = t)
    (δ : GL (Fin 2) (L ⊗[K] A)) :
    twistedCentralizer K L A σ δ ≤
      Subgroup.centralizer ({normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A))) := by
  intro t ht
  rw [Subgroup.mem_centralizer_singleton_iff]
  have ht' : t * δ * (sigmaGL K L A σ t)⁻¹ = δ := ht
  have key := mul_prod_range_iterate (sigmaGL K L A σ) (mul_inv_eq_iff_eq_mul.mp ht')
    (Module.finrank K L)
  rw [hσ t] at key
  exact key

theorem sigmaTensor_mul_apply (σ σ' : L ≃ₐ[K] L) (z : L ⊗[K] A) :
    sigmaTensor K L A (σ * σ') z = sigmaTensor K L A σ (sigmaTensor K L A σ' z) := by
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro l a
    simp [sigmaTensor, Algebra.TensorProduct.map_tmul, AlgEquiv.mul_apply]
  · intro x y hx hy
    simp only [map_add, hx, hy]

theorem sigmaTensor_one_apply (z : L ⊗[K] A) : sigmaTensor K L A 1 z = z := by
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro l a
    simp [sigmaTensor, Algebra.TensorProduct.map_tmul, AlgEquiv.one_apply]
  · intro x y hx hy
    simp only [map_add, hx, hy]

theorem sigmaGL_mul_apply (σ σ' : L ≃ₐ[K] L) (g : GL (Fin 2) (L ⊗[K] A)) :
    sigmaGL K L A (σ * σ') g = sigmaGL K L A σ (sigmaGL K L A σ' g) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show Matrix.GeneralLinearGroup.map (sigmaTensor K L A (σ * σ')) g i j =
    Matrix.GeneralLinearGroup.map (sigmaTensor K L A σ)
      (Matrix.GeneralLinearGroup.map (sigmaTensor K L A σ') g) i j
  simp only [Matrix.GeneralLinearGroup.map_apply, sigmaTensor_mul_apply]

theorem sigmaGL_one_apply (g : GL (Fin 2) (L ⊗[K] A)) : sigmaGL K L A 1 g = g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show Matrix.GeneralLinearGroup.map (sigmaTensor K L A 1) g i j = g i j
  simp only [Matrix.GeneralLinearGroup.map_apply, sigmaTensor_one_apply]

theorem sigmaGL_iterate (σ : L ≃ₐ[K] L) (n : ℕ) (g : GL (Fin 2) (L ⊗[K] A)) :
    (⇑(sigmaGL K L A σ))^[n] g = sigmaGL K L A (σ ^ n) g := by
  induction n with
  | zero => simp [sigmaGL_one_apply]
  | succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ', sigmaGL_mul_apply]

theorem pow_finrank_eq_one [FiniteDimensional K L] (σ : L ≃ₐ[K] L) : σ ^ Module.finrank K L = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one, ← Nat.card_zpowers, ← IntermediateField.finrank_fixedField_eq_card]
  exact Dvd.intro_left _
    (Module.finrank_mul_finrank K (IntermediateField.fixedField (Subgroup.zpowers σ)) L)

theorem sigmaGL_iterate_finrank [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
    (g : GL (Fin 2) (L ⊗[K] A)) : (⇑(sigmaGL K L A σ))^[Module.finrank K L] g = g := by
  rw [sigmaGL_iterate, pow_finrank_eq_one, sigmaGL_one_apply]

theorem twistedCentralizer_le_centralizer_normString [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
    (δ : GL (Fin 2) (L ⊗[K] A)) :
    twistedCentralizer K L A σ δ ≤
      Subgroup.centralizer ({normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A))) :=
  twistedCentralizer_le_centralizer_normString_of_iterate K L A σ
    (sigmaGL_iterate_finrank K L A σ) δ

end Twisted

end RegularCentralizer

end CentralizerCommutative

section OrbitalCarriersBlock

open NumberField IsDedekindDomain MeasureTheory TopologicalSpace TensorProduct Topology
open scoped TensorProduct.RightActions
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_smul_splitFibreIntegral_of_isTwistedOrbitalIntegralOn_of_algHom_of_prime_of_forall_exists_isSectionFnOn_of_isMulRightInvariant.AutomorphicForm"

namespace OrbitalCarriers

section GLCarrier

variable (A : Type) [CommRing A] [TopologicalSpace A]

private theorem _root_.AutomorphicForm.SplitTransfer.OrbitalCarriers.secondCountableTopology_gl [SecondCountableTopology A] :
    SecondCountableTopology (GL (Fin 2) A) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → A))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

p2m_export "AutomorphicForm.SplitTransfer.OrbitalCarriers" "secondCountableTopology_gl"
theorem locallyCompactSpace_gl [IsTopologicalRing A] [T2Space A] [LocallyCompactSpace A] :
    LocallyCompactSpace (GL (Fin 2) A) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → A))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem sigmaCompactSpace_gl [IsTopologicalRing A] [T2Space A] [LocallyCompactSpace A]
    [SecondCountableTopology A] : SigmaCompactSpace (GL (Fin 2) A) := by
  haveI := locallyCompactSpace_gl A
  haveI := secondCountableTopology_gl A
  exact sigmaCompactSpace_of_locallyCompact_secondCountable

theorem isClosed_centralizer [IsTopologicalRing A] [T2Space A] (γ : GL (Fin 2) A) :
    IsClosed ((Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) : Subgroup (GL (Fin 2) A)) :
      Set (GL (Fin 2) A)) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
  haveI : T2Space (GL (Fin 2) A) := Units.isEmbedding_embedProduct.t2Space
  have h : ((Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) : Subgroup (GL (Fin 2) A)) :
      Set (GL (Fin 2) A)) = {x | x * γ = γ * x} := by
    ext x
    exact Subgroup.mem_centralizer_singleton_iff
  rw [h]
  exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)

end GLCarrier

section TwistedClosed

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
  (σ : L ≃ₐ[K] L)

theorem isClosed_twistedCentralizer (hσc : Continuous (sigmaGL K L A σ))
    (δ : GL (Fin 2) (L ⊗[K] A)) :
    IsClosed ((twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) :
      Set (GL (Fin 2) (L ⊗[K] A))) := by
  haveI := isTopologicalRing_tensor K L A
  haveI := t2Space_tensorGL K L A
  have h : ((twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) :
      Set (GL (Fin 2) (L ⊗[K] A))) = {t | t * δ * (sigmaGL K L A σ t)⁻¹ = δ} := by
    ext t
    exact mem_sigmaCentralizer_iff
  rw [h]
  exact isClosed_eq ((continuous_id.mul continuous_const).mul hσc.inv) continuous_const

end TwistedClosed

section Torus

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G]

theorem regular_of_isHaarMeasure_of_isClosed (T : Subgroup G) (hT : IsClosed (T : Set G))
    (τ : @Measure T (borel T)) (hτ : @Measure.IsHaarMeasure T _ _ (borel T) τ) :
    @Measure.Regular T (borel T) _ τ := by
  letI : MeasurableSpace T := borel T
  haveI : BorelSpace T := ⟨rfl⟩
  haveI : LocallyCompactSpace T := hT.locallyCompactSpace
  haveI : SecondCountableTopology T := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI : SigmaCompactSpace T := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI := hτ
  obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : T)
  exact Measure.regular_of_isMulLeftInvariant hC ⟨1, mem_interior_iff_mem_nhds.2 hC1⟩
    hC.measure_lt_top.ne

open scoped IsMulCommutative in

theorem isInvInvariant_of_isHaarMeasure_of_isClosed (T : Subgroup G) (hT : IsClosed (T : Set G))
    (hcomm : IsMulCommutative T) (τ : @Measure T (borel T))
    (hτ : @Measure.IsHaarMeasure T _ _ (borel T) τ) : @Measure.IsInvInvariant T (borel T) _ τ := by
  letI : MeasurableSpace T := borel T
  haveI : BorelSpace T := ⟨rfl⟩
  haveI : LocallyCompactSpace T := hT.locallyCompactSpace
  haveI : SecondCountableTopology T := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI := hτ
  haveI := hcomm
  haveI := regular_of_isHaarMeasure_of_isClosed T hT τ hτ
  exact Measure.IsHaarMeasure.isInvInvariant_of_regular τ

omit [IsTopologicalGroup G] in
theorem sfinite_of_isHaarMeasure_of_isClosed (T : Subgroup G) (hT : IsClosed (T : Set G))
    (τ : @Measure T (borel T)) (hτ : @Measure.IsHaarMeasure T _ _ (borel T) τ) :
    @SFinite T (borel T) τ := by
  letI : MeasurableSpace T := borel T
  haveI : BorelSpace T := ⟨rfl⟩
  haveI : LocallyCompactSpace T := hT.locallyCompactSpace
  haveI : SecondCountableTopology T := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI : SigmaCompactSpace T := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI := hτ
  infer_instance

end Torus

section PiBorel

variable (A : Type) [CommRing A] [TopologicalSpace A] [SecondCountableTopology A]

theorem borelSpace_pi_gl (m : ℕ) :
    @BorelSpace (Fin m → GL (Fin 2) A) _ (@MeasurableSpace.pi _ _ fun _ => glBorelOf A) := by
  letI : MeasurableSpace (GL (Fin 2) A) := glBorelOf A
  haveI := borelSpace_glBorelOf A
  haveI := secondCountableTopology_gl A
  infer_instance

end PiBorel

end OrbitalCarriers

end OrbitalCarriersBlock

section HaarScalarBlock

open MeasureTheory

namespace HaarScalar

section Generic

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
variable {ι : Type*} [Fintype ι] {H : ι → Type*} [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)]
  [∀ i, IsTopologicalGroup (H i)] [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)]
  [∀ i, LocallyCompactSpace (H i)] [∀ i, SecondCountableTopology (H i)]

example (ν : ∀ i, Measure (H i)) [∀ i, (ν i).IsHaarMeasure] : SigmaFinite (Measure.pi ν) := inferInstance

example (ν : ∀ i, Measure (H i)) [∀ i, (ν i).IsHaarMeasure] : (Measure.pi ν).IsMulLeftInvariant := inferInstance

example : MeasurableMul₂ (∀ i, H i) := inferInstance

theorem exists_map_eq_smul_pi (μ : Measure G) [μ.IsHaarMeasure] (ν : ∀ i, Measure (H i))
    [∀ i, (ν i).IsHaarMeasure] (Θ : G ≃* (∀ i, H i)) (hΘ : Continuous Θ) (hΘs : Continuous Θ.symm) :
    ∃ c : NNReal, c ≠ 0 ∧ Measure.map Θ μ = c • Measure.pi ν := by
  haveI : (Measure.map Θ μ).IsHaarMeasure := Θ.isHaarMeasure_map μ hΘ hΘs
  exact ⟨Measure.haarScalarFactor (Measure.map Θ μ) (Measure.pi ν),
    (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne',
    Measure.isMulLeftInvariant_eq_smul _ _⟩

end Generic

end HaarScalar

end HaarScalarBlock

section CentralizerEmbeddingBlock

p2m_open "MeasureTheory Topology AutomorphicForm P2MW.S_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_smul_splitFibreIntegral_of_isTwistedOrbitalIntegralOn_of_algHom_of_prime_of_forall_exists_isSectionFnOn_of_isMulRightInvariant.AutomorphicForm"
open scoped TensorProduct
open scoped TensorProduct.RightActions

namespace CentralizerEmbedding

section Embed

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]

theorem continuous_algebraMap_tensor : Continuous (algebraMap A (L ⊗[K] A)) :=
  IsModuleTopology.continuous_of_linearMap (Algebra.linearMap A (L ⊗[K] A))

omit [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] in
theorem coe_toTensorGL (g : GL (Fin 2) A) :
    ((toTensorGL K L A g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))
      = (g : Matrix (Fin 2) (Fin 2) A).map (algebraMap A (L ⊗[K] A)) := by
  ext i j
  simp [toTensorGL, Matrix.GeneralLinearGroup.map_apply, TensorProduct.RightActions.algebraMap_eval]

theorem continuous_toTensorGL : Continuous (toTensorGL K L A) := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · have h : (Units.val ∘ toTensorGL K L A) =
        fun g : GL (Fin 2) A => (g : Matrix (Fin 2) (Fin 2) A).map (algebraMap A (L ⊗[K] A)) :=
      funext fun g => coe_toTensorGL K L A g
    rw [h]
    exact Units.continuous_val.matrix_map (continuous_algebraMap_tensor K L A)
  · have h : (fun g : GL (Fin 2) A => ((toTensorGL K L A g)⁻¹ : GL (Fin 2) (L ⊗[K] A)).val) =
        fun g : GL (Fin 2) A => ((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A).map (algebraMap A (L ⊗[K] A)) :=
      funext fun g => by rw [← map_inv, coe_toTensorGL]
    rw [h]
    exact Units.continuous_coe_inv.matrix_map (continuous_algebraMap_tensor K L A)

theorem measurable_toTensorGL :
    @Measurable _ _ (glBorelOf A) (glBorelOf (L ⊗[K] A)) (toTensorGL K L A) := by
  letI := glBorelOf A
  letI := glBorelOf (L ⊗[K] A)
  haveI := borelSpace_glBorelOf A
  haveI := borelSpace_glBorelOf (L ⊗[K] A)
  exact (continuous_toTensorGL K L A).measurable

theorem measurableEmbedding_conj (y : GL (Fin 2) (L ⊗[K] A)) :
    @MeasurableEmbedding _ _ (glBorelOf (L ⊗[K] A)) (glBorelOf (L ⊗[K] A))
      (fun t : GL (Fin 2) (L ⊗[K] A) => y⁻¹ * t * y) := by
  letI := glBorelOf (L ⊗[K] A)
  haveI := borelSpace_glBorelOf (L ⊗[K] A)
  haveI := isTopologicalGroup_tensorGL K L A
  exact ((Homeomorph.mulLeft y⁻¹).trans (Homeomorph.mulRight y)).measurableEmbedding

end Embed

section Tori

variable (A : Type) [CommRing A] [TopologicalSpace A]

theorem measurableEmbedding_centralizer_val (γ : GL (Fin 2) A)
    (hc : IsClosed ((Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) : Subgroup (GL (Fin 2) A)) :
      Set (GL (Fin 2) A))) :
    @MeasurableEmbedding _ _ (centralizerBorel A γ) (glBorelOf A)
      ((↑) : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) → GL (Fin 2) A) := by
  letI := glBorelOf A
  letI := centralizerBorel A γ
  haveI := borelSpace_glBorelOf A
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) := ⟨rfl⟩
  have he : IsClosedEmbedding ((↑) : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) → GL (Fin 2) A) :=
    hc.isClosedEmbedding_subtypeVal
  exact he.measurableEmbedding

end Tori

section TwistedTori

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] (σ : L ≃ₐ[K] L)

theorem measurableEmbedding_twistedCentralizer_val (δ : GL (Fin 2) (L ⊗[K] A))
    (hc : IsClosed ((twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) :
      Set (GL (Fin 2) (L ⊗[K] A)))) :
    @MeasurableEmbedding _ _ (twistedCentralizerBorel K L A σ δ) (glBorelOf (L ⊗[K] A))
      ((↑) : twistedCentralizer K L A σ δ → GL (Fin 2) (L ⊗[K] A)) := by
  letI := glBorelOf (L ⊗[K] A)
  letI := twistedCentralizerBorel K L A σ δ
  haveI := borelSpace_glBorelOf (L ⊗[K] A)
  haveI : BorelSpace (twistedCentralizer K L A σ δ) := ⟨rfl⟩
  have he : IsClosedEmbedding ((↑) : twistedCentralizer K L A σ δ → GL (Fin 2) (L ⊗[K] A)) :=
    hc.isClosedEmbedding_subtypeVal
  exact he.measurableEmbedding

end TwistedTori

end CentralizerEmbedding

end CentralizerEmbeddingBlock

section CoupledProjectionBlock

open MeasureTheory NumberField

open scoped TensorProduct
open scoped TensorProduct.RightActions

namespace CoupledProjection

section Main

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] (σ : L ≃ₐ[K] L)

open _root_.AutomorphicForm _root_.P2MW.S_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_smul_splitFibreIntegral_of_isTwistedOrbitalIntegralOn_of_algHom_of_prime_of_forall_exists_isSectionFnOn_of_isMulRightInvariant.AutomorphicForm in

theorem map_conj_eq_map_val_of_coupled (γ : GL (Fin 2) A) (δ y : GL (Fin 2) (L ⊗[K] A))
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ))
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
    (hc : Coupled K L A σ γ δ y τ τ')
    (ρ : GL (Fin 2) (L ⊗[K] A) → GL (Fin 2) A)
    (hρ : @Measurable _ _ (glBorelOf (L ⊗[K] A)) (glBorelOf A) ρ)
    (hρi : ∀ s : GL (Fin 2) A, ρ (toTensorGL K L A s) = s)
    (hρy : ∀ g, ρ (y⁻¹ * g * y) = (ρ y)⁻¹ * ρ g * ρ y)
    (hval' : @Measurable _ _ (twistedCentralizerBorel K L A σ δ) (glBorelOf (L ⊗[K] A))
      (fun t : twistedCentralizer K L A σ δ => (t : GL (Fin 2) (L ⊗[K] A))))
    (hval : @Measurable _ _ (centralizerBorel A γ) (glBorelOf A)
      (fun s : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) => (s : GL (Fin 2) A)))
    (htor : @Measurable _ _ (glBorelOf A) (glBorelOf (L ⊗[K] A)) (toTensorGL K L A)) :
    @Measure.map _ _ (twistedCentralizerBorel K L A σ δ) (glBorelOf A)
        (fun t : twistedCentralizer K L A σ δ => (ρ y)⁻¹ * ρ (t : GL (Fin 2) (L ⊗[K] A)) * ρ y) τ' =
      @Measure.map _ _ (centralizerBorel A γ) (glBorelOf A)
        (fun s : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) => (s : GL (Fin 2) A)) τ := by
  letI := glBorelOf (L ⊗[K] A)
  letI := glBorelOf A
  letI := centralizerBorel A γ
  letI := twistedCentralizerBorel K L A σ δ
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] A)) := borelSpace_glBorelOf (L ⊗[K] A)
  haveI := isTopologicalGroup_tensorGL K L A
  have hconj : Measurable (fun t : twistedCentralizer K L A σ δ => y⁻¹ * (t : GL (Fin 2) (L ⊗[K] A)) * y) :=
    (hval'.const_mul y⁻¹).mul_const y
  dsimp only [Coupled] at hc
  have h := congrArg (Measure.map ρ) hc
  have hts : Measurable (fun s : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) =>
      toTensorGL K L A (s : GL (Fin 2) A)) := htor.comp hval
  rw [Measure.map_map hρ hconj, Measure.map_map hρ hts] at h
  convert h using 2 <;> funext t <;> simp only [Function.comp_def, hρy, hρi]

end Main

end CoupledProjection

end CoupledProjectionBlock

section TensorBlock

p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_smul_splitFibreIntegral_of_isTwistedOrbitalIntegralOn_of_algHom_of_prime_of_forall_exists_isSectionFnOn_of_isMulRightInvariant.AutomorphicForm"

namespace TensorFacts

section Generic

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]

theorem secondCountableTopology_tensor [SecondCountableTopology A] : SecondCountableTopology (L ⊗[K] A) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A (L ⊗[K] A)
  have hq : IsOpenQuotientMap f := IsModuleTopology.isOpenQuotientMap_of_surjective hf
  exact hq.isQuotientMap.secondCountableTopology hq.isOpenMap

end Generic

section SigmaContinuous

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] (σ : L ≃ₐ[K] L)

omit [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] in
theorem sigmaTensor_tmul (x : L) (a : A) : sigmaTensor K L A σ (x ⊗ₜ a) = σ x ⊗ₜ a := by
  simp [sigmaTensor, Algebra.TensorProduct.map_tmul]

omit [IsTopologicalRing A] in
theorem continuous_sigmaTensor : Continuous (sigmaTensor K L A σ) := by
  have hs : ∀ (a : A) (x : L) (b : A), a • (x ⊗ₜ[K] b : L ⊗[K] A) = x ⊗ₜ (a * b) := by
    intro a x b
    simp only [TensorProduct.RightActions.smul_def, TensorProduct.comm_tmul]
    rw [TensorProduct.smul_tmul']
    simp only [smul_eq_mul, TensorProduct.comm_symm_tmul]
  let f : L ⊗[K] A →ₗ[A] L ⊗[K] A :=
    { toFun := sigmaTensor K L A σ
      map_add' := fun x y => map_add (sigmaTensor K L A σ) x y
      map_smul' := fun a z => by
        rw [RingHom.id_apply]
        induction z with
        | zero => rw [smul_zero, map_zero, smul_zero]
        | tmul x b => rw [hs, sigmaTensor_tmul K L A σ, sigmaTensor_tmul K L A σ, hs]
        | add y w hy hw => rw [smul_add, map_add, map_add, smul_add, hy, hw] }
  exact IsModuleTopology.continuous_of_linearMap f

omit [IsTopologicalRing A] in
theorem continuous_sigmaGL : Continuous (sigmaGL K L A σ) := by
  rw [Units.continuous_iff]
  exact ⟨Units.continuous_val.matrix_map (continuous_sigmaTensor K L A σ),
    Units.continuous_coe_inv.matrix_map (continuous_sigmaTensor K L A σ)⟩

end SigmaContinuous

end TensorFacts

end TensorBlock

section CutoffBlock

namespace Cutoff

variable {G : Type} [TopologicalSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G]
  [OpensMeasurableSpace G] (μ : Measure G)

theorem exists_cutoff {n : ℕ} (Φ : (Fin (n + 1) → G) → ℂ) (hc : HasCompactSupport Φ)
    [IsFiniteMeasureOnCompacts (Measure.pi fun _ : Fin n => μ)] :
    ∃ β : (Fin n → G) → ℝ, (∀ c, 0 ≤ β c) ∧ Measurable β ∧
      Integrable β (Measure.pi fun _ => μ) ∧ ∀ c h, Φ (Fin.snoc c h) ≠ 0 → β c = 1 := by
  set S : Set (Fin n → G) := (fun x : Fin (n + 1) → G => (Fin.init x : Fin n → G)) '' tsupport Φ
    with hS_def
  have hScompact : IsCompact S := hc.image (continuous_pi fun i => continuous_apply _)
  have hSm : MeasurableSet S := hScompact.isClosed.measurableSet
  refine ⟨S.indicator fun _ => (1 : ℝ), fun c => Set.indicator_nonneg (fun _ _ => zero_le_one) c,
    measurable_const.indicator hSm, ?_, fun c h hne => ?_⟩
  · rw [integrable_indicator_iff hSm]
    exact integrableOn_const hScompact.measure_lt_top.ne
  · have hcS : c ∈ S := ⟨Fin.snoc c h, subset_tsupport Φ hne, Fin.init_snoc _ _⟩
    exact Set.indicator_of_mem hcS _

end Cutoff

end CutoffBlock

section Interface

p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_smul_splitFibreIntegral_of_isTwistedOrbitalIntegralOn_of_algHom_of_prime_of_forall_exists_isSectionFnOn_of_isMulRightInvariant.AutomorphicForm"

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
  [LocallyCompactSpace A] [SecondCountableTopology A] (σ : L ≃ₐ[K] L)

omit [IsTopologicalRing A] [T2Space A] [LocallyCompactSpace A] in
theorem secondCountable_gl : SecondCountableTopology (GL (Fin 2) A) :=
  OrbitalCarriers.secondCountableTopology_gl A

theorem sigmaCompact_gl : SigmaCompactSpace (GL (Fin 2) A) :=
  OrbitalCarriers.sigmaCompactSpace_gl A

omit [SecondCountableTopology A] in
theorem locallyCompact_gl : LocallyCompactSpace (GL (Fin 2) A) :=
  OrbitalCarriers.locallyCompactSpace_gl A

omit [IsTopologicalRing A] [T2Space A] [LocallyCompactSpace A] in
theorem borelSpace_pi (m : ℕ) :
    @BorelSpace (Fin m → GL (Fin 2) A) _ (@MeasurableSpace.pi _ _ fun _ => glBorelOf A) :=
  OrbitalCarriers.borelSpace_pi_gl A m

omit [IsTopologicalRing A] [T2Space A] [LocallyCompactSpace A] in

theorem measurable_mulEquiv {n : ℕ} (Θ : GL (Fin 2) (L ⊗[K] A) ≃* (Fin (n + 1) → GL (Fin 2) A))
    (hΘ : Continuous Θ) (hΘs : Continuous Θ.symm) :
    @Measurable _ _ (glBorelOf (L ⊗[K] A)) (@MeasurableSpace.pi _ _ fun _ => glBorelOf A) Θ ∧
      @Measurable _ _ (@MeasurableSpace.pi _ _ fun _ => glBorelOf A) (glBorelOf (L ⊗[K] A)) Θ.symm := by
  letI : MeasurableSpace (GL (Fin 2) A) := glBorelOf A
  letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] A)) := glBorelOf (L ⊗[K] A)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] A)) := borelSpace_glBorelOf _
  haveI : BorelSpace (Fin (n + 1) → GL (Fin 2) A) := borelSpace_pi A (n + 1)
  exact ⟨hΘ.measurable, hΘs.measurable⟩

theorem local_group_facts (μA : @Measure (GL (Fin 2) A) (glBorelOf A))
    (hμA : @Measure.IsHaarMeasure (GL (Fin 2) A) _ _ (glBorelOf A) μA) :
    @MeasurableMul₂ (GL (Fin 2) A) (glBorelOf A) _ ∧
      @MeasurableInv (GL (Fin 2) A) _ (glBorelOf A) ∧
      @SigmaFinite _ (glBorelOf A) μA ∧
      @Measure.IsMulLeftInvariant _ (glBorelOf A) _ μA := by
  letI := glBorelOf A
  haveI := borelSpace_glBorelOf A
  haveI := OrbitalCarriers.secondCountableTopology_gl A
  haveI := OrbitalCarriers.sigmaCompactSpace_gl A
  haveI := hμA
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

omit [T2Space A] [LocallyCompactSpace A] [SecondCountableTopology A] in
theorem carrier_facts (γ : GL (Fin 2) A) :
    @MeasurableInv (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) _ (centralizerBorel A γ) ∧
      @Measurable _ _ (centralizerBorel A γ) (glBorelOf A)
        (fun s : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) => (s : GL (Fin 2) A)) := by
  letI := glBorelOf A
  letI := centralizerBorel A γ
  haveI := borelSpace_glBorelOf A
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) := ⟨rfl⟩
  exact ⟨inferInstance, continuous_subtype_val.measurable⟩

omit [T2Space A] [LocallyCompactSpace A] [SecondCountableTopology A] in
theorem twisted_carrier_facts (δ : GL (Fin 2) (L ⊗[K] A)) :
    @MeasurableInv (twistedCentralizer K L A σ δ) _ (twistedCentralizerBorel K L A σ δ) ∧
      @Measurable _ _ (twistedCentralizerBorel K L A σ δ) (glBorelOf (L ⊗[K] A))
        (fun t : twistedCentralizer K L A σ δ => (t : GL (Fin 2) (L ⊗[K] A))) := by
  letI := glBorelOf (L ⊗[K] A)
  letI := twistedCentralizerBorel K L A σ δ
  haveI := borelSpace_glBorelOf (L ⊗[K] A)
  haveI := isTopologicalGroup_tensorGL K L A
  haveI : BorelSpace (twistedCentralizer K L A σ δ) := ⟨rfl⟩
  exact ⟨inferInstance, continuous_subtype_val.measurable⟩

theorem torus_facts (γ : GL (Fin 2) A) (hγ : IsRegularSemisimple γ)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel A γ) τ) :
    @SFinite _ (centralizerBorel A γ) τ ∧ @Measure.IsInvInvariant _ (centralizerBorel A γ) _ τ := by
  haveI := OrbitalCarriers.secondCountableTopology_gl A
  haveI := OrbitalCarriers.locallyCompactSpace_gl A
  have hT := OrbitalCarriers.isClosed_centralizer A γ
  exact ⟨OrbitalCarriers.sfinite_of_isHaarMeasure_of_isClosed _ hT τ hτ,
    OrbitalCarriers.isInvInvariant_of_isHaarMeasure_of_isClosed _ hT
      (RegularCentralizer.isMulCommutative_centralizer_of_isRegularSemisimple hγ) τ hτ⟩

theorem twisted_torus_facts (δ : GL (Fin 2) (L ⊗[K] A))
    (hδ : IsRegularSemisimple (normString K L A σ δ))
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L A σ δ) τ') :
    @SFinite _ (twistedCentralizerBorel K L A σ δ) τ' ∧
      @Measure.IsInvInvariant _ (twistedCentralizerBorel K L A σ δ) _ τ' := by
  haveI := isTopologicalRing_tensor K L A
  haveI := t2Space_tensor K L A
  haveI := locallyCompactSpace_tensor K L A
  haveI := TensorFacts.secondCountableTopology_tensor K L A
  haveI := isTopologicalGroup_tensorGL K L A
  haveI := OrbitalCarriers.locallyCompactSpace_gl (L ⊗[K] A)
  haveI := OrbitalCarriers.secondCountableTopology_gl (L ⊗[K] A)
  have hT := OrbitalCarriers.isClosed_twistedCentralizer K L A σ
    (TensorFacts.continuous_sigmaGL K L A σ) δ
  have hle := RegularCentralizer.twistedCentralizer_le_centralizer_normString K L A σ δ
  have hcN := RegularCentralizer.isMulCommutative_centralizer_of_isRegularSemisimple hδ
  have hcomm : IsMulCommutative (twistedCentralizer K L A σ δ) :=
    ⟨⟨fun a b => by
      have h := congrArg Subtype.val (hcN.is_comm.comm ⟨a.1, hle a.2⟩ ⟨b.1, hle b.2⟩)
      exact Subtype.ext h⟩⟩
  exact ⟨OrbitalCarriers.sfinite_of_isHaarMeasure_of_isClosed _ hT τ' hτ',
    OrbitalCarriers.isInvInvariant_of_isHaarMeasure_of_isClosed _ hT hcomm τ' hτ'⟩

theorem exists_scalar {n : ℕ} (Θ : GL (Fin 2) (L ⊗[K] A) ≃* (Fin (n + 1) → GL (Fin 2) A))
    (hΘ : Continuous Θ) (hΘs : Continuous Θ.symm)
    (μL : @Measure (GL (Fin 2) (L ⊗[K] A)) (glBorelOf (L ⊗[K] A)))
    (hμL : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] A)) _ _ (glBorelOf (L ⊗[K] A)) μL)
    (μA : @Measure (GL (Fin 2) A) (glBorelOf A))
    (hμA : @Measure.IsHaarMeasure (GL (Fin 2) A) _ _ (glBorelOf A) μA) :
    ∃ c : NNReal, c ≠ 0 ∧
      @Measure.map _ _ (glBorelOf (L ⊗[K] A)) (@MeasurableSpace.pi _ _ fun _ => glBorelOf A) Θ μL =
        c • @Measure.pi (Fin (n + 1)) (fun _ => GL (Fin 2) A) _ (fun _ => glBorelOf A) (fun _ => μA) := by
  exact @HaarScalar.exists_map_eq_smul_pi _ _ _ (isTopologicalGroup_tensorGL K L A)
    (glBorelOf (L ⊗[K] A)) (borelSpace_glBorelOf (L ⊗[K] A))
    (Fin (n + 1)) _ (fun _ => GL (Fin 2) A) _ _ _
    (fun _ => glBorelOf A) (fun _ => borelSpace_glBorelOf A)
    (fun _ => OrbitalCarriers.locallyCompactSpace_gl A)
    (fun _ => OrbitalCarriers.secondCountableTopology_gl A)
    μL hμL (fun _ => μA) (fun _ => hμA) Θ hΘ hΘs

omit [T2Space A] [LocallyCompactSpace A] [SecondCountableTopology A] in

theorem coupling {n : ℕ} (Θ : GL (Fin 2) (L ⊗[K] A) ≃* (Fin (n + 1) → GL (Fin 2) A))
    (hΘ : Continuous Θ) (hΘ1 : ∀ g : GL (Fin 2) A, Θ (toTensorGL K L A g) = fun _ => g)
    (γ : GL (Fin 2) A) (δ y : GL (Fin 2) (L ⊗[K] A))
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ))
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
    (hc : Coupled K L A σ γ δ y τ τ') :
    @Measure.map _ _ (twistedCentralizerBorel K L A σ δ) (glBorelOf A)
        (fun t : twistedCentralizer K L A σ δ => (Θ y 0)⁻¹ * Θ (t : GL (Fin 2) (L ⊗[K] A)) 0 * Θ y 0) τ' =
      @Measure.map _ _ (centralizerBorel A γ) (glBorelOf A)
        (fun s : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) => (s : GL (Fin 2) A)) τ := by
  have hρ : @Measurable _ _ (glBorelOf (L ⊗[K] A)) (glBorelOf A) (fun g => Θ g 0) := by
    letI := glBorelOf (L ⊗[K] A)
    letI := glBorelOf A
    haveI := borelSpace_glBorelOf (L ⊗[K] A)
    haveI := borelSpace_glBorelOf A
    exact ((continuous_apply (0 : Fin (n + 1))).comp hΘ).measurable
  exact CoupledProjection.map_conj_eq_map_val_of_coupled K L A σ γ δ y τ τ' hc
    (fun g => Θ g 0) hρ
    (fun s => congrFun (hΘ1 s) 0) (fun g => by simp)
    (twisted_carrier_facts K L A σ δ).2 (carrier_facts A γ).2
    (CentralizerEmbedding.measurable_toTensorGL K L A)

omit [IsTopologicalRing A] [T2Space A] [LocallyCompactSpace A] [SecondCountableTopology A] in

theorem phi_facts (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (hφc : Continuous φ) (hφcs : HasCompactSupport φ) :
    @Measurable _ _ (glBorelOf (L ⊗[K] A)) _ φ ∧ (∃ C, ∀ x, ‖φ x‖ ≤ C) := by
  refine ⟨?_, ?_⟩
  · letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] A)) := glBorelOf (L ⊗[K] A)
    haveI := borelSpace_glBorelOf (L ⊗[K] A)
    exact hφc.measurable
  · obtain ⟨C, hC⟩ := hφcs.isCompact.exists_bound_of_continuousOn hφc.continuousOn
    refine ⟨max C 0, fun x => ?_⟩
    by_cases hx : x ∈ tsupport φ
    · exact (hC x hx).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
      exact le_max_right _ _

omit [IsTopologicalRing A] [T2Space A] [LocallyCompactSpace A] [SecondCountableTopology A] in

theorem model_fn_facts {n : ℕ} (Θ : GL (Fin 2) (L ⊗[K] A) ≃* (Fin (n + 1) → GL (Fin 2) A))
    (hΘ : Continuous Θ) (hΘs : Continuous Θ.symm)
    (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (hφc : Continuous φ) (hφcs : HasCompactSupport φ) :
    Continuous (φ ∘ Θ.symm) ∧ HasCompactSupport (φ ∘ Θ.symm) :=
  ⟨hφc.comp hΘs, hφcs.comp_homeomorph ⟨Θ.symm.toEquiv, hΘs, hΘ⟩⟩

theorem exists_cutoff_fn {n : ℕ} (μA : @Measure (GL (Fin 2) A) (glBorelOf A))
    (hμA : @Measure.IsHaarMeasure (GL (Fin 2) A) _ _ (glBorelOf A) μA)
    (Φ : (Fin (n + 1) → GL (Fin 2) A) → ℂ) (hcs : HasCompactSupport Φ) :
    ∃ β : (Fin n → GL (Fin 2) A) → ℝ, (∀ c, 0 ≤ β c) ∧
      @Measurable _ _ (@MeasurableSpace.pi _ _ fun _ => glBorelOf A) _ β ∧
      @Integrable ℝ _ _ _ (@MeasurableSpace.pi _ _ fun _ => glBorelOf A) β
        (@Measure.pi (Fin n) (fun _ => GL (Fin 2) A) _ (fun _ => glBorelOf A) fun _ => μA) ∧
      ∀ c h, Φ (Fin.snoc c h) ≠ 0 → β c = 1 := by
  letI : MeasurableSpace (GL (Fin 2) A) := glBorelOf A
  haveI : BorelSpace (GL (Fin 2) A) := borelSpace_glBorelOf A
  haveI := OrbitalCarriers.secondCountableTopology_gl A
  haveI := OrbitalCarriers.sigmaCompactSpace_gl A
  haveI := OrbitalCarriers.locallyCompactSpace_gl A
  haveI : μA.IsHaarMeasure := hμA
  exact Cutoff.exists_cutoff μA Φ hcs

omit [T2Space A] [LocallyCompactSpace A] [SecondCountableTopology A] in

theorem hasCompactSupport_fibreIntegral {n : ℕ} (μ : @Measure (GL (Fin 2) A) (glBorelOf A))
    (Φ : (Fin (n + 1) → GL (Fin 2) A) → ℂ) (hc : HasCompactSupport Φ) :
    HasCompactSupport fun h : GL (Fin 2) A =>
      @integral _ _ _ _ (@MeasurableSpace.pi _ _ fun _ => glBorelOf A)
        (@Measure.pi (Fin n) (fun _ => GL (Fin 2) A) _ (fun _ => glBorelOf A) fun _ => μ)
        fun c : Fin n → GL (Fin 2) A => Φ (Fin.snoc c (((List.ofFn c).prod)⁻¹ * h)) := by
  letI : MeasurableSpace (GL (Fin 2) A) := glBorelOf A
  let proj : (Fin (n + 1) → GL (Fin 2) A) → GL (Fin 2) A :=
    fun y => (List.ofFn (Fin.init y)).prod * y (Fin.last n)
  have hproj : Continuous proj := by
    have h1 : Continuous fun y : Fin (n + 1) → GL (Fin 2) A => Fin.init y :=
      continuous_pi fun i => continuous_apply (Fin.castSucc i)
    have h2 : Continuous fun c : Fin n → GL (Fin 2) A => (List.ofFn c).prod := by
      simp only [List.ofFn_eq_map]
      exact continuous_list_prod _ fun i _ => continuous_apply i
    exact (h2.comp h1).mul (continuous_apply (Fin.last n))
  have hps : ∀ (c : Fin n → GL (Fin 2) A) (h : GL (Fin 2) A),
      proj (Fin.snoc c ((List.ofFn c).prod⁻¹ * h)) = h := fun c h => by
    simp only [proj, Fin.init_snoc, Fin.snoc_last, mul_inv_cancel_left]
  refine HasCompactSupport.intro (IsCompact.image hc hproj) fun h hh => ?_
  have hzero : (fun c : Fin n → GL (Fin 2) A => Φ (Fin.snoc c ((List.ofFn c).prod⁻¹ * h))) = fun _ => 0 := by
    funext c
    by_contra hne
    exact hh ⟨_, subset_closure (Function.mem_support.2 hne), hps c h⟩
  rw [hzero, integral_zero]

omit [IsTopologicalRing A] [T2Space A] [LocallyCompactSpace A] [SecondCountableTopology A] in
theorem hasCompactSupport_norm_cast {X : Type} [TopologicalSpace X] {Φ : X → ℂ} (hc : HasCompactSupport Φ) :
    HasCompactSupport fun y => (‖Φ y‖ : ℂ) :=
  hc.comp_left (g := fun z : ℂ => ((‖z‖ : ℝ) : ℂ)) (by simp)

end Interface

section TransportBlock

namespace Transport

variable {Γ G : Type} [Group Γ] [Group G] {n : ℕ}

def imageSubgroup (Θ : Γ ≃* (Fin (n + 1) → G)) (Tw : Subgroup Γ) : Subgroup (Fin (n + 1) → G) :=
  Tw.map (Θ : Γ →* (Fin (n + 1) → G))

theorem mem_imageSubgroup_iff (Θ : Γ ≃* (Fin (n + 1) → G)) (Tw : Subgroup Γ) (δ : Fin (n + 1) → G)
    (hTw : ∀ s : Γ, s ∈ Tw ↔ ∀ j, (Θ s j)⁻¹ * δ j * Θ s (j + 1) = δ j) (t : Fin (n + 1) → G) :
    t ∈ imageSubgroup Θ Tw ↔ ∀ j, (t j)⁻¹ * δ j * t (j + 1) = δ j := by
  rw [imageSubgroup, Subgroup.mem_map]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact (hTw s).1 hs
  · intro ht
    refine ⟨Θ.symm t, (hTw _).2 ?_, by simp⟩
    simpa only [MulEquiv.apply_symm_apply] using ht

def toImage (Θ : Γ ≃* (Fin (n + 1) → G)) (Tw : Subgroup Γ) (t : Tw) : imageSubgroup Θ Tw :=
  ⟨Θ (t : Γ), Subgroup.mem_map.2 ⟨(t : Γ), t.2, rfl⟩⟩

@[scoped simp] theorem coe_toImage (Θ : Γ ≃* (Fin (n + 1) → G)) (Tw : Subgroup Γ) (t : Tw) :
    ((toImage Θ Tw t : imageSubgroup Θ Tw) : Fin (n + 1) → G) = Θ (t : Γ) := rfl

theorem toImage_mul (Θ : Γ ≃* (Fin (n + 1) → G)) (Tw : Subgroup Γ) (s t : Tw) :
    toImage Θ Tw (s * t) = toImage Θ Tw s * toImage Θ Tw t :=
  Subtype.ext (by simp [coe_toImage, map_mul])

theorem toImage_inv (Θ : Γ ≃* (Fin (n + 1) → G)) (Tw : Subgroup Γ) (t : Tw) :
    toImage Θ Tw t⁻¹ = (toImage Θ Tw t)⁻¹ :=
  Subtype.ext (by simp [coe_toImage, map_inv])

theorem toImage_surjective (Θ : Γ ≃* (Fin (n + 1) → G)) (Tw : Subgroup Γ) :
    Function.Surjective (toImage Θ Tw) := by
  rintro ⟨t, ht⟩
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 ht
  exact ⟨⟨s, hs⟩, rfl⟩

variable [MeasurableSpace Γ] [MeasurableSpace G]

theorem measurableInv_subgroup {H : Type} [Group H] [MeasurableSpace H] [MeasurableInv H]
    (S : Subgroup H) : MeasurableInv S :=
  ⟨measurable_subtype_coe.inv.subtype_mk⟩

theorem measurable_toImage (Θ : Γ ≃* (Fin (n + 1) → G)) (hΘm : Measurable Θ) (Tw : Subgroup Γ)
    [MeasurableSpace Tw] (hTwval : Measurable fun t : Tw => (t : Γ)) :
    Measurable (toImage Θ Tw) :=
  (hΘm.comp hTwval).subtype_mk

noncomputable def transportMeasure (Θ : Γ ≃* (Fin (n + 1) → G)) (Tw : Subgroup Γ) [MeasurableSpace Tw]
    (τ' : Measure Tw) : Measure (imageSubgroup Θ Tw) :=
  Measure.map (toImage Θ Tw) τ'

theorem isInvInvariant_transportMeasure [MeasurableInv G] (Θ : Γ ≃* (Fin (n + 1) → G)) (hΘm : Measurable Θ)
    (Tw : Subgroup Γ) [MeasurableSpace Tw] [MeasurableInv Tw] (hTwval : Measurable fun t : Tw => (t : Γ))
    (τ' : Measure Tw) [τ'.IsInvInvariant] :
    letI : MeasurableInv (imageSubgroup Θ Tw) := measurableInv_subgroup _
    (transportMeasure Θ Tw τ').IsInvInvariant := by
  haveI : MeasurableInv (imageSubgroup Θ Tw) := measurableInv_subgroup _
  have hem := measurable_toImage Θ hΘm Tw hTwval
  refine ⟨?_⟩
  show Measure.map Inv.inv (Measure.map (toImage Θ Tw) τ') = Measure.map (toImage Θ Tw) τ'
  rw [Measure.map_map measurable_inv hem]
  have hcomm : (Inv.inv ∘ toImage Θ Tw) = toImage Θ Tw ∘ (Inv.inv : Tw → Tw) := by
    funext t
    simp only [Function.comp_apply, toImage_inv]
  rw [hcomm, ← Measure.map_map hem measurable_inv, Measure.map_inv_eq_self]

omit [MeasurableSpace Γ] in
theorem sfinite_transportMeasure (Θ : Γ ≃* (Fin (n + 1) → G))
    (Tw : Subgroup Γ) [MeasurableSpace Tw] (τ' : Measure Tw) [SFinite τ'] : SFinite (transportMeasure Θ Tw τ') := by
  unfold transportMeasure
  infer_instance

omit [MeasurableSpace Γ] in
theorem measurable_conj_apply_zero (y₀ : G) [MeasurableMul₂ G] (Θ : Γ ≃* (Fin (n + 1) → G)) (Tw : Subgroup Γ) :
    Measurable fun t : imageSubgroup Θ Tw => y₀⁻¹ * (t : Fin (n + 1) → G) 0 * y₀ :=
  (measurable_const.mul ((measurable_pi_apply 0).comp measurable_subtype_coe)).mul_const _

theorem map_conj_transportMeasure_eq [MeasurableMul₂ G] (Θ : Γ ≃* (Fin (n + 1) → G)) (hΘm : Measurable Θ)
    (Tw : Subgroup Γ) [MeasurableSpace Tw] (hTwval : Measurable fun t : Tw => (t : Γ))
    (τ' : Measure Tw) (y₀ γ : G)
    [MeasurableSpace (Subgroup.centralizer ({γ} : Set G))]
    (τ : Measure (Subgroup.centralizer ({γ} : Set G)))
    (hcoup : Measure.map (fun t : Tw => y₀⁻¹ * Θ (t : Γ) 0 * y₀) τ' =
      Measure.map (fun s : Subgroup.centralizer ({γ} : Set G) => (s : G)) τ) :
    Measure.map (fun t : imageSubgroup Θ Tw => y₀⁻¹ * (t : Fin (n + 1) → G) 0 * y₀)
        (transportMeasure Θ Tw τ') =
      Measure.map (fun s : Subgroup.centralizer ({γ} : Set G) => (s : G)) τ := by
  rw [transportMeasure, Measure.map_map (measurable_conj_apply_zero y₀ Θ Tw)
    (measurable_toImage Θ hΘm Tw hTwval), ← hcoup]
  rfl

theorem integral_transportMeasure_comp_symm (Θ : Γ ≃* (Fin (n + 1) → G)) (hΘm : Measurable Θ)
    (hΘsm : Measurable Θ.symm) [MeasurableMul₂ G]
    (Tw : Subgroup Γ) [MeasurableSpace Tw] (hTwval : Measurable fun t : Tw => (t : Γ))
    (τ' : Measure Tw) (W : Γ → ℝ) (hWm : Measurable W) (z : Fin (n + 1) → G) :
    ∫ t : imageSubgroup Θ Tw, (W ∘ Θ.symm) ((t : Fin (n + 1) → G) * z) ∂(transportMeasure Θ Tw τ') =
      ∫ t : Tw, W ((t : Γ) * Θ.symm z) ∂τ' := by
  have hem := measurable_toImage Θ hΘm Tw hTwval
  have hsm : StronglyMeasurable fun t : imageSubgroup Θ Tw => (W ∘ Θ.symm) ((t : Fin (n + 1) → G) * z) :=
    ((hWm.comp hΘsm).comp (measurable_subtype_coe.mul_const z)).stronglyMeasurable
  rw [transportMeasure, integral_map_of_stronglyMeasurable hem hsm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [Function.comp_apply, coe_toImage, map_mul, MulEquiv.symm_apply_apply]

theorem huniq_image [MeasurableMul₂ G] [MeasurableInv G] (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant]
    (Θ : Γ ≃* (Fin (n + 1) → G)) (hΘm : Measurable Θ)
    (Tw : Subgroup Γ) [MeasurableSpace Tw] [MeasurableInv Tw] (hTwval : Measurable fun t : Tw => (t : Γ))
    (τ' : Measure Tw) [SFinite τ'] [τ'.IsInvInvariant] :
    ∀ F : (Fin (n + 1) → G) → ℂ, Measurable F →
      (∀ (t : imageSubgroup Θ Tw) (x : Fin (n + 1) → G), F ((t : Fin (n + 1) → G) * x) = F x) →
      ∀ w w' : (Fin (n + 1) → G) → ℝ, (∀ x, 0 ≤ w x) → (∀ x, 0 ≤ w' x) →
        Measurable w → Measurable w' →
        (∀ x, F x ≠ 0 → ∫ t : imageSubgroup Θ Tw, w ((t : Fin (n + 1) → G) * x) ∂(transportMeasure Θ Tw τ') = 1) →
        (∀ x, F x ≠ 0 → ∫ t : imageSubgroup Θ Tw, w' ((t : Fin (n + 1) → G) * x) ∂(transportMeasure Θ Tw τ') = 1) →
        ∫ x, F x * (w x : ℂ) ∂(Measure.pi fun _ : Fin (n + 1) => μ) =
          ∫ x, F x * (w' x : ℂ) ∂(Measure.pi fun _ : Fin (n + 1) => μ) := by
  haveI : MeasurableInv (imageSubgroup Θ Tw) := measurableInv_subgroup _
  haveI := isInvInvariant_transportMeasure Θ hΘm Tw hTwval τ'
  haveI := sfinite_transportMeasure Θ Tw τ'
  exact AutomorphicForm.integral_mul_eq_integral_mul_of_forall_integral_subgroup_mul_eq_one
    (Measure.pi fun _ : Fin (n + 1) => μ) (imageSubgroup Θ Tw) measurable_subtype_coe (transportMeasure Θ Tw τ')

omit [MeasurableSpace Γ] in

theorem huniq_centralizer [MeasurableMul₂ G] (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant] (γ : G)
    [MeasurableSpace (Subgroup.centralizer ({γ} : Set G))]
    [MeasurableInv (Subgroup.centralizer ({γ} : Set G))]
    (hval : Measurable fun s : Subgroup.centralizer ({γ} : Set G) => (s : G))
    (τ : Measure (Subgroup.centralizer ({γ} : Set G))) [SFinite τ] [τ.IsInvInvariant] :
    ∀ F : G → ℂ, Measurable F →
      (∀ (s : Subgroup.centralizer ({γ} : Set G)) (h : G), F ((s : G) * h) = F h) →
      ∀ w w' : G → ℝ, (∀ h, 0 ≤ w h) → (∀ h, 0 ≤ w' h) → Measurable w → Measurable w' →
        (∀ h, F h ≠ 0 → ∫ s : Subgroup.centralizer ({γ} : Set G), w ((s : G) * h) ∂τ = 1) →
        (∀ h, F h ≠ 0 → ∫ s : Subgroup.centralizer ({γ} : Set G), w' ((s : G) * h) ∂τ = 1) →
        ∫ h, F h * (w h : ℂ) ∂μ = ∫ h, F h * (w' h : ℂ) ∂μ :=
  AutomorphicForm.integral_mul_eq_integral_mul_of_forall_integral_subgroup_mul_eq_one μ
    (Subgroup.centralizer ({γ} : Set G)) hval τ

end Transport
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_smul_splitFibreIntegral_of_isTwistedOrbitalIntegralOn_of_algHom_of_prime_of_forall_exists_isSectionFnOn_of_isMulRightInvariant.AutomorphicForm.SplitTransfer.Transport"

end TransportBlock
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_smul_splitFibreIntegral_of_isTwistedOrbitalIntegralOn_of_algHom_of_prime_of_forall_exists_isSectionFnOn_of_isMulRightInvariant.AutomorphicForm.SplitTransfer.Transport"

section ShiftFacts

p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_smul_splitFibreIntegral_of_isTwistedOrbitalIntegralOn_of_algHom_of_prime_of_forall_exists_isSectionFnOn_of_isMulRightInvariant.AutomorphicForm"

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L)

theorem mem_twistedCentralizer_iff_shift {n : ℕ} (Θ : GL (Fin 2) (L ⊗[K] A) ≃* (Fin (n + 1) → GL (Fin 2) A))
    (hΘσ : ∀ x δ : GL (Fin 2) (L ⊗[K] A),
      Θ (x⁻¹ * δ * sigmaGL K L A σ x) = fun j => (Θ x j)⁻¹ * Θ δ j * Θ x (j + 1))
    (δ s : GL (Fin 2) (L ⊗[K] A)) :
    s ∈ twistedCentralizer K L A σ δ ↔ ∀ j, (Θ s j)⁻¹ * Θ δ j * Θ s (j + 1) = Θ δ j := by
  rw [twistedCentralizer, mem_sigmaCentralizer_iff_inv, ← Θ.injective.eq_iff, hΘσ, funext_iff]

theorem eq_conj_prod_of_isNormConjugator {n : ℕ} (Θ : GL (Fin 2) (L ⊗[K] A) ≃* (Fin (n + 1) → GL (Fin 2) A))
    (hΘ1 : ∀ g : GL (Fin 2) A, Θ (toTensorGL K L A g) = fun _ => g)
    (hΘN : ∀ δ : GL (Fin 2) (L ⊗[K] A), Θ (normString K L A σ δ) 0 = (List.ofFn (Θ δ)).prod)
    (γ : GL (Fin 2) A) (δ y : GL (Fin 2) (L ⊗[K] A)) (hy : IsNormConjugator K L A σ γ δ y) :
    γ = (Θ y 0)⁻¹ * (List.ofFn (Θ δ)).prod * Θ y 0 := by
  have h1 := congrArg (fun g => Θ g 0) (show toTensorGL K L A γ = y⁻¹ * normString K L A σ δ * y from hy)
  simp only [hΘ1, map_mul, map_inv, Pi.mul_apply, Pi.inv_apply, hΘN] at h1
  exact h1

end ShiftFacts
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_smul_splitFibreIntegral_of_isTwistedOrbitalIntegralOn_of_algHom_of_prime_of_forall_exists_isSectionFnOn_of_isMulRightInvariant.AutomorphicForm.SplitTransfer.Transport"

section SectionFnFacts

p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_smul_splitFibreIntegral_of_isTwistedOrbitalIntegralOn_of_algHom_of_prime_of_forall_exists_isSectionFnOn_of_isMulRightInvariant.AutomorphicForm"

variable (A : Type) [CommRing A] [TopologicalSpace A]

theorem integrable_of_continuous_hasCompactSupport (μA : @Measure (GL (Fin 2) A) (glBorelOf A))
    (hμA : @Measure.IsHaarMeasure (GL (Fin 2) A) _ _ (glBorelOf A) μA)
    (w : GL (Fin 2) A → ℝ) (hwc : Continuous w) (hwcs : HasCompactSupport w) :
    @Integrable ℝ _ _ _ (glBorelOf A) w μA := by
  letI := glBorelOf A
  haveI := borelSpace_glBorelOf A
  haveI := hμA
  exact hwc.integrable_of_hasCompactSupport hwcs

end SectionFnFacts
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_smul_splitFibreIntegral_of_isTwistedOrbitalIntegralOn_of_algHom_of_prime_of_forall_exists_isSectionFnOn_of_isMulRightInvariant.AutomorphicForm.SplitTransfer.Transport"

end AutomorphicForm.SplitTransfer
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_smul_splitFibreIntegral_of_isTwistedOrbitalIntegralOn_of_algHom_of_prime_of_forall_exists_isSectionFnOn_of_isMulRightInvariant.AutomorphicForm.SplitTransfer.Transport P2MW.S_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_smul_splitFibreIntegral_of_isTwistedOrbitalIntegralOn_of_algHom_of_prime_of_forall_exists_isSectionFnOn_of_isMulRightInvariant.AutomorphicForm P2MW.S_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_smul_splitFibreIntegral_of_isTwistedOrbitalIntegralOn_of_algHom_of_prime_of_forall_exists_isSectionFnOn_of_isMulRightInvariant.AutomorphicForm.SplitTransfer"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_smul_splitFibreIntegral_of_isTwistedOrbitalIntegralOn_of_algHom_of_prime_of_forall_exists_isSectionFnOn_of_isMulRightInvariant.AutomorphicForm.SplitTransfer.Transport P2MW.S_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_smul_splitFibreIntegral_of_isTwistedOrbitalIntegralOn_of_algHom_of_prime_of_forall_exists_isSectionFnOn_of_isMulRightInvariant.AutomorphicForm"

theorem SplitCoordAux.isRegularSemisimple_normString_of_isNormConjugator
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L)
    (γ : GL (Fin 2) A) (δ y : GL (Fin 2) (L ⊗[K] A))
    (hy : AutomorphicForm.IsNormConjugator K L A σ γ δ y) (hγ : AutomorphicForm.IsRegularSemisimple γ) :
    AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L A σ δ) := by
  have hN : AutomorphicForm.normString K L A σ δ = y * AutomorphicForm.toTensorGL K L A γ * y⁻¹ := by
    rw [show AutomorphicForm.toTensorGL K L A γ = y⁻¹ * AutomorphicForm.normString K L A σ δ * y from hy]; group
  unfold AutomorphicForm.IsRegularSemisimple at hγ ⊢
  rw [hN]
  set T : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) := ((AutomorphicForm.toTensorGL K L A γ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))
  have hyy : ((y⁻¹ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) * (y : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have htr : Matrix.trace (((y * AutomorphicForm.toTensorGL K L A γ * y⁻¹ : GL (Fin 2) (L ⊗[K] A))) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) = Matrix.trace T := by
    rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, hyy, Matrix.one_mul]
  have hdet : Matrix.det (((y * AutomorphicForm.toTensorGL K L A γ * y⁻¹ : GL (Fin 2) (L ⊗[K] A))) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) = Matrix.det T := by
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm (Matrix.det (y : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))), mul_assoc,
      ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, mul_one]
  rw [htr, hdet]

  let f : A →+* L ⊗[K] A := (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom
  have hT : T = (γ : Matrix (Fin 2) (Fin 2) A).map f := rfl
  rw [hT]
  have hdet2 : Matrix.det ((γ : Matrix (Fin 2) (Fin 2) A).map f) = f (Matrix.det (γ : Matrix (Fin 2) (Fin 2) A)) := (RingHom.map_det f _).symm
  rw [hdet2]
  have htr2 : Matrix.trace ((γ : Matrix (Fin 2) (Fin 2) A).map f) = f (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) A)) := by
    simp [Matrix.trace, Matrix.map_apply, map_sum]
  rw [htr2, ← map_pow, show (4 : L ⊗[K] A) = f 4 from (map_ofNat f 4).symm, ← map_mul, ← map_sub]
  exact hγ.map f

open MeasureTheory
open scoped NNReal ENNReal

namespace SplitCentralAux
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_smul_splitFibreIntegral_of_isTwistedOrbitalIntegralOn_of_algHom_of_prime_of_forall_exists_isSectionFnOn_of_isMulRightInvariant.AutomorphicForm"

variable (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
  [LocallyCompactSpace A] [SecondCountableTopology A]

private theorem _root_.SplitCentralAux.secondCountableTopology_gl : SecondCountableTopology (GL (Fin 2) A) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → A))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

p2m_export "SplitCentralAux" "secondCountableTopology_gl"
private theorem _root_.SplitCentralAux.locallyCompactSpace_gl : LocallyCompactSpace (GL (Fin 2) A) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → A))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

p2m_export "SplitCentralAux" "locallyCompactSpace_gl"

theorem exists_isSectionFnOn_scalar
    (μA : @Measure (GL (Fin 2) A) (glBorelOf A))
    (hμA : @Measure.IsHaarMeasure (GL (Fin 2) A) _ _ (glBorelOf A) μA)
    (hμAr : @Measure.IsMulRightInvariant (GL (Fin 2) A) (glBorelOf A) _ μA)
    (z : Aˣ)
    (τ : @Measure (Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) z} : Set (GL (Fin 2) A)))
      (centralizerBorel A (Matrix.GeneralLinearGroup.scalar (Fin 2) z)))
    (c₀ : ℝ≥0) (hc₀ : c₀ ≠ 0)
    (hτ : @Measure.map _ _ (centralizerBorel A (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) (glBorelOf A)
      Subtype.val τ = c₀ • μA)
    (f : GL (Fin 2) A → ℂ) :
    letI : MeasurableSpace (GL (Fin 2) A) := glBorelOf A
    ∃ w : GL (Fin 2) A → ℝ, IsSectionFnOn A (Matrix.GeneralLinearGroup.scalar (Fin 2) z) τ f w ∧
      Integrable w μA ∧ ∫ x, w x ∂μA = ((c₀ : ℝ))⁻¹ := by
  letI : MeasurableSpace (GL (Fin 2) A) := glBorelOf A
  letI : MeasurableSpace (Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) z} : Set (GL (Fin 2) A))) :=
    centralizerBorel A (Matrix.GeneralLinearGroup.scalar (Fin 2) z)
  haveI : BorelSpace (GL (Fin 2) A) := borelSpace_glBorelOf A
  haveI : BorelSpace (Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) z} : Set (GL (Fin 2) A))) := ⟨rfl⟩
  haveI := locallyCompactSpace_gl A
  haveI := secondCountableTopology_gl A
  haveI : μA.IsHaarMeasure := hμA
  haveI : μA.IsMulRightInvariant := hμAr

  obtain ⟨K₀, hK₀c, hK₀n⟩ := exists_compact_mem_nhds (1 : GL (Fin 2) A)
  have hK₀pos : 0 < μA K₀ := Measure.measure_pos_of_mem_nhds μA hK₀n
  have hK₀fin : μA K₀ < ∞ := hK₀c.measure_lt_top
  set m : ℝ := (μA K₀).toReal with hm
  have hmpos : 0 < m := ENNReal.toReal_pos hK₀pos.ne' hK₀fin.ne
  set a : ℝ := ((c₀ : ℝ) * m)⁻¹ with ha
  have hc₀pos : 0 < (c₀ : ℝ) := by exact_mod_cast pos_iff_ne_zero.mpr hc₀
  have hapos : 0 < a := by rw [ha]; positivity
  let w : GL (Fin 2) A → ℝ := fun x => a * K₀.indicator (1 : GL (Fin 2) A → ℝ) x
  have hwm : Measurable w := (measurable_const.indicator hK₀c.measurableSet).const_mul a
  have hw0 : ∀ x, 0 ≤ w x := fun x => mul_nonneg hapos.le (Set.indicator_nonneg (fun _ _ => zero_le_one) x)
  have hwcs : HasCompactSupport w := by
    refine HasCompactSupport.intro hK₀c fun x hx => ?_
    simp [w, Set.indicator_of_notMem hx]
  have hwint : ∫ x, w x ∂μA = ((c₀ : ℝ))⁻¹ := by
    simp only [w]
    rw [integral_const_mul, integral_indicator_one hK₀c.measurableSet, Measure.real, ← hm, ha]
    field_simp
  have hwi : Integrable w μA := (((integrable_indicator_iff hK₀c.measurableSet).2
      (integrableOn_const hK₀fin.ne)).const_mul a)
  refine ⟨w, ⟨hw0, hwm, hwcs, fun x _ => ?_⟩, hwi, hwint⟩

  have hval : Measurable (Subtype.val : Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) z} : Set (GL (Fin 2) A)) → GL (Fin 2) A) :=
    continuous_subtype_val.measurable
  have h1 : ∫ t : Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) z} : Set (GL (Fin 2) A)), w ((t : GL (Fin 2) A) * x) ∂τ
      = ∫ g, w (g * x) ∂(Measure.map Subtype.val τ) := by
    rw [integral_map hval.aemeasurable]
    exact ((hwm.comp (measurable_id.mul_const x)).aestronglyMeasurable)
  rw [h1, hτ, integral_smul_nnreal_measure, integral_mul_right_eq_self (fun g => w g) x, hwint]
  rw [NNReal.smul_def, smul_eq_mul]; push_cast
  field_simp

end SplitCentralAux
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_smul_splitFibreIntegral_of_isTwistedOrbitalIntegralOn_of_algHom_of_prime_of_forall_exists_isSectionFnOn_of_isMulRightInvariant.AutomorphicForm.SplitTransfer.Transport P2MW.S_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_smul_splitFibreIntegral_of_isTwistedOrbitalIntegralOn_of_algHom_of_prime_of_forall_exists_isSectionFnOn_of_isMulRightInvariant.AutomorphicForm P2MW.S_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_smul_splitFibreIntegral_of_isTwistedOrbitalIntegralOn_of_algHom_of_prime_of_forall_exists_isSectionFnOn_of_isMulRightInvariant.AutomorphicForm.SplitTransfer"

namespace SplitCoordAux
private theorem _root_.SplitCoordAux.secondCountableTopology_gl (A : Type) [CommRing A] [TopologicalSpace A] [SecondCountableTopology A] :
    SecondCountableTopology (GL (Fin 2) A) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → A))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology
p2m_export "SplitCoordAux" "secondCountableTopology_gl"
end SplitCoordAux
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_smul_splitFibreIntegral_of_isTwistedOrbitalIntegralOn_of_algHom_of_prime_of_forall_exists_isSectionFnOn_of_isMulRightInvariant.AutomorphicForm.SplitTransfer.Transport P2MW.S_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_smul_splitFibreIntegral_of_isTwistedOrbitalIntegralOn_of_algHom_of_prime_of_forall_exists_isSectionFnOn_of_isMulRightInvariant.AutomorphicForm P2MW.S_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_smul_splitFibreIntegral_of_isTwistedOrbitalIntegralOn_of_algHom_of_prime_of_forall_exists_isSectionFnOn_of_isMulRightInvariant.AutomorphicForm.SplitTransfer"

theorem solution
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [Finite (MaximalSpectrum A)]
    (ι : L →ₐ[K] A)
    (μL : @Measure (GL (Fin 2) (L ⊗[K] A)) (AutomorphicForm.glBorelOf (L ⊗[K] A)))
    (hμL : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] A)) _ _ (AutomorphicForm.glBorelOf (L ⊗[K] A)) μL)
    (μA : @Measure (GL (Fin 2) A) (AutomorphicForm.glBorelOf A))
    (hμA : @Measure.IsHaarMeasure (GL (Fin 2) A) _ _ (AutomorphicForm.glBorelOf A) μA)

    (hsec : ∀ γ : GL (Fin 2) A, AutomorphicForm.IsRegularSemisimple γ →
      ∀ τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (AutomorphicForm.centralizerBorel A γ),
        @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.centralizerBorel A γ) τ →
      ∀ f : GL (Fin 2) A → ℂ, HasCompactSupport f →
        ∃ w : GL (Fin 2) A → ℝ, AutomorphicForm.IsSectionFnOn A γ τ f w ∧ Continuous w)

    (hμAr : @Measure.IsMulRightInvariant (GL (Fin 2) A) (AutomorphicForm.glBorelOf A) _ μA) :
    ∃ c : ℝ, 0 < c ∧
      ∀ φ : GL (Fin 2) (L ⊗[K] A) → ℂ, Continuous φ → HasCompactSupport φ →
        (∀ (δ : GL (Fin 2) (L ⊗[K] A)) (γ : GL (Fin 2) A), AutomorphicForm.IsRegularSemisimple γ →
          ∀ y : GL (Fin 2) (L ⊗[K] A), AutomorphicForm.IsNormConjugator K L A σ γ δ y →
          ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)))
                (AutomorphicForm.centralizerBorel A γ))
            (τ' : @Measure (AutomorphicForm.twistedCentralizer K L A σ δ)
                (AutomorphicForm.twistedCentralizerBorel K L A σ δ)),
            @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.centralizerBorel A γ) τ →
            @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L A σ δ) τ' →
            AutomorphicForm.Coupled K L A σ γ δ y τ τ' →
            ∀ I' : ℂ, AutomorphicForm.IsTwistedOrbitalIntegralOn K L A σ μL δ τ' φ I' →
              AutomorphicForm.IsOrbitalIntegralOn A μA γ τ
                (c • AutomorphicForm.splitFibreIntegral K L hdeg σ hσ A ι μA φ) I') ∧
        (∀ (δ : GL (Fin 2) (L ⊗[K] A)) (z : Aˣ) (y : GL (Fin 2) (L ⊗[K] A)),
          AutomorphicForm.IsNormConjugator K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) δ y →
          ∀ (τ : @Measure (Subgroup.centralizer
                  ({Matrix.GeneralLinearGroup.scalar (Fin 2) z} : Set (GL (Fin 2) A)))
                (AutomorphicForm.centralizerBorel A (Matrix.GeneralLinearGroup.scalar (Fin 2) z)))
            (τ' : @Measure (AutomorphicForm.twistedCentralizer K L A σ δ)
                (AutomorphicForm.twistedCentralizerBorel K L A σ δ)),
            @Measure.IsHaarMeasure _ _ _
              (AutomorphicForm.centralizerBorel A (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) τ →
            @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L A σ δ) τ' →
            AutomorphicForm.Coupled K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) δ y τ τ' →
            ∀ c₀ : NNReal,
              @Measure.map _ _
                  (AutomorphicForm.centralizerBorel A (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
                  (AutomorphicForm.glBorelOf A) Subtype.val τ = c₀ • μA →
              ∀ I' : ℂ, AutomorphicForm.IsTwistedOrbitalIntegralOn K L A σ μL δ τ' φ I' →
                I' = (c • AutomorphicForm.splitFibreIntegral K L hdeg σ hσ A ι μA φ)
                  (Matrix.GeneralLinearGroup.scalar (Fin 2) z) * ((((c₀ : ℝ))⁻¹ : ℝ) : ℂ)) := by
  classical
  letI : MeasurableSpace (GL (Fin 2) A) := AutomorphicForm.glBorelOf A
  letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] A)) := AutomorphicForm.glBorelOf (L ⊗[K] A)

  obtain ⟨hΘc, hΘc', hΘσ, hΘ1, hΘN, hΘN0, c, hc0, hcμ⟩ :=
    AutomorphicForm.SplitPlace.continuous_coords_and_coords_sigmaGL_and_coords_normString_and_exists_pos_map_coords_eq_smul_pi
      K L hdeg σ hσ A ι μL hμL μA hμA
  set Θ := AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ with hΘdef
  refine ⟨(c : ℝ), by exact_mod_cast hc0, fun φ hφc hφs => ⟨?_, ?_⟩⟩
  ·
    intro δ' γ hγ y hy τ τ' hτ hτ' hcpl I' hI'

    set δ : Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A := Θ δ' with hδ
    set y₀ : GL (Fin 2) A := Θ y 0 with hy₀
    set Φ : (Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A) → ℂ := fun ξ => φ (Θ.symm ξ) with hΦ

    have hγeq : γ = y₀⁻¹ * (List.ofFn δ).prod * y₀ := by
      have h := congrArg (fun g => Θ g 0) hy
      simp only [map_mul, map_inv, Pi.mul_apply, Pi.inv_apply] at h
      rw [hΘ1] at h
      rw [← hΘN0 δ']; exact h

    have htwc : ∀ x : GL (Fin 2) (L ⊗[K] A), ∀ j,
        Θ (x⁻¹ * δ' * AutomorphicForm.sigmaGL K L A σ x) j = (Θ x j)⁻¹ * δ j * Θ x (j + 1) := by
      intro x j
      simp only [map_mul, map_inv, Pi.mul_apply, Pi.inv_apply, hΘσ, hδ]

    haveI : BorelSpace (GL (Fin 2) A) := AutomorphicForm.borelSpace_glBorelOf A
    haveI : BorelSpace (GL (Fin 2) (L ⊗[K] A)) := AutomorphicForm.borelSpace_glBorelOf (L ⊗[K] A)
    haveI : SecondCountableTopology (GL (Fin 2) A) := SplitCoordAux.secondCountableTopology_gl A
    haveI hTRL : IsTopologicalRing (L ⊗[K] A) := AutomorphicForm.isTopologicalRing_tensor K L A
    let ΘH : GL (Fin 2) (L ⊗[K] A) ≃ₜ (Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A) :=
      { toEquiv := Θ.toEquiv, continuous_toFun := hΘc, continuous_invFun := hΘc' }
    let Θm : GL (Fin 2) (L ⊗[K] A) ≃ᵐ (Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A) := ΘH.toMeasurableEquiv
    have hΘm : ∀ x, Θm x = Θ x := fun x => rfl

    have hcov : ∀ F : GL (Fin 2) (L ⊗[K] A) → ℂ,
        ∫ x, F x ∂μL = (c : ℝ) * ∫ ξ, F (Θ.symm ξ) ∂(Measure.pi fun _ : Fin (Module.finrank K L - 1 + 1) => μA) := by
      intro F
      have h1 : ∫ ξ, F (Θ.symm ξ) ∂(Measure.map Θm μL) = ∫ x, F (Θ.symm (Θm x)) ∂μL :=
        MeasureTheory.integral_map_equiv Θm (fun ξ => F (Θ.symm ξ))
      have h2 : ∀ x, F (Θ.symm (Θm x)) = F x := fun x => by rw [hΘm, MulEquiv.symm_apply_apply]
      simp only [h2] at h1
      have h3 : Measure.map (⇑Θm) μL = Measure.map (⇑Θ) μL := by congr 1
      rw [← h1, h3, hcμ, MeasureTheory.integral_smul_nnreal_measure]
      simp [Complex.real_smul, NNReal.smul_def]

    obtain ⟨w', hw', hI'eq⟩ := hI'

    open AutomorphicForm.SplitTransfer in
    obtain ⟨hMM, hMI, hSF, hLI⟩ := local_group_facts A μA hμA
    haveI : MeasurableMul₂ (GL (Fin 2) A) := hMM
    haveI : MeasurableInv (GL (Fin 2) A) := hMI
    haveI : SigmaFinite μA := hSF
    haveI : μA.IsMulLeftInvariant := hLI
    have hΘmm := AutomorphicForm.SplitTransfer.measurable_mulEquiv K L A Θ hΘc hΘc'

    have hΘσ' : ∀ x d : GL (Fin 2) (L ⊗[K] A),
        Θ (x⁻¹ * d * AutomorphicForm.sigmaGL K L A σ x) = fun j => (Θ x j)⁻¹ * Θ d j * Θ x (j + 1) := by
      intro x d; funext j; simp only [map_mul, map_inv, Pi.mul_apply, Pi.inv_apply, hΘσ]

    let Tw := AutomorphicForm.twistedCentralizer K L A σ δ'
    letI : MeasurableSpace Tw := AutomorphicForm.twistedCentralizerBorel K L A σ δ'
    letI : MeasurableSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) := AutomorphicForm.centralizerBorel A γ
    obtain ⟨hTwInv, hTwVal⟩ := AutomorphicForm.SplitTransfer.twisted_carrier_facts K L A σ δ'
    obtain ⟨hCInv, hCVal⟩ := AutomorphicForm.SplitTransfer.carrier_facts A γ
    haveI : MeasurableInv Tw := hTwInv
    haveI : MeasurableInv (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) := hCInv
    let T : Subgroup (Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A) := AutomorphicForm.SplitTransfer.Transport.imageSubgroup Θ Tw
    have hT : ∀ t, t ∈ T ↔ ∀ j, (t j)⁻¹ * δ j * t (j + 1) = δ j :=
      AutomorphicForm.SplitTransfer.Transport.mem_imageSubgroup_iff Θ Tw δ
        (fun s => AutomorphicForm.SplitTransfer.mem_twistedCentralizer_iff_shift K L A σ Θ hΘσ' δ' s)
    let τT := AutomorphicForm.SplitTransfer.Transport.transportMeasure Θ Tw τ'

    have hδreg : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L A σ δ') :=
      SplitCoordAux.isRegularSemisimple_normString_of_isNormConjugator K L A σ γ δ' y hy hγ
    obtain ⟨hτSF, hτInv⟩ := AutomorphicForm.SplitTransfer.torus_facts A γ hγ τ hτ
    obtain ⟨hτ'SF, hτ'Inv⟩ := AutomorphicForm.SplitTransfer.twisted_torus_facts K L A σ δ' hδreg τ' hτ'
    haveI : SFinite τ := hτSF
    haveI : τ.IsInvInvariant := hτInv
    haveI : SFinite τ' := hτ'SF
    haveI : τ'.IsInvInvariant := hτ'Inv

    have hcoup := AutomorphicForm.SplitTransfer.coupling K L A σ Θ hΘc hΘ1 γ δ' y τ τ' hcpl
    have hτT := AutomorphicForm.SplitTransfer.Transport.map_conj_transportMeasure_eq Θ hΘmm.1 Tw hTwVal τ' y₀ γ τ hcoup

    obtain ⟨hΦc, hΦcs⟩ := AutomorphicForm.SplitTransfer.model_fn_facts K L A Θ hΘc hΘc' φ hφc hφs
    haveI : BorelSpace (Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A) := AutomorphicForm.SplitTransfer.borelSpace_pi A _
    have hΦm : Measurable Φ := hΦc.measurable
    obtain ⟨CΦ, hCΦ⟩ := hΦcs.exists_bound_of_continuous hΦc

    obtain ⟨hw'0, hw'm, hw'cs, hw'1⟩ := hw'
    let W₀ : (Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A) → ℝ := fun ξ => w' (Θ.symm ξ)
    have hW₀0 : ∀ ξ, 0 ≤ W₀ ξ := fun ξ => hw'0 _
    have hW₀m : Measurable W₀ := hw'm.comp hΘmm.2
    have htwcΘ : ∀ ξ : Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A,
        Θ.symm (fun j => (ξ j)⁻¹ * δ j * ξ (j + 1)) = (Θ.symm ξ)⁻¹ * δ' * AutomorphicForm.sigmaGL K L A σ (Θ.symm ξ) := by
      intro ξ; apply Θ.injective; rw [MulEquiv.apply_symm_apply, hΘσ']; simp only [MulEquiv.apply_symm_apply, hδ]
    have hW₀1 : ∀ ξ, Φ (fun j => (ξ j)⁻¹ * δ j * ξ (j + 1)) ≠ 0 → ∫ t : T, W₀ ((t : Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A) * ξ) ∂τT = 1 := by
      intro ξ hξ
      have h := AutomorphicForm.SplitTransfer.Transport.integral_transportMeasure_comp_symm Θ hΘmm.1 hΘmm.2 Tw hTwVal τ' w' hw'm ξ
      show ∫ t : T, (w' ∘ Θ.symm) ((t : Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A) * ξ) ∂τT = 1
      rw [h]
      apply hw'1
      rw [← htwcΘ]
      simpa [hΦ] using hξ

    let f : GL (Fin 2) A → ℂ := fun h => ∫ cc : Fin (Module.finrank K L - 1) → GL (Fin 2) A,
      Φ (Fin.snoc cc (((List.ofFn cc).prod)⁻¹ * h)) ∂(Measure.pi fun _ => μA)
    let Φ₁ : (Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A) → ℂ := fun ξ => (‖Φ ξ‖ : ℂ)
    let f₁ : GL (Fin 2) A → ℂ := fun h => ∫ cc : Fin (Module.finrank K L - 1) → GL (Fin 2) A,
      Φ₁ (Fin.snoc cc (((List.ofFn cc).prod)⁻¹ * h)) ∂(Measure.pi fun _ => μA)
    have hfcs : HasCompactSupport f := AutomorphicForm.SplitTransfer.hasCompactSupport_fibreIntegral A μA Φ hΦcs
    have hΦ₁cs : HasCompactSupport Φ₁ := AutomorphicForm.SplitTransfer.hasCompactSupport_norm_cast hΦcs
    have hf₁cs : HasCompactSupport f₁ := AutomorphicForm.SplitTransfer.hasCompactSupport_fibreIntegral A μA Φ₁ hΦ₁cs

    obtain ⟨w₀, ⟨hw₀0, hw₀m, hw₀cs, hw₀1⟩, hw₀c⟩ := hsec γ hγ τ hτ f hfcs
    obtain ⟨w₁, ⟨hw₁0, hw₁m, hw₁cs, hw₁1⟩, hw₁c⟩ := hsec γ hγ τ hτ f₁ hf₁cs
    have hw₁i : Integrable w₁ μA := AutomorphicForm.SplitTransfer.integrable_of_continuous_hasCompactSupport A μA hμA w₁ hw₁c hw₁cs
    obtain ⟨β, hβ0, hβm, hβi, hβ1⟩ := AutomorphicForm.SplitTransfer.exists_cutoff_fn A μA hμA Φ hΦcs

    have key := AutomorphicForm.integral_twistedConj_mul_eq_integral_conj_fibreIntegral_mul μA δ
      (fun x j => (x j)⁻¹ * δ j * x (j + 1)) (fun _ _ => rfl) T hT y₀ γ hγeq Φ hΦm ⟨CΦ, hCΦ⟩ f f₁
      (fun _ => rfl) (fun _ => rfl) τT (AutomorphicForm.SplitTransfer.Transport.measurable_conj_apply_zero y₀ Θ Tw)
      τ hCVal hτT
      (AutomorphicForm.SplitTransfer.Transport.huniq_image μA Θ hΘmm.1 Tw hTwVal τ')
      (AutomorphicForm.SplitTransfer.Transport.huniq_centralizer μA γ hCVal τ)
      W₀ hW₀0 hW₀m hW₀1 w₀ hw₀0 hw₀m hw₀1 ⟨w₁, hw₁0, hw₁m, hw₁i, hw₁1⟩ ⟨β, hβ0, hβm, hβi, hβ1⟩

    have hfF : AutomorphicForm.splitFibreIntegral K L hdeg σ hσ A ι μA φ = f := by
      funext h
      simp only [AutomorphicForm.splitFibreIntegral, AutomorphicForm.SplitPlace.string, AutomorphicForm.SplitPlace.listProd, hΦ]
      rfl
    refine ⟨w₀, ⟨hw₀0, hw₀m, hw₀cs, ?_⟩, ?_⟩
    · intro x hx
      apply hw₀1 x
      intro h0; apply hx
      show ((c : ℝ) • AutomorphicForm.splitFibreIntegral K L hdeg σ hσ A ι μA φ) (x⁻¹ * γ * x) = 0
      rw [Pi.smul_apply, hfF, h0, smul_zero]
    ·
      have hint : ∀ x : GL (Fin 2) A, ((c : ℝ) • AutomorphicForm.splitFibreIntegral K L hdeg σ hσ A ι μA φ) (x⁻¹ * γ * x) * (w₀ x : ℂ)
          = (c : ℂ) * (f (x⁻¹ * γ * x) * (w₀ x : ℂ)) := by
        intro x; rw [Pi.smul_apply, hfF, Complex.real_smul]; push_cast; ring
      simp_rw [hint]
      rw [MeasureTheory.integral_const_mul, ← key, hI'eq, hcov]
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
      show φ ((Θ.symm ξ)⁻¹ * δ' * AutomorphicForm.sigmaGL K L A σ (Θ.symm ξ)) * ((w' (Θ.symm ξ) : ℝ) : ℂ) = Φ (fun j => (ξ j)⁻¹ * δ j * ξ (j + 1)) * (W₀ ξ : ℂ)
      rw [← htwcΘ]
  ·
    intro δ' z y hy τ τ' hτ hτ' hcpl c₀ hc₀ I' hI'

    set δ : Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A := Θ δ' with hδ
    set y₀ : GL (Fin 2) A := Θ y 0 with hy₀
    set Φ : (Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A) → ℂ := fun ξ => φ (Θ.symm ξ) with hΦ

    have hγeq : (Matrix.GeneralLinearGroup.scalar (Fin 2) z) = y₀⁻¹ * (List.ofFn δ).prod * y₀ := by
      have h := congrArg (fun g => Θ g 0) hy
      simp only [map_mul, map_inv, Pi.mul_apply, Pi.inv_apply] at h
      rw [hΘ1] at h
      rw [← hΘN0 δ']; exact h

    have htwc : ∀ x : GL (Fin 2) (L ⊗[K] A), ∀ j,
        Θ (x⁻¹ * δ' * AutomorphicForm.sigmaGL K L A σ x) j = (Θ x j)⁻¹ * δ j * Θ x (j + 1) := by
      intro x j
      simp only [map_mul, map_inv, Pi.mul_apply, Pi.inv_apply, hΘσ, hδ]

    haveI : BorelSpace (GL (Fin 2) A) := AutomorphicForm.borelSpace_glBorelOf A
    haveI : BorelSpace (GL (Fin 2) (L ⊗[K] A)) := AutomorphicForm.borelSpace_glBorelOf (L ⊗[K] A)
    haveI : SecondCountableTopology (GL (Fin 2) A) := SplitCoordAux.secondCountableTopology_gl A
    haveI hTRL : IsTopologicalRing (L ⊗[K] A) := AutomorphicForm.isTopologicalRing_tensor K L A
    let ΘH : GL (Fin 2) (L ⊗[K] A) ≃ₜ (Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A) :=
      { toEquiv := Θ.toEquiv, continuous_toFun := hΘc, continuous_invFun := hΘc' }
    let Θm : GL (Fin 2) (L ⊗[K] A) ≃ᵐ (Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A) := ΘH.toMeasurableEquiv
    have hΘm : ∀ x, Θm x = Θ x := fun x => rfl

    have hcov : ∀ F : GL (Fin 2) (L ⊗[K] A) → ℂ,
        ∫ x, F x ∂μL = (c : ℝ) * ∫ ξ, F (Θ.symm ξ) ∂(Measure.pi fun _ : Fin (Module.finrank K L - 1 + 1) => μA) := by
      intro F
      have h1 : ∫ ξ, F (Θ.symm ξ) ∂(Measure.map Θm μL) = ∫ x, F (Θ.symm (Θm x)) ∂μL :=
        MeasureTheory.integral_map_equiv Θm (fun ξ => F (Θ.symm ξ))
      have h2 : ∀ x, F (Θ.symm (Θm x)) = F x := fun x => by rw [hΘm, MulEquiv.symm_apply_apply]
      simp only [h2] at h1
      have h3 : Measure.map (⇑Θm) μL = Measure.map (⇑Θ) μL := by congr 1
      rw [← h1, h3, hcμ, MeasureTheory.integral_smul_nnreal_measure]
      simp [Complex.real_smul, NNReal.smul_def]

    obtain ⟨w', hw', hI'eq⟩ := hI'

    open AutomorphicForm.SplitTransfer in
    obtain ⟨hMM, hMI, hSF, hLI⟩ := local_group_facts A μA hμA
    haveI : MeasurableMul₂ (GL (Fin 2) A) := hMM
    haveI : MeasurableInv (GL (Fin 2) A) := hMI
    haveI : SigmaFinite μA := hSF
    haveI : μA.IsMulLeftInvariant := hLI
    have hΘmm := AutomorphicForm.SplitTransfer.measurable_mulEquiv K L A Θ hΘc hΘc'

    have hΘσ' : ∀ x d : GL (Fin 2) (L ⊗[K] A),
        Θ (x⁻¹ * d * AutomorphicForm.sigmaGL K L A σ x) = fun j => (Θ x j)⁻¹ * Θ d j * Θ x (j + 1) := by
      intro x d; funext j; simp only [map_mul, map_inv, Pi.mul_apply, Pi.inv_apply, hΘσ]

    let Tw := AutomorphicForm.twistedCentralizer K L A σ δ'
    letI : MeasurableSpace Tw := AutomorphicForm.twistedCentralizerBorel K L A σ δ'
    letI : MeasurableSpace (Subgroup.centralizer ({(Matrix.GeneralLinearGroup.scalar (Fin 2) z)} : Set (GL (Fin 2) A))) := AutomorphicForm.centralizerBorel A (Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    obtain ⟨hTwInv, hTwVal⟩ := AutomorphicForm.SplitTransfer.twisted_carrier_facts K L A σ δ'
    obtain ⟨hCInv, hCVal⟩ := AutomorphicForm.SplitTransfer.carrier_facts A (Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    haveI : MeasurableInv Tw := hTwInv
    haveI : MeasurableInv (Subgroup.centralizer ({(Matrix.GeneralLinearGroup.scalar (Fin 2) z)} : Set (GL (Fin 2) A))) := hCInv
    let T : Subgroup (Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A) := AutomorphicForm.SplitTransfer.Transport.imageSubgroup Θ Tw
    have hT : ∀ t, t ∈ T ↔ ∀ j, (t j)⁻¹ * δ j * t (j + 1) = δ j :=
      AutomorphicForm.SplitTransfer.Transport.mem_imageSubgroup_iff Θ Tw δ
        (fun s => AutomorphicForm.SplitTransfer.mem_twistedCentralizer_iff_shift K L A σ Θ hΘσ' δ' s)
    let τT := AutomorphicForm.SplitTransfer.Transport.transportMeasure Θ Tw τ'

    haveI : BorelSpace (GL (Fin 2) A) := AutomorphicForm.borelSpace_glBorelOf A
    haveI : BorelSpace (Subgroup.centralizer ({(Matrix.GeneralLinearGroup.scalar (Fin 2) z)} : Set (GL (Fin 2) A))) := ⟨rfl⟩
    haveI : LocallyCompactSpace (GL (Fin 2) A) := AutomorphicForm.SplitTransfer.OrbitalCarriers.locallyCompactSpace_gl A
    haveI : SecondCountableTopology (GL (Fin 2) A) := AutomorphicForm.SplitTransfer.OrbitalCarriers.secondCountableTopology_gl A
    haveI : μA.IsHaarMeasure := hμA
    haveI : μA.IsMulRightInvariant := hμAr
    haveI hμAinv : μA.IsInvInvariant := MeasureTheory.Measure.isInvInvariant_of_isMulRightInvariant μA
    haveI : τ.IsHaarMeasure := hτ

    have hc₀ne : c₀ ≠ 0 := by
      intro h0
      have h1 : Measure.map (fun s : Subgroup.centralizer ({(Matrix.GeneralLinearGroup.scalar (Fin 2) z)} : Set (GL (Fin 2) A)) => (s : GL (Fin 2) A)) τ Set.univ = 0 := by
        rw [show (fun s : Subgroup.centralizer ({(Matrix.GeneralLinearGroup.scalar (Fin 2) z)} : Set (GL (Fin 2) A)) => (s : GL (Fin 2) A)) = Subtype.val from rfl, hc₀, h0, zero_smul]; rfl
      rw [Measure.map_apply hCVal MeasurableSet.univ, Set.preimage_univ] at h1
      exact (NeZero.ne (τ Set.univ)) h1

    haveI : SFinite τ := AutomorphicForm.SplitTransfer.OrbitalCarriers.sfinite_of_isHaarMeasure_of_isClosed _
      (AutomorphicForm.SplitTransfer.OrbitalCarriers.isClosed_centralizer A (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) τ hτ
    haveI hτInv : τ.IsInvInvariant := by
      have hemb : MeasurableEmbedding (Subtype.val : Subgroup.centralizer ({(Matrix.GeneralLinearGroup.scalar (Fin 2) z)} : Set (GL (Fin 2) A)) → GL (Fin 2) A) :=
        (AutomorphicForm.SplitTransfer.OrbitalCarriers.isClosed_centralizer A (Matrix.GeneralLinearGroup.scalar (Fin 2) z)).isClosedEmbedding_subtypeVal.measurableEmbedding
      refine ⟨?_⟩

      have hpush : Measure.map Subtype.val τ.inv = Measure.map Subtype.val τ := by
        rw [Measure.inv, Measure.map_map hCVal measurable_inv]
        have hcomm : (Subtype.val ∘ (Inv.inv : Subgroup.centralizer ({(Matrix.GeneralLinearGroup.scalar (Fin 2) z)} : Set (GL (Fin 2) A)) → _)) = (Inv.inv ∘ Subtype.val) := by
          funext t; rfl
        rw [hcomm, ← Measure.map_map measurable_inv hCVal]
        rw [hc₀]
        rw [Measure.map_smul, ← Measure.inv, Measure.inv_eq_self]
      ext s hs
      rw [← Set.preimage_image_eq s Subtype.val_injective, ← hemb.map_apply, ← hemb.map_apply, hpush]
    haveI : SFinite τ' := by
      haveI := AutomorphicForm.isTopologicalRing_tensor K L A
      haveI := AutomorphicForm.t2Space_tensor K L A
      haveI := AutomorphicForm.locallyCompactSpace_tensor K L A
      haveI := AutomorphicForm.SplitTransfer.TensorFacts.secondCountableTopology_tensor K L A
      haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L A
      haveI := AutomorphicForm.SplitTransfer.OrbitalCarriers.locallyCompactSpace_gl (L ⊗[K] A)
      haveI := AutomorphicForm.SplitTransfer.OrbitalCarriers.secondCountableTopology_gl (L ⊗[K] A)
      exact AutomorphicForm.SplitTransfer.OrbitalCarriers.sfinite_of_isHaarMeasure_of_isClosed _
        (AutomorphicForm.SplitTransfer.OrbitalCarriers.isClosed_twistedCentralizer K L A σ
          (AutomorphicForm.SplitTransfer.TensorFacts.continuous_sigmaGL K L A σ) δ') τ' hτ'
    haveI : τ'.IsInvInvariant := AutomorphicForm.isInvInvariant_of_coupled_of_isInvInvariant K L σ A (Matrix.GeneralLinearGroup.scalar (Fin 2) z) δ' y τ τ' hcpl hτInv

    have hcoup := AutomorphicForm.SplitTransfer.coupling K L A σ Θ hΘc hΘ1 (Matrix.GeneralLinearGroup.scalar (Fin 2) z) δ' y τ τ' hcpl
    have hτT := AutomorphicForm.SplitTransfer.Transport.map_conj_transportMeasure_eq Θ hΘmm.1 Tw hTwVal τ' y₀ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) τ hcoup

    obtain ⟨hΦc, hΦcs⟩ := AutomorphicForm.SplitTransfer.model_fn_facts K L A Θ hΘc hΘc' φ hφc hφs
    haveI : BorelSpace (Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A) := AutomorphicForm.SplitTransfer.borelSpace_pi A _
    have hΦm : Measurable Φ := hΦc.measurable
    obtain ⟨CΦ, hCΦ⟩ := hΦcs.exists_bound_of_continuous hΦc

    obtain ⟨hw'0, hw'm, hw'cs, hw'1⟩ := hw'
    let W₀ : (Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A) → ℝ := fun ξ => w' (Θ.symm ξ)
    have hW₀0 : ∀ ξ, 0 ≤ W₀ ξ := fun ξ => hw'0 _
    have hW₀m : Measurable W₀ := hw'm.comp hΘmm.2
    have htwcΘ : ∀ ξ : Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A,
        Θ.symm (fun j => (ξ j)⁻¹ * δ j * ξ (j + 1)) = (Θ.symm ξ)⁻¹ * δ' * AutomorphicForm.sigmaGL K L A σ (Θ.symm ξ) := by
      intro ξ; apply Θ.injective; rw [MulEquiv.apply_symm_apply, hΘσ']; simp only [MulEquiv.apply_symm_apply, hδ]
    have hW₀1 : ∀ ξ, Φ (fun j => (ξ j)⁻¹ * δ j * ξ (j + 1)) ≠ 0 → ∫ t : T, W₀ ((t : Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A) * ξ) ∂τT = 1 := by
      intro ξ hξ
      have h := AutomorphicForm.SplitTransfer.Transport.integral_transportMeasure_comp_symm Θ hΘmm.1 hΘmm.2 Tw hTwVal τ' w' hw'm ξ
      show ∫ t : T, (w' ∘ Θ.symm) ((t : Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A) * ξ) ∂τT = 1
      rw [h]
      apply hw'1
      rw [← htwcΘ]
      simpa [hΦ] using hξ

    let f : GL (Fin 2) A → ℂ := fun h => ∫ cc : Fin (Module.finrank K L - 1) → GL (Fin 2) A,
      Φ (Fin.snoc cc (((List.ofFn cc).prod)⁻¹ * h)) ∂(Measure.pi fun _ => μA)
    let Φ₁ : (Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A) → ℂ := fun ξ => (‖Φ ξ‖ : ℂ)
    let f₁ : GL (Fin 2) A → ℂ := fun h => ∫ cc : Fin (Module.finrank K L - 1) → GL (Fin 2) A,
      Φ₁ (Fin.snoc cc (((List.ofFn cc).prod)⁻¹ * h)) ∂(Measure.pi fun _ => μA)
    have hfcs : HasCompactSupport f := AutomorphicForm.SplitTransfer.hasCompactSupport_fibreIntegral A μA Φ hΦcs
    have hΦ₁cs : HasCompactSupport Φ₁ := AutomorphicForm.SplitTransfer.hasCompactSupport_norm_cast hΦcs
    have hf₁cs : HasCompactSupport f₁ := AutomorphicForm.SplitTransfer.hasCompactSupport_fibreIntegral A μA Φ₁ hΦ₁cs

    obtain ⟨w₀, ⟨hw₀0, hw₀m, hw₀cs, hw₀1⟩, hw₀i, hw₀int⟩ := SplitCentralAux.exists_isSectionFnOn_scalar A μA hμA hμAr z τ c₀ hc₀ne hc₀ f
    obtain ⟨w₁, ⟨hw₁0, hw₁m, hw₁cs, hw₁1⟩, hw₁i, -⟩ := SplitCentralAux.exists_isSectionFnOn_scalar A μA hμA hμAr z τ c₀ hc₀ne hc₀ f₁
    obtain ⟨β, hβ0, hβm, hβi, hβ1⟩ := AutomorphicForm.SplitTransfer.exists_cutoff_fn A μA hμA Φ hΦcs

    have key := AutomorphicForm.integral_twistedConj_mul_eq_integral_conj_fibreIntegral_mul μA δ
      (fun x j => (x j)⁻¹ * δ j * x (j + 1)) (fun _ _ => rfl) T hT y₀ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) hγeq Φ hΦm ⟨CΦ, hCΦ⟩ f f₁
      (fun _ => rfl) (fun _ => rfl) τT (AutomorphicForm.SplitTransfer.Transport.measurable_conj_apply_zero y₀ Θ Tw)
      τ hCVal hτT
      (AutomorphicForm.SplitTransfer.Transport.huniq_image μA Θ hΘmm.1 Tw hTwVal τ')
      (AutomorphicForm.SplitTransfer.Transport.huniq_centralizer μA (Matrix.GeneralLinearGroup.scalar (Fin 2) z) hCVal τ)
      W₀ hW₀0 hW₀m hW₀1 w₀ hw₀0 hw₀m hw₀1 ⟨w₁, hw₁0, hw₁m, hw₁i, hw₁1⟩ ⟨β, hβ0, hβm, hβi, hβ1⟩

    have hfF : AutomorphicForm.splitFibreIntegral K L hdeg σ hσ A ι μA φ = f := by
      funext h
      simp only [AutomorphicForm.splitFibreIntegral, AutomorphicForm.SplitPlace.string, AutomorphicForm.SplitPlace.listProd, hΦ]
      rfl
    have hcentral : ∀ h : GL (Fin 2) A, h⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 2) z) * h = (Matrix.GeneralLinearGroup.scalar (Fin 2) z) := by
      intro h
      have hc : (Matrix.GeneralLinearGroup.scalar (Fin 2) z) * h = h * (Matrix.GeneralLinearGroup.scalar (Fin 2) z) := by
        refine Units.ext ?_
        push_cast
        exact (Matrix.scalar_commute (z : A) (fun r' => mul_comm _ r') (h : Matrix (Fin 2) (Fin 2) A)).eq
      rw [mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [hI'eq, hcov]
    have hL : ∫ ξ, φ ((Θ.symm ξ)⁻¹ * δ' * AutomorphicForm.sigmaGL K L A σ (Θ.symm ξ)) * ((w' (Θ.symm ξ) : ℝ) : ℂ) ∂(Measure.pi fun _ : Fin (Module.finrank K L - 1 + 1) => μA)
        = ∫ ξ, Φ (fun j => (ξ j)⁻¹ * δ j * ξ (j + 1)) * (W₀ ξ : ℂ) ∂(Measure.pi fun _ : Fin (Module.finrank K L - 1 + 1) => μA) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
      show φ ((Θ.symm ξ)⁻¹ * δ' * AutomorphicForm.sigmaGL K L A σ (Θ.symm ξ)) * ((w' (Θ.symm ξ) : ℝ) : ℂ) = Φ (fun j => (ξ j)⁻¹ * δ j * ξ (j + 1)) * (W₀ ξ : ℂ)
      rw [← htwcΘ]
    rw [hL, key]
    simp_rw [hcentral]
    rw [MeasureTheory.integral_const_mul, integral_complex_ofReal, hw₀int, Pi.smul_apply, hfF, Complex.real_smul]
    push_cast
    ring

#print axioms solution

end S_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_smul_splitFibreIntegral_of_isTwistedOrbitalIntegralOn_of_algHom_of_prime_of_forall_exists_isSectionFnOn_of_isMulRightInvariant
end P2MW
export P2MW.S_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_smul_splitFibreIntegral_of_isTwistedOrbitalIntegralOn_of_algHom_of_prime_of_forall_exists_isSectionFnOn_of_isMulRightInvariant (solution)
