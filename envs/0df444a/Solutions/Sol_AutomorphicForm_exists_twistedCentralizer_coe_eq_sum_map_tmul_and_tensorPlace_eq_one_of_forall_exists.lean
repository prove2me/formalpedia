-- Prove2me | solution 1 for AutomorphicForm.exists_twistedCentralizer_coe_eq_sum_map_tmul_and_tensorPlace_eq_one_of_forall_exists
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/a59a5dd2-3b44-55d3-a60c-5dfc0fff5c76

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_TwistedCommutant
import Definitions.Def_Mathlib_Topology_Algebra_RestrictedProduct_TopologicalSpace
import Definitions.Def_Mathlib_LinearAlgebra_Countable
import Theorems.Thm_NumberField_AdeleRing_exists_isAddHaarMeasure_map_pi_fst_snd_eq_prod
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_AutomorphicForm_exists_homeomorph_twistedCommutant_map_mul_scalar_forall_coe_eq_sum_map_tmul_of_linearIndependent
import Theorems.Thm_AutomorphicForm_linearIndependent_mulVec_and_span_eq_top_of_forall_isUnit_of_card_eq_four
import Theorems.Thm_AutomorphicForm_exists_mul_map_eq_scalar_and_forall_isUnit_of_normString_eq_toTensorGL_centralScalar_of_forall_ne_scalar
import Theorems.Thm_MvPolynomial_measure_setOf_eval_eq_zero_of_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_twistedCentralizer_coe_eq_sum_map_tmul_and_tensorPlace_eq_one_of_forall_exists

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory Filter NumberField NumberField.AdelicBox IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions Topology Classical

noncomputable section

namespace Ws25L3

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

end TopologyPart

end Mu1
p2m_reactivate "P2MW.S_AutomorphicForm_exists_twistedCentralizer_coe_eq_sum_map_tmul_and_tensorPlace_eq_one_of_forall_exists.Ws25L3.Mu1"

section Split

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {ι : Type} [Fintype ι] (b : ι → Matrix (Fin 2) (Fin 2) L) (v : Fin 2 → L)

attribute [local instance] Mu1.algAL

theorem AL_snd_sum {α : Type} (s : Finset α) (f : α → AdeleRing (𝓞 L) L) :
    (∑ i ∈ s, f i).2 = ∑ i ∈ s, (f i).2 :=
  map_sum (RingHom.snd (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)) f s

theorem AL_fst_sum {α : Type} (s : Finset α) (f : α → AdeleRing (𝓞 L) L) :
    (∑ i ∈ s, f i).1 = ∑ i ∈ s, (f i).1 :=
  map_sum (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)) f s

theorem Xi_snd_eq (a a' : ι → AdeleRing (𝓞 K) K) (h : ∀ k, (a k).2 = (a' k).2) (j : Fin 2) :
    (Mu1.Xi K L b v a j).2 = (Mu1.Xi K L b v a' j).2 := by
  rw [Mu1.Xi_apply, Mu1.Xi_apply, AL_snd_sum, AL_snd_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Mu1.smul_def', Mu1.smul_def']
  show (M4aHerbrand.Bridge.genuineβ K L (a i)).2 * _ = (M4aHerbrand.Bridge.genuineβ K L (a' i)).2 * _
  rw [M4aHerbrand.Bridge.genuineβ_snd, M4aHerbrand.Bridge.genuineβ_snd, h i]

theorem Xi_fst_eq (a a' : ι → AdeleRing (𝓞 K) K) (h : ∀ k, (a k).1 = (a' k).1) (j : Fin 2) :
    (Mu1.Xi K L b v a j).1 = (Mu1.Xi K L b v a' j).1 := by
  rw [Mu1.Xi_apply, Mu1.Xi_apply, AL_fst_sum, AL_fst_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Mu1.smul_def', Mu1.smul_def']
  show (M4aHerbrand.Bridge.genuineβ K L (a i)).1 * _ = (M4aHerbrand.Bridge.genuineβ K L (a' i)).1 * _
  rw [M4aHerbrand.Bridge.genuineβ_fst, M4aHerbrand.Bridge.genuineβ_fst, h i]

def finAdele (y : ι → FiniteAdeleRing (𝓞 K) K) : ι → AdeleRing (𝓞 K) K := fun k => ((0 : InfiniteAdeleRing K), y k)

def Xif (y : ι → FiniteAdeleRing (𝓞 K) K) : Fin 2 → FiniteAdeleRing (𝓞 L) L :=
  fun j => (Mu1.Xi K L b v (finAdele K y) j).2

theorem Xi_snd (a : ι → AdeleRing (𝓞 K) K) (j : Fin 2) :
    (Mu1.Xi K L b v a j).2 = Xif K L b v (fun k => (a k).2) j :=
  Xi_snd_eq K L b v a (finAdele K fun k => (a k).2) (fun _ => rfl) j

theorem Xi_zero : Mu1.Xi K L b v 0 = 0 := by
  funext j; rw [Mu1.Xi_apply]; simp

theorem Xi_finAdele_fst (y : ι → FiniteAdeleRing (𝓞 K) K) (j : Fin 2) :
    (Mu1.Xi K L b v (finAdele K y) j).1 = 0 := by
  rw [Xi_fst_eq K L b v (finAdele K y) 0 (fun _ => rfl) j, Xi_zero]; rfl

theorem continuous_finAdele : Continuous (finAdele K (ι := ι)) :=
  continuous_pi fun k => (continuous_const.prodMk (continuous_apply k))

variable (hli : LinearIndependent K fun i => (b i).mulVec v)
  (hsp : Submodule.span K (Set.range fun i => (b i).mulVec v) = ⊤)

include hli hsp in
theorem continuous_Xi : Continuous (Mu1.Xi K L b v : (ι → AdeleRing (𝓞 K) K) → Fin 2 → AdeleRing (𝓞 L) L) := by
  rw [← Mu1.coe_XiCAE K L b v hli hsp]; exact (Mu1.XiCAE K L b v hli hsp).continuous

include hli hsp in
theorem continuous_Xif : Continuous (Xif K L b v : (ι → FiniteAdeleRing (𝓞 K) K) → Fin 2 → FiniteAdeleRing (𝓞 L) L) :=
  continuous_pi fun j => continuous_snd.comp ((continuous_apply j).comp
    ((continuous_Xi K L b v hli hsp).comp (continuous_finAdele K)))

include hli hsp in

theorem isCompact_preimage_Xif {U : Set (Fin 2 → FiniteAdeleRing (𝓞 L) L)} (hU : IsCompact U) :
    IsCompact ((Xif K L b v) ⁻¹' U) := by
  set U' : Set (Fin 2 → AdeleRing (𝓞 L) L) := (fun u : Fin 2 → FiniteAdeleRing (𝓞 L) L =>
    fun j => ((0 : InfiniteAdeleRing L), u j)) '' U with hU'
  have hU'c : IsCompact U' := hU.image (continuous_pi fun j => continuous_const.prodMk (continuous_apply j))
  have h1 : IsCompact ((Mu1.XiCAE K L b v hli hsp) ⁻¹' U') :=
    (Mu1.XiCAE K L b v hli hsp).toHomeomorph.isCompact_preimage.mpr hU'c
  have h2 : (Xif K L b v) ⁻¹' U = (fun a : ι → AdeleRing (𝓞 K) K => fun k => (a k).2) ''
      ((Mu1.XiCAE K L b v hli hsp) ⁻¹' U') := by
    ext y
    constructor
    · intro hy
      refine ⟨finAdele K y, ?_, rfl⟩
      show Mu1.XiCAE K L b v hli hsp (finAdele K y) ∈ U'
      rw [Mu1.XiCAE_apply]
      refine ⟨Xif K L b v y, hy, ?_⟩
      funext j
      exact Prod.ext (Xi_finAdele_fst K L b v y j).symm rfl
    · rintro ⟨a, ha, rfl⟩
      have ha' : Mu1.Xi K L b v a ∈ U' := by rw [← Mu1.XiCAE_apply K L b v hli hsp]; exact ha
      obtain ⟨u, hu, hua⟩ := ha'
      show Xif K L b v (fun k => (a k).2) ∈ U
      have : Xif K L b v (fun k => (a k).2) = u := by
        funext j; rw [← Xi_snd, ← hua]
      rwa [this]
  rw [h2]
  exact h1.image (continuous_pi fun k => continuous_snd.comp (continuous_apply k))

end Split
p2m_reactivate "P2MW.S_AutomorphicForm_exists_twistedCentralizer_coe_eq_sum_map_tmul_and_tensorPlace_eq_one_of_forall_exists.Ws25L3.Mu1"

section FinAdele

open scoped RestrictedProduct

variable (K : Type) [Field K] [NumberField K]

scoped instance countableIdeal_l3 (R : Type) [CommRing R] [Countable R] [IsNoetherianRing R] : Countable (Ideal R) := by
  have hsurj : Function.Surjective (fun s : Finset R => Ideal.span (s : Set R)) := by
    intro I
    obtain ⟨s, hs⟩ := IsNoetherian.noetherian I
    exact ⟨s, hs⟩
  exact hsurj.countable

scoped instance countableHeightOneSpectrum_l3 (R : Type) [CommRing R] [IsDedekindDomain R] [Countable R] :
    Countable (HeightOneSpectrum R) := by
  have hinj : Function.Injective (fun v : HeightOneSpectrum R => v.asIdeal) := fun v w h => HeightOneSpectrum.ext h
  exact hinj.countable

scoped instance countableRingOfIntegers_l3 : Countable (𝓞 K) :=
  Function.Injective.countable (RingOfIntegers.coe_injective (K := K))

scoped instance secondCountable_finiteAdeleRing_l3 : SecondCountableTopology (FiniteAdeleRing (𝓞 K) K) := by
  haveI : SecondCountableTopology
      (Πʳ v : HeightOneSpectrum (𝓞 K), [v.adicCompletion K, v.adicCompletionIntegers K]) :=
    RestrictedProduct.secondCountableTopology fun v => Valued.isOpen_valuationSubring _
  exact inferInstanceAs <| SecondCountableTopology <|
    Πʳ v : HeightOneSpectrum (𝓞 K), [v.adicCompletion K, v.adicCompletionIntegers K]

scoped instance secondCountable_infiniteAdeleRing_l3 : SecondCountableTopology (InfiniteAdeleRing K) := by
  haveI : ∀ v : NumberField.InfinitePlace K, SecondCountableTopology v.Completion := by
    intro v
    haveI : Countable (WithAbs v.1) := (WithAbs.equiv v.1).toEquiv.injective.countable
    exact UniformSpace.secondCountable_of_separable _
  exact inferInstanceAs <| SecondCountableTopology <| (v : NumberField.InfinitePlace K) → v.Completion

theorem not_discreteTopology_adicCompletion (v : HeightOneSpectrum (𝓞 K)) :
    ¬ DiscreteTopology (v.adicCompletion K) := by
  intro hd
  have hc : IsCompact ((v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    isCompact_iff_compactSpace.2 (NumberField.AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 K) K v)
  have hfin : ((v.adicCompletionIntegers K : Set (v.adicCompletion K))).Finite := hc.finite_of_discrete
  have hinj : Function.Injective (fun r : 𝓞 K => algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K r)) :=
    (algebraMap K (v.adicCompletion K)).injective.comp (IsFractionRing.injective (𝓞 K) K)
  have hinf : ((v.adicCompletionIntegers K : Set (v.adicCompletion K))).Infinite :=
    Set.infinite_of_injective_forall_mem hinj
      (fun r => NumberField.AdelicBox.algebraMap_mem_adicCompletionIntegers (𝓞 K) K v r)
  exact hinf hfin

variable {ι : Type} [Fintype ι]

def HS (S : Finset (HeightOneSpectrum (𝓞 K))) : Set (ι → FiniteAdeleRing (𝓞 K) K) :=
  {y : ι → FiniteAdeleRing (𝓞 K) K | ∀ k, ∀ v ∉ S, (y k) v ∈ v.adicCompletionIntegers K}

omit [Fintype ι] in
theorem HS_mono {S T : Finset (HeightOneSpectrum (𝓞 K))} (h : S ⊆ T) : HS K (ι := ι) S ⊆ HS K T :=
  fun _ hy k v hv => hy k v (fun hvS => hv (h hvS))

theorem isOpen_integralOutside (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IsOpen {x : FiniteAdeleRing (𝓞 K) K | ∀ v ∉ S, x v ∈ v.adicCompletionIntegers K} :=
  RestrictedProduct.isOpen_forall_imp_mem (R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (A := fun v : HeightOneSpectrum (𝓞 K) => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    (fun v => Valued.isOpen_valuationSubring _) (p := fun v => v ∉ S)

theorem isOpen_HS (S : Finset (HeightOneSpectrum (𝓞 K))) : IsOpen (HS K (ι := ι) S) := by
  have h : HS K (ι := ι) S = ⋂ k, (fun y : ι → FiniteAdeleRing (𝓞 K) K => y k) ⁻¹'
      {x : FiniteAdeleRing (𝓞 K) K | ∀ v ∉ S, x v ∈ v.adicCompletionIntegers K} := by
    ext y; simp [HS]
  rw [h]
  exact isOpen_iInter_of_finite fun k => (isOpen_integralOutside K S).preimage (continuous_apply k)

theorem exists_finset_subset_HS {C : Set (ι → FiniteAdeleRing (𝓞 K) K)} (hC : IsCompact C) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), C ⊆ HS K S := by
  refine hC.elim_directed_cover (fun S : Finset (HeightOneSpectrum (𝓞 K)) => HS K (ι := ι) S)
    (fun S => isOpen_HS K S) ?_ ?_
  · intro y _
    have hk : ∀ k, ∀ᶠ v in cofinite, (y k) v ∈ v.adicCompletionIntegers K := fun k => (y k).2
    have hall : ∀ᶠ v in cofinite, ∀ k, (y k) v ∈ v.adicCompletionIntegers K := Filter.eventually_all.2 hk
    have hfin : {v : HeightOneSpectrum (𝓞 K) | ¬ ∀ k, (y k) v ∈ v.adicCompletionIntegers K}.Finite :=
      Filter.eventually_cofinite.1 hall
    refine Set.mem_iUnion.2 ⟨hfin.toFinset, fun k v hv => ?_⟩
    by_contra h
    exact hv (hfin.mem_toFinset.2 fun hall' => h (hall' k))
  · intro S T
    exact ⟨S ∪ T, HS_mono K Finset.subset_union_left, HS_mono K Finset.subset_union_right⟩

theorem exists_finset_forall_mem_of_mem_nhds_zero {V : Set (ι → FiniteAdeleRing (𝓞 K) K)}
    (hV : V ∈ 𝓝 (0 : ι → FiniteAdeleRing (𝓞 K) K)) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)), ∀ z : ι → FiniteAdeleRing (𝓞 K) K,
      (∀ k, (∀ v ∈ T, (z k) v = 0) ∧ ∀ v, (z k) v ∈ v.adicCompletionIntegers K) → z ∈ V := by
  classical
  rw [nhds_pi] at hV
  obtain ⟨I, -, t, ht, hsub⟩ := Filter.mem_pi.1 hV

  let R : HeightOneSpectrum (𝓞 K) → Type := fun v => v.adicCompletion K
  let A : ∀ v : HeightOneSpectrum (𝓞 K), Set (R v) := fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))
  have hopen : ∀ v, IsOpen (A v) := fun v => Valued.isOpen_valuationSubring _
  let x₀ : ∀ v, A v := fun v => ⟨(0 : v.adicCompletion K), (v.adicCompletionIntegers K).zero_mem⟩
  have h0 : (0 : FiniteAdeleRing (𝓞 K) K) = RestrictedProduct.structureMap R A cofinite x₀ :=
    FiniteAdeleRing.ext K fun v => rfl
  have hnhds : ∀ k, ∃ J : Set (HeightOneSpectrum (𝓞 K)), J.Finite ∧
      ∀ o : ∀ v, A v, (∀ v ∈ J, (o v : R v) = 0) → RestrictedProduct.structureMap R A cofinite o ∈ t k := by
    intro k
    have htk : t k ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 K) K) := ht k
    rw [h0] at htk
    erw [RestrictedProduct.nhds_eq_map_structureMap (R := R) (A := A) hopen x₀] at htk
    have htk' : (RestrictedProduct.structureMap R A cofinite) ⁻¹' (t k) ∈ 𝓝 x₀ := htk
    rw [nhds_pi] at htk'
    obtain ⟨J, hJ, s, hs, hJsub⟩ := Filter.mem_pi.1 htk'
    refine ⟨J, hJ, fun o ho => hJsub fun v hv => ?_⟩
    have : o v = x₀ v := Subtype.ext (ho v hv)
    rw [this]
    exact mem_of_mem_nhds (hs v)
  choose J hJ hJt using hnhds
  refine ⟨(Set.finite_iUnion hJ).toFinset, fun z hz => hsub fun k _ => ?_⟩
  have hz' : z k = RestrictedProduct.structureMap R A cofinite (fun v => ⟨(z k) v, (hz k).2 v⟩) :=
    FiniteAdeleRing.ext K fun v => rfl
  rw [hz']
  exact hJt k _ fun v hv => (hz k).1 v ((Set.finite_iUnion hJ).mem_toFinset.2 (Set.mem_iUnion.2 ⟨k, hv⟩))

def liftS (S : Finset (HeightOneSpectrum (𝓞 K))) (β : ι → K)
    (x : ∀ v : ↥S, ι → v.1.adicCompletion K) : ι → FiniteAdeleRing (𝓞 K) K := fun k =>
  ⟨fun v => if h : v ∈ S then x ⟨v, h⟩ k else algebraMap K (FiniteAdeleRing (𝓞 K) K) (β k) v, by
    filter_upwards [(algebraMap K (FiniteAdeleRing (𝓞 K) K) (β k)).2, S.finite_toSet.compl_mem_cofinite]
      with v hv hvS
    have hvS' : v ∉ S := fun h => hvS (Finset.mem_coe.mpr h)
    rw [dif_neg hvS']
    exact hv⟩

theorem liftS_apply_of_mem (S : Finset (HeightOneSpectrum (𝓞 K))) (β : ι → K)
    (x : ∀ v : ↥S, ι → v.1.adicCompletion K) (k : ι) (v : ↥S) :
    (liftS K S β x k) v.1 = x v k := by
  show (if h : v.1 ∈ S then x ⟨v.1, h⟩ k else algebraMap K (FiniteAdeleRing (𝓞 K) K) (β k) v.1) = x v k
  rw [dif_pos v.2]

theorem liftS_apply_of_not_mem (S : Finset (HeightOneSpectrum (𝓞 K))) (β : ι → K)
    (x : ∀ v : ↥S, ι → v.1.adicCompletion K) (k : ι) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) :
    (liftS K S β x k) v = algebraMap K (FiniteAdeleRing (𝓞 K) K) (β k) v := by
  show (if h : v ∈ S then x ⟨v, h⟩ k else algebraMap K (FiniteAdeleRing (𝓞 K) K) (β k) v) = _
  rw [dif_neg hv]

theorem proj_liftS (S : Finset (HeightOneSpectrum (𝓞 K))) (β : ι → K)
    (x : ∀ v : ↥S, ι → v.1.adicCompletion K) :
    (fun (y : ι → FiniteAdeleRing (𝓞 K) K) (v : ↥S) (k : ι) => (y k) v.1) (liftS K S β x) = x := by
  funext v k; exact liftS_apply_of_mem K S β x k v

theorem liftS_mem_HS (S : Finset (HeightOneSpectrum (𝓞 K))) (β : ι → K)
    (hβ : ∀ k, ∀ v ∉ S, algebraMap K (FiniteAdeleRing (𝓞 K) K) (β k) v ∈ v.adicCompletionIntegers K)
    (x : ∀ v : ↥S, ι → v.1.adicCompletion K) : liftS K S β x ∈ HS K S := by
  intro k v hv
  rw [liftS_apply_of_not_mem K S β x k hv]
  exact hβ k v hv

end FinAdele
p2m_reactivate "P2MW.S_AutomorphicForm_exists_twistedCentralizer_coe_eq_sum_map_tmul_and_tensorPlace_eq_one_of_forall_exists.Ws25L3.Mu1"

section AdelicPoint

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {ι : Type} [Fintype ι] (b : ι → Matrix (Fin 2) (Fin 2) L)

def Amat (R : Type) [CommRing R] [Algebra K R] (a : ι → R) : Matrix (Fin 2) (Fin 2) (L ⊗[K] R) :=
  ∑ k, (b k).map fun l : L => l ⊗ₜ[K] a k

omit [NumberField K] [NumberField L] in
theorem Amat_map {R R' : Type} [CommRing R] [Algebra K R] [CommRing R'] [Algebra K R']
    (φ : L ⊗[K] R →ₐ[K] L ⊗[K] R') (ψ : R → R') (hφ : ∀ (l : L) (r : R), φ (l ⊗ₜ[K] r) = l ⊗ₜ[K] ψ r)
    (a : ι → R) : (Amat K L b R a).map φ = Amat K L b R' (fun k => ψ (a k)) := by
  ext i j
  simp only [Amat, Matrix.map_apply, Matrix.sum_apply, map_sum, hφ]

omit [NumberField K] [NumberField L] in
theorem Amat_algebraMap_eq_one {R : Type} [CommRing R] [Algebra K R] (β : ι → K) (hβ : ∑ k, β k • b k = 1)
    (a : ι → R) (ha : ∀ k, a k = algebraMap K R (β k)) : Amat K L b R a = 1 := by
  have h : Amat K L b R a = (∑ k, β k • b k).map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] R) := by
    unfold Amat
    rw [← RingHom.mapMatrix_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [RingHom.mapMatrix_apply]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, ha k]
    show b k i j ⊗ₜ[K] algebraMap K R (β k) = (β k • b k i j) ⊗ₜ[K] (1 : R)
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  rw [h, hβ]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem matrix_eq_of_map_tensorArchHom_eq_of_forall_map_tensorPlaceHom_eq
    {M N : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)}
    (h₁ : M.map (AutomorphicForm.tensorArchHom K L) = N.map (AutomorphicForm.tensorArchHom K L))
    (h₂ : ∀ w : HeightOneSpectrum (𝓞 K),
      M.map (AutomorphicForm.tensorPlaceHom K L w) = N.map (AutomorphicForm.tensorPlaceHom K L w)) :
    M = N := by
  ext i j
  apply (AutomorphicForm.baseChangeEquiv K L).injective
  refine Prod.ext ?_ ?_
  · rw [AutomorphicForm.fst_baseChangeEquiv, AutomorphicForm.fst_baseChangeEquiv]
    exact congrArg _ (congrFun (congrFun h₁ i) j)
  · have key := AutomorphicForm.matrix_eq_of_forall_semiLocalEval_mapMatrix_eq K L
      (M := fun i j => (AutomorphicForm.baseChangeEquiv K L (M i j)).2)
      (N := fun i j => (AutomorphicForm.baseChangeEquiv K L (N i j)).2) (fun w => ?_)
    · exact congrFun (congrFun key i) j
    · ext i' j'
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
      rw [AutomorphicForm.semiLocalEval_snd_baseChangeEquiv, AutomorphicForm.semiLocalEval_snd_baseChangeEquiv]
      exact congrFun (congrFun (h₂ w) i') j'

variable (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)

local notation "δA" => (Matrix.GeneralLinearGroup.map
  (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
    Matrix.GeneralLinearGroup.scalar (Fin 2) c)

def cAt (w : HeightOneSpectrum (𝓞 K)) : (L ⊗[K] w.adicCompletion K)ˣ :=
  Units.map (AutomorphicForm.tensorPlaceHom K L w).toRingHom.toMonoidHom c

omit [NumberField L] in
theorem tensorPlace_map_includeLeft (w : HeightOneSpectrum (𝓞 K)) :
    AutomorphicForm.tensorPlace K L w (Matrix.GeneralLinearGroup.map
        (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀) =
      Matrix.GeneralLinearGroup.map
        (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] w.adicCompletion K) δ₀ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [AutomorphicForm.tensorPlace_apply]
  show AutomorphicForm.tensorPlaceHom K L w ((δ₀ : Matrix (Fin 2) (Fin 2) L) i j ⊗ₜ[K] (1 : AdeleRing (𝓞 K) K)) =
    (δ₀ : Matrix (Fin 2) (Fin 2) L) i j ⊗ₜ[K] (1 : w.adicCompletion K)
  rw [AutomorphicForm.tensorPlaceHom_tmul]
  rfl

omit [NumberField L] in
theorem tensorPlace_scalar (w : HeightOneSpectrum (𝓞 K)) :
    AutomorphicForm.tensorPlace K L w (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (cAt K L c w) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [AutomorphicForm.tensorPlace_apply]
  show AutomorphicForm.tensorPlaceHom K L w (Matrix.scalar (Fin 2) (c : L ⊗[K] AdeleRing (𝓞 K) K) i j) =
    Matrix.scalar (Fin 2) ((cAt K L c w : (L ⊗[K] w.adicCompletion K)ˣ) : L ⊗[K] w.adicCompletion K) i j
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs
  · rfl
  · exact map_zero _

theorem tensorPlace_delta (w : HeightOneSpectrum (𝓞 K)) :
    AutomorphicForm.tensorPlace K L w δA =
      Matrix.GeneralLinearGroup.map
        (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] w.adicCompletion K) δ₀ *
      Matrix.GeneralLinearGroup.scalar (Fin 2) (cAt K L c w) := by
  rw [map_mul, tensorPlace_map_includeLeft, tensorPlace_scalar]

variable (hb : LinearIndependent K b)
  (hbspan : ∀ X : Matrix (Fin 2) (Fin 2) L,
    X * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * X.map σ ↔
      X ∈ Submodule.span K (Set.range b))

include hb hbspan in

theorem exists_homeomorph_local [FiniteDimensional K L] (w : HeightOneSpectrum (𝓞 K)) :
    ∃ e : (ι → w.adicCompletion K) ≃ₜ ↥(AutomorphicForm.twistedCommutant K L (w.adicCompletion K) σ
        (AutomorphicForm.tensorPlace K L w δA)),
      ∀ a : ι → w.adicCompletion K,
        ((e a : AutomorphicForm.twistedCommutant K L (w.adicCompletion K) σ
            (AutomorphicForm.tensorPlace K L w δA)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)) =
          Amat K L b (w.adicCompletion K) a := by
  rw [tensorPlace_delta]
  exact AutomorphicForm.exists_homeomorph_twistedCommutant_map_mul_scalar_forall_coe_eq_sum_map_tmul_of_linearIndependent
    K L (w.adicCompletion K) σ δ₀ (cAt K L c w) ι b hb hbspan

include hb hbspan in
theorem exists_homeomorph_adelic [FiniteDimensional K L] :
    ∃ e : (ι → AdeleRing (𝓞 K) K) ≃ₜ ↥(AutomorphicForm.twistedCommutant K L (AdeleRing (𝓞 K) K) σ δA),
      ∀ a : ι → AdeleRing (𝓞 K) K,
        ((e a : AutomorphicForm.twistedCommutant K L (AdeleRing (𝓞 K) K) σ δA) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) = Amat K L b (AdeleRing (𝓞 K) K) a :=
  AutomorphicForm.exists_homeomorph_twistedCommutant_map_mul_scalar_forall_coe_eq_sum_map_tmul_of_linearIndependent
    K L (AdeleRing (𝓞 K) K) σ δ₀ c ι b hb hbspan

end AdelicPoint
p2m_reactivate "P2MW.S_AutomorphicForm_exists_twistedCentralizer_coe_eq_sum_map_tmul_and_tensorPlace_eq_one_of_forall_exists.Ws25L3.Mu1"

section GlobalPoint

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem globalPoint
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)
    (ι : Type) [Fintype ι] [DecidableEq ι] (b : ι → Matrix (Fin 2) (Fin 2) L) (hb : LinearIndependent K b)
    (hbspan : ∀ X : Matrix (Fin 2) (Fin 2) L,
      X * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * X.map σ ↔
        X ∈ Submodule.span K (Set.range b))
    (β : ι → K) (hβ : ∑ k, β k • b k = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (a : ι → AdeleRing (𝓞 K) K)
    (harch : ∀ k, (a k).1 = algebraMap K (InfiniteAdeleRing K) (β k))
    (hS : ∀ w ∈ S, ∃ t : ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L w (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))),
          ((t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)) =
            ∑ k, (b k).map fun l : L => l ⊗ₜ[K] (a k).2 w)
    (hoff : ∀ k, ∀ w ∉ S, (a k).2 w = algebraMap K (w.adicCompletion K) (β k)) :
    ∃ t : ↥(AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
          (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)),
      ((t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) =
          (∑ k, (b k).map fun l : L => l ⊗ₜ[K] a k) ∧
      ∀ w ∉ S, AutomorphicForm.tensorPlace K L w (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) = 1 := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2

  have he := fun w : HeightOneSpectrum (𝓞 K) => exists_homeomorph_local K L b σ δ₀ c hb hbspan w
  choose e he using he
  have hinv : ∀ w : HeightOneSpectrum (𝓞 K), ∃ x' : ι → w.adicCompletion K,
      (w ∈ S → Amat K L b (w.adicCompletion K) (fun k => (a k).2 w) * Amat K L b (w.adicCompletion K) x' = 1 ∧
        Amat K L b (w.adicCompletion K) x' * Amat K L b (w.adicCompletion K) (fun k => (a k).2 w) = 1) ∧
      (w ∉ S → x' = fun k => algebraMap K (w.adicCompletion K) (β k)) := by
    intro w
    by_cases hw : w ∈ S
    · obtain ⟨t, ht⟩ := hS w hw
      have hmem : (((t⁻¹ : ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ _)) :
          GL (Fin 2) (L ⊗[K] w.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)) ∈
          AutomorphicForm.twistedCommutant K L (w.adicCompletion K) σ
            (AutomorphicForm.tensorPlace K L w (Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
                Matrix.GeneralLinearGroup.scalar (Fin 2) c)) :=
        (AutomorphicForm.mem_twistedCentralizer_iff_coe_mem_twistedCommutant _ _).1 (t⁻¹).2
      refine ⟨(e w).symm ⟨_, hmem⟩, fun _ => ?_, fun h => (h hw).elim⟩
      have hA : Amat K L b (w.adicCompletion K) ((e w).symm ⟨_, hmem⟩) =
          (((t⁻¹ : ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ _)) :
            GL (Fin 2) (L ⊗[K] w.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)) := by
        rw [← he w, Homeomorph.apply_symm_apply]
      have ht' : Amat K L b (w.adicCompletion K) (fun k => (a k).2 w) =
          ((t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)) :=
        ht.symm
      rw [hA, ht', Subgroup.coe_inv, Units.mul_inv, Units.inv_mul]
      exact ⟨rfl, rfl⟩
    · exact ⟨fun k => algebraMap K (w.adicCompletion K) (β k), fun h => (hw h).elim, fun _ => rfl⟩
  choose x' hx'S hx'off using hinv

  let a' : ι → AdeleRing (𝓞 K) K := fun k =>
    (algebraMap K (InfiniteAdeleRing K) (β k),
      ⟨fun w => x' w k, by
        filter_upwards [(algebraMap K (FiniteAdeleRing (𝓞 K) K) (β k)).2, S.finite_toSet.compl_mem_cofinite]
          with w hw hwS
        have hwS' : w ∉ S := fun h => hwS (Finset.mem_coe.mpr h)
        rw [hx'off w hwS']
        exact hw⟩)
  have ha'2 : ∀ k w, (a' k).2 w = x' w k := fun _ _ => rfl

  have hplace : ∀ w : HeightOneSpectrum (𝓞 K), ∀ d : ι → AdeleRing (𝓞 K) K,
      (Amat K L b _ d).map (AutomorphicForm.tensorPlaceHom K L w) = Amat K L b _ (fun k => (d k).2 w) :=
    fun w d => Amat_map K L b (AutomorphicForm.tensorPlaceHom K L w)
      (fun r : AdeleRing (𝓞 K) K => r.2 w) (fun l r => rfl) d
  have harch' : ∀ d : ι → AdeleRing (𝓞 K) K, (∀ k, (d k).1 = algebraMap K (InfiniteAdeleRing K) (β k)) →
      (Amat K L b _ d).map (AutomorphicForm.tensorArchHom K L) = 1 := by
    intro d hd
    rw [Amat_map K L b (AutomorphicForm.tensorArchHom K L) (fun r : AdeleRing (𝓞 K) K => r.1)
      (fun l r => rfl) d]
    exact Amat_algebraMap_eq_one K L b β hβ _ hd
  have hoffA : ∀ w ∉ S, Amat K L b _ (fun k => (a k).2 w) = 1 := fun w hw =>
    Amat_algebraMap_eq_one K L b β hβ _ (fun k => hoff k w hw)
  have hoffA' : ∀ w ∉ S, Amat K L b _ (fun k => (a' k).2 w) = 1 := fun w hw =>
    Amat_algebraMap_eq_one K L b β hβ _ (fun k => by rw [ha'2, hx'off w hw])

  have hmul : Amat K L b _ a * Amat K L b _ a' = 1 := by
    apply matrix_eq_of_map_tensorArchHom_eq_of_forall_map_tensorPlaceHom_eq K L
    · rw [Matrix.map_mul, harch' a harch, harch' a' (fun k => rfl), Matrix.map_one _ (map_zero _) (map_one _), one_mul]
    · intro w
      rw [Matrix.map_mul, hplace, hplace, Matrix.map_one _ (map_zero _) (map_one _)]
      by_cases hw : w ∈ S
      · have := (hx'S w hw).1
        simpa only [ha'2] using this
      · rw [hoffA w hw, hoffA' w hw, one_mul]
  have hmul' : Amat K L b _ a' * Amat K L b _ a = 1 := by
    apply matrix_eq_of_map_tensorArchHom_eq_of_forall_map_tensorPlaceHom_eq K L
    · rw [Matrix.map_mul, harch' a harch, harch' a' (fun k => rfl), Matrix.map_one _ (map_zero _) (map_one _), one_mul]
    · intro w
      rw [Matrix.map_mul, hplace, hplace, Matrix.map_one _ (map_zero _) (map_one _)]
      by_cases hw : w ∈ S
      · have := (hx'S w hw).2
        simpa only [ha'2] using this
      · rw [hoffA w hw, hoffA' w hw, one_mul]
  let tA : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) := ⟨Amat K L b _ a, Amat K L b _ a', hmul, hmul'⟩
  have htA : tA ∈ AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
      (Matrix.GeneralLinearGroup.map
        (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
        Matrix.GeneralLinearGroup.scalar (Fin 2) c) := by
    rw [AutomorphicForm.mem_twistedCentralizer_iff_coe_mem_twistedCommutant]
    obtain ⟨eA, heA⟩ := exists_homeomorph_adelic K L b σ δ₀ c hb hbspan
    show Amat K L b _ a ∈ _
    rw [← heA a]
    exact (eA a).2
  refine ⟨⟨tA, htA⟩, rfl, fun w hw => ?_⟩
  apply Units.ext
  show (Amat K L b _ a).map (AutomorphicForm.tensorPlaceHom K L w) = (1 : Matrix (Fin 2) (Fin 2) _)
  rw [hplace, hoffA w hw]

end GlobalPoint
p2m_reactivate "P2MW.S_AutomorphicForm_exists_twistedCentralizer_coe_eq_sum_map_tmul_and_tensorPlace_eq_one_of_forall_exists.Ws25L3.Mu1"

end Ws25L3
p2m_reactivate "P2MW.S_AutomorphicForm_exists_twistedCentralizer_coe_eq_sum_map_tmul_and_tensorPlace_eq_one_of_forall_exists.Ws25L3.Mu1 P2MW.S_AutomorphicForm_exists_twistedCentralizer_coe_eq_sum_map_tmul_and_tensorPlace_eq_one_of_forall_exists.Ws25L3"

open AutomorphicForm in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)
    (ι : Type) [Fintype ι] [DecidableEq ι] (b : ι → Matrix (Fin 2) (Fin 2) L) (hb : LinearIndependent K b)
    (hbspan : ∀ X : Matrix (Fin 2) (Fin 2) L,
      X * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * X.map σ ↔
        X ∈ Submodule.span K (Set.range b))
    (β : ι → K) (hβ : ∑ k, β k • b k = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (a : ι → AdeleRing (𝓞 K) K)
    (harch : ∀ k, (a k).1 = algebraMap K (InfiniteAdeleRing K) (β k))
    (hS : ∀ w ∈ S, ∃ t : ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L w (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))),
          ((t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)) =
            ∑ k, (b k).map fun l : L => l ⊗ₜ[K] (a k).2 w)
    (hoff : ∀ k, ∀ w ∉ S, (a k).2 w = algebraMap K (w.adicCompletion K) (β k)) :
    ∃ t : ↥(AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
          (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)),
      ((t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) =
          (∑ k, (b k).map fun l : L => l ⊗ₜ[K] a k) ∧
      ∀ w ∉ S, AutomorphicForm.tensorPlace K L w (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) = 1 :=
  Ws25L3.globalPoint K L h2 σ δ₀ c ι b hb hbspan β hβ S a harch hS hoff

#print axioms solution

end
end S_AutomorphicForm_exists_twistedCentralizer_coe_eq_sum_map_tmul_and_tensorPlace_eq_one_of_forall_exists
end P2MW
export P2MW.S_AutomorphicForm_exists_twistedCentralizer_coe_eq_sum_map_tmul_and_tensorPlace_eq_one_of_forall_exists (solution)
