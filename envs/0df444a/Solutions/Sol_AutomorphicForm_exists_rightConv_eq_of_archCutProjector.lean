-- Prove2me | solution 1 for AutomorphicForm.exists_rightConv_eq_of_archCutProjector
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/1a8202ed-9cd0-54c3-b597-afcf0ab10e08

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Theorems.Thm_AutomorphicForm_continuous_rightConv_of_continuous_of_hasCompactSupport
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_Representation_exists_isCompl_forall_mem_of_compactSpace_of_continuous
import Theorems.Thm_AutomorphicForm_exists_mem_span_rightTranslate_mem_archDualCutSubmodule_and_rightConv_eq
import Theorems.Thm_AutomorphicForm_le_iSup_typeSubmodule_of_surjective_of_le_iSup_typeSubmodule
import Theorems.Thm_AutomorphicForm_isFactorizableTestFn_sum_mul_comp_mul_mul
import Theorems.Thm_AutomorphicForm_finiteDimensional_span_rightTranslate_of_mem_archCutSubmodule
import Theorems.Thm_AutomorphicForm_finiteDimensional_span_rightTranslate_of_mem_archDualCutSubmodule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_AutomorphicForm_exists_rightConv_eq_of_archCutProjector
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel
open AutomorphicForm.CuspidalConstituent
open scoped Pointwise BigOperators

noncomputable section

namespace F4CutWords

theorem isCompact_rowIsometrySubgroup₀ (K : Type*) [Field K] [NumberField K] (w : InfinitePlace K) :
    IsCompact (rowIsometrySubgroup₀ w.Completion : Set (GL (Fin 2) w.Completion)) := by
  set C : Set (Matrix (Fin 2) (Fin 2) w.Completion) := {m | ∀ i j, ‖m i j‖ ≤ 1} with hC_def
  have hC : IsCompact C := by
    have hpi : C = Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 =>
        {x : w.Completion | ‖x‖ ≤ 1} := by
      ext m
      exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
    rw [hpi]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_setOf_norm_le_one_completion K w
  have hK : IsCompact ((Units.embedProduct (Matrix (Fin 2) (Fin 2) w.Completion)) ⁻¹'
      (C ×ˢ (MulOpposite.op '' C))) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage (hC.prod (hC.image MulOpposite.continuous_op))
  have hset : (rowIsometrySubgroup₀ w.Completion : Set (GL (Fin 2) w.Completion)) =
      {k : GL (Fin 2) w.Completion | ((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det = 1} ∩
        {k : GL (Fin 2) w.Completion | IsRowIsometry k} := by
    ext k
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_setOf_eq]
    show k ∈ (Matrix.GeneralLinearGroup.det : GL (Fin 2) w.Completion →* _).ker ⊓ rowIsometrySubgroup w.Completion ↔ _
    rw [Subgroup.mem_inf, MonoidHom.mem_ker, mem_rowIsometrySubgroup_iff, ← Units.val_eq_one,
      Matrix.GeneralLinearGroup.val_det_apply]
  have hclosed : IsClosed (rowIsometrySubgroup₀ w.Completion : Set (GL (Fin 2) w.Completion)) := by
    rw [hset]
    refine IsClosed.inter ?_ (isClosed_setOf_isRowIsometry w.Completion)
    exact isClosed_eq ((continuous_id.matrix_det).comp Units.continuous_val) continuous_const
  refine hK.of_isClosed_subset hclosed ?_
  intro k hk
  have hk' : IsRowIsometry k := by rw [hset] at hk; exact hk.2
  have hki : IsRowIsometry k⁻¹ := by
    have : k⁻¹ ∈ (rowIsometrySubgroup₀ w.Completion : Set _) := (rowIsometrySubgroup₀ w.Completion).inv_mem hk
    rw [hset] at this; exact this.2
  simp only [Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod, Set.mem_image]
  exact ⟨fun i j => hk'.norm_apply_le_one i j, ⟨_, fun i j => hki.norm_apply_le_one i j, rfl⟩⟩

scoped instance compactSpace_rowIsometrySubgroup₀ (K : Type*) [Field K] [NumberField K] (w : InfinitePlace K) :
    CompactSpace (rowIsometrySubgroup₀ w.Completion) :=
  isCompact_iff_compactSpace.mp (isCompact_rowIsometrySubgroup₀ K w)

variable (F : Type) [Field F] [NumberField F]

theorem val_adelicArchGLInclAt_apply (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) (i j : Fin 2) :
    ((adelicArchGLInclAt F w k : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j =
      (archMatrixUpdate F w (k : Matrix (Fin 2) (Fin 2) w.Completion) i j,
        (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) := rfl

theorem continuous_archMatrixUpdate (w : InfinitePlace F) : Continuous (archMatrixUpdate F w) := by
  classical
  have h1 : Continuous fun m : Matrix (Fin 2) (Fin 2) w.Completion =>
      Function.update (1 : Π v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion) w m :=
    continuous_const.update w continuous_id

  have h2 : Continuous fun f : (Π v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion) =>
      (archMatrixPiEquiv F).symm f := by
    refine continuous_pi fun i => continuous_pi fun j => continuous_pi fun v => ?_
    exact ((continuous_apply j).comp ((continuous_apply i).comp (continuous_apply v)))
  exact h2.comp h1

theorem continuous_adelicArchGLInclAt (w : InfinitePlace F) : Continuous (adelicArchGLInclAt F w) := by
  rw [Units.continuous_iff]
  have hval : ∀ {f : GL (Fin 2) w.Completion → GL (Fin 2) w.Completion}, Continuous f →
      Continuous fun k => ((adelicArchGLInclAt F w (f k) : AdelicGL2 (𝓞 F) F) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
    intro f hf
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp_rw [val_adelicArchGLInclAt_apply]
    refine Continuous.prodMk ?_ continuous_const
    exact (continuous_apply j).comp ((continuous_apply i).comp
      ((continuous_archMatrixUpdate F w).comp (Units.continuous_val.comp hf)))
  refine ⟨hval continuous_id, ?_⟩
  simp_rw [← map_inv]
  exact hval continuous_inv

theorem continuous_rowIsometryInclAt₀ (w : InfinitePlace F) : Continuous (rowIsometryInclAt₀ F w) :=
  (continuous_adelicArchGLInclAt F w).comp continuous_subtype_val

abbrev ArchIsometryProd : Type := Π w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion

def archProdIncl : ArchIsometryProd F →* AdelicGL2 (𝓞 F) F :=
  MonoidHom.noncommPiCoprod (fun w => rowIsometryInclAt₀ F w) fun v w hvw x y => by
    rw [rowIsometryInclAt₀_apply, rowIsometryInclAt₀_apply]
    exact commute_adelicArchGLInclAt_of_ne F hvw _ _

theorem archProdIncl_range :
    (archProdIncl F).range = ⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range := by
  unfold archProdIncl
  exact MonoidHom.noncommPiCoprod_range _

theorem continuous_finset_noncommProd {X M ι : Type*} [TopologicalSpace X] [TopologicalSpace M] [Monoid M]
    [ContinuousMul M] (s : Finset ι) (f : ι → X → M) (hf : ∀ i, Continuous (f i))
    (comm : ∀ x, (s : Set ι).Pairwise fun i j => Commute (f i x) (f j x)) :
    Continuous fun x => s.noncommProd (fun i => f i x) (comm x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.noncommProd_empty]; exact continuous_const
  | @insert a s ha ih =>
    have comm' : ∀ x, (s : Set ι).Pairwise fun i j => Commute (f i x) (f j x) := fun x =>
      (comm x).mono (by simp)
    simp_rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha]
    exact (hf a).mul (ih comm')

theorem continuous_archProdIncl : Continuous (archProdIncl F) := by
  classical
  show Continuous fun k : ArchIsometryProd F => archProdIncl F k
  simp only [archProdIncl, MonoidHom.noncommPiCoprod_apply]
  exact continuous_finset_noncommProd _ (fun w (k : ArchIsometryProd F) => rowIsometryInclAt₀ F w (k w))
    (fun w => (continuous_rowIsometryInclAt₀ F w).comp (continuous_apply w)) _

theorem isCompact_iSup_range_rowIsometryInclAt₀ :
    IsCompact ((⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range : Subgroup (AdelicGL2 (𝓞 F) F)) :
      Set (AdelicGL2 (𝓞 F) F)) := by
  rw [← archProdIncl_range, MonoidHom.coe_range]
  exact isCompact_range (continuous_archProdIncl F)

section FdSemisimple

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
variable {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]

theorem exists_stable_compl (π : Representation ℂ H E)
    (hπ : ∀ (ℓ : Module.Dual ℂ E) (v : E), Continuous fun k => ℓ (π k v))
    (P : Submodule ℂ E) (hP : ∀ k : H, ∀ v ∈ P, π k v ∈ P) :
    ∃ Pc : Submodule ℂ E, IsCompl P Pc ∧ ∀ k : H, ∀ v ∈ Pc, π k v ∈ Pc :=
  Representation.exists_isCompl_forall_mem_of_compactSpace_of_continuous π hπ P hP

end FdSemisimple

section PartB

variable (F : Type) [Field F] [NumberField F]

local instance : MeasurableSpace (ArchIsometryProd F) := borel _
local instance : BorelSpace (ArchIsometryProd F) := ⟨rfl⟩

def archRep : Representation ℂ (ArchIsometryProd F) (AdelicGL2 (𝓞 F) F → ℂ) :=
  (rightRegular F).comp (archProdIncl F)

theorem archRep_apply (k : ArchIsometryProd F) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archRep F k φ = rightTranslate F (archProdIncl F k) φ := rfl

theorem archRep_apply_apply (k : ArchIsometryProd F) (φ : AdelicGL2 (𝓞 F) F → ℂ) (x : AdelicGL2 (𝓞 F) F) :
    archRep F k φ x = φ (x * archProdIncl F k) := rfl

theorem continuous_archRep {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) (k : ArchIsometryProd F) :
    Continuous (archRep F k φ) :=
  hφ.comp (continuous_mul_const _)

theorem continuous_dual_apply_of_separating {H : Type*} [Group H] [TopologicalSpace H]
    {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E] (π : Representation ℂ H E)
    {X : Type*} (ev : X → Module.Dual ℂ E) (hsep : ∀ v : E, (∀ x, ev x v = 0) → v = 0)
    (hcont : ∀ (x : X) (v : E), Continuous fun k => ev x (π k v)) :
    ∀ (ℓ : Module.Dual ℂ E) (v : E), Continuous fun k => ℓ (π k v) := by
  let D : Submodule ℂ (Module.Dual ℂ E) :=
    { carrier := {ℓ | ∀ v : E, Continuous fun k => ℓ (π k v)}
      zero_mem' := fun v => by simpa using continuous_const
      add_mem' := fun {a b} ha hb v => by simpa using (ha v).fun_add (hb v)
      smul_mem' := fun c {a} ha v => by simpa using (ha v).fun_const_smul c }
  have hD : D = ⊤ := by
    have hco : D.dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [Submodule.mem_dualCoannihilator] at hv
      rw [Submodule.mem_bot]
      exact hsep v fun x => hv _ (hcont x)
    have hfin := Subspace.finrank_add_finrank_dualCoannihilator_eq D
    rw [hco, finrank_bot, add_zero] at hfin
    exact Submodule.eq_top_of_finrank_eq (hfin.trans (Subspace.dual_finrank_eq).symm)
  intro ℓ v
  have : ℓ ∈ D := by rw [hD]; trivial
  exact this v

def orbitSpan (φ : AdelicGL2 (𝓞 F) F → ℂ) : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
  Submodule.span ℂ (Set.range fun k : ArchIsometryProd F => archRep F k φ)

theorem mem_orbitSpan_self (φ : AdelicGL2 (𝓞 F) F → ℂ) : φ ∈ orbitSpan F φ :=
  Submodule.subset_span ⟨1, by simp⟩

theorem archRep_mem_orbitSpan (φ : AdelicGL2 (𝓞 F) F → ℂ) (k : ArchIsometryProd F) :
    ∀ ψ ∈ orbitSpan F φ, archRep F k ψ ∈ orbitSpan F φ := by
  intro ψ hψ
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hψ
  · rintro _ ⟨j, rfl⟩
    refine Submodule.subset_span ⟨k * j, ?_⟩
    show archRep F (k * j) φ = archRep F k (archRep F j φ)
    rw [map_mul]; rfl
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [map_add]; exact Submodule.add_mem _ ha hb
  · intro c a _ ha; rw [map_smul]; exact Submodule.smul_mem _ c ha

theorem orbitSpan_le_of_mem {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (h : ψ ∈ orbitSpan F φ) :
    orbitSpan F ψ ≤ orbitSpan F φ := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨k, rfl⟩
  exact archRep_mem_orbitSpan F φ k ψ h

theorem continuous_of_mem_orbitSpan {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) :
    ∀ ψ ∈ orbitSpan F φ, Continuous ψ := by
  intro ψ hψ
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hψ
  · rintro _ ⟨k, rfl⟩; exact continuous_archRep F hφ k
  · exact continuous_const
  · intro a b _ _ ha hb; exact ha.add hb
  · intro c a _ ha; exact ha.const_smul c

def Ecf : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) where
  carrier := {φ | Continuous φ ∧ FiniteDimensional ℂ (orbitSpan F φ)}
  zero_mem' := by
    refine ⟨continuous_const, ?_⟩
    have : orbitSpan F (0 : AdelicGL2 (𝓞 F) F → ℂ) ≤ ⊥ := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨k, rfl⟩; simp
    exact Submodule.finiteDimensional_of_le this
  add_mem' := by
    rintro a b ⟨hac, haf⟩ ⟨hbc, hbf⟩
    refine ⟨hac.add hbc, ?_⟩
    have : orbitSpan F (a + b) ≤ orbitSpan F a ⊔ orbitSpan F b := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨k, rfl⟩
      show archRep F k (a + b) ∈ _
      rw [map_add]
      exact Submodule.add_mem_sup (mem_orbitSpan_self F a |> archRep_mem_orbitSpan F a k _)
        (mem_orbitSpan_self F b |> archRep_mem_orbitSpan F b k _)
    exact Submodule.finiteDimensional_of_le this
  smul_mem' := by
    rintro c a ⟨hac, haf⟩
    refine ⟨hac.const_smul c, ?_⟩
    have : orbitSpan F (c • a) ≤ orbitSpan F a := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨k, rfl⟩
      show archRep F k (c • a) ∈ _
      rw [map_smul]
      exact Submodule.smul_mem _ c (mem_orbitSpan_self F a |> archRep_mem_orbitSpan F a k _)
    exact Submodule.finiteDimensional_of_le this

theorem mem_Ecf {φ : AdelicGL2 (𝓞 F) F → ℂ} :
    φ ∈ Ecf F ↔ Continuous φ ∧ FiniteDimensional ℂ (orbitSpan F φ) := Iff.rfl

theorem archRep_mem_Ecf (k : ArchIsometryProd F) {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ Ecf F) :
    archRep F k φ ∈ Ecf F := by
  refine ⟨continuous_archRep F hφ.1 k, ?_⟩
  haveI := hφ.2
  exact Submodule.finiteDimensional_of_le
    (orbitSpan_le_of_mem F (archRep_mem_orbitSpan F φ k φ (mem_orbitSpan_self F φ)))

theorem orbitSpan_le_Ecf {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ Ecf F) : orbitSpan F φ ≤ Ecf F := by
  intro ψ hψ
  refine ⟨continuous_of_mem_orbitSpan F hφ.1 ψ hψ, ?_⟩
  haveI := hφ.2
  exact Submodule.finiteDimensional_of_le (orbitSpan_le_of_mem F hψ)

def ρc : Representation ℂ (ArchIsometryProd F) (Ecf F) where
  toFun k := (archRep F k).restrict fun φ hφ => archRep_mem_Ecf F k hφ
  map_one' := by ext v; simp
  map_mul' a b := by ext v; simp

theorem ρc_apply_coe (k : ArchIsometryProd F) (φ : Ecf F) :
    ((ρc F k φ : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) = archRep F k φ := rfl

theorem exists_invt_compl (E : Submodule ℂ (Ecf F)) [FiniteDimensional ℂ E] (hE : E ∈ (ρc F).invtSubmodule)
    (P : Submodule ℂ (Ecf F)) (hP : P ∈ (ρc F).invtSubmodule) (hPE : P ≤ E) :
    ∃ Pc : Submodule ℂ (Ecf F), Pc ∈ (ρc F).invtSubmodule ∧ P ⊓ Pc = ⊥ ∧ P ⊔ Pc = E := by
  rw [Representation.mem_invtSubmodule] at hE hP

  let π : Representation ℂ (ArchIsometryProd F) E :=
    { toFun := fun k => (ρc F k).restrict fun v hv => hE k hv
      map_one' := by ext v; simp
      map_mul' := fun a b => by ext v; simp }
  have hπ : ∀ (k : ArchIsometryProd F) (v : E), ((π k v : E) : Ecf F) = ρc F k v := fun k v => rfl

  have hcont : ∀ (ℓ : Module.Dual ℂ E) (v : E), Continuous fun k => ℓ (π k v) := by
    refine continuous_dual_apply_of_separating (H := ArchIsometryProd F) (E := E) π
      (fun x : AdelicGL2 (𝓞 F) F => (LinearMap.proj x).comp ((Ecf F).subtype.comp E.subtype)) ?_ ?_
    · intro v hv
      apply Subtype.ext; apply Subtype.ext
      funext x; exact hv x
    · intro x v
      show Continuous fun k => (((π k v : E) : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) x
      simp only [hπ, ρc_apply_coe, archRep_apply_apply]
      exact (v.1.2.1).comp (continuous_const.mul (continuous_archProdIncl F))
  let P₀ : Submodule ℂ E := P.comap E.subtype
  have hP₀ : ∀ (k : ArchIsometryProd F) (v : E), v ∈ P₀ → π k v ∈ P₀ := fun k v hv => hP k hv
  obtain ⟨Pc₀, hc, hst⟩ := exists_stable_compl (H := ArchIsometryProd F) (E := E) π hcont P₀ hP₀
  refine ⟨Pc₀.map E.subtype, ?_, ?_, ?_⟩
  · rw [Representation.mem_invtSubmodule]
    intro g x hx
    obtain ⟨v, hv, rfl⟩ := hx
    exact ⟨π g v, hst g v hv, rfl⟩
  · have hPmap : P = P₀.map E.subtype := by
      rw [Submodule.map_comap_subtype, inf_eq_right.mpr hPE]
    rw [hPmap, ← Submodule.map_inf E.subtype Subtype.val_injective, hc.inf_eq_bot, Submodule.map_bot]
  · have hPmap : P = P₀.map E.subtype := by
      rw [Submodule.map_comap_subtype, inf_eq_right.mpr hPE]
    rw [hPmap, ← Submodule.map_sup, hc.sup_eq_top, Submodule.map_top, Submodule.range_subtype]

end PartB

section PartB3

variable (F : Type) [Field F] [NumberField F]

open Representation in

def orbitSpanc (φ : Ecf F) : Submodule ℂ (Ecf F) :=
  Submodule.span ℂ (Set.range fun k : ArchIsometryProd F => ρc F k φ)

theorem mem_orbitSpanc_self (φ : Ecf F) : φ ∈ orbitSpanc F φ :=
  Submodule.subset_span ⟨1, by simp⟩

theorem map_orbitSpanc (φ : Ecf F) : (orbitSpanc F φ).map (Ecf F).subtype = orbitSpan F φ := by
  rw [orbitSpanc, Submodule.map_span, orbitSpan]
  congr 1
  ext ψ
  simp only [Set.mem_image, Set.mem_range, Submodule.subtype_apply, exists_exists_eq_and, ρc_apply_coe]

scoped instance finiteDimensional_orbitSpanc (φ : Ecf F) : FiniteDimensional ℂ (orbitSpanc F φ) := by
  haveI : FiniteDimensional ℂ (orbitSpan F (φ : AdelicGL2 (𝓞 F) F → ℂ)) := φ.2.2
  have e := Submodule.equivMapOfInjective (Ecf F).subtype Subtype.val_injective (orbitSpanc F φ)
  rw [map_orbitSpanc] at e
  exact LinearEquiv.finiteDimensional e.symm

theorem orbitSpanc_mem_invtSubmodule (φ : Ecf F) : orbitSpanc F φ ∈ (ρc F).invtSubmodule := by
  rw [Representation.mem_invtSubmodule]
  intro k
  change orbitSpanc F φ ≤ (orbitSpanc F φ).comap (ρc F k)
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨j, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap]
  refine Submodule.subset_span ⟨k * j, ?_⟩
  show ρc F (k * j) φ = ρc F k (ρc F j φ)
  rw [map_mul]; rfl

end PartB3

section PartB8lite
variable (F : Type) [Field F] [NumberField F]

theorem rightTranslate_mem_of_mem_iSup_range' (Z : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hZ : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion),
      ∀ φ ∈ Z, rightTranslate F (rowIsometryInclAt₀ F w k) φ ∈ Z)
    {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ ⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range) :
    ∀ φ ∈ Z, rightTranslate F g φ ∈ Z := by
  refine Subgroup.iSup_induction _ (C := fun g => ∀ φ ∈ Z, rightTranslate F g φ ∈ Z) hg ?_ ?_ ?_
  · rintro w g ⟨k', rfl⟩; exact hZ w k'
  · intro φ hφ
    have : rightTranslate F 1 φ = φ := by funext x; simp [rightTranslate]
    rwa [this]
  · intro a b ha hb φ hφ
    rw [← rightTranslate_rightTranslate]
    exact ha _ (hb _ hφ)

theorem archProdIncl_mem_iSup (k : ArchIsometryProd F) :
    archProdIncl F k ∈ ⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range := by
  rw [← archProdIncl_range]; exact ⟨k, rfl⟩

end PartB8lite

section Lambda4
variable (F : Type) [Field F] [NumberField F]

open MeasureTheory

private abbrev L4GMeas : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F

attribute [local instance] L4GMeas

private theorem L4GBorel : BorelSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F

attribute [local instance] L4GBorel

private theorem L4GHaar : (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure :=
  AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F

attribute [local instance] L4GHaar

private theorem L4_integrable_mul {ψ f : AdelicGL2 (𝓞 F) F → ℂ} (hψ : Continuous ψ)
    (hf : Continuous f) (hfs : HasCompactSupport f) (x : AdelicGL2 (𝓞 F) F) :
    Integrable (fun y => ψ (x * y) * f y) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) :=
  ((hψ.comp (continuous_const.mul continuous_id)).mul hf).integrable_of_hasCompactSupport hfs.mul_left

private theorem L4_rightConv_add_right {ψ f g : AdelicGL2 (𝓞 F) F → ℂ} (hψ : Continuous ψ)
    (hf : Continuous f) (hfs : HasCompactSupport f) (hg : Continuous g) (hgs : HasCompactSupport g) :
    rightConv F ψ (f + g) = rightConv F ψ f + rightConv F ψ g := by
  funext x
  rw [Pi.add_apply, rightConv_apply, rightConv_apply, rightConv_apply,
    ← integral_add (L4_integrable_mul F hψ hf hfs x)
      (L4_integrable_mul F hψ hg hgs x)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show ψ (x * y) * (f y + g y) = ψ (x * y) * f y + ψ (x * y) * g y
  ring

private theorem L4_rightConv_smul_right (c : ℂ) (ψ f : AdelicGL2 (𝓞 F) F → ℂ) :
    rightConv F ψ (c • f) = c • rightConv F ψ f := by
  funext x
  rw [Pi.smul_apply, smul_eq_mul, rightConv_apply, rightConv_apply, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show ψ (x * y) * (c * f y) = c * (ψ (x * y) * f y)
  ring

private theorem L4_rightConv_smul_left (c : ℂ) (ψ f : AdelicGL2 (𝓞 F) F → ℂ) :
    rightConv F (c • ψ) f = c • rightConv F ψ f := by
  funext x
  rw [Pi.smul_apply, smul_eq_mul, rightConv_apply, rightConv_apply, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show c * ψ (x * y) * f y = c * (ψ (x * y) * f y)
  ring

theorem exists_bilin_rightConv (S T : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hS : ∀ s ∈ S, Continuous s) (hT : ∀ t ∈ T, Continuous t ∧ HasCompactSupport t) :
    ∃ β : S →ₗ[ℂ] T →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ),
      ∀ (s : S) (t : T), β s t = rightConv F (s : AdelicGL2 (𝓞 F) F → ℂ) (t : AdelicGL2 (𝓞 F) F → ℂ) := by
  refine ⟨LinearMap.mk₂ ℂ (fun (s : S) (t : T) => rightConv F (s : AdelicGL2 (𝓞 F) F → ℂ) (t : AdelicGL2 (𝓞 F) F → ℂ))
    ?_ ?_ ?_ ?_, fun s t => rfl⟩
  · intro s s' t
    beta_reduce
    rw [Submodule.coe_add]
    exact rightConv_add_left F (hS s s.2) (hS s' s'.2) (hT t t.2).1 (hT t t.2).2
  · intro c s t
    beta_reduce
    rw [Submodule.coe_smul]
    exact L4_rightConv_smul_left F c s t
  · intro s t t'
    beta_reduce
    rw [Submodule.coe_add]
    exact L4_rightConv_add_right F (hS s s.2) (hT t t.2).1 (hT t t.2).2 (hT t' t'.2).1 (hT t' t'.2).2
  · intro c s t
    beta_reduce
    rw [Submodule.coe_smul]
    exact L4_rightConv_smul_right F c s t

end Lambda4

section PartC2

set_option backward.isDefEq.respectTransparency false

variable (F : Type) [Field F] [NumberField F]

open Representation

def reflL : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) where
  toFun X := fun z => X z⁻¹
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem reflL_apply (X : AdelicGL2 (𝓞 F) F → ℂ) (z : AdelicGL2 (𝓞 F) F) : reflL F X z = X z⁻¹ := rfl

theorem reflL_reflL (X : AdelicGL2 (𝓞 F) F → ℂ) : reflL F (reflL F X) = X := by
  funext z; simp [reflL_apply]

theorem reflL_rightTranslate (h : AdelicGL2 (𝓞 F) F) (X : AdelicGL2 (𝓞 F) F → ℂ) :
    reflL F (rightTranslate F h X) = fun z => reflL F X (h⁻¹ * z) := by
  funext z; simp [reflL_apply, rightTranslate, mul_inv_rev]

theorem continuous_reflL {X : AdelicGL2 (𝓞 F) F → ℂ} (hX : Continuous X) : Continuous (reflL F X) :=
  hX.comp continuous_inv

theorem hasCompactSupport_reflL {X : AdelicGL2 (𝓞 F) F → ℂ} (hX : HasCompactSupport X) :
    HasCompactSupport (reflL F X) :=
  hX.comp_homeomorph (Homeomorph.inv (AdelicGL2 (𝓞 F) F))

theorem hasCompactSupport_of_mem_orbitSpan {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : HasCompactSupport φ) :
    ∀ ψ ∈ orbitSpan F φ, HasCompactSupport ψ := by
  intro ψ hψ
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hψ
  · rintro _ ⟨k, rfl⟩
    exact hφ.comp_homeomorph (Homeomorph.mulRight (archProdIncl F k))
  · exact HasCompactSupport.zero
  · intro a b _ _ ha hb; exact ha.add hb
  · intro c a _ ha
    show HasCompactSupport (c • a)
    exact ha.smul_left

theorem rightConv_rightTranslate_rightTranslate' (ψ f : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    rightConv F (rightTranslate F g ψ) (rightTranslate F g f) = rightConv F ψ f := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar F
  funext x
  show (∫ z, ψ (x * z * g) * f (z * g) ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)) =
    ∫ z, ψ (x * z) * f z ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
  simp_rw [mul_assoc]
  exact MeasureTheory.integral_mul_right_eq_self (fun z => ψ (x * z) * f z) g

theorem rightConv_comp_mul_left_eq (ψ f : AdelicGL2 (𝓞 F) F → ℂ) (h : AdelicGL2 (𝓞 F) F) :
    rightConv F ψ (fun z => f (h⁻¹ * z)) = rightTranslate F h (rightConv F ψ f) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  funext x
  show (∫ z, ψ (x * z) * f (h⁻¹ * z) ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)) =
    ∫ z, ψ (x * h * z) * f z ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
  rw [← MeasureTheory.integral_mul_left_eq_self (fun z => ψ (x * z) * f (h⁻¹ * z)) h]
  simp only [mul_assoc, inv_mul_cancel_left]

variable {F} in

structure LamData (y G0 : Ecf F) where
  raw : orbitSpan F (G0 : AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ)
  raw_apply : ∀ X, raw X = rightConv F y (reflL F X)

theorem exists_lamData (y G0 : Ecf F) (hG0s : HasCompactSupport (G0 : AdelicGL2 (𝓞 F) F → ℂ)) :
    Nonempty (LamData y G0) := by
  let O := orbitSpan F (G0 : AdelicGL2 (𝓞 F) F → ℂ)
  let T := O.map (reflL F)
  have hT : ∀ t ∈ T, Continuous t ∧ HasCompactSupport t := by
    rintro _ ⟨X, hX, rfl⟩
    exact ⟨continuous_reflL F (continuous_of_mem_orbitSpan F G0.2.1 X hX),
      hasCompactSupport_reflL F (hasCompactSupport_of_mem_orbitSpan F hG0s X hX)⟩
  obtain ⟨β, hβ⟩ := exists_bilin_rightConv F (Submodule.span ℂ {(y : AdelicGL2 (𝓞 F) F → ℂ)}) T
    (fun s hs => by
      rw [Submodule.mem_span_singleton] at hs
      obtain ⟨c, rfl⟩ := hs
      exact y.2.1.const_smul c) hT
  let r : O →ₗ[ℂ] T := (reflL F).restrict fun X hX => Submodule.mem_map_of_mem hX
  refine ⟨⟨(β ⟨y, Submodule.mem_span_singleton_self _⟩) ∘ₗ r, fun X => ?_⟩⟩
  rw [LinearMap.comp_apply, hβ]
  rfl

theorem LamData.raw_archRep {y G0 : Ecf F} (L : LamData y G0) (k : ArchIsometryProd F)
    (X : orbitSpan F (G0 : AdelicGL2 (𝓞 F) F → ℂ)) :
    L.raw ⟨archRep F k X, archRep_mem_orbitSpan F _ k _ X.2⟩ = archRep F k (L.raw X) := by
  rw [L.raw_apply, L.raw_apply]
  dsimp only
  rw [archRep_apply, archRep_apply, reflL_rightTranslate]
  exact rightConv_comp_mul_left_eq F _ _ _

theorem LamData.raw_mem_Ecf {y G0 : Ecf F} (L : LamData y G0)
    (hG0s : HasCompactSupport (G0 : AdelicGL2 (𝓞 F) F → ℂ)) (X : orbitSpan F (G0 : AdelicGL2 (𝓞 F) F → ℂ)) :
    L.raw X ∈ Ecf F := by
  haveI : FiniteDimensional ℂ (orbitSpan F (G0 : AdelicGL2 (𝓞 F) F → ℂ)) := G0.2.2
  refine ⟨?_, ?_⟩
  · rw [L.raw_apply]
    exact AutomorphicForm.continuous_rightConv_of_continuous_of_hasCompactSupport F _ y.2.1 _
      (continuous_reflL F (continuous_of_mem_orbitSpan F G0.2.1 _ X.2))
      (hasCompactSupport_reflL F (hasCompactSupport_of_mem_orbitSpan F hG0s _ X.2))
  · have : orbitSpan F (L.raw X) ≤ LinearMap.range L.raw := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨k, rfl⟩
      exact ⟨⟨archRep F k X, archRep_mem_orbitSpan F _ k _ X.2⟩, L.raw_archRep F k X⟩
    exact Submodule.finiteDimensional_of_le this

def LamData.toEcf {y G0 : Ecf F} (L : LamData y G0) (hG0s : HasCompactSupport (G0 : AdelicGL2 (𝓞 F) F → ℂ)) :
    orbitSpanc F G0 →ₗ[ℂ] Ecf F where
  toFun X := ⟨L.raw ⟨(X : Ecf F), by
      have := Submodule.mem_map_of_mem (f := (Ecf F).subtype) X.2
      rwa [map_orbitSpanc] at this⟩, L.raw_mem_Ecf F hG0s _⟩
  map_add' a b := by
    apply Subtype.ext
    show L.raw ⟨(a : Ecf F) + (b : Ecf F), _⟩ = L.raw _ + L.raw _
    rw [← map_add]; rfl
  map_smul' c a := by
    apply Subtype.ext
    show L.raw ⟨c • ((a : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ), _⟩ = c • L.raw _
    rw [← map_smul]; rfl

theorem LamData.toEcf_coe {y G0 : Ecf F} (L : LamData y G0) (hG0s : HasCompactSupport (G0 : AdelicGL2 (𝓞 F) F → ℂ))
    (X : orbitSpanc F G0) :
    ((L.toEcf F hG0s X : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) = rightConv F y (reflL F ((X : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ)) :=
  L.raw_apply _

theorem LamData.toEcf_ρc {y G0 : Ecf F} (L : LamData y G0) (hG0s : HasCompactSupport (G0 : AdelicGL2 (𝓞 F) F → ℂ))
    (k : ArchIsometryProd F) (X : orbitSpanc F G0) :
    L.toEcf F hG0s ⟨ρc F k X, (Representation.mem_invtSubmodule _).mp (orbitSpanc_mem_invtSubmodule F G0) k X.2⟩ =
      ρc F k (L.toEcf F hG0s X) := by
  apply Subtype.ext
  show L.raw ⟨archRep F k ((X : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ), _⟩ = archRep F k (L.raw _)
  exact L.raw_archRep F k ⟨_, _⟩

end PartC2

section FarmLeftStable

theorem comp_mul_left_mem_typeSubmodule {G H : Type*} [Group G] [Group H] {ι : H →* G}
    {W : Type*} [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ H W} {f : G → ℂ}
    (hf : f ∈ typeSubmodule ι ρ) (h : G) : (fun x => f (h * x)) ∈ typeSubmodule ι ρ := by
  refine Submodule.span_induction (p := fun f _ => (fun x => f (h * x)) ∈ typeSubmodule ι ρ)
    ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨T, hT, v, rfl⟩
    let Lh : (G → ℂ) →ₗ[ℂ] (G → ℂ) :=
      { toFun := fun u x => u (h * x)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hT' : IsRightEquivariant ι ρ (Lh ∘ₗ T) := by
      intro k v x
      show T (ρ k v) (h * x) = T v (h * (x * ι k))
      rw [hT k v (h * x), mul_assoc]
    exact mem_typeSubmodule_of_isRightEquivariant hT' v
  · exact (typeSubmodule ι ρ).zero_mem
  · intro f g _ _ hf hg
    exact (typeSubmodule ι ρ).add_mem hf hg
  · intro c f _ hf
    exact (typeSubmodule ι ρ).smul_mem c hf

theorem comp_mul_left_mem_archCutSubmodule (F : Type) [Field F] [NumberField F] (tys : ArchTypeFamily F)
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : f ∈ archCutSubmodule F tys) (h : AdelicGL2 (𝓞 F) F) :
    (fun x => f (h * x)) ∈ archCutSubmodule F tys := by
  rw [mem_archCutSubmodule_iff] at hf ⊢
  intro w
  refine Submodule.iSup_induction _
    (motive := fun f => (fun x => f (h * x)) ∈ ⨆ i : Fin (tys.card w), archTypeSubmoduleAt F w (tys.rep w i))
    (hf w) ?_ ?_ ?_
  · intro i f hfi
    exact le_iSup (fun j => archTypeSubmoduleAt F w (tys.rep w j)) i (comp_mul_left_mem_typeSubmodule hfi h)
  · exact Submodule.zero_mem _
  · exact fun _ _ hu hv => Submodule.add_mem _ hu hv

theorem comp_mul_left_mem_archDualCutSubmodule (F : Type) [Field F] [NumberField F] (tys : ArchTypeFamily F)
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : f ∈ archDualCutSubmodule F tys) (h : AdelicGL2 (𝓞 F) F) :
    (fun x => f (h * x)) ∈ archDualCutSubmodule F tys := by
  rw [mem_archDualCutSubmodule_iff] at hf ⊢
  intro w
  refine Submodule.iSup_induction _
    (motive := fun f => (fun x => f (h * x)) ∈ ⨆ i : Fin (tys.card w), archDualTypeSubmoduleAt F w (tys.rep w i))
    (hf w) ?_ ?_ ?_
  · intro i f hfi
    exact le_iSup (fun j => archDualTypeSubmoduleAt F w (tys.rep w j)) i (comp_mul_left_mem_typeSubmodule hfi h)
  · exact Submodule.zero_mem _
  · exact fun _ _ hu hv => Submodule.add_mem _ hu hv

end FarmLeftStable

section FarmSpan

theorem exists_eq_sum_of_mem_span_range {G : Type*} {ι : Type*} (t : ι → G → ℂ) {h : G → ℂ}
    (hh : h ∈ Submodule.span ℂ (Set.range t)) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (k : Fin n → ι), h = fun x => ∑ j, c j * t (k j) x := by
  classical
  obtain ⟨n, c, v, hv⟩ := (Submodule.mem_span_set').mp hh
  have hk : ∀ j : Fin n, ∃ i : ι, t i = (v j : G → ℂ) := fun j => (v j).2
  choose k hk using hk
  refine ⟨n, c, k, ?_⟩
  rw [← hv]
  funext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => by rw [hk j]

theorem exists_eq_sum_of_mem_span_translates {G : Type*} [Group G] {ι : Type*} (g : ι → G) {f h : G → ℂ}
    (hh : h ∈ Submodule.span ℂ (Set.range fun i : ι => fun x : G => f (x * g i))) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (k : Fin n → ι), h = fun x => ∑ j, c j * f (x * g (k j)) :=
  exists_eq_sum_of_mem_span_range (fun i x => f (x * g i)) hh

end FarmSpan

section PartTQC

variable (F : Type) [Field F] [NumberField F]

open Representation

open scoped Classical in
theorem archProdIncl_mulSingle (w : InfinitePlace F) (kw : rowIsometrySubgroup₀ w.Completion) :
    archProdIncl F (Pi.mulSingle w kw) = rowIsometryInclAt₀ F w kw := by
  classical
  unfold archProdIncl
  exact MonoidHom.noncommPiCoprod_mulSingle (fun v => rowIsometryInclAt₀ F v) w kw

theorem injective_of_forall_apply_eq_zero {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (p : Submodule ℂ V) (q : Submodule ℂ V') (f : p →ₗ[ℂ] q) (h : ∀ m, f m = 0 → m = 0) :
    Function.Injective f := by
  intro a b hab
  have h1 : f (a - b) + f b = f b := by rw [← map_add, sub_add_cancel, hab]
  have h2 : f (a - b) = 0 := add_right_cancel (h1.trans (zero_add _).symm)
  exact sub_eq_zero.mp (h _ h2)

theorem rowIsometryInclAt₀_injective (w : InfinitePlace F) : Function.Injective (rowIsometryInclAt₀ F w) := by
  intro a c hac
  apply Subtype.ext
  apply Units.ext
  ext i j'
  have := congrArg (fun g : AdelicGL2 (𝓞 F) F => ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j').1 w) hac
  simp only [rowIsometryInclAt₀_apply, val_adelicArchGLInclAt_apply, archMatrixUpdate_apply_self] at this
  exact this

theorem le_iSup_archTypeSubmoduleAt_of_surjective' (w : InfinitePlace F) (tys : ArchTypeFamily F)
    (S S' : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) [FiniteDimensional ℂ S]
    (hS' : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ s ∈ S', rightTranslate F (rowIsometryInclAt₀ F w k) s ∈ S')
    (hS : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ s ∈ S, rightTranslate F (rowIsometryInclAt₀ F w k) s ∈ S)
    (θ : S →ₗ[ℂ] S') (hθs : Function.Surjective θ)
    (hθ : ∀ (k : rowIsometrySubgroup₀ w.Completion) (s : S),
      (θ ⟨rightTranslate F (rowIsometryInclAt₀ F w k) s, hS k s s.2⟩ : AdelicGL2 (𝓞 F) F → ℂ) =
        rightTranslate F (rowIsometryInclAt₀ F w k) (θ s))
    (hSA : S ≤ ⨆ i : Fin (tys.card w), archTypeSubmoduleAt F w (tys.rep w i)) :
    S' ≤ ⨆ i : Fin (tys.card w), archTypeSubmoduleAt F w (tys.rep w i) :=
  AutomorphicForm.le_iSup_typeSubmodule_of_surjective_of_le_iSup_typeSubmodule (rowIsometryInclAt₀ F w)
    (rowIsometryInclAt₀_injective F w) (fun i : Fin (tys.card w) => Fin (tys.rep w i).n → ℂ)
    (fun i => (tys.rep w i).ρ) S S' hS' hS θ hθs hθ hSA

theorem range_archRep_eq (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    Set.range (fun k : ArchIsometryProd F => archRep F k φ) =
      {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
        ψ = rightTranslate F k φ} := by
  ext ψ
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨archProdIncl F k, archProdIncl_mem_iSup F k, archRep_apply F k φ⟩
  · rintro ⟨k, hk, rfl⟩
    rw [← archProdIncl_range] at hk
    obtain ⟨k', rfl⟩ := hk
    exact ⟨k', archRep_apply F k' φ⟩

theorem orbitSpan_eq_span (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    orbitSpan F φ = Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range), ψ = rightTranslate F k φ} := by
  rw [orbitSpan, range_archRep_eq]

theorem mem_Ecf_of_mem_archCut' (tys : ArchTypeFamily F) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hA : φ ∈ archCutSubmodule F tys) (hc : Continuous φ) : φ ∈ Ecf F := by
  refine ⟨hc, ?_⟩
  rw [orbitSpan_eq_span]
  exact AutomorphicForm.finiteDimensional_span_rightTranslate_of_mem_archCutSubmodule F tys hA

theorem mem_Ecf_of_mem_archDualCut' (tys : ArchTypeFamily F) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hA : φ ∈ archDualCutSubmodule F tys) (hc : Continuous φ) : φ ∈ Ecf F := by
  refine ⟨hc, ?_⟩
  rw [orbitSpan_eq_span]
  exact AutomorphicForm.finiteDimensional_span_rightTranslate_of_mem_archDualCutSubmodule F tys hA

theorem rightTranslate_mem_archCutSubmodule_of_mem_iSup_range (tys : ArchTypeFamily F)
    {k : AdelicGL2 (𝓞 F) F} (hk : k ∈ ⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range) :
    ∀ φ ∈ archCutSubmodule F tys, rightTranslate F k φ ∈ archCutSubmodule F tys :=
  rightTranslate_mem_of_mem_iSup_range' F _
    (fun w k φ hφ => comp_mul_rowIsometryInclAt₀_mem_archCutSubmodule F hφ w k) hk

theorem orbitSpan_le_archCut (tys : ArchTypeFamily F) {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ archCutSubmodule F tys) :
    orbitSpan F φ ≤ archCutSubmodule F tys := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨k, rfl⟩
  exact rightTranslate_mem_archCutSubmodule_of_mem_iSup_range F tys (archProdIncl_mem_iSup F k) φ hφ

theorem orbitSpanc_le_of_mem {φ ψ : Ecf F} (h : ψ ∈ orbitSpanc F φ) : orbitSpanc F ψ ≤ orbitSpanc F φ := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨k, rfl⟩
  exact (Representation.mem_invtSubmodule _).mp (orbitSpanc_mem_invtSubmodule F φ) k h

theorem coe_mem_orbitSpan_of_mem_orbitSpanc {φ ψ : Ecf F} (h : ψ ∈ orbitSpanc F φ) :
    (ψ : AdelicGL2 (𝓞 F) F → ℂ) ∈ orbitSpan F (φ : AdelicGL2 (𝓞 F) F → ℂ) := by
  rw [← map_orbitSpanc]; exact Submodule.mem_map_of_mem h

theorem mem_orbitSpanc_of_coe_mem_orbitSpan {φ ψ : Ecf F} (h : (ψ : AdelicGL2 (𝓞 F) F → ℂ) ∈ orbitSpan F (φ : AdelicGL2 (𝓞 F) F → ℂ)) :
    ψ ∈ orbitSpanc F φ := by
  rw [← map_orbitSpanc] at h
  obtain ⟨ψ', hψ', he⟩ := h
  have : ψ' = ψ := Subtype.ext he
  rwa [this] at hψ'

variable {F} in

theorem LamData.raw_mem_archCutSubmodule {y G0 : Ecf F} (L : LamData y G0) (tys : ArchTypeFamily F)
    {q : AdelicGL2 (𝓞 F) F → ℂ} (hqO : q ∈ orbitSpan F (G0 : AdelicGL2 (𝓞 F) F → ℂ)) (hqA : q ∈ archCutSubmodule F tys) :
    L.raw ⟨q, hqO⟩ ∈ archCutSubmodule F tys := by
  classical
  haveI : FiniteDimensional ℂ (orbitSpan F (G0 : AdelicGL2 (𝓞 F) F → ℂ)) := G0.2.2
  let S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := orbitSpan F q
  have hSO : S ≤ orbitSpan F (G0 : AdelicGL2 (𝓞 F) F → ℂ) := orbitSpan_le_of_mem F hqO
  haveI : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hSO
  let θ₀ : S →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) := L.raw ∘ₗ Submodule.inclusion hSO
  have hθ₀ : ∀ (k : ArchIsometryProd F) (s : S),
      θ₀ ⟨archRep F k s, archRep_mem_orbitSpan F q k s s.2⟩ = archRep F k (θ₀ s) := by
    intro k s
    show L.raw ⟨archRep F k (s : AdelicGL2 (𝓞 F) F → ℂ), _⟩ = archRep F k (L.raw ⟨s, _⟩)
    exact L.raw_archRep F k ⟨s, hSO s.2⟩
  have hSA : S ≤ archCutSubmodule F tys := orbitSpan_le_archCut F tys hqA
  rw [mem_archCutSubmodule_iff]
  intro w
  refine (le_iSup_archTypeSubmoduleAt_of_surjective' F w tys S (LinearMap.range θ₀) ?_ ?_
    θ₀.rangeRestrict (LinearMap.surjective_rangeRestrict θ₀) ?_ ?_)
    (LinearMap.mem_range_self θ₀ ⟨q, mem_orbitSpan_self F q⟩)
  · rintro k _ ⟨s, rfl⟩
    refine ⟨⟨archRep F (Pi.mulSingle w k) s, archRep_mem_orbitSpan F q _ s s.2⟩, ?_⟩
    refine (hθ₀ (Pi.mulSingle w k) s).trans ?_
    rw [archRep_apply, archProdIncl_mulSingle]
  · intro k s hs
    have := archRep_mem_orbitSpan F q (Pi.mulSingle w k) s hs
    rwa [archRep_apply, archProdIncl_mulSingle] at this
  · intro k s
    show (θ₀ ⟨rightTranslate F (rowIsometryInclAt₀ F w k) s, _⟩ : AdelicGL2 (𝓞 F) F → ℂ) = rightTranslate F _ (θ₀ s)
    have h := hθ₀ (Pi.mulSingle w k) s
    simp only [archRep_apply, archProdIncl_mulSingle] at h
    refine Eq.trans ?_ h
    rfl
  · intro s hs
    exact (mem_archCutSubmodule_iff F tys s).mp (hSA hs) w

variable {F} in

theorem eq_zero_of_injective_equivariant (tys : ArchTypeFamily F)
    (Pc : Submodule ℂ (Ecf F)) (hPcinv : ∀ (k : ArchIsometryProd F) (c : Ecf F), c ∈ Pc → ρc F k c ∈ Pc)
    (hPcA : ∀ c : Pc, ((c : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) ∈ archCutSubmodule F tys → c = 0)
    (Rc : Pc →ₗ[ℂ] Ecf F) (hRc : ∀ (k : ArchIsometryProd F) (c : Pc), Rc ⟨ρc F k c, hPcinv k c c.2⟩ = ρc F k (Rc c))
    (hRinj : Function.Injective Rc)
    (c₀ : Pc) (hvA : ((Rc c₀ : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) ∈ archCutSubmodule F tys) : Rc c₀ = 0 := by
  classical
  set v : Ecf F := Rc c₀ with hv
  let e := LinearEquiv.ofInjective Rc hRinj
  have he : ∀ c : Pc, ((e c : LinearMap.range Rc) : Ecf F) = Rc c := fun c => rfl
  have hrangeinv : ∀ (k : ArchIsometryProd F), ∀ r ∈ LinearMap.range Rc, ρc F k r ∈ LinearMap.range Rc := by
    rintro k _ ⟨c, rfl⟩
    exact ⟨⟨ρc F k c, hPcinv k c c.2⟩, hRc k c⟩
  have hOv : ∀ s ∈ orbitSpan F (v : AdelicGL2 (𝓞 F) F → ℂ), ∃ hs : s ∈ Ecf F, (⟨s, hs⟩ : Ecf F) ∈ LinearMap.range Rc := by
    intro s hs
    have hs' : s ∈ (LinearMap.range Rc).map (Ecf F).subtype := by
      refine (Submodule.span_le.mpr ?_) hs
      rintro _ ⟨k, rfl⟩
      exact ⟨ρc F k v, hrangeinv k v ⟨c₀, rfl⟩, rfl⟩
    obtain ⟨r, hr, rfl⟩ := hs'
    exact ⟨r.2, by simpa using hr⟩
  let S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := orbitSpan F (v : AdelicGL2 (𝓞 F) F → ℂ)
  haveI : FiniteDimensional ℂ S := v.2.2

  let ι₁ : S →ₗ[ℂ] LinearMap.range Rc :=
    { toFun := fun s => ⟨⟨(s : AdelicGL2 (𝓞 F) F → ℂ), (hOv s s.2).1⟩, (hOv s s.2).2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let cof : S → Pc := fun s => e.symm (ι₁ s)
  have hcof : ∀ s : S, ((Rc (cof s) : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) = s := by
    intro s
    have h1 : e (cof s) = ι₁ s := LinearEquiv.apply_symm_apply e (ι₁ s)
    have h2 : ((e (cof s) : LinearMap.range Rc) : Ecf F) = Rc (cof s) := he (cof s)
    rw [h1] at h2

    have h3 : (((ι₁ s : LinearMap.range Rc) : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) = s := rfl
    rw [← h3, h2]
  have hcof_add : ∀ a b : S, cof (a + b) = cof a + cof b := fun a b => by
    show e.symm (ι₁ (a + b)) = _; rw [map_add, map_add]
  have hcof_smul : ∀ (r : ℂ) (a : S), cof (r • a) = r • cof a := fun r a => by
    show e.symm (ι₁ (r • a)) = _; rw [map_smul, map_smul]
  let θ₀ : S →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) :=
    { toFun := fun s => (((cof s : Pc) : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ)
      map_add' := fun a b => by simp only [hcof_add, Submodule.coe_add]
      map_smul' := fun r a => by simp only [hcof_smul, Submodule.coe_smul, RingHom.id_apply] }
  have hθ₀_def : ∀ s : S, θ₀ s = (((cof s : Pc) : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) := fun s => rfl
  have hcof_eq : ∀ (k : ArchIsometryProd F) (s : S),
      cof ⟨archRep F k s, archRep_mem_orbitSpan F _ k s s.2⟩ = ⟨ρc F k (cof s : Pc), hPcinv k _ (cof s).2⟩ := by
    intro k s
    apply hRinj
    rw [hRc]
    apply Subtype.ext
    rw [hcof, ρc_apply_coe, hcof]
  have hθ₀ : ∀ (k : ArchIsometryProd F) (s : S),
      θ₀ ⟨archRep F k s, archRep_mem_orbitSpan F _ k s s.2⟩ = archRep F k (θ₀ s) := by
    intro k s
    rw [hθ₀_def, hθ₀_def, hcof_eq]
    rfl

  have hSA : S ≤ archCutSubmodule F tys := orbitSpan_le_archCut F tys hvA
  have hθ₀A : ∀ s : S, θ₀ s ∈ archCutSubmodule F tys := by
    intro s
    rw [mem_archCutSubmodule_iff]
    intro w
    refine (le_iSup_archTypeSubmoduleAt_of_surjective' F w tys S (LinearMap.range θ₀) ?_ ?_
      θ₀.rangeRestrict (LinearMap.surjective_rangeRestrict θ₀) ?_ ?_) (LinearMap.mem_range_self θ₀ s)
    · rintro k _ ⟨s, rfl⟩
      refine ⟨⟨archRep F (Pi.mulSingle w k) s, archRep_mem_orbitSpan F _ _ s s.2⟩, ?_⟩
      refine (hθ₀ (Pi.mulSingle w k) s).trans ?_
      rw [archRep_apply, archProdIncl_mulSingle]
    · intro k s hs
      have := archRep_mem_orbitSpan F (v : AdelicGL2 (𝓞 F) F → ℂ) (Pi.mulSingle w k) s hs
      rwa [archRep_apply, archProdIncl_mulSingle] at this
    · intro k s
      show (θ₀ ⟨rightTranslate F (rowIsometryInclAt₀ F w k) s, _⟩ : AdelicGL2 (𝓞 F) F → ℂ) = rightTranslate F _ (θ₀ s)
      have h' := hθ₀ (Pi.mulSingle w k) s
      simp only [archRep_apply, archProdIncl_mulSingle] at h'
      refine Eq.trans ?_ h'
      rfl
    · intro s hs
      exact (mem_archCutSubmodule_iff F tys s).mp (hSA hs) w
  have hz : cof ⟨v, mem_orbitSpan_self F _⟩ = 0 := hPcA _ (by rw [← hθ₀_def]; exact hθ₀A _)
  have := hcof ⟨v, mem_orbitSpan_self F _⟩
  rw [hz, map_zero] at this
  apply Subtype.ext
  exact this.symm

variable {F} in

theorem LamData.apply_raw_eq_zero {y G0 : Ecf F} (L : LamData y G0)
    (hG0s : HasCompactSupport (G0 : AdelicGL2 (𝓞 F) F → ℂ)) (tys : ArchTypeFamily F)
    (Q : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ))
    (h1 : ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ → φ ∈ archCutSubmodule F tys → Q φ = φ)
    (h2 : ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, φ ∈ Ecf F → Q φ ∈ archCutSubmodule F tys ∧ Q φ ∈ orbitSpan F φ)
    (h3 : ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, φ ∈ Ecf F → ∀ k : ArchIsometryProd F, Q (archRep F k φ) = archRep F k (Q φ))
    (hc : Ecf F) (hhO : (hc : AdelicGL2 (𝓞 F) F → ℂ) ∈ orbitSpan F (G0 : AdelicGL2 (𝓞 F) F → ℂ)) (hQh : Q hc = 0) :
    Q (L.raw ⟨hc, hhO⟩) = 0 := by
  classical

  have hQW : ∀ w' ∈ orbitSpan F (hc : AdelicGL2 (𝓞 F) F → ℂ), Q w' = 0 := by
    intro w' hw'
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hw'
    · rintro _ ⟨k, rfl⟩; rw [h3 _ hc.2 k, hQh, map_zero]
    · exact map_zero Q
    · intro a b _ _ ha hb; rw [map_add, ha, hb, add_zero]
    · intro c a _ ha; rw [map_smul, ha, smul_zero]

  have hWA : ∀ w' ∈ orbitSpan F (hc : AdelicGL2 (𝓞 F) F → ℂ), w' ∈ archCutSubmodule F tys → w' = 0 := by
    intro w' hw' hA
    rw [← h1 w' (continuous_of_mem_orbitSpan F hc.2.1 w' hw') hA]
    exact hQW w' hw'

  have hhcO : hc ∈ orbitSpanc F G0 := mem_orbitSpanc_of_coe_mem_orbitSpan F hhO
  have hWOc : orbitSpanc F hc ≤ orbitSpanc F G0 := orbitSpanc_le_of_mem F hhcO
  have hWinv : ∀ (k : ArchIsometryProd F) (x : Ecf F), x ∈ orbitSpanc F hc → ρc F k x ∈ orbitSpanc F hc :=
    fun k x hx => (Representation.mem_invtSubmodule (ρc F)).mp (orbitSpanc_mem_invtSubmodule F hc) k hx
  let ΛW : orbitSpanc F hc →ₗ[ℂ] Ecf F := L.toEcf F hG0s ∘ₗ Submodule.inclusion hWOc
  have hΛW_def : ∀ x : orbitSpanc F hc, ΛW x = L.toEcf F hG0s ⟨x, hWOc x.2⟩ := fun x => rfl
  have hΛW : ∀ (k : ArchIsometryProd F) (x : orbitSpanc F hc), ΛW ⟨ρc F k x, hWinv k x x.2⟩ = ρc F k (ΛW x) := by
    intro k x
    rw [hΛW_def, hΛW_def]
    exact L.toEcf_ρc F hG0s k ⟨x, hWOc x.2⟩
  have hΛWcoe : ∀ x : orbitSpanc F hc, ((ΛW x : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) =
      L.raw ⟨(x : Ecf F), coe_mem_orbitSpan_of_mem_orbitSpanc F (hWOc x.2)⟩ := fun x => rfl

  let P : Submodule ℂ (Ecf F) := (LinearMap.ker ΛW).map (orbitSpanc F hc).subtype
  have hPW : P ≤ orbitSpanc F hc := Submodule.map_subtype_le _ _
  have hPinv : P ∈ (ρc F).invtSubmodule := by
    rw [Representation.mem_invtSubmodule]
    rintro k _ ⟨x, hx, rfl⟩
    have hx' : ΛW x = 0 := hx
    refine ⟨⟨ρc F k x, hWinv k x x.2⟩, ?_, rfl⟩
    show ΛW ⟨ρc F k x, _⟩ = 0
    rw [hΛW, hx', map_zero]
  obtain ⟨Pc, hPcinv, hPPc, hPsup⟩ :=
    exists_invt_compl F (orbitSpanc F hc) (orbitSpanc_mem_invtSubmodule F hc) P hPinv hPW
  have hPcinv' : ∀ (k : ArchIsometryProd F) (c : Ecf F), c ∈ Pc → ρc F k c ∈ Pc :=
    fun k c hcm => (Representation.mem_invtSubmodule (ρc F)).mp hPcinv k hcm
  have hPcW : Pc ≤ orbitSpanc F hc := by rw [← hPsup]; exact le_sup_right
  let Rc : Pc →ₗ[ℂ] Ecf F := ΛW ∘ₗ Submodule.inclusion hPcW
  have hRc_def : ∀ c : Pc, Rc c = ΛW ⟨c, hPcW c.2⟩ := fun c => rfl
  have hRc : ∀ (k : ArchIsometryProd F) (c : Pc), Rc ⟨ρc F k c, hPcinv' k c c.2⟩ = ρc F k (Rc c) := by
    intro k c
    rw [hRc_def, hRc_def]
    exact hΛW k ⟨c, hPcW c.2⟩
  have hRinj : Function.Injective Rc := by
    refine injective_of_forall_apply_eq_zero Pc (Ecf F) Rc fun c hc0 => ?_
    have hcP : (c : Ecf F) ∈ P := ⟨⟨c, hPcW c.2⟩, hc0, rfl⟩
    have hmem : (c : Ecf F) ∈ P ⊓ Pc := ⟨hcP, c.2⟩
    rw [hPPc, Submodule.mem_bot] at hmem
    exact Subtype.ext hmem
  have hPcA : ∀ c : Pc, ((c : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) ∈ archCutSubmodule F tys → c = 0 := by
    intro c hcA
    have h0 := hWA _ (coe_mem_orbitSpan_of_mem_orbitSpanc F (hPcW c.2)) hcA
    apply Subtype.ext; apply Subtype.ext; exact h0

  have hrange : ∀ x : orbitSpanc F hc, ∃ c : Pc, Rc c = ΛW x := by
    intro x
    have hx : (x : Ecf F) ∈ P ⊔ Pc := by rw [hPsup]; exact x.2
    obtain ⟨p, hp, c, hcm, hpc⟩ := Submodule.mem_sup.mp hx
    obtain ⟨p', hp', rfl⟩ := hp
    have hp'' : ΛW p' = 0 := hp'
    refine ⟨⟨c, hcm⟩, ?_⟩
    have hxe : x = p' + ⟨c, hPcW hcm⟩ := Subtype.ext hpc.symm
    rw [hRc_def, hxe, map_add, hp'', zero_add]

  have hΛhE : L.raw ⟨hc, hhO⟩ ∈ Ecf F := L.raw_mem_Ecf F hG0s ⟨hc, hhO⟩
  obtain ⟨hQA, hQO⟩ := h2 _ hΛhE
  have hΛh_eq : L.raw ⟨hc, hhO⟩ = ((ΛW ⟨hc, mem_orbitSpanc_self F hc⟩ : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) := by
    rw [hΛWcoe]
  obtain ⟨c₁, hc₁⟩ := hrange ⟨hc, mem_orbitSpanc_self F hc⟩
  have hmem : ∀ s ∈ orbitSpan F (L.raw ⟨hc, hhO⟩), ∃ c : Pc, ((Rc c : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) = s := by
    intro s hs
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hs
    · rintro _ ⟨k, rfl⟩
      refine ⟨⟨ρc F k c₁, hPcinv' k c₁ c₁.2⟩, ?_⟩
      rw [hRc, ρc_apply_coe, hc₁, ← hΛh_eq]
    · exact ⟨0, by rw [map_zero]; rfl⟩
    · rintro a b _ _ ⟨ca, rfl⟩ ⟨cb, rfl⟩
      exact ⟨ca + cb, by rw [map_add]; rfl⟩
    · rintro r a _ ⟨ca, rfl⟩
      exact ⟨r • ca, by rw [map_smul]; rfl⟩
  obtain ⟨c, hcq⟩ := hmem _ hQO
  rw [← hcq] at hQA ⊢
  rw [eq_zero_of_injective_equivariant tys Pc hPcinv' hPcA Rc hRc hRinj c hQA]
  rfl

theorem exists_rightConv_eq_of_projector (tys : ArchTypeFamily F)
    (Q : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ))
    (h1 : ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ → φ ∈ archCutSubmodule F tys → Q φ = φ)
    (h2 : ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ → FiniteDimensional ℂ (Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range), ψ = rightTranslate F k φ}) →
        Q φ ∈ archCutSubmodule F tys ⊓ Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range), ψ = rightTranslate F k φ})
    (h3 : ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ → FiniteDimensional ℂ (Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range), ψ = rightTranslate F k φ}) →
        ∀ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
          Q (rightTranslate F k φ) = rightTranslate F k (Q φ))
    {y : AdelicGL2 (𝓞 F) F → ℂ} (hyc : Continuous y) (hy : y ∈ archCutSubmodule F tys)
    {f : AdelicGL2 (𝓞 F) F → ℂ} (tys' : ArchTypeFamily F) (hf : IsFactorizableTestFn F f) (hbf : IsArchBiFinite F tys' f) :
    ∃ f' : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f' ∧ IsArchBiFinite F tys f' ∧ Q (rightConv F y f) = rightConv F y f' := by
  classical

  have h2' : ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, φ ∈ Ecf F → Q φ ∈ archCutSubmodule F tys ∧ Q φ ∈ orbitSpan F φ := by
    intro φ hφ
    have hfd : FiniteDimensional ℂ (Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range), ψ = rightTranslate F k φ}) := by
      rw [← orbitSpan_eq_span]; exact hφ.2
    obtain ⟨hA, hS⟩ := h2 φ hφ.1 hfd
    exact ⟨hA, by rw [orbitSpan_eq_span]; exact hS⟩
  have h3' : ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, φ ∈ Ecf F → ∀ k : ArchIsometryProd F, Q (archRep F k φ) = archRep F k (Q φ) := by
    intro φ hφ k
    have hfd : FiniteDimensional ℂ (Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range), ψ = rightTranslate F k φ}) := by
      rw [← orbitSpan_eq_span]; exact hφ.2
    rw [archRep_apply]
    exact h3 φ hφ.1 hfd _ (archProdIncl_mem_iSup F k)

  obtain ⟨hfc, hfs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hf
  have hG0A : reflL F f ∈ archCutSubmodule F tys' := hbf.1
  have hG0c : Continuous (reflL F f) := continuous_reflL F hfc
  have hG0s : HasCompactSupport (reflL F f) := hasCompactSupport_reflL F hfs
  have hG0E : reflL F f ∈ Ecf F := mem_Ecf_of_mem_archCut' F tys' hG0A hG0c
  set G0 : Ecf F := ⟨reflL F f, hG0E⟩ with hG0
  have hyE : y ∈ Ecf F := mem_Ecf_of_mem_archCut' F tys hy hyc
  obtain ⟨L⟩ := exists_lamData F ⟨y, hyE⟩ G0 hG0s
  have hconv : rightConv F y f = L.raw ⟨reflL F f, mem_orbitSpan_self F _⟩ := by
    rw [L.raw_apply, reflL_reflL]

  obtain ⟨hqA, hqO⟩ := h2' (reflL F f) hG0E
  have hqc : Continuous (Q (reflL F f)) := continuous_of_mem_orbitSpan F hG0c _ hqO
  have hqs : HasCompactSupport (Q (reflL F f)) := hasCompactSupport_of_mem_orbitSpan F hG0s _ hqO
  have hhO : reflL F f - Q (reflL F f) ∈ orbitSpan F (reflL F f) := Submodule.sub_mem _ (mem_orbitSpan_self F _) hqO
  have hQh : Q (reflL F f - Q (reflL F f)) = 0 := by
    rw [map_sub, h1 _ hqc hqA, sub_self]
  have hsplit : L.raw ⟨reflL F f, mem_orbitSpan_self F _⟩ = L.raw ⟨Q (reflL F f), hqO⟩ + L.raw ⟨_, hhO⟩ := by
    rw [← map_add]; congr 1; apply Subtype.ext; simp
  have hΛqA : L.raw ⟨Q (reflL F f), hqO⟩ ∈ archCutSubmodule F tys := L.raw_mem_archCutSubmodule tys hqO hqA
  have hΛqE : L.raw ⟨Q (reflL F f), hqO⟩ ∈ Ecf F := L.raw_mem_Ecf F hG0s ⟨_, hqO⟩
  have hQΛq : Q (L.raw ⟨Q (reflL F f), hqO⟩) = L.raw ⟨Q (reflL F f), hqO⟩ := h1 _ hΛqE.1 hΛqA
  have hQΛh : Q (L.raw ⟨_, hhO⟩) = 0 :=
    L.apply_raw_eq_zero hG0s tys Q h1 h2' h3' ⟨_, orbitSpan_le_Ecf F hG0E hhO⟩ hhO hQh
  have hQconv : Q (rightConv F y f) = rightConv F y (reflL F (Q (reflL F f))) := by
    rw [hconv, hsplit, map_add, hQΛq, hQΛh, add_zero, L.raw_apply]

  set q := Q (reflL F f) with hq
  obtain ⟨n, c, κ, hqsum⟩ := exists_eq_sum_of_mem_span_translates (archProdIncl F) (f := reflL F f) (h := q)
    (by exact hqO)
  have hf2 : reflL F q = fun x => ∑ j, c j * f ((archProdIncl F (κ j))⁻¹ * x * 1) := by
    funext x
    rw [reflL_apply, hqsum]
    simp only [reflL_apply, mul_inv_rev, inv_inv, mul_one]
  have hf2T : IsFactorizableTestFn F (reflL F q) := by
    rw [hf2]
    exact AutomorphicForm.isFactorizableTestFn_sum_mul_comp_mul_mul F hf c _ _
      (fun j => Subgroup.inv_mem _ (archProdIncl_mem_iSup F (κ j))) (fun _ => Subgroup.one_mem _)
  have hf2D : reflL F q ∈ archDualCutSubmodule F tys' := by
    have : reflL F q = ∑ j, c j • fun x => f ((archProdIncl F (κ j))⁻¹ * x) := by
      rw [hf2]; funext x; simp [Finset.sum_apply]
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (comp_mul_left_mem_archDualCutSubmodule F tys' hbf.2 _)
  have hf2c : Continuous (reflL F q) := continuous_reflL F hqc
  have hf2s : HasCompactSupport (reflL F q) := hasCompactSupport_reflL F hqs
  have hf2E : reflL F q ∈ Ecf F := mem_Ecf_of_mem_archDualCut' F tys' hf2D hf2c
  have hf2K : FiniteDimensional ℂ (Submodule.span ℂ
      {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
        ψ = rightTranslate F k (reflL F q)}) := by
    rw [← orbitSpan_eq_span]; exact hf2E.2

  obtain ⟨f3, hf3S, hf3D, hf3conv⟩ :=
    AutomorphicForm.exists_mem_span_rightTranslate_mem_archDualCutSubmodule_and_rightConv_eq F tys hyc hy hf2c hf2s hf2K
  rw [← orbitSpan_eq_span] at hf3S
  obtain ⟨m, c', κ', hf3sum⟩ := exists_eq_sum_of_mem_span_translates (archProdIncl F) (f := reflL F q) (h := f3)
    (by exact hf3S)
  refine ⟨f3, ?_, ⟨?_, hf3D⟩, ?_⟩
  · have : f3 = fun x => ∑ j, c' j * reflL F q (1 * x * archProdIncl F (κ' j)) := by
      rw [hf3sum]; funext x; simp only [one_mul]
    rw [this]
    exact AutomorphicForm.isFactorizableTestFn_sum_mul_comp_mul_mul F hf2T c' _ _
      (fun _ => Subgroup.one_mem _) (fun j => archProdIncl_mem_iSup F (κ' j))
  ·
    have : (fun x => f3 x⁻¹) = ∑ j, c' j • fun x => q ((archProdIncl F (κ' j))⁻¹ * x) := by
      rw [hf3sum]; funext x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, reflL_apply, mul_inv_rev, inv_inv]
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (comp_mul_left_mem_archCutSubmodule F tys hqA _)
  · rw [hQconv, hf3conv]

end PartTQC

end F4CutWords
p2m_reactivate "P2MW.S_AutomorphicForm_exists_rightConv_eq_of_archCutProjector.F4CutWords"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_rightConv_eq_of_archCutProjector.F4CutWords"

open F4CutWords in

theorem solution
    (F : Type) [Field F] [NumberField F] (tys : ArchTypeFamily F)
    (Q : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ))
    (hQ :
      (∀ φ : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ → φ ∈ archCutSubmodule F tys → Q φ = φ) ∧
      (∀ φ : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ →
        FiniteDimensional ℂ (Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range), ψ = rightTranslate F k φ}) →
        Q φ ∈ archCutSubmodule F tys ⊓ Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range), ψ = rightTranslate F k φ}) ∧
      (∀ φ : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ →
        FiniteDimensional ℂ (Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range), ψ = rightTranslate F k φ}) →
        ∀ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
          Q (rightTranslate F k φ) = rightTranslate F k (Q φ)))
    {y : AdelicGL2 (𝓞 F) F → ℂ} (hyc : Continuous y) (hy : y ∈ archCutSubmodule F tys)
    {f : AdelicGL2 (𝓞 F) F → ℂ} (tys' : ArchTypeFamily F) (hf : IsFactorizableTestFn F f) (hbf : IsArchBiFinite F tys' f) :
    ∃ f' : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f' ∧ IsArchBiFinite F tys f' ∧ Q (rightConv F y f) = rightConv F y f' :=
  F4CutWords.exists_rightConv_eq_of_projector F tys Q hQ.1 hQ.2.1 hQ.2.2 hyc hy tys' hf hbf

end S_AutomorphicForm_exists_rightConv_eq_of_archCutProjector
end P2MW
export P2MW.S_AutomorphicForm_exists_rightConv_eq_of_archCutProjector (solution)
