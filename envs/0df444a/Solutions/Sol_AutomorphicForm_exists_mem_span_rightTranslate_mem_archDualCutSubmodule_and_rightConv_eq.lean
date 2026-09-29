-- Prove2me | solution 1 for AutomorphicForm.exists_mem_span_rightTranslate_mem_archDualCutSubmodule_and_rightConv_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/36280687-66cd-5b96-ada9-9566a4117cc4

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_Representation_exists_isCompl_forall_mem_of_compactSpace_of_continuous
import Theorems.Thm_Representation_exists_extend_forall_apply_mul_of_injective
import Theorems.Thm_Representation_pairing_eq_zero_of_invariant_of_isSimpleOrder_of_exists_ne_zero
import Theorems.Thm_AutomorphicForm_le_iSup_typeSubmodule_dual_of_invariant_pairing
import Theorems.Thm_AutomorphicForm_le_iSup_typeSubmodule_of_surjective_of_le_iSup_typeSubmodule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_exists_mem_span_rightTranslate_mem_archDualCutSubmodule_and_rightConv_eq

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
      add_mem' := fun {a b} ha hb v => by have h__af := (ha v).add (hb v); simp at h__af ⊢; exact h__af
      smul_mem' := fun c {a} ha v => by have h__af := (ha v).const_smul c; simp at h__af ⊢; exact h__af }
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

open Representation in
set_option backward.isDefEq.respectTransparency false in

theorem isSemisimpleModule_ρc :
    IsSemisimpleModule (MonoidAlgebra ℂ (ArchIsometryProd F)) (ρc F).asModule := by
  classical
  let e := (ρc F).mapSubmodule
  let O : Ecf F → (ρc F).invtSubmodule := fun φ => ⟨orbitSpanc F φ, orbitSpanc_mem_invtSubmodule F φ⟩
  let p : Ecf F → Submodule (MonoidAlgebra ℂ (ArchIsometryProd F)) (ρc F).asModule := fun φ => e (O φ)
  refine isSemisimpleModule_of_isSemisimpleModule_submodule' (p := p) (fun φ => ?_) ?_
  ·
    rw [isSemisimpleModule_iff, (Submodule.mapIic (p φ)).complementedLattice_iff]
    refine ⟨fun q => ?_⟩
    obtain ⟨q, hq⟩ := q
    let T : (ρc F).invtSubmodule := e.symm q
    have hT : (T : Submodule ℂ (Ecf F)) ≤ orbitSpanc F φ := by
      have : T ≤ O φ := by
        have := e.symm.monotone hq
        simpa [T, p, e.symm_apply_apply] using this
      exact this
    obtain ⟨Pc, hPcinv, hinf, hsup⟩ :=
      exists_invt_compl F (orbitSpanc F φ) (orbitSpanc_mem_invtSubmodule F φ) T T.2 hT
    let Tc : (ρc F).invtSubmodule := ⟨Pc, hPcinv⟩
    have hTc : Tc ≤ O φ := by
      show (Pc : Submodule ℂ (Ecf F)) ≤ orbitSpanc F φ
      rw [← hsup]; exact le_sup_right
    have hq' : e T = q := e.apply_symm_apply q
    refine ⟨⟨e Tc, e.monotone hTc⟩, ?_, ?_⟩
    · rw [disjoint_iff]
      apply Subtype.ext
      show q ⊓ e Tc = ⊥
      rw [← hq', ← e.map_inf, ← e.map_bot]
      congr 1
      apply Subtype.ext
      show (T : Submodule ℂ (Ecf F)) ⊓ Pc = ⊥
      exact hinf
    · rw [codisjoint_iff]
      apply Subtype.ext
      show q ⊔ e Tc = p φ
      rw [← hq', ← e.map_sup]
      congr 1
      apply Subtype.ext
      show (T : Submodule ℂ (Ecf F)) ⊔ Pc = orbitSpanc F φ
      exact hsup
  ·
    rw [eq_top_iff]
    intro m _
    refine Submodule.mem_iSup_of_mem ((ρc F).asModuleEquiv m) ?_
    change m ∈ ((orbitSpanc F ((ρc F).asModuleEquiv m)).toAddSubmonoid.map
      ((ρc F).asModuleEquiv.symm : (Ecf F) →+ (ρc F).asModule))
    exact AddSubmonoid.mem_map.mpr ⟨(ρc F).asModuleEquiv m, mem_orbitSpanc_self F _,
      (ρc F).asModuleEquiv.symm_apply_apply m⟩

end PartB3

section PartB4

set_option backward.isDefEq.respectTransparency false

variable (F : Type) [Field F] [NumberField F]

open Representation

abbrev ℂK : Type := MonoidAlgebra ℂ (ArchIsometryProd F)

theorem isCompl_biSup_isotypicComponents (good : Set (isotypicComponents (ℂK F) (ρc F).asModule)) :
    IsCompl (⨆ c ∈ good, (c : Submodule (ℂK F) (ρc F).asModule))
      (⨆ c ∈ goodᶜ, (c : Submodule (ℂK F) (ρc F).asModule)) := by
  haveI := isSemisimpleModule_ρc F
  haveI : IsModularLattice (Submodule (ℂK F) (ρc F).asModule) :=
    @Submodule.instIsModularLattice (ℂK F) (ρc F).asModule _ inferInstance (ρc F).instModuleMonoidAlgebraAsModule
  haveI : IsCompactlyGenerated (Submodule (ℂK F) (ρc F).asModule) :=
    @Submodule.instIsCompactlyGenerated (ℂK F) (ρc F).asModule _ inferInstance (ρc F).instModuleMonoidAlgebraAsModule
  have hind : iSupIndep (Subtype.val : isotypicComponents (ℂK F) (ρc F).asModule → _) :=
    (sSupIndep_iff _).mp (sSupIndep_isotypicComponents (ℂK F) (ρc F).asModule)
  refine ⟨hind.disjoint_biSup_biSup disjoint_compl_right, ?_⟩
  rw [codisjoint_iff, eq_top_iff, ← sSup_isotypicComponents (ℂK F) (ρc F).asModule, sSup_eq_iSup']
  refine iSup_le fun c => ?_
  by_cases hc : c ∈ good
  · exact le_sup_of_le_left (le_biSup _ hc)
  · exact le_sup_of_le_right (le_biSup _ hc)

end PartB4

section PartB8

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

def placeOrbitSpan (w : InfinitePlace F) (φ : AdelicGL2 (𝓞 F) F → ℂ) : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
  Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ w.Completion => rightTranslate F (rowIsometryInclAt₀ F w k) φ)

theorem placeOrbitSpan_mono_of_mem {w : InfinitePlace F} {φ ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (Z : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hZ : ∀ k : rowIsometrySubgroup₀ w.Completion, ∀ z ∈ Z, rightTranslate F (rowIsometryInclAt₀ F w k) z ∈ Z)
    (hψ : ψ ∈ Z) : placeOrbitSpan F w ψ ≤ Z :=
  Submodule.span_le.mpr (by rintro _ ⟨k, rfl⟩; exact hZ k ψ hψ)

theorem finiteDimensional_placeOrbitSpan_of_mem_archTypeSubmoduleAt (w : InfinitePlace F) (τ : ArchRepAt F w)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ archTypeSubmoduleAt F w τ) :
    FiniteDimensional ℂ (placeOrbitSpan F w φ) := by
  refine Submodule.span_induction (p := fun φ _ => FiniteDimensional ℂ (placeOrbitSpan F w φ)) ?_ ?_ ?_ ?_ hφ
  · rintro f ⟨T, hT, v, rfl⟩

    have : placeOrbitSpan F w (T v) ≤ LinearMap.range T := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨k, rfl⟩
      refine ⟨τ.ρ k v, ?_⟩
      funext x; exact hT k v x
    exact Submodule.finiteDimensional_of_le this
  · have : placeOrbitSpan F w (0 : AdelicGL2 (𝓞 F) F → ℂ) ≤ ⊥ :=
      Submodule.span_le.mpr (by rintro _ ⟨k, rfl⟩; simp [rightTranslate_zero])
    exact Submodule.finiteDimensional_of_le this
  · intro a b _ _ ha hb
    have : placeOrbitSpan F w (a + b) ≤ placeOrbitSpan F w a ⊔ placeOrbitSpan F w b := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨k, rfl⟩
      show rightTranslate F _ (a + b) ∈ _
      rw [rightTranslate_add]
      exact Submodule.add_mem_sup (Submodule.subset_span ⟨k, rfl⟩) (Submodule.subset_span ⟨k, rfl⟩)
    exact Submodule.finiteDimensional_of_le this
  · intro c a _ ha
    have : placeOrbitSpan F w (c • a) ≤ placeOrbitSpan F w a := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨k, rfl⟩
      show rightTranslate F _ (c • a) ∈ _
      rw [rightTranslate_smul]
      exact Submodule.smul_mem _ c (Submodule.subset_span ⟨k, rfl⟩)
    exact Submodule.finiteDimensional_of_le this

theorem finiteDimensional_placeOrbitSpan_of_mem_archCutSubmodule (tys : ArchTypeFamily F) (w : InfinitePlace F)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ archCutSubmodule F tys) :
    FiniteDimensional ℂ (placeOrbitSpan F w φ) := by
  rw [mem_archCutSubmodule_iff] at hφ
  refine Submodule.iSup_induction _ (motive := fun φ => FiniteDimensional ℂ (placeOrbitSpan F w φ)) (hφ w)
    (fun i f hf => finiteDimensional_placeOrbitSpan_of_mem_archTypeSubmoduleAt F w _ hf) ?_ ?_
  · have : placeOrbitSpan F w (0 : AdelicGL2 (𝓞 F) F → ℂ) ≤ ⊥ :=
      Submodule.span_le.mpr (by rintro _ ⟨k, rfl⟩; simp [rightTranslate_zero])
    exact Submodule.finiteDimensional_of_le this
  · intro a b ha hb
    have : placeOrbitSpan F w (a + b) ≤ placeOrbitSpan F w a ⊔ placeOrbitSpan F w b := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨k, rfl⟩
      show rightTranslate F _ (a + b) ∈ _
      rw [rightTranslate_add]
      exact Submodule.add_mem_sup (Submodule.subset_span ⟨k, rfl⟩) (Submodule.subset_span ⟨k, rfl⟩)
    exact Submodule.finiteDimensional_of_le this

theorem mem_Ecf_of_mem_archCutSubmodule (tys : ArchTypeFamily F) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : φ ∈ archCutSubmodule F tys) (hc : Continuous φ) : φ ∈ Ecf F := by
  classical
  refine ⟨hc, ?_⟩

  have key : ∀ s : Finset (InfinitePlace F), ∃ Z : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ),
      FiniteDimensional ℂ Z ∧ φ ∈ Z ∧ Z ≤ archCutSubmodule F tys ∧
      ∀ w ∈ s, ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ z ∈ Z, rightTranslate F (rowIsometryInclAt₀ F w k) z ∈ Z := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨Submodule.span ℂ {φ}, inferInstance, Submodule.subset_span rfl,
        Submodule.span_le.mpr (by simpa using hφ), by simp⟩
    | @insert w s hw ih =>
      obtain ⟨Z, hZfd, hφZ, hZA, hZst⟩ := ih
      let Z' : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
        ⨆ k : rowIsometrySubgroup₀ w.Completion, Z.map (rightRegular F (rowIsometryInclAt₀ F w k))
      have hgen : ∀ (k : rowIsometrySubgroup₀ w.Completion) (z), z ∈ Z →
          rightTranslate F (rowIsometryInclAt₀ F w k) z ∈ Z' := fun k z hz =>
        Submodule.mem_iSup_of_mem k ⟨z, hz, rfl⟩
      refine ⟨Z', ?_, ?_, ?_, ?_⟩
      ·
        let b := Module.finBasis ℂ Z
        have hle : Z' ≤ ⨆ i, placeOrbitSpan F w (b i : AdelicGL2 (𝓞 F) F → ℂ) := by
          refine iSup_le fun k => Submodule.map_le_iff_le_comap.mpr fun z hz => ?_
          rw [Submodule.mem_comap]
          have hz' : (⟨z, hz⟩ : Z) ∈ Submodule.span ℂ (Set.range b) := by rw [b.span_eq]; trivial
          have : z ∈ Submodule.span ℂ (Set.range fun i => (b i : AdelicGL2 (𝓞 F) F → ℂ)) := by
            have := Submodule.mem_map_of_mem (f := Z.subtype) hz'
            rw [Submodule.map_span, ← Set.range_comp] at this
            exact this
          refine Submodule.span_induction ?_ ?_ ?_ ?_ this
          · rintro _ ⟨i, rfl⟩
            exact Submodule.mem_iSup_of_mem i (Submodule.subset_span ⟨k, rfl⟩)
          · show rightTranslate F (rowIsometryInclAt₀ F w k) 0 ∈ _
            rw [rightTranslate_zero]; exact Submodule.zero_mem _
          · intro a c _ _ ha hc
            show rightTranslate F _ (a + c) ∈ _
            rw [rightTranslate_add]; exact Submodule.add_mem _ ha hc
          · intro c a _ ha
            show rightTranslate F _ (c • a) ∈ _
            rw [rightTranslate_smul]; exact Submodule.smul_mem _ c ha
        haveI : ∀ i, FiniteDimensional ℂ (placeOrbitSpan F w (b i : AdelicGL2 (𝓞 F) F → ℂ)) := fun i =>
          finiteDimensional_placeOrbitSpan_of_mem_archCutSubmodule F tys w (hZA (b i).2)
        exact Submodule.finiteDimensional_of_le hle
      · have := hgen 1 φ hφZ
        rwa [map_one, show rightTranslate F (1 : AdelicGL2 (𝓞 F) F) φ = φ from funext fun x => by simp [rightTranslate]]
          at this
      · refine iSup_le fun k => Submodule.map_le_iff_le_comap.mpr fun z hz => ?_
        rw [Submodule.mem_comap]
        exact comp_mul_rowIsometryInclAt₀_mem_archCutSubmodule F (hZA hz) w k
      · intro w' hw' k'
        refine fun z hz => Submodule.iSup_induction _
          (motive := fun z => rightTranslate F (rowIsometryInclAt₀ F w' k') z ∈ Z') hz ?_ ?_ ?_
        · rintro k _ ⟨z₀, hz₀, rfl⟩
          show rightTranslate F (rowIsometryInclAt₀ F w' k') (rightTranslate F (rowIsometryInclAt₀ F w k) z₀) ∈ Z'
          rcases Finset.mem_insert.mp hw' with rfl | hw's
          · rw [rightTranslate_rightTranslate, ← map_mul]
            exact hgen _ z₀ hz₀
          · have hne : w' ≠ w := fun h => hw (h ▸ hw's)
            rw [rightTranslate_rightTranslate, rowIsometryInclAt₀_apply, rowIsometryInclAt₀_apply,
              (commute_adelicArchGLInclAt_of_ne F hne _ _).eq, ← rightTranslate_rightTranslate]
            exact hgen k _ (hZst w' hw's k' z₀ hz₀)
        · show rightTranslate F _ 0 ∈ Z'
          rw [rightTranslate_zero]; exact Submodule.zero_mem _
        · intro a c ha hc; rw [rightTranslate_add]; exact Submodule.add_mem _ ha hc
  obtain ⟨Z, hZfd, hφZ, -, hZst⟩ := key Finset.univ
  have hsub : orbitSpan F φ ≤ Z := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    show archRep F k φ ∈ Z
    rw [archRep_apply]
    refine rightTranslate_mem_of_mem_iSup_range' F Z (fun w k z hz => hZst w (Finset.mem_univ w) k z hz) ?_ φ hφZ
    rw [← archProdIncl_range]; exact ⟨k, rfl⟩
  exact Submodule.finiteDimensional_of_le hsub

end PartB8

section PartB6

variable (F : Type) [Field F] [NumberField F]

theorem archProdIncl_mem_iSup (k : ArchIsometryProd F) :
    archProdIncl F k ∈ ⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range := by
  rw [← archProdIncl_range]; exact ⟨k, rfl⟩

end PartB6

section FarmE26

theorem le_biSup_isotypicComponents_of_forall_linearEquiv_le
    {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M] [IsSemisimpleModule R M]
    (A : Submodule R M)
    (hA : ∀ (m m' : Submodule R M), IsSimpleModule R m → Nonempty (m ≃ₗ[R] m') → m ≤ A → m' ≤ A) :
    A ≤ ⨆ c ∈ {c : isotypicComponents R M | (c : Submodule R M) ≤ A}, (c : Submodule R M) := by
  conv_lhs => rw [← IsSemisimpleModule.sSup_simples_le (R := R) (M := M) A]
  refine sSup_le fun T ⟨hT, hTA⟩ => ?_
  haveI := hT

  have hcA : isotypicComponent R M T ≤ A := sSup_le fun m ⟨e⟩ => hA T m hT ⟨e.symm⟩ hTA
  have hc : isotypicComponent R M T ∈ isotypicComponents R M := ⟨T, hT, rfl⟩
  exact T.le_isotypicComponent.trans
    (le_biSup (fun c : isotypicComponents R M => (c : Submodule R M)) (i := ⟨_, hc⟩) hcA)

end FarmE26

section FarmE26C3

open scoped MonoidAlgebra

section
variable {k : Type*} [Field k] {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module k V]

private def restrictEquiv (ρ : Representation k G V) (N : Submodule (MonoidAlgebra k G) ρ.asModule) :
    ↥(N.restrictScalars k) ≃ₗ[k] ↥N where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

set_option backward.isDefEq.respectTransparency false in

theorem exists_linearEquiv_map_asModuleEquiv_of_linearEquiv
    (ρ : Representation k G V) (N N' : Submodule (MonoidAlgebra k G) ρ.asModule)
    (e : N ≃ₗ[MonoidAlgebra k G] N') :
    ∃ (hS : ∀ (g : G), ∀ v ∈ (N.restrictScalars k).map ρ.asModuleEquiv.toLinearMap,
          ρ g v ∈ (N.restrictScalars k).map ρ.asModuleEquiv.toLinearMap)
      (θ : ((N.restrictScalars k).map ρ.asModuleEquiv.toLinearMap) ≃ₗ[k]
          ((N'.restrictScalars k).map ρ.asModuleEquiv.toLinearMap)),
      ∀ (g : G) (s : (N.restrictScalars k).map ρ.asModuleEquiv.toLinearMap),
        ((θ ⟨ρ g s, hS g s s.2⟩ : (N'.restrictScalars k).map ρ.asModuleEquiv.toLinearMap) : V) = ρ g (θ s : V) := by

  have hstab : ∀ (M : Submodule (MonoidAlgebra k G) ρ.asModule) (g : G),
      ∀ v ∈ (M.restrictScalars k).map ρ.asModuleEquiv.toLinearMap, ρ g v ∈ (M.restrictScalars k).map ρ.asModuleEquiv.toLinearMap := by
    intro M g v hv
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hv
    refine Submodule.mem_map.mpr ⟨MonoidAlgebra.of k G g • x, M.smul_mem _ hx, ?_⟩
    change ρ.asModuleEquiv (MonoidAlgebra.of k G g • x) = ρ g (ρ.asModuleEquiv x)
    rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]

  let θ : ((N.restrictScalars k).map ρ.asModuleEquiv.toLinearMap) ≃ₗ[k] ((N'.restrictScalars k).map ρ.asModuleEquiv.toLinearMap) :=
    (ρ.asModuleEquiv.submoduleMap (N.restrictScalars k)).symm
      ≪≫ₗ restrictEquiv ρ N ≪≫ₗ e.restrictScalars k ≪≫ₗ (restrictEquiv ρ N').symm
      ≪≫ₗ ρ.asModuleEquiv.submoduleMap (N'.restrictScalars k)
  have hθ : ∀ s : (N.restrictScalars k).map ρ.asModuleEquiv.toLinearMap,
      ((θ s : (N'.restrictScalars k).map ρ.asModuleEquiv.toLinearMap) : V) =
        ρ.asModuleEquiv ((e ⟨ρ.asModuleEquiv.symm (s : V),
          by obtain ⟨x, hx, hxs⟩ := Submodule.mem_map.mp s.2; rw [← hxs]; simpa using hx⟩ : N') : ρ.asModule) := by
    intro s
    rfl
  refine ⟨hstab N, θ, fun g s => ?_⟩
  rw [hθ, hθ]

  have h1 : (⟨ρ.asModuleEquiv.symm (ρ g (s : V)), by
        obtain ⟨x, hx, hxs⟩ := Submodule.mem_map.mp (hstab N g s s.2); rw [← hxs]; simpa using hx⟩ : N) =
      MonoidAlgebra.of k G g • ⟨ρ.asModuleEquiv.symm (s : V), by
        obtain ⟨x, hx, hxs⟩ := Submodule.mem_map.mp s.2; rw [← hxs]; simpa using hx⟩ := by
    apply Subtype.ext
    change ρ.asModuleEquiv.symm (ρ g (s : V)) = MonoidAlgebra.of k G g • ρ.asModuleEquiv.symm (s : V)
    exact Representation.asModuleEquiv_symm_map_rho ρ g (s : V)
  rw [h1, map_smul, Submodule.coe_smul, Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]

end

end FarmE26C3

section FarmE25

open IsSemisimpleModule

theorem exists_add_eq_of_isCompl_biSup_isotypicComponents {R : Type*} [Ring R] {M : Type*} [AddCommGroup M]
    [Module R M] [IsSemisimpleModule R M] (good : Set (isotypicComponents R M))
    (hc : IsCompl (⨆ c ∈ good, (c : Submodule R M)) (⨆ c ∈ goodᶜ, (c : Submodule R M)))
    (N : Submodule R M) (x : M) (hx : x ∈ N) :
    ∃ a ∈ N ⊓ ⨆ c ∈ good, (c : Submodule R M), ∃ b ∈ N ⊓ ⨆ c ∈ goodᶜ, (c : Submodule R M), x = a + b := by

  have hN : N ≤ (N ⊓ ⨆ c ∈ good, (c : Submodule R M)) ⊔ (N ⊓ ⨆ c ∈ goodᶜ, (c : Submodule R M)) := by
    conv_lhs => rw [← sSup_simples_le N]
    refine sSup_le ?_
    rintro T ⟨hT, hTN⟩
    haveI := hT
    let cT : isotypicComponents R M := ⟨isotypicComponent R M T, ⟨T, hT, rfl⟩⟩
    have hTc : T ≤ (cT : Submodule R M) := T.le_isotypicComponent
    by_cases hg : cT ∈ good
    · refine le_sup_of_le_left (le_inf hTN (hTc.trans ?_))
      exact le_biSup (fun c : isotypicComponents R M => (c : Submodule R M)) hg
    · refine le_sup_of_le_right (le_inf hTN (hTc.trans ?_))
      exact le_biSup (fun c : isotypicComponents R M => (c : Submodule R M)) (Set.mem_compl hg)
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (hN hx)
  exact ⟨a, ha, b, hb, hab.symm⟩

theorem exists_eq_span_singleton_of_isSimpleModule {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
    (T : Submodule R M) [IsSimpleModule R T] : ∃ t : M, t ∈ T ∧ T = R ∙ t := by
  have hne : T ≠ ⊥ := by
    intro h
    have := IsSimpleModule.nontrivial R T
    rw [Submodule.nontrivial_iff_ne_bot] at this
    exact this h
  obtain ⟨t, htT, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨t, htT, ?_⟩
  have hatom : IsAtom T := isSimpleModule_iff_isAtom.mp inferInstance
  have hle : R ∙ t ≤ T := (Submodule.span_singleton_le_iff_mem t T).mpr htT
  rcases hatom.le_iff.mp hle with h | h
  · exact absurd (Submodule.span_singleton_eq_bot.mp h) ht0
  · exact h.symm

end FarmE25

section PartB7

set_option backward.isDefEq.respectTransparency false

variable (F : Type) [Field F] [NumberField F]

open Representation

theorem mem_mapSubmodule_iff {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
    (ρ : Representation k G V) (p : ρ.invtSubmodule) (x : ρ.asModule) :
    x ∈ ρ.mapSubmodule p ↔ ρ.asModuleEquiv x ∈ (p : Submodule k V) := by
  change x ∈ ((p : Submodule k V).toAddSubmonoid.map (ρ.asModuleEquiv.symm : V →+ ρ.asModule)) ↔ _
  rw [AddSubmonoid.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩; simpa using hv
  · intro h; exact ⟨ρ.asModuleEquiv x, h, by simp⟩

open scoped Classical in

theorem archProdIncl_mulSingle (w : InfinitePlace F) (kw : rowIsometrySubgroup₀ w.Completion) :
    archProdIncl F (Pi.mulSingle w kw) = rowIsometryInclAt₀ F w kw := by
  classical
  unfold archProdIncl
  exact MonoidHom.noncommPiCoprod_mulSingle (fun v => rowIsometryInclAt₀ F v) w kw

abbrev underSub (N : Submodule (ℂK F) (ρc F).asModule) : Submodule ℂ (Ecf F) :=
  (N.restrictScalars ℂ).map (ρc F).asModuleEquiv.toLinearMap

theorem mem_underSub_iff (N : Submodule (ℂK F) (ρc F).asModule) (v : Ecf F) :
    v ∈ underSub F N ↔ (ρc F).asModuleEquiv.symm v ∈ N := by
  constructor
  · rintro ⟨x, hx, rfl⟩; simpa using hx
  · intro h; exact ⟨(ρc F).asModuleEquiv.symm v, h, by simp⟩

theorem finiteDimensional_underSub_of_eq_span (N : Submodule (ℂK F) (ρc F).asModule) (t : (ρc F).asModule)
    (hNt : N = Submodule.span (ℂK F) {t}) :
    FiniteDimensional ℂ (underSub F N) := by

  let t' : Ecf F := (ρc F).asModuleEquiv t
  have hle : N ≤ (ρc F).mapSubmodule ⟨orbitSpanc F t', orbitSpanc_mem_invtSubmodule F t'⟩ := by
    rw [hNt]
    refine (Submodule.span_singleton_le_iff_mem _ _).mpr ?_
    rw [mem_mapSubmodule_iff]
    exact mem_orbitSpanc_self F t'
  have : underSub F N ≤ orbitSpanc F t' := by
    intro v hv
    rw [mem_underSub_iff] at hv
    have := hle hv
    rw [mem_mapSubmodule_iff] at this
    simpa using this
  exact Submodule.finiteDimensional_of_le this

end PartB7

section PartC2

set_option backward.isDefEq.respectTransparency false

variable (F : Type) [Field F] [NumberField F]

open Representation

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

end PartC2

section FarmC3G1G2

open scoped MonoidAlgebra

namespace Representation

variable {k : Type*} [Field k] {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module k V]

def restrictRep (ρ : _root_.Representation k G V) (S : Submodule k V) (hS : ∀ (g : G), ∀ v ∈ S, ρ g v ∈ S) :
    _root_.Representation k G S where
  toFun g := (ρ g).restrict (fun v hv => hS g v hv)
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

@[scoped simp] theorem restrictRep_apply_coe (ρ : _root_.Representation k G V) (S : Submodule k V)
    (hS : ∀ (g : G), ∀ v ∈ S, ρ g v ∈ S) (g : G) (v : S) : ((restrictRep ρ S hS g v : S) : V) = ρ g v := rfl

def restrictInvt (ρ : _root_.Representation k G V) (p : ρ.invtSubmodule) : _root_.Representation k G (p : Submodule k V) :=
  restrictRep ρ p fun g v hv => (Module.End.mem_invtSubmodule _).mp ((ρ.mem_invtSubmodule).mp p.2 g) hv

@[scoped simp] theorem restrictInvt_apply_coe (ρ : _root_.Representation k G V) (p : ρ.invtSubmodule) (g : G) (v : (p : Submodule k V)) :
    ((restrictInvt ρ p g v : (p : Submodule k V)) : V) = ρ g v := rfl

set_option backward.isDefEq.respectTransparency false in

theorem coe_asAlgebraHom_restrictRep (ρ : _root_.Representation k G V) (S : Submodule k V)
    (hS : ∀ (g : G), ∀ v ∈ S, ρ g v ∈ S) (r : MonoidAlgebra k G) (y : S) :
    (((restrictRep ρ S hS).asAlgebraHom r y : S) : V) = ρ.asAlgebraHom r (y : V) := by
  induction r using MonoidAlgebra.induction_on with
  | of g =>
      rw [_root_.Representation.asAlgebraHom_of, _root_.Representation.asAlgebraHom_of]
      rfl
  | add a b ha hb => rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, Submodule.coe_add, ha, hb]
  | smul c a ha => rw [map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, Submodule.coe_smul, ha]

set_option backward.isDefEq.respectTransparency false in

theorem exists_linearEquiv_asModule_mapSubmodule (ρ : _root_.Representation k G V) (p : ρ.invtSubmodule) :
    ∃ e : (restrictInvt ρ p).asModule ≃ₗ[MonoidAlgebra k G] ↥(ρ.mapSubmodule p),
      ∀ x : (restrictInvt ρ p).asModule,
        ((e x : ρ.mapSubmodule p) : ρ.asModule) =
          ρ.asModuleEquiv.symm (((restrictInvt ρ p).asModuleEquiv x : (p : Submodule k V)) : V) := by
  let π := restrictInvt ρ p
  have hmem : ∀ x : π.asModule,
      ρ.asModuleEquiv.symm ((π.asModuleEquiv x : (p : Submodule k V)) : V) ∈ ρ.mapSubmodule p := fun x =>
    ⟨((π.asModuleEquiv x : (p : Submodule k V)) : V), (π.asModuleEquiv x).2, rfl⟩
  have hmem' : ∀ y : ρ.mapSubmodule p, ρ.asModuleEquiv (y : ρ.asModule) ∈ (p : Submodule k V) := by
    rintro ⟨y, ⟨v, hv, rfl⟩⟩
    simpa using hv
  let e : π.asModule ≃ₗ[MonoidAlgebra k G] ↥(ρ.mapSubmodule p) :=
    { toFun := fun x => ⟨_, hmem x⟩
      invFun := fun y => π.asModuleEquiv.symm ⟨ρ.asModuleEquiv (y : ρ.asModule), hmem' y⟩
      map_add' := fun x y => by
        apply Subtype.ext
        simp only [map_add, Submodule.coe_add]
      map_smul' := fun r x => by
        apply Subtype.ext
        change ρ.asModuleEquiv.symm ((π.asModuleEquiv (r • x) : (p : Submodule k V)) : V) =
          r • ρ.asModuleEquiv.symm ((π.asModuleEquiv x : (p : Submodule k V)) : V)
        rw [LinearEquiv.symm_apply_eq, _root_.Representation.asModuleEquiv_map_smul,
          _root_.Representation.asModuleEquiv_map_smul, LinearEquiv.apply_symm_apply]
        exact coe_asAlgebraHom_restrictRep ρ p _ r (π.asModuleEquiv x)
      left_inv := fun x => by simp
      right_inv := fun y => by apply Subtype.ext; simp }
  exact ⟨e, fun x => rfl⟩

set_option backward.isDefEq.respectTransparency false in

theorem isIrreducible_of_isSimpleModule (ρ : _root_.Representation k G V) (T : Submodule (MonoidAlgebra k G) ρ.asModule)
    [IsSimpleModule (MonoidAlgebra k G) T]
    (hS : ∀ (g : G), ∀ v ∈ (T.restrictScalars k).map ρ.asModuleEquiv.toLinearMap,
      ρ g v ∈ (T.restrictScalars k).map ρ.asModuleEquiv.toLinearMap) :
    _root_.Representation.IsIrreducible (restrictRep ρ ((T.restrictScalars k).map ρ.asModuleEquiv.toLinearMap) hS) := by

  let p : ρ.invtSubmodule := ⟨(T.restrictScalars k).map ρ.asModuleEquiv.toLinearMap, by
    rw [_root_.Representation.mem_invtSubmodule]
    intro g
    rw [Module.End.mem_invtSubmodule]
    intro v hv
    exact hS g v hv⟩
  have hpT : ρ.mapSubmodule p = T := by
    apply le_antisymm
    · rintro x ⟨v, hv, rfl⟩
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hv
      simpa using hy
    · intro x hx
      refine ⟨ρ.asModuleEquiv x, Submodule.mem_map.mpr ⟨x, hx, rfl⟩, ?_⟩
      simp
  have hπ : restrictRep ρ ((T.restrictScalars k).map ρ.asModuleEquiv.toLinearMap) hS = restrictInvt ρ p := rfl
  rw [hπ, _root_.Representation.irreducible_iff_isSimpleModule_asModule]
  obtain ⟨e, -⟩ := exists_linearEquiv_asModule_mapSubmodule ρ p
  haveI : IsSimpleModule (MonoidAlgebra k G) ↥(ρ.mapSubmodule p) := by rw [hpT]; infer_instance
  exact IsSimpleModule.congr e

end Representation
p2m_reactivate "P2MW.S_AutomorphicForm_exists_mem_span_rightTranslate_mem_archDualCutSubmodule_and_rightConv_eq.F4CutWords.Representation"

end FarmC3G1G2
p2m_reactivate "P2MW.S_AutomorphicForm_exists_mem_span_rightTranslate_mem_archDualCutSubmodule_and_rightConv_eq.F4CutWords.Representation"

section PartC3

set_option backward.isDefEq.respectTransparency false

variable (F : Type) [Field F] [NumberField F]

open Representation

private abbrev c3GMeas : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F

attribute [local instance] c3GMeas

private theorem c3GBorel : BorelSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F

attribute [local instance] c3GBorel

private theorem c3GHaar : (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure :=
  AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F

attribute [local instance] c3GHaar

private theorem c3_integrable_mul {ψ f : AdelicGL2 (𝓞 F) F → ℂ} (hψ : Continuous ψ)
    (hf : Continuous f) (hfs : HasCompactSupport f) (x : AdelicGL2 (𝓞 F) F) :
    MeasureTheory.Integrable (fun y => ψ (x * y) * f y) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) :=
  ((hψ.comp (continuous_const.mul continuous_id)).mul hf).integrable_of_hasCompactSupport hfs.mul_left

private theorem c3_rightConv_add_right {ψ f g : AdelicGL2 (𝓞 F) F → ℂ} (hψ : Continuous ψ)
    (hf : Continuous f) (hfs : HasCompactSupport f) (hg : Continuous g) (hgs : HasCompactSupport g) :
    rightConv F ψ (f + g) = rightConv F ψ f + rightConv F ψ g := by
  funext x
  rw [Pi.add_apply, rightConv_apply, rightConv_apply, rightConv_apply,
    ← MeasureTheory.integral_add (c3_integrable_mul F hψ hf hfs x) (c3_integrable_mul F hψ hg hgs x)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show ψ (x * y) * (f y + g y) = ψ (x * y) * f y + ψ (x * y) * g y
  ring

private theorem c3_rightConv_smul_right (c : ℂ) (ψ f : AdelicGL2 (𝓞 F) F → ℂ) :
    rightConv F ψ (c • f) = c • rightConv F ψ f := by
  funext x
  rw [Pi.smul_apply, smul_eq_mul, rightConv_apply, rightConv_apply, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show ψ (x * y) * (c * f y) = c * (ψ (x * y) * f y)
  ring

private theorem c3_rightConv_smul_left (c : ℂ) (ψ f : AdelicGL2 (𝓞 F) F → ℂ) :
    rightConv F (c • ψ) f = c • rightConv F ψ f := by
  funext x
  rw [Pi.smul_apply, smul_eq_mul, rightConv_apply, rightConv_apply, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show c * ψ (x * y) * f y = c * (ψ (x * y) * f y)
  ring

private theorem c3_exists_bilin_eval_fun (S T : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hS : ∀ s ∈ S, Continuous s) (hT : ∀ t ∈ T, Continuous t ∧ HasCompactSupport t) (x0 : AdelicGL2 (𝓞 F) F) :
    ∃ β : S →ₗ[ℂ] T →ₗ[ℂ] ℂ, ∀ (s : S) (t : T),
      β s t = rightConv F (s : AdelicGL2 (𝓞 F) F → ℂ) (t : AdelicGL2 (𝓞 F) F → ℂ) x0 := by
  refine ⟨LinearMap.mk₂ ℂ (fun (s : S) (t : T) => rightConv F (s : AdelicGL2 (𝓞 F) F → ℂ) (t : AdelicGL2 (𝓞 F) F → ℂ) x0)
    ?_ ?_ ?_ ?_, fun s t => rfl⟩
  · intro s s' t
    rw [Submodule.coe_add, rightConv_add_left F (hS s s.2) (hS s' s'.2) (hT t t.2).1 (hT t t.2).2, Pi.add_apply]
  · intro c s t
    rw [Submodule.coe_smul, c3_rightConv_smul_left F c, Pi.smul_apply]
  · intro s t t'
    rw [Submodule.coe_add, c3_rightConv_add_right F (hS s s.2) (hT t t.2).1 (hT t t.2).2 (hT t' t'.2).1 (hT t' t'.2).2,
      Pi.add_apply]
  · intro c s t
    rw [Submodule.coe_smul, c3_rightConv_smul_right F c, Pi.smul_apply]

private theorem c3_exists_bilin_eval (S T : Submodule ℂ (Ecf F))
    (hT : ∀ t ∈ T, HasCompactSupport ((t : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ)) (x0 : AdelicGL2 (𝓞 F) F) :
    ∃ β : S →ₗ[ℂ] T →ₗ[ℂ] ℂ, ∀ (s : S) (t : T),
      β s t = rightConv F ((s : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) ((t : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) x0 := by
  refine ⟨LinearMap.mk₂ ℂ
    (fun (s : S) (t : T) => rightConv F ((s : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) ((t : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) x0)
    ?_ ?_ ?_ ?_, fun s t => rfl⟩
  · intro s s' t
    rw [Submodule.coe_add, Submodule.coe_add,
      rightConv_add_left F (s : Ecf F).2.1 (s' : Ecf F).2.1 (t : Ecf F).2.1 (hT t t.2), Pi.add_apply]
  · intro c s t
    rw [Submodule.coe_smul, Submodule.coe_smul, c3_rightConv_smul_left F c, Pi.smul_apply]
  · intro s t t'
    beta_reduce
    rw [Submodule.coe_add, Submodule.coe_add,
      c3_rightConv_add_right F (s : Ecf F).2.1 (t : Ecf F).2.1 (hT t t.2) (t' : Ecf F).2.1 (hT t' t'.2), Pi.add_apply]
  · intro c s t
    beta_reduce
    rw [Submodule.coe_smul, Submodule.coe_smul, c3_rightConv_smul_right F c, Pi.smul_apply]

theorem rowIsometryInclAt₀_injective (w : InfinitePlace F) : Function.Injective (rowIsometryInclAt₀ F w) := by
  intro a c hac
  apply Subtype.ext
  apply Units.ext
  ext i j' : 1
  have := congrArg (fun g : AdelicGL2 (𝓞 F) F => ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j').1 w) hac
  simp only [rowIsometryInclAt₀_apply, val_adelicArchGLInclAt_apply, archMatrixUpdate_apply_self] at this
  exact this

theorem comp_mul_rowIsometryInclAt₀_mem_archDualCutSubmodule {tys : ArchTypeFamily F}
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : f ∈ archDualCutSubmodule F tys) (w : InfinitePlace F)
    (k : rowIsometrySubgroup₀ w.Completion) :
    (fun x => f (x * rowIsometryInclAt₀ F w k)) ∈ archDualCutSubmodule F tys := by
  rw [mem_archDualCutSubmodule_iff] at hf ⊢
  intro w'
  refine Submodule.iSup_induction _
    (motive := fun f => (fun x => f (x * rowIsometryInclAt₀ F w k)) ∈
      ⨆ i : Fin (tys.card w'), archDualTypeSubmoduleAt F w' (tys.rep w' i)) (hf w') ?_ ?_ ?_
  · intro i f hfi
    refine le_iSup (fun j => archDualTypeSubmoduleAt F w' (tys.rep w' j)) i ?_
    by_cases hw : w' = w
    · subst hw
      exact comp_mul_mem_typeSubmodule hfi k
    · exact comp_mul_mem_typeSubmodule_of_commute hfi _ fun k' =>
        commute_adelicArchGLInclAt_of_ne F (fun h => hw h.symm) _ _
  · exact Submodule.zero_mem _
  · exact fun _ _ hu hw => Submodule.add_mem _ hu hw

def cutDc (tys : ArchTypeFamily F) : Submodule ℂ (Ecf F) := (archDualCutSubmodule F tys).comap (Ecf F).subtype

theorem mem_cutDc {tys : ArchTypeFamily F} {φ : Ecf F} :
    φ ∈ cutDc F tys ↔ (φ : AdelicGL2 (𝓞 F) F → ℂ) ∈ archDualCutSubmodule F tys := Iff.rfl

theorem cutDc_mem_invtSubmodule (tys : ArchTypeFamily F) : cutDc F tys ∈ (ρc F).invtSubmodule := by
  rw [Representation.mem_invtSubmodule]
  intro k φ hφ
  show ((ρc F k φ : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) ∈ archDualCutSubmodule F tys
  rw [ρc_apply_coe, archRep_apply]
  exact rightTranslate_mem_of_mem_iSup_range' F (archDualCutSubmodule F tys)
    (fun w k φ hφ => comp_mul_rowIsometryInclAt₀_mem_archDualCutSubmodule F hφ w k) (archProdIncl_mem_iSup F k) _ hφ

def cutDM (tys : ArchTypeFamily F) : Submodule (ℂK F) (ρc F).asModule :=
  (ρc F).mapSubmodule ⟨cutDc F tys, cutDc_mem_invtSubmodule F tys⟩

theorem mem_cutDM_iff (tys : ArchTypeFamily F) (x : (ρc F).asModule) :
    x ∈ cutDM F tys ↔ (((ρc F).asModuleEquiv x : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) ∈ archDualCutSubmodule F tys :=
  mem_mapSubmodule_iff (ρc F) _ x

def goodComponentsD (tys : ArchTypeFamily F) : Set (isotypicComponents (ℂK F) (ρc F).asModule) :=
  {c | (c : Submodule (ℂK F) (ρc F).asModule) ≤ cutDM F tys}

def CAD (tys : ArchTypeFamily F) : Submodule (ℂK F) (ρc F).asModule :=
  ⨆ c ∈ goodComponentsD F tys, (c : Submodule (ℂK F) (ρc F).asModule)

def CBD (tys : ArchTypeFamily F) : Submodule (ℂK F) (ρc F).asModule :=
  ⨆ c ∈ (goodComponentsD F tys)ᶜ, (c : Submodule (ℂK F) (ρc F).asModule)

theorem isCompl_CAD_CBD (tys : ArchTypeFamily F) : IsCompl (CAD F tys) (CBD F tys) :=
  isCompl_biSup_isotypicComponents F (goodComponentsD F tys)

theorem CAD_le_cutDM (tys : ArchTypeFamily F) : CAD F tys ≤ cutDM F tys :=
  iSup₂_le fun c hc => hc

theorem ρc_mem_underSub (N : Submodule (ℂK F) (ρc F).asModule) (g : ArchIsometryProd F) {v : Ecf F}
    (hv : v ∈ underSub F N) : ρc F g v ∈ underSub F N := by
  rw [mem_underSub_iff] at hv ⊢
  rw [Representation.asModuleEquiv_symm_map_rho]
  exact N.smul_mem _ hv

open scoped Classical in

theorem coe_ρc_mulSingle (w : InfinitePlace F) (kw : rowIsometrySubgroup₀ w.Completion) (v : Ecf F) :
    ((ρc F (Pi.mulSingle w kw) v : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) =
      rightTranslate F (rowIsometryInclAt₀ F w kw) v := by
  classical
  rw [ρc_apply_coe, archRep_apply, archProdIncl_mulSingle]

theorem rightTranslate_mem_map_subtype_of_forall (P : Submodule ℂ (Ecf F))
    (hP : ∀ (g : ArchIsometryProd F), ∀ v ∈ P, ρc F g v ∈ P) (w : InfinitePlace F)
    (kw : rowIsometrySubgroup₀ w.Completion) :
    ∀ s ∈ P.map (Ecf F).subtype, rightTranslate F (rowIsometryInclAt₀ F w kw) s ∈ P.map (Ecf F).subtype := by
  classical
  intro s hs
  obtain ⟨v, hv, rfl⟩ := hs
  refine ⟨ρc F (Pi.mulSingle w kw) v, hP _ v hv, ?_⟩
  exact coe_ρc_mulSingle F w kw v

theorem cutDM_le_CAD (tys : ArchTypeFamily F) : cutDM F tys ≤ CAD F tys := by
  classical
  haveI := isSemisimpleModule_ρc F
  refine @le_biSup_isotypicComponents_of_forall_linearEquiv_le (ℂK F) _ (ρc F).asModule inferInstance
    (ρc F).instModuleMonoidAlgebraAsModule inferInstance (cutDM F tys) ?_
  intro m m' hm hmm' hmA
  haveI := hm
  obtain ⟨e⟩ := hmm'
  obtain ⟨hS, θ, hθ⟩ := exists_linearEquiv_map_asModuleEquiv_of_linearEquiv (ρc F) m m' e
  obtain ⟨t, -, hmt⟩ := @exists_eq_span_singleton_of_isSimpleModule (ℂK F) _ (ρc F).asModule inferInstance
    (ρc F).instModuleMonoidAlgebraAsModule m hm
  haveI : FiniteDimensional ℂ (underSub F m) := finiteDimensional_underSub_of_eq_span F m t hmt
  have hS' := (exists_linearEquiv_map_asModuleEquiv_of_linearEquiv (ρc F) m' m' (LinearEquiv.refl _ _)).1

  let ι₀ := (Ecf F).subtype
  let Sf : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := (underSub F m).map ι₀
  let Sf' : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := (underSub F m').map ι₀
  let eS : underSub F m ≃ₗ[ℂ] Sf := Submodule.equivMapOfInjective ι₀ Subtype.val_injective _
  let eS' : underSub F m' ≃ₗ[ℂ] Sf' := Submodule.equivMapOfInjective ι₀ Subtype.val_injective _
  haveI : FiniteDimensional ℂ Sf := Module.Finite.map (underSub F m) ι₀
  let θf : Sf →ₗ[ℂ] Sf' := eS'.toLinearMap ∘ₗ θ.toLinearMap ∘ₗ eS.symm.toLinearMap
  have hθf_surj : Function.Surjective θf := by
    intro y
    refine ⟨eS (θ.symm (eS'.symm y)), ?_⟩
    simp [θf]
  have heS : ∀ (v : underSub F m), ((eS v : Sf) : AdelicGL2 (𝓞 F) F → ℂ) = (v : Ecf F) := fun v => rfl
  have heS' : ∀ (v : underSub F m'), ((eS' v : Sf') : AdelicGL2 (𝓞 F) F → ℂ) = (v : Ecf F) := fun v => rfl
  have heSsymm : ∀ (s : Sf), (((eS.symm s : underSub F m) : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) = s := fun s =>
    (heS _).symm.trans (congrArg Subtype.val (eS.apply_symm_apply s))

  intro x hx
  rw [mem_cutDM_iff, mem_archDualCutSubmodule_iff]
  intro w
  have hxSf' : (((ρc F).asModuleEquiv x : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) ∈ Sf' :=
    ⟨(ρc F).asModuleEquiv x, (mem_underSub_iff F m' _).mpr (by simpa using hx), rfl⟩
  show (((ρc F).asModuleEquiv x : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) ∈
    ⨆ i : Fin (tys.card w), typeSubmodule (rowIsometryInclAt₀ F w) (tys.rep w i).ρ.dual
  refine AutomorphicForm.le_iSup_typeSubmodule_of_surjective_of_le_iSup_typeSubmodule (rowIsometryInclAt₀ F w)
    (rowIsometryInclAt₀_injective F w) (fun i : Fin (tys.card w) => Module.Dual ℂ (Fin (tys.rep w i).n → ℂ))
    (fun i => (tys.rep w i).ρ.dual) Sf Sf'
    (rightTranslate_mem_map_subtype_of_forall F (underSub F m') hS' w)
    (rightTranslate_mem_map_subtype_of_forall F (underSub F m) hS w) θf hθf_surj ?_ ?_ hxSf'
  ·
    intro kw s
    have h1 : eS.symm ⟨fun x => (s : AdelicGL2 (𝓞 F) F → ℂ) (x * rowIsometryInclAt₀ F w kw),
          rightTranslate_mem_map_subtype_of_forall F (underSub F m) hS w kw s s.2⟩ =
        ⟨ρc F (Pi.mulSingle w kw) (eS.symm s : underSub F m), hS _ _ (eS.symm s).2⟩ := by
      apply eS.injective
      rw [eS.apply_symm_apply]
      apply Subtype.ext
      show rightTranslate F (rowIsometryInclAt₀ F w kw) (s : AdelicGL2 (𝓞 F) F → ℂ) = _
      rw [heS, coe_ρc_mulSingle, heSsymm]
    show ((eS' (θ (eS.symm ⟨_, _⟩)) : Sf') : AdelicGL2 (𝓞 F) F → ℂ) =
      rightTranslate F _ ((eS' (θ (eS.symm s)) : Sf') : _)
    rw [h1, heS', heS', hθ (Pi.mulSingle w kw) (eS.symm s), coe_ρc_mulSingle]
  ·
    rintro _ ⟨v, hv, rfl⟩
    have hv' := (mem_underSub_iff F m v).mp hv
    have := hmA hv'
    rw [mem_cutDM_iff, mem_archDualCutSubmodule_iff, LinearEquiv.apply_symm_apply] at this
    exact this w

theorem rightConv_eq_zero_of_isIrreducible_of_le_CBD (tys : ArchTypeFamily F) (y : Ecf F)
    (hy : (y : AdelicGL2 (𝓞 F) F → ℂ) ∈ archCutSubmodule F tys)
    (T : Submodule (ℂK F) (ρc F).asModule)
    (hTc : ∀ (g : ArchIsometryProd F), ∀ v ∈ underSub F T, ρc F g v ∈ underSub F T)
    (hTirr : IsSimpleOrder (Subrepresentation (Representation.restrictRep (ρc F) (underSub F T) hTc)))
    (hTcs : ∀ v ∈ underSub F T, HasCompactSupport ((v : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ))
    (hTB : T ≤ CBD F tys) :
    ∀ v ∈ underSub F T, rightConv F y v = 0 := by
  classical
  haveI := isSemisimpleModule_ρc F
  haveI := hTirr
  by_contra hcon
  push_neg at hcon
  obtain ⟨v0, hv0, hne⟩ := hcon
  obtain ⟨x0, hx0⟩ : ∃ x0, rightConv F y v0 x0 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)

  have hSc : ∀ (g : ArchIsometryProd F), ∀ s ∈ orbitSpanc F y, ρc F g s ∈ orbitSpanc F y := fun g s hs =>
    (Module.End.mem_invtSubmodule _).mp (((ρc F).mem_invtSubmodule).mp (orbitSpanc_mem_invtSubmodule F y) g) hs

  obtain ⟨βc, hβc⟩ := c3_exists_bilin_eval F (orbitSpanc F y) (underSub F T) hTcs x0
  have hβc_inv : ∀ (g : ArchIsometryProd F) (s : orbitSpanc F y) (t : underSub F T),
      βc (Representation.restrictRep (ρc F) (orbitSpanc F y) hSc g s)
        (Representation.restrictRep (ρc F) (underSub F T) hTc g t) = βc s t := by
    intro g s t
    rw [hβc, hβc, Representation.restrictRep_apply_coe, Representation.restrictRep_apply_coe,
      ρc_apply_coe, ρc_apply_coe, archRep_apply, archRep_apply, rightConv_rightTranslate_rightTranslate']
  have hβc_ne : βc ≠ 0 := by
    intro h
    apply hx0
    have := hβc ⟨y, mem_orbitSpanc_self F y⟩ ⟨v0, hv0⟩
    rw [h, LinearMap.zero_apply, LinearMap.zero_apply] at this
    exact this.symm

  have hnd_c : ∀ t : underSub F T, (∀ s : orbitSpanc F y, βc s t = 0) → t = 0 := by
    intro t ht
    by_contra ht0
    exact hβc_ne (Representation.pairing_eq_zero_of_invariant_of_isSimpleOrder_of_exists_ne_zero _ _ βc hβc_inv
        ⟨t, ht0, ht⟩)

  let ι₀ := (Ecf F).subtype
  let Sf : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := (orbitSpanc F y).map ι₀
  let Tf : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := (underSub F T).map ι₀
  haveI : FiniteDimensional ℂ Sf := Module.Finite.map (orbitSpanc F y) ι₀
  obtain ⟨βf, hβf⟩ := c3_exists_bilin_eval_fun F Sf Tf
    (by rintro _ ⟨v, -, rfl⟩; exact v.2.1) (by rintro _ ⟨v, hv, rfl⟩; exact ⟨v.2.1, hTcs v hv⟩) x0
  have hnd_f : ∀ t : Tf, (∀ s : Sf, βf s t = 0) → t = 0 := by
    rintro ⟨_, v, hv, rfl⟩ ht
    have hv0 : (⟨v, hv⟩ : underSub F T) = 0 := by
      apply hnd_c
      rintro ⟨s, hs⟩
      rw [hβc]
      have := ht ⟨(s : AdelicGL2 (𝓞 F) F → ℂ), s, hs, rfl⟩
      rw [hβf] at this
      exact this
    apply Subtype.ext
    have := congrArg (fun u : underSub F T => ((u : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ)) hv0
    exact this

  have hy_orbit : orbitSpan F (y : AdelicGL2 (𝓞 F) F → ℂ) ≤ archCutSubmodule F tys := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    show archRep F k (y : AdelicGL2 (𝓞 F) F → ℂ) ∈ archCutSubmodule F tys
    rw [archRep_apply]
    exact rightTranslate_mem_of_mem_iSup_range' F (archCutSubmodule F tys)
      (fun w k φ hφ => comp_mul_rowIsometryInclAt₀_mem_archCutSubmodule F hφ w k) (archProdIncl_mem_iSup F k) _ hy
  have hSle : ∀ w : InfinitePlace F, Sf ≤ ⨆ i : Fin (tys.card w), archTypeSubmoduleAt F w (tys.rep w i) := by
    intro w f hf
    obtain ⟨v, hv, rfl⟩ := hf
    have : ((v : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) ∈ orbitSpan F (y : AdelicGL2 (𝓞 F) F → ℂ) := by
      rw [← map_orbitSpanc]; exact ⟨v, hv, rfl⟩
    exact (mem_archCutSubmodule_iff F tys _).mp (hy_orbit this) w

  have hTf_le : ∀ w : InfinitePlace F, Tf ≤ ⨆ i : Fin (tys.card w), archDualTypeSubmoduleAt F w (tys.rep w i) := by
    intro w
    exact AutomorphicForm.le_iSup_typeSubmodule_dual_of_invariant_pairing (rowIsometryInclAt₀ F w)
      (rowIsometryInclAt₀_injective F w)
      (fun i : Fin (tys.card w) => Fin (tys.rep w i).n → ℂ) (fun i => (tys.rep w i).ρ) Sf Tf
      (rightTranslate_mem_map_subtype_of_forall F (orbitSpanc F y) hSc w)
      (rightTranslate_mem_map_subtype_of_forall F (underSub F T) hTc w) βf
      (fun k s t => by
        rw [hβf, hβf]
        exact congrFun (rightConv_rightTranslate_rightTranslate' F s t (rowIsometryInclAt₀ F w k)) x0)
      hnd_f (hSle w)

  have hT_cut : T ≤ cutDM F tys := by
    intro x hx
    rw [mem_cutDM_iff, mem_archDualCutSubmodule_iff]
    intro w
    exact hTf_le w ⟨(ρc F).asModuleEquiv x, (mem_underSub_iff F T _).mpr (by simpa using hx), rfl⟩
  have hT_bot : T = ⊥ := le_bot_iff.mp
    ((le_inf (hT_cut.trans (cutDM_le_CAD F tys)) hTB).trans (isCompl_CAD_CBD F tys).disjoint.le_bot)

  have hv0T := (mem_underSub_iff F T v0).mp hv0
  rw [hT_bot, Submodule.mem_bot (ℂK F), LinearEquiv.map_eq_zero_iff] at hv0T
  apply hne
  rw [hv0T]
  exact rightConv_zero_right F _

theorem hasCompactSupport_of_mem_mapSubmodule_orbitSpanc (F2 : Ecf F)
    (hF2s : HasCompactSupport (F2 : AdelicGL2 (𝓞 F) F → ℂ)) (x : (ρc F).asModule)
    (hx : x ∈ (ρc F).mapSubmodule ⟨orbitSpanc F F2, orbitSpanc_mem_invtSubmodule F F2⟩) :
    HasCompactSupport (((ρc F).asModuleEquiv x : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) := by
  rw [mem_mapSubmodule_iff] at hx
  have : (((ρc F).asModuleEquiv x : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) ∈ orbitSpan F (F2 : AdelicGL2 (𝓞 F) F → ℂ) := by
    rw [← map_orbitSpanc]; exact ⟨_, hx, rfl⟩
  exact hasCompactSupport_of_mem_orbitSpan F hF2s _ this

theorem rightConv_eq_zero_of_mem_inf_CBD (tys : ArchTypeFamily F) (y : Ecf F)
    (hy : (y : AdelicGL2 (𝓞 F) F → ℂ) ∈ archCutSubmodule F tys) (F2 : Ecf F)
    (hF2s : HasCompactSupport (F2 : AdelicGL2 (𝓞 F) F → ℂ)) (b : (ρc F).asModule)
    (hb : b ∈ (ρc F).mapSubmodule ⟨orbitSpanc F F2, orbitSpanc_mem_invtSubmodule F F2⟩ ⊓ CBD F tys) :
    rightConv F y (((ρc F).asModuleEquiv b : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) = 0 := by
  classical
  haveI := isSemisimpleModule_ρc F
  set N : Submodule (ℂK F) (ρc F).asModule :=
    (ρc F).mapSubmodule ⟨orbitSpanc F F2, orbitSpanc_mem_invtSubmodule F F2⟩ with hN
  have hNcs : ∀ x ∈ N, HasCompactSupport (((ρc F).asModuleEquiv x : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) :=
    fun x hx => hasCompactSupport_of_mem_mapSubmodule_orbitSpanc F F2 hF2s x (by rw [hN] at hx; exact hx)
  have hsup := IsSemisimpleModule.sSup_simples_le (R := ℂK F) (M := (ρc F).asModule) (N ⊓ CBD F tys)
  rw [← hsup, sSup_eq_iSup'] at hb
  refine (Submodule.iSup_induction _
    (motive := fun x => x ∈ N ∧ rightConv F y (((ρc F).asModuleEquiv x : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) = 0)
    hb ?_ ?_ ?_).2
  · rintro ⟨T, hT, hTle⟩ x hx
    haveI := hT
    refine ⟨(hTle hx).1, ?_⟩
    have hTc : ∀ (g : ArchIsometryProd F), ∀ v ∈ underSub F T, ρc F g v ∈ underSub F T := fun g v hv =>
      ρc_mem_underSub F T g hv
    have hTirr : IsSimpleOrder (Subrepresentation (Representation.restrictRep (ρc F) (underSub F T) hTc)) :=
      Representation.isIrreducible_of_isSimpleModule (ρc F) T hTc
    refine rightConv_eq_zero_of_isIrreducible_of_le_CBD F tys y hy T hTc hTirr ?_ (hTle.trans inf_le_right) _ ?_
    · intro v hv
      have hv' := (mem_underSub_iff F T v).mp hv
      have := hNcs _ (hTle hv').1
      rwa [LinearEquiv.apply_symm_apply] at this
    · exact (mem_underSub_iff F T _).mpr (by simpa using hx)
  · refine ⟨Submodule.zero_mem _, ?_⟩
    rw [map_zero]
    exact rightConv_zero_right F _
  · rintro a c ⟨haN, ha⟩ ⟨hcN, hc⟩
    refine ⟨Submodule.add_mem _ haN hcN, ?_⟩
    rw [map_add, Submodule.coe_add,
      c3_rightConv_add_right F y.2.1 ((ρc F).asModuleEquiv a).2.1 (hNcs a haN) ((ρc F).asModuleEquiv c).2.1 (hNcs c hcN),
      ha, hc, add_zero]

theorem exists_mem_orbitSpanc_mem_archDualCut_rightConv_eq (tys : ArchTypeFamily F) (y F2 : Ecf F)
    (hy : (y : AdelicGL2 (𝓞 F) F → ℂ) ∈ archCutSubmodule F tys)
    (hF2s : HasCompactSupport (F2 : AdelicGL2 (𝓞 F) F → ℂ)) :
    ∃ F3 : orbitSpanc F F2, ((F3 : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) ∈ archDualCutSubmodule F tys ∧
      rightConv F y (F3 : Ecf F) = rightConv F y F2 := by
  classical
  haveI := isSemisimpleModule_ρc F
  let N : Submodule (ℂK F) (ρc F).asModule :=
    (ρc F).mapSubmodule ⟨orbitSpanc F F2, orbitSpanc_mem_invtSubmodule F F2⟩
  have hxN : (ρc F).asModuleEquiv.symm F2 ∈ N := by
    rw [mem_mapSubmodule_iff]; simpa using mem_orbitSpanc_self F F2
  obtain ⟨a, ha, b, hb, hab⟩ := exists_add_eq_of_isCompl_biSup_isotypicComponents (goodComponentsD F tys)
    (isCompl_CAD_CBD F tys) N _ hxN
  refine ⟨⟨(ρc F).asModuleEquiv a, (mem_mapSubmodule_iff (ρc F) _ a).mp ha.1⟩, ?_, ?_⟩
  · exact (mem_cutDM_iff F tys a).mp (CAD_le_cutDM F tys ha.2)
  · have hb0 := rightConv_eq_zero_of_mem_inf_CBD F tys y hy F2 hF2s b hb
    have hF2 : (F2 : AdelicGL2 (𝓞 F) F → ℂ) =
        (((ρc F).asModuleEquiv a : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) + ((ρc F).asModuleEquiv b : Ecf F) := by
      have := congrArg (ρc F).asModuleEquiv hab
      rw [LinearEquiv.apply_symm_apply, map_add] at this
      rw [this, Submodule.coe_add]
    show rightConv F y ((ρc F).asModuleEquiv a : Ecf F) = rightConv F y F2
    rw [hF2, c3_rightConv_add_right F y.2.1 ((ρc F).asModuleEquiv a).2.1
      (hasCompactSupport_of_mem_mapSubmodule_orbitSpanc F F2 hF2s a ha.1) ((ρc F).asModuleEquiv b).2.1
      (hasCompactSupport_of_mem_mapSubmodule_orbitSpanc F F2 hF2s b hb.1), hb0, add_zero]

end PartC3
p2m_reactivate "P2MW.S_AutomorphicForm_exists_mem_span_rightTranslate_mem_archDualCutSubmodule_and_rightConv_eq.F4CutWords.Representation"

section PartC3Bridge

variable (F : Type) [Field F] [NumberField F]

theorem orbitSpan_eq_span (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    orbitSpan F φ = Submodule.span ℂ
      {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
        ψ = rightTranslate F k φ} := by
  unfold orbitSpan
  congr 1
  ext ψ
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨archProdIncl F k, archProdIncl_mem_iSup F k, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    rw [← archProdIncl_range] at hg
    obtain ⟨k, rfl⟩ := hg
    exact ⟨k, rfl⟩

end PartC3Bridge
p2m_reactivate "P2MW.S_AutomorphicForm_exists_mem_span_rightTranslate_mem_archDualCutSubmodule_and_rightConv_eq.F4CutWords.Representation"

end F4CutWords
p2m_reactivate "P2MW.S_AutomorphicForm_exists_mem_span_rightTranslate_mem_archDualCutSubmodule_and_rightConv_eq.F4CutWords.Representation P2MW.S_AutomorphicForm_exists_mem_span_rightTranslate_mem_archDualCutSubmodule_and_rightConv_eq.F4CutWords"

theorem solution
    (F : Type) [Field F] [NumberField F] (tys : ArchTypeFamily F)
    {y : AdelicGL2 (𝓞 F) F → ℂ} (hyc : Continuous y) (hy : y ∈ archCutSubmodule F tys)
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hfc : Continuous f) (hfs : HasCompactSupport f)
    (hfK : FiniteDimensional ℂ (Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range), ψ = rightTranslate F k f})) :
    ∃ f' ∈ Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range), ψ = rightTranslate F k f},
      f' ∈ archDualCutSubmodule F tys ∧ rightConv F y f' = rightConv F y f := by
  have hyE : y ∈ F4CutWords.Ecf F := F4CutWords.mem_Ecf_of_mem_archCutSubmodule F tys hy hyc
  have hfE : f ∈ F4CutWords.Ecf F := by
    refine ⟨hfc, ?_⟩
    rw [F4CutWords.orbitSpan_eq_span]
    exact hfK
  obtain ⟨F3, hF3D, hF3c⟩ :=
    F4CutWords.exists_mem_orbitSpanc_mem_archDualCut_rightConv_eq F tys ⟨y, hyE⟩ ⟨f, hfE⟩ hy hfs
  refine ⟨((F3 : F4CutWords.Ecf F) : AdelicGL2 (𝓞 F) F → ℂ), ?_, hF3D, hF3c⟩
  rw [← F4CutWords.orbitSpan_eq_span]
  show _ ∈ F4CutWords.orbitSpan F ((⟨f, hfE⟩ : F4CutWords.Ecf F) : AdelicGL2 (𝓞 F) F → ℂ)
  rw [← F4CutWords.map_orbitSpanc]
  exact ⟨F3, F3.2, rfl⟩

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_mem_span_rightTranslate_mem_archDualCutSubmodule_and_rightConv_eq.F4CutWords.Representation P2MW.S_AutomorphicForm_exists_mem_span_rightTranslate_mem_archDualCutSubmodule_and_rightConv_eq.F4CutWords"

end S_AutomorphicForm_exists_mem_span_rightTranslate_mem_archDualCutSubmodule_and_rightConv_eq
end P2MW
export P2MW.S_AutomorphicForm_exists_mem_span_rightTranslate_mem_archDualCutSubmodule_and_rightConv_eq (solution)
