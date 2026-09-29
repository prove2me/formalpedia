-- Prove2me | solution 1 for AutomorphicForm.exists_linearMap_archCutProjector_comm_rightTranslate
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/ffb19504-f63b-574b-95ab-2559b5a62b2a

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Theorems.Thm_Representation_exists_isCompl_forall_mem_of_compactSpace_of_continuous
import Theorems.Thm_Representation_exists_extend_forall_apply_mul_of_injective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_exists_linearMap_archCutProjector_comm_rightTranslate

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

section Ext

variable {H G : Type*} [Group H] [Group G] {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem exists_equivariant_extend (ι : H →* G) (hι : Function.Injective ι)
    (ρ : Representation ℂ H W) (P : Submodule ℂ W) (hP : ∀ k : H, ∀ v ∈ P, ρ k v ∈ P)
    (T : P →ₗ[ℂ] (G → ℂ))
    (hT : ∀ (k : H) (v : P) (x : G), T ⟨ρ k v, hP k v v.2⟩ x = T v (x * ι k)) :
    ∃ T' : W →ₗ[ℂ] (G → ℂ),
      (∀ (k : H) (v : W) (x : G), T' (ρ k v) x = T' v (x * ι k)) ∧ ∀ v : P, T' v = T v :=
  Representation.exists_extend_forall_apply_mul_of_injective ι hι ρ P hP T hT

end Ext

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

section PartB5

variable (F : Type) [Field F] [NumberField F]

abbrev TypeWitness (w : InfinitePlace F) (tys : ArchTypeFamily F) : Type :=
  Σ i : Fin (tys.card w), {T : (Fin (tys.rep w i).n → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) //
    IsRightEquivariant (rowIsometryInclAt₀ F w) (tys.rep w i).ρ T}

theorem exists_finset_typeWitness_of_mem_iSup (w : InfinitePlace F) (tys : ArchTypeFamily F)
    {s : AdelicGL2 (𝓞 F) F → ℂ} (hs : s ∈ ⨆ i : Fin (tys.card w), archTypeSubmoduleAt F w (tys.rep w i)) :
    ∃ J : Finset (TypeWitness F w tys), s ∈ ⨆ j ∈ J, LinearMap.range j.2.1 := by
  classical
  have mono : ∀ (A B : Finset (TypeWitness F w tys)), A ⊆ B →
      (⨆ j ∈ A, LinearMap.range j.2.1) ≤ ⨆ j ∈ B, LinearMap.range j.2.1 := fun A B h =>
    biSup_mono fun j hj => h hj
  refine Submodule.iSup_induction _
    (motive := fun s => ∃ J : Finset (TypeWitness F w tys), s ∈ ⨆ j ∈ J, LinearMap.range j.2.1) hs ?_ ?_ ?_
  · intro i f hf
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · rintro f ⟨T, hT, hfT⟩
      refine ⟨{⟨i, T, hT⟩}, ?_⟩
      simp only [Finset.mem_singleton, iSup_iSup_eq_left]
      exact hfT
    · exact ⟨∅, by simp⟩
    · rintro a b - - ⟨Ja, ha⟩ ⟨Jb, hb⟩
      refine ⟨Ja ∪ Jb, Submodule.add_mem _ ?_ ?_⟩
      · exact mono _ _ Finset.subset_union_left ha
      · exact mono _ _ Finset.subset_union_right hb
    · rintro c a - ⟨J, ha⟩
      exact ⟨J, Submodule.smul_mem _ c ha⟩
  · exact ⟨∅, by simp⟩
  · rintro a b ⟨Ja, ha⟩ ⟨Jb, hb⟩
    refine ⟨Ja ∪ Jb, Submodule.add_mem _ ?_ ?_⟩
    · exact mono _ _ Finset.subset_union_left ha
    · exact mono _ _ Finset.subset_union_right hb

theorem le_iSup_archTypeSubmoduleAt_of_surjective (w : InfinitePlace F) (tys : ArchTypeFamily F)
    (S S' : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) [FiniteDimensional ℂ S]
    (hS' : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ s ∈ S', rightTranslate F (rowIsometryInclAt₀ F w k) s ∈ S')
    (hS : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ s ∈ S, rightTranslate F (rowIsometryInclAt₀ F w k) s ∈ S)
    (θ : S →ₗ[ℂ] S') (hθs : Function.Surjective θ)
    (hθ : ∀ (k : rowIsometrySubgroup₀ w.Completion) (s : S),
      (θ ⟨rightTranslate F (rowIsometryInclAt₀ F w k) s, hS k s s.2⟩ : AdelicGL2 (𝓞 F) F → ℂ) =
        rightTranslate F (rowIsometryInclAt₀ F w k) (θ s))
    (hSA : S ≤ ⨆ i : Fin (tys.card w), archTypeSubmoduleAt F w (tys.rep w i)) :
    S' ≤ ⨆ i : Fin (tys.card w), archTypeSubmoduleAt F w (tys.rep w i) := by
  classical

  obtain ⟨J, hJ⟩ : ∃ J : Finset (TypeWitness F w tys), S ≤ ⨆ j ∈ J, LinearMap.range j.2.1 := by
    let b := Module.finBasis ℂ S
    choose Jf hJf using fun l => exists_finset_typeWitness_of_mem_iSup F w tys (hSA (b l).2)
    refine ⟨Finset.univ.biUnion Jf, ?_⟩
    have mono : ∀ (A B : Finset (TypeWitness F w tys)), A ⊆ B →
        (⨆ j ∈ A, LinearMap.range j.2.1) ≤ ⨆ j ∈ B, LinearMap.range j.2.1 := fun A B h =>
      biSup_mono fun j hj => h hj
    intro s hs
    have hs' : (⟨s, hs⟩ : S) ∈ Submodule.span ℂ (Set.range b) := by rw [b.span_eq]; trivial
    have hs'' : s ∈ Submodule.span ℂ (Set.range fun l => (b l : AdelicGL2 (𝓞 F) F → ℂ)) := by
      have := Submodule.mem_map_of_mem (f := S.subtype) hs'
      rw [Submodule.map_span, ← Set.range_comp] at this
      exact this
    refine (Submodule.span_le.mpr ?_) hs''
    rintro _ ⟨l, rfl⟩
    exact mono _ _ (Finset.subset_biUnion_of_mem Jf (Finset.mem_univ l)) (hJf l)

  let K := rowIsometrySubgroup₀ w.Completion
  let WJ : Type := ∀ j : J, (Fin (tys.rep w j.1.1).n → ℂ)
  let ρJ : Representation ℂ K WJ :=
    { toFun := fun k => LinearMap.pi fun j => ((tys.rep w j.1.1).ρ k) ∘ₗ LinearMap.proj j
      map_one' := by ext x j; simp
      map_mul' := fun a c => by ext x j; simp }
  have hρJ : ∀ (k : K) (x : WJ) (j : J), ρJ k x j = (tys.rep w j.1.1).ρ k (x j) := fun k x j => rfl
  let TJ : WJ →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) := ∑ j : J, (j.1.2.1) ∘ₗ LinearMap.proj j
  have hTJ_apply : ∀ x : WJ, TJ x = ∑ j : J, j.1.2.1 (x j) := fun x => by
    simp only [TJ, LinearMap.sum_apply, LinearMap.comp_apply]
    rfl
  have hTJ : ∀ (k : K) (x : WJ) (y : AdelicGL2 (𝓞 F) F),
      TJ (ρJ k x) y = TJ x (y * rowIsometryInclAt₀ F w k) := by
    intro k x y
    simp only [hTJ_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hρJ]; exact j.1.2.2 k (x j) y

  have hSrange : S ≤ LinearMap.range TJ := by
    refine hJ.trans (iSup₂_le fun j hj => ?_)
    rintro _ ⟨v, rfl⟩
    refine ⟨Pi.single ⟨j, hj⟩ v, ?_⟩
    rw [hTJ_apply, Finset.sum_eq_single ⟨j, hj⟩]
    · simp
    · intro j' _ hj'; simp [Pi.single_eq_of_ne hj']
    · simp

  let P : Submodule ℂ WJ := S.comap TJ
  have hP : ∀ k : K, ∀ x ∈ P, ρJ k x ∈ P := by
    intro k x hx
    show TJ (ρJ k x) ∈ S
    have : TJ (ρJ k x) = rightTranslate F (rowIsometryInclAt₀ F w k) (TJ x) := funext fun y => hTJ k x y
    rw [this]; exact hS k _ hx
  let toS : P →ₗ[ℂ] S := LinearMap.codRestrict S (TJ ∘ₗ P.subtype) fun x => x.2
  let f : P →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) := S'.subtype ∘ₗ θ ∘ₗ toS
  have hf : ∀ (k : K) (x : P) (y : AdelicGL2 (𝓞 F) F), f ⟨ρJ k x, hP k x x.2⟩ y = f x (y * rowIsometryInclAt₀ F w k) := by
    intro k x y
    have h1 : toS ⟨ρJ k x, hP k x x.2⟩ = ⟨rightTranslate F (rowIsometryInclAt₀ F w k) (toS x : _), hS k _ (toS x).2⟩ := by
      apply Subtype.ext
      funext y'
      exact hTJ k x y'
    show (θ (toS ⟨ρJ k x, hP k x x.2⟩) : AdelicGL2 (𝓞 F) F → ℂ) y = (θ (toS x) : AdelicGL2 (𝓞 F) F → ℂ) (y * _)
    rw [h1, hθ k (toS x)]
    rfl

  have hinj : Function.Injective (rowIsometryInclAt₀ F w) := by
    intro a c hac
    apply Subtype.ext
    apply Units.ext
    ext i j' : 1
    have := congrArg (fun g : AdelicGL2 (𝓞 F) F => ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j').1 w) hac
    simp only [rowIsometryInclAt₀_apply, val_adelicArchGLInclAt_apply, archMatrixUpdate_apply_self] at this
    exact this
  obtain ⟨T', hT'eq, hT'ext⟩ := exists_equivariant_extend (rowIsometryInclAt₀ F w) hinj ρJ P hP f hf

  intro s' hs'
  obtain ⟨s, hθs'⟩ := hθs ⟨s', hs'⟩
  rw [show s' = ((θ s : S') : AdelicGL2 (𝓞 F) F → ℂ) from (congrArg Subtype.val hθs').symm]
  obtain ⟨x, hx⟩ : ∃ x : WJ, TJ x = s := hSrange s.2
  have hxP : x ∈ P := by show TJ x ∈ S; rw [hx]; exact s.2
  have hs_eq : (θ s : AdelicGL2 (𝓞 F) F → ℂ) = T' x := by
    rw [hT'ext ⟨x, hxP⟩]
    show _ = (θ (toS ⟨x, hxP⟩) : AdelicGL2 (𝓞 F) F → ℂ)
    congr 2
    apply Subtype.ext; exact hx.symm
  show (θ s : AdelicGL2 (𝓞 F) F → ℂ) ∈ _
  rw [hs_eq, show x = ∑ j : J, Pi.single j (x j) from (Finset.univ_sum_single x).symm, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  refine Submodule.mem_iSup_of_mem j.1.1 ?_

  refine mem_typeSubmodule_of_isRightEquivariant (T := T' ∘ₗ LinearMap.single ℂ (fun j : J => Fin (tys.rep w j.1.1).n → ℂ) j) ?_ (x j)
  intro k v y
  show T' (Pi.single j ((tys.rep w j.1.1).ρ k v)) y = T' (Pi.single j v) (y * _)
  rw [← hT'eq k]
  have hsingle : (Pi.single j ((tys.rep w j.1.1).ρ k v) : WJ) = ρJ k (Pi.single j v) := by
    funext j'
    rw [hρJ]
    by_cases hjj : j' = j
    · subst hjj; simp
    · simp [Pi.single_eq_of_ne hjj]
  rw [hsingle]

end PartB5

section PartB6

set_option backward.isDefEq.respectTransparency false

variable (F : Type) [Field F] [NumberField F]

open Representation

def cutc (tys : ArchTypeFamily F) : Submodule ℂ (Ecf F) := (archCutSubmodule F tys).comap (Ecf F).subtype

theorem mem_cutc {tys : ArchTypeFamily F} {φ : Ecf F} :
    φ ∈ cutc F tys ↔ (φ : AdelicGL2 (𝓞 F) F → ℂ) ∈ archCutSubmodule F tys := Iff.rfl

theorem archProdIncl_mem_iSup (k : ArchIsometryProd F) :
    archProdIncl F k ∈ ⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range := by
  rw [← archProdIncl_range]; exact ⟨k, rfl⟩

theorem cutc_mem_invtSubmodule (tys : ArchTypeFamily F) : cutc F tys ∈ (ρc F).invtSubmodule := by
  rw [Representation.mem_invtSubmodule]
  intro k φ hφ
  show ((ρc F k φ : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) ∈ archCutSubmodule F tys
  rw [ρc_apply_coe, archRep_apply]
  exact rightTranslate_mem_of_mem_iSup_range' F (archCutSubmodule F tys)
    (fun w k φ hφ => comp_mul_rowIsometryInclAt₀_mem_archCutSubmodule F hφ w k) (archProdIncl_mem_iSup F k) _ hφ

def cutM (tys : ArchTypeFamily F) : Submodule (ℂK F) (ρc F).asModule :=
  (ρc F).mapSubmodule ⟨cutc F tys, cutc_mem_invtSubmodule F tys⟩

def goodComponents (tys : ArchTypeFamily F) : Set (isotypicComponents (ℂK F) (ρc F).asModule) :=
  {c | (c : Submodule (ℂK F) (ρc F).asModule) ≤ cutM F tys}

def CA (tys : ArchTypeFamily F) : Submodule (ℂK F) (ρc F).asModule :=
  ⨆ c ∈ goodComponents F tys, (c : Submodule (ℂK F) (ρc F).asModule)

def CB (tys : ArchTypeFamily F) : Submodule (ℂK F) (ρc F).asModule :=
  ⨆ c ∈ (goodComponents F tys)ᶜ, (c : Submodule (ℂK F) (ρc F).asModule)

theorem isCompl_CA_CB (tys : ArchTypeFamily F) : IsCompl (CA F tys) (CB F tys) :=
  isCompl_biSup_isotypicComponents F (goodComponents F tys)

theorem CA_le_cutM (tys : ArchTypeFamily F) : CA F tys ≤ cutM F tys :=
  iSup₂_le fun c hc => hc

def projCA (tys : ArchTypeFamily F) : (ρc F).asModule →ₗ[ℂK F] CA F tys :=
  @Submodule.linearProjOfIsCompl (ℂK F) _ (ρc F).asModule inferInstance (ρc F).instModuleMonoidAlgebraAsModule
    (CA F tys) (CB F tys) (isCompl_CA_CB F tys)

theorem projCA_apply_left (tys : ArchTypeFamily F) (x : CA F tys) : projCA F tys x = x :=
  @Submodule.linearProjOfIsCompl_apply_left (ℂK F) _ (ρc F).asModule inferInstance
    (ρc F).instModuleMonoidAlgebraAsModule (CA F tys) (CB F tys) (isCompl_CA_CB F tys) x

theorem projCA_apply_right (tys : ArchTypeFamily F) (x : CB F tys) : projCA F tys x = 0 :=
  @Submodule.linearProjOfIsCompl_apply_right (ℂK F) _ (ρc F).asModule inferInstance
    (ρc F).instModuleMonoidAlgebraAsModule (CA F tys) (CB F tys) (isCompl_CA_CB F tys) x

def QM (tys : ArchTypeFamily F) : (ρc F).asModule →ₗ[ℂK F] (ρc F).asModule :=
  (CA F tys).subtype.comp (projCA F tys)

theorem QM_apply_of_mem_CA (tys : ArchTypeFamily F) {m : (ρc F).asModule} (hm : m ∈ CA F tys) : QM F tys m = m := by
  show ((projCA F tys m : CA F tys) : (ρc F).asModule) = m
  rw [projCA_apply_left F tys ⟨m, hm⟩]

theorem QM_apply_of_mem_CB (tys : ArchTypeFamily F) {m : (ρc F).asModule} (hm : m ∈ CB F tys) : QM F tys m = 0 := by
  show ((projCA F tys m : CA F tys) : (ρc F).asModule) = 0
  rw [projCA_apply_right F tys ⟨m, hm⟩]; rfl

theorem QM_mem_CA (tys : ArchTypeFamily F) (m : (ρc F).asModule) : QM F tys m ∈ CA F tys :=
  Submodule.coe_mem (projCA F tys m)

def Qc (tys : ArchTypeFamily F) : Ecf F →ₗ[ℂ] Ecf F :=
  (ρc F).asModuleEquiv.toLinearMap ∘ₗ (QM F tys).restrictScalars ℂ ∘ₗ (ρc F).asModuleEquiv.symm.toLinearMap

theorem Qc_apply (tys : ArchTypeFamily F) (φ : Ecf F) :
    Qc F tys φ = (ρc F).asModuleEquiv (QM F tys ((ρc F).asModuleEquiv.symm φ)) := rfl

theorem Qc_ρc (tys : ArchTypeFamily F) (k : ArchIsometryProd F) (φ : Ecf F) :
    Qc F tys (ρc F k φ) = ρc F k (Qc F tys φ) := by
  rw [Qc_apply, Qc_apply, Representation.asModuleEquiv_symm_map_rho, map_smul,
    Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]

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

private def coann {k : Type*} [Field k] {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (W : Subrepresentation ρ.dual) : Subrepresentation ρ where
  toSubmodule := W.toSubmodule.dualCoannihilator
  apply_mem_toSubmodule g v hv := by
    rw [Submodule.mem_dualCoannihilator] at hv ⊢
    intro φ hφ

    have hmem := W.apply_mem_toSubmodule g⁻¹ hφ
    have := hv _ hmem
    simpa [Representation.dual_apply, Module.Dual.transpose_apply] using this

private theorem coann_toSubmodule {k : Type*} [Field k] {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (W : Subrepresentation ρ.dual) :
    (coann ρ W).toSubmodule = W.toSubmodule.dualCoannihilator := rfl

theorem Representation.isIrreducible_dual
    {k : Type*} [Field k] {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) [Representation.IsIrreducible ρ] : Representation.IsIrreducible ρ.dual := by
  have hinj : Function.Injective (Subrepresentation.toSubmodule : Subrepresentation ρ → Submodule k V) :=
    Subrepresentation.toSubmodule_injective
  have hinj' : Function.Injective (Subrepresentation.toSubmodule : Subrepresentation ρ.dual → Submodule k (Module.Dual k V)) :=
    Subrepresentation.toSubmodule_injective
  have hbot : (⊥ : Subrepresentation ρ).toSubmodule = ⊥ := rfl
  have htop : (⊤ : Subrepresentation ρ).toSubmodule = ⊤ := rfl
  have hbot' : (⊥ : Subrepresentation ρ.dual).toSubmodule = ⊥ := rfl
  have htop' : (⊤ : Subrepresentation ρ.dual).toSubmodule = ⊤ := rfl

  haveI : Nontrivial V := by
    rw [← Submodule.nontrivial_iff (R := k)]
    refine ⟨⟨⊥, ⊤, fun h => ?_⟩⟩
    exact (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤) (hinj (by rw [hbot, htop, h]))
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun W => ?_ }
  · have := congrArg Subrepresentation.toSubmodule h
    rw [hbot', htop'] at this
    exact (bot_ne_top : (⊥ : Submodule k (Module.Dual k V)) ≠ ⊤) this
  · haveI : FiniteDimensional k W.toSubmodule := inferInstance
    have hW : W.toSubmodule = (coann ρ W).toSubmodule.dualAnnihilator := by
      rw [coann_toSubmodule, Subspace.dualCoannihilator_dualAnnihilator_eq]
    rcases IsSimpleOrder.eq_bot_or_eq_top (coann ρ W) with h | h
    · right
      apply hinj'
      rw [hW, h, hbot, Submodule.dualAnnihilator_bot, htop']
    · left
      apply hinj'
      rw [hW, h, htop, Submodule.dualAnnihilator_top, hbot']

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

theorem map_mem_of_mem_isotypicComponents {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
    [IsSemisimpleModule R M] (N : Submodule R M) (f : N →ₗ[R] M) (c : Submodule R M)
    (hc : c ∈ isotypicComponents R M) (x : N) (hx : (x : M) ∈ c) : f x ∈ c := by
  obtain ⟨S, hS, rfl⟩ := hc
  set P : Submodule R N := (isotypicComponent R M S).comap N.subtype with hP
  have hxP : x ∈ P := hx

  have hiso : IsIsotypicOfType R P S := by
    refine IsIsotypicOfType.of_injective (IsIsotypicOfType.isotypicComponent R M S)
      ((N.subtype.restrict (p := P) (q := isotypicComponent R M S) fun y hy => hy)) ?_
    intro a b h
    have h' : ((a : N) : M) = ((b : N) : M) := by
      have := congrArg (fun z : ↥(isotypicComponent R M S) => (z : M)) h
      simpa [LinearMap.restrict_apply] using this
    exact Subtype.ext (Subtype.ext h')
  have hle : P ≤ isotypicComponent R N S := le_isotypicComponent_iff.mpr hiso
  exact LinearMap.le_comap_isotypicComponent S f (hle hxP)

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

theorem mem_cutM_iff (tys : ArchTypeFamily F) (x : (ρc F).asModule) :
    x ∈ cutM F tys ↔ (((ρc F).asModuleEquiv x : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) ∈ archCutSubmodule F tys :=
  mem_mapSubmodule_iff (ρc F) _ x

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

theorem cutM_le_CA (tys : ArchTypeFamily F) : cutM F tys ≤ CA F tys := by
  classical
  haveI := isSemisimpleModule_ρc F
  refine @le_biSup_isotypicComponents_of_forall_linearEquiv_le (ℂK F) _ (ρc F).asModule inferInstance
    (ρc F).instModuleMonoidAlgebraAsModule inferInstance (cutM F tys) ?_
  intro m m' hm hmm' hmA
  haveI := hm
  obtain ⟨e⟩ := hmm'
  obtain ⟨hS, θ, hθ⟩ := exists_linearEquiv_map_asModuleEquiv_of_linearEquiv (ρc F) m m' e
  obtain ⟨t, -, hmt⟩ := @exists_eq_span_singleton_of_isSimpleModule (ℂK F) _ (ρc F).asModule inferInstance
    (ρc F).instModuleMonoidAlgebraAsModule m hm
  haveI : FiniteDimensional ℂ (underSub F m) := finiteDimensional_underSub_of_eq_span F m t hmt

  let ι₀ := (Ecf F).subtype
  let Sf : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := (underSub F m).map ι₀
  let Sf' : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := (underSub F m').map ι₀
  have hS' := (exists_linearEquiv_map_asModuleEquiv_of_linearEquiv (ρc F) m' m' (LinearEquiv.refl _ _)).1
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
  have heSsymm : ∀ (s : Sf), (((eS.symm s : underSub F m) : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) = s := fun s => by
    rw [← heS (eS.symm s), eS.apply_symm_apply]

  have hact : ∀ (w : InfinitePlace F) (kw : rowIsometrySubgroup₀ w.Completion) (v : Ecf F),
      ((ρc F (Pi.mulSingle w kw) v : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) = rightTranslate F (rowIsometryInclAt₀ F w kw) v := by
    intro w kw v
    rw [ρc_apply_coe, archRep_apply, archProdIncl_mulSingle]

  have hstab : ∀ (N : Submodule (ℂK F) (ρc F).asModule)
      (hN : ∀ (g : ArchIsometryProd F), ∀ v ∈ underSub F N, ρc F g v ∈ underSub F N)
      (w : InfinitePlace F) (kw : rowIsometrySubgroup₀ w.Completion),
      ∀ s ∈ (underSub F N).map ι₀, rightTranslate F (rowIsometryInclAt₀ F w kw) s ∈ (underSub F N).map ι₀ := by
    intro N hN w kw s hs
    obtain ⟨v, hv, rfl⟩ := hs
    refine ⟨ρc F (Pi.mulSingle w kw) v, hN _ v hv, ?_⟩
    exact hact w kw v

  intro x hx
  rw [mem_cutM_iff, mem_archCutSubmodule_iff]
  intro w
  have hxSf' : (((ρc F).asModuleEquiv x : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) ∈ Sf' :=
    ⟨(ρc F).asModuleEquiv x, (mem_underSub_iff F m' _).mpr (by simpa using hx), rfl⟩
  refine le_iSup_archTypeSubmoduleAt_of_surjective F w tys Sf Sf' (hstab m' hS' w) (hstab m hS w) θf hθf_surj ?_ ?_ hxSf'
  ·
    intro kw s
    have h1 : eS.symm ⟨rightTranslate F (rowIsometryInclAt₀ F w kw) s, hstab m hS w kw s s.2⟩ =
        ⟨ρc F (Pi.mulSingle w kw) (eS.symm s : underSub F m), hS _ _ (eS.symm s).2⟩ := by
      apply eS.injective
      rw [eS.apply_symm_apply]
      apply Subtype.ext
      rw [heS, hact, heSsymm]
    show ((eS' (θ (eS.symm ⟨_, _⟩)) : Sf') : AdelicGL2 (𝓞 F) F → ℂ) = rightTranslate F _ ((eS' (θ (eS.symm s)) : Sf') : _)
    rw [h1, heS', heS', hθ (Pi.mulSingle w kw) (eS.symm s), hact]
  ·
    rintro _ ⟨v, hv, rfl⟩
    replace hv := (mem_underSub_iff F m v).mp hv
    have := hmA hv
    rw [mem_cutM_iff, mem_archCutSubmodule_iff] at this
    have h__af := this w
    simp at h__af
    exact h__af

theorem Qc_eq_self_of_mem_cutc (tys : ArchTypeFamily F) {φ : Ecf F} (hφ : φ ∈ cutc F tys) : Qc F tys φ = φ := by
  rw [Qc_apply]
  have hx : (ρc F).asModuleEquiv.symm φ ∈ cutM F tys := by
    rw [mem_cutM_iff]; (simp at hφ ⊢; exact hφ)
  rw [QM_apply_of_mem_CA F tys (cutM_le_CA F tys hx)]
  simp

theorem Qc_mem_orbitSpanc (tys : ArchTypeFamily F) (φ : Ecf F) : Qc F tys φ ∈ orbitSpanc F φ := by
  classical
  haveI := isSemisimpleModule_ρc F
  let N : Submodule (ℂK F) (ρc F).asModule := (ρc F).mapSubmodule ⟨orbitSpanc F φ, orbitSpanc_mem_invtSubmodule F φ⟩
  have hxN : (ρc F).asModuleEquiv.symm φ ∈ N := by
    rw [mem_mapSubmodule_iff]; simpa using mem_orbitSpanc_self F φ
  obtain ⟨a, ha, b, hb, hab⟩ := exists_add_eq_of_isCompl_biSup_isotypicComponents (goodComponents F tys)
    (isCompl_CA_CB F tys) N _ hxN
  rw [Qc_apply, hab, map_add, QM_apply_of_mem_CA F tys ha.2, QM_apply_of_mem_CB F tys hb.2, add_zero]
  exact (mem_mapSubmodule_iff (ρc F) _ a).mp ha.1

end PartB7

section PartTQE

set_option backward.isDefEq.respectTransparency false

variable (F : Type) [Field F] [NumberField F]

open Representation

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
      {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
        ψ = rightTranslate F k φ} := by
  rw [orbitSpan, range_archRep_eq]

theorem mem_Ecf_of_finiteDimensional_span {φ : AdelicGL2 (𝓞 F) F → ℂ} (hc : Continuous φ)
    (hfd : FiniteDimensional ℂ (Submodule.span ℂ
      {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
        ψ = rightTranslate F k φ})) : φ ∈ Ecf F := by
  refine ⟨hc, ?_⟩
  rw [orbitSpan_eq_span]
  exact hfd

theorem exists_archCutProjector (tys : ArchTypeFamily F) :
    ∃ Q : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ),
      (∀ φ : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ → φ ∈ archCutSubmodule F tys → Q φ = φ) ∧
      (∀ φ : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ →
        FiniteDimensional ℂ (Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
            ψ = rightTranslate F k φ}) →
        Q φ ∈ archCutSubmodule F tys ⊓ Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
            ψ = rightTranslate F k φ}) ∧
      (∀ φ : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ →
        FiniteDimensional ℂ (Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
            ψ = rightTranslate F k φ}) →
        ∀ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
          Q (rightTranslate F k φ) = rightTranslate F k (Q φ)) := by
  classical
  obtain ⟨Q, hQ⟩ := LinearMap.exists_extend ((Ecf F).subtype ∘ₗ Qc F tys)
  have hQ' : ∀ (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ Ecf F), Q φ = Qc F tys ⟨φ, hφ⟩ :=
    fun φ hφ => LinearMap.congr_fun hQ ⟨φ, hφ⟩
  refine ⟨Q, ?_, ?_, ?_⟩
  · intro φ hc hA
    have hE : φ ∈ Ecf F := mem_Ecf_of_mem_archCutSubmodule F tys hA hc
    rw [hQ' φ hE, Qc_eq_self_of_mem_cutc F tys (show (⟨φ, hE⟩ : Ecf F) ∈ cutc F tys from hA)]
  · intro φ hc hfd
    have hE : φ ∈ Ecf F := mem_Ecf_of_finiteDimensional_span F hc hfd
    rw [hQ' φ hE]
    refine ⟨?_, ?_⟩
    · have h1 : QM F tys ((ρc F).asModuleEquiv.symm ⟨φ, hE⟩) ∈ cutM F tys :=
        CA_le_cutM F tys (QM_mem_CA F tys _)
      rw [mem_cutM_iff] at h1
      rw [Qc_apply]
      exact h1
    · have h2 := Qc_mem_orbitSpanc F tys ⟨φ, hE⟩
      have h3 : ((Qc F tys ⟨φ, hE⟩ : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) ∈ (orbitSpanc F ⟨φ, hE⟩).map (Ecf F).subtype :=
        Submodule.mem_map_of_mem h2
      rw [map_orbitSpanc] at h3
      change _ ∈ orbitSpan F φ at h3
      rwa [orbitSpan_eq_span] at h3
  · intro φ hc hfd k hk
    have hE : φ ∈ Ecf F := mem_Ecf_of_finiteDimensional_span F hc hfd
    rw [← archProdIncl_range] at hk
    obtain ⟨k', rfl⟩ := hk
    have hE' : rightTranslate F (archProdIncl F k') φ ∈ Ecf F := archRep_mem_Ecf F k' hE
    rw [hQ' _ hE', hQ' φ hE]
    have hρ : (ρc F k' ⟨φ, hE⟩ : Ecf F) = ⟨rightTranslate F (archProdIncl F k') φ, hE'⟩ := Subtype.ext rfl
    rw [← hρ, Qc_ρc F tys k' ⟨φ, hE⟩, ρc_apply_coe, archRep_apply]

end PartTQE

end F4CutWords
p2m_reactivate "P2MW.S_AutomorphicForm_exists_linearMap_archCutProjector_comm_rightTranslate.F4CutWords"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_linearMap_archCutProjector_comm_rightTranslate.F4CutWords"

open F4CutWords in

theorem solution
    (F : Type) [Field F] [NumberField F] (tys : ArchTypeFamily F) :
    ∃ Q : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ),
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
          Q (rightTranslate F k φ) = rightTranslate F k (Q φ)) :=
  F4CutWords.exists_archCutProjector F tys

end S_AutomorphicForm_exists_linearMap_archCutProjector_comm_rightTranslate
end P2MW
export P2MW.S_AutomorphicForm_exists_linearMap_archCutProjector_comm_rightTranslate (solution)
