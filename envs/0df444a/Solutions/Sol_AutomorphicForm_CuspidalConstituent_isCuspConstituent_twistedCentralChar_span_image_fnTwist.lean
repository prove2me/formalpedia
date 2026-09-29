-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.isCuspConstituent_twistedCentralChar_span_image_fnTwist
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/4ad3d988-c83b-5100-a8be-e5ab33fbebfb

import Mathlib
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_HeckeCharacter_FiniteOrder
import Theorems.Thm_AutomorphicForm_isSmoothCuspAutomorphicFnAt_twistedCentralChar_fnTwist_productionPinsOf
import Theorems.Thm_AutomorphicForm_isFactorizableTestFn_chiDet_mul_of_continuous_of_isOfFinOrder
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_isCuspConstituent_twistedCentralChar_span_image_fnTwist

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open AutomorphicForm AutomorphicForm.CuspidalConstituent

noncomputable section

namespace P2mS28R7

variable (F : Type) [Field F] [NumberField F]

def twistLin (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) where
  toFun := fnTwist F η
  map_add' φ ψ := by ext g; simp [fnTwist, mul_add]
  map_smul' c φ := by ext g; simp [fnTwist]; ring

@[scoped simp] theorem twistLin_apply (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    twistLin F η φ = fnTwist F η φ := rfl

theorem fnTwist_inv_fnTwist (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    fnTwist F η⁻¹ (fnTwist F η φ) = φ := by
  funext g
  simp only [fnTwist_apply, chiDet, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  exact inv_mul_cancel_left₀ (Units.ne_zero _) _

theorem fnTwist_fnTwist_inv (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    fnTwist F η (fnTwist F η⁻¹ φ) = φ := by
  funext g
  simp only [fnTwist_apply, chiDet, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  exact mul_inv_cancel_left₀ (Units.ne_zero _) _

def twistEquiv (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) : (AdelicGL2 (𝓞 F) F → ℂ) ≃ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) :=
  { twistLin F η with
    invFun := fnTwist F η⁻¹
    left_inv := fnTwist_inv_fnTwist F η
    right_inv := fnTwist_fnTwist_inv F η }

@[scoped simp] theorem twistEquiv_apply (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    twistEquiv F η φ = fnTwist F η φ := rfl

theorem span_image_fnTwist (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) :
    Submodule.span ℂ ((fun φ => fnTwist F η φ) '' (V : Set (AdelicGL2 (𝓞 F) F → ℂ))) = V.map (twistLin F η) := by
  rw [show (fun φ => fnTwist F η φ) = (twistLin F η : (AdelicGL2 (𝓞 F) F → ℂ) → _) from rfl,
    Submodule.span_image, Submodule.span_eq]

theorem mem_map_twistLin_iff (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (ψ : AdelicGL2 (𝓞 F) F → ℂ) : ψ ∈ V.map (twistLin F η) ↔ fnTwist F η⁻¹ ψ ∈ V := by
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    simpa [fnTwist_inv_fnTwist] using hφ
  · intro h
    exact ⟨fnTwist F η⁻¹ ψ, h, fnTwist_fnTwist_inv F η ψ⟩

theorem map_twistLin_map_twistLin_inv (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) :
    (W.map (twistLin F η⁻¹)).map (twistLin F η) = W := by
  ext ψ
  constructor
  · rintro ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
    rw [twistLin_apply, twistLin_apply, fnTwist_fnTwist_inv]
    exact hφ
  · intro h
    exact ⟨fnTwist F η⁻¹ ψ, ⟨ψ, h, rfl⟩, fnTwist_fnTwist_inv F η ψ⟩

theorem map_twistLin_inv_map_twistLin (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) :
    (W.map (twistLin F η)).map (twistLin F η⁻¹) = W := by
  ext ψ
  constructor
  · rintro ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
    rw [twistLin_apply, twistLin_apply, fnTwist_inv_fnTwist]
    exact hφ
  · intro h
    exact ⟨fnTwist F η ψ, ⟨ψ, h, rfl⟩, fnTwist_inv_fnTwist F η ψ⟩

theorem isFiniteOrderHeckeChar_inv {η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hη : HeckeCharacter.IsFiniteOrderHeckeChar F η) :
    HeckeCharacter.IsFiniteOrderHeckeChar F η⁻¹ where
  isIdeleClassChar u := by rw [MonoidHom.inv_apply, hη.isIdeleClassChar u, inv_one]
  continuous := by
    have : (η⁻¹ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) = fun x => (η x)⁻¹ := by ext x; rfl
    rw [this]
    exact hη.continuous.inv
  isOfFinOrder := hη.isOfFinOrder.inv

theorem twistedCentralChar_twistedCentralChar_inv (Z : Subgroup (AdeleRing (𝓞 F) F)ˣ) (ξ : Z →* ℂˣ)
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) :
    twistedCentralChar F Z (twistedCentralChar F Z ξ η) η⁻¹ = ξ := by
  ext z
  simp [twistedCentralChar, mul_assoc]

theorem rightTranslate_fnTwist (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (g : AdelicGL2 (𝓞 F) F) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    rightTranslate F g (fnTwist F η φ) = chiDet (𝓞 F) F η g • fnTwist F η (rightTranslate F g φ) := by
  funext x
  simp only [rightTranslate_apply, fnTwist_apply, Pi.smul_apply, smul_eq_mul, chiDet, map_mul, Units.val_mul]
  ring

theorem det_rowIsometryInclAt₀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    Matrix.GeneralLinearGroup.det (rowIsometryInclAt₀ F w k) = 1 := by
  have hk : ((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det = 1 :=
    ((mem_rowIsometrySubgroup₀_iff w.Completion).mp k.2).1
  set g : AdelicGL2 (𝓞 F) F := rowIsometryInclAt₀ F w k with hg

  have harch := Matrix.GeneralLinearGroup.map_det (AdelicLevel.adeleArch (𝓞 F) F) g
  rw [show Matrix.GeneralLinearGroup.map (AdelicLevel.adeleArch (𝓞 F) F) = AdelicLevel.glArch (𝓞 F) F from rfl] at harch
  have hfin := Matrix.GeneralLinearGroup.map_det (AdelicLevel.adeleFin (𝓞 F) F) g
  rw [show Matrix.GeneralLinearGroup.map (AdelicLevel.adeleFin (𝓞 F) F) = AdelicLevel.glFin (𝓞 F) F from rfl] at hfin
  have hgarch : AdelicLevel.glArch (𝓞 F) F g = archGLIncl F w k := by
    rw [hg, rowIsometryInclAt₀_apply, adelicArchGLInclAt, MonoidHom.comp_apply, glArch_adelicArchGLIncl]
  have hgfin : AdelicLevel.glFin (𝓞 F) F g = 1 := by
    rw [hg, rowIsometryInclAt₀_apply, adelicArchGLInclAt, MonoidHom.comp_apply, glFin_adelicArchGLIncl]

  have hdarch : Matrix.GeneralLinearGroup.det (archGLIncl F w (k : GL (Fin 2) w.Completion)) = 1 := by
    apply Units.ext
    funext v
    have hv := Matrix.GeneralLinearGroup.map_det (AdelicLevel.archEval F v) (archGLIncl F w (k : GL (Fin 2) w.Completion))
    rw [show Matrix.GeneralLinearGroup.map (AdelicLevel.archEval F v) = AdelicLevel.archComponent F v from rfl] at hv
    have hv' := congrArg Units.val hv
    rw [Units.coe_map] at hv'
    change _ = (AdelicLevel.archEval F v) (Matrix.GeneralLinearGroup.det (archGLIncl F w ↑k)).val at hv'
    rw [AdelicLevel.archEval_apply] at hv'
    rw [Units.val_one, ← hv']
    by_cases hvw : v = w
    · subst hvw
      rw [archComponent_archGLIncl_self, Matrix.GeneralLinearGroup.val_det_apply, hk]
      rfl
    · rw [archComponent_archGLIncl_of_ne F hvw, map_one, Units.val_one]
      rfl
  rw [hgarch, hdarch] at harch
  rw [hgfin, map_one] at hfin
  apply Units.ext
  refine Prod.ext ?_ ?_
  · have := congrArg Units.val harch
    rw [Units.coe_map] at this
    exact this.symm
  · have := congrArg Units.val hfin
    rw [Units.coe_map] at this
    exact this.symm

theorem chiDet_mul_rowIsometryInclAt₀ (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (w : InfinitePlace F)
    (k : rowIsometrySubgroup₀ w.Completion) (x : AdelicGL2 (𝓞 F) F) :
    chiDet (𝓞 F) F η (x * rowIsometryInclAt₀ F w k) = chiDet (𝓞 F) F η x := by
  simp only [chiDet, map_mul, det_rowIsometryInclAt₀, mul_one]

theorem rightTranslate_rowIsometryInclAt₀_fnTwist (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (w : InfinitePlace F)
    (k : rowIsometrySubgroup₀ w.Completion) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    rightTranslate F (rowIsometryInclAt₀ F w k) (fnTwist F η φ) =
      fnTwist F η (rightTranslate F (rowIsometryInclAt₀ F w k) φ) := by
  funext x
  simp only [rightTranslate_apply, fnTwist_apply, chiDet_mul_rowIsometryInclAt₀]

theorem rightConv_fnTwist (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (φ f : AdelicGL2 (𝓞 F) F → ℂ) :
    rightConv F (fnTwist F η φ) f = fnTwist F η (rightConv F φ (fun x => chiDet (𝓞 F) F η x * f x)) := by
  funext g
  rw [rightConv_apply, fnTwist_apply, rightConv_apply]
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  rw [← integral_const_mul]
  congr 1
  funext x
  simp only [fnTwist_apply, chiDet, map_mul, Units.val_mul]
  ring

theorem mul_mem_typeSubmodule {G H W : Type*} [Group G] [Group H] [AddCommGroup W] [Module ℂ W]
    (ι : H →* G) (ρ : Representation ℂ H W) (c : G → ℂ) (hc : ∀ x k, c (x * ι k) = c x)
    {f : G → ℂ} (hf : f ∈ typeSubmodule ι ρ) : (fun x => c x * f x) ∈ typeSubmodule ι ρ := by
  refine Submodule.span_induction (p := fun f _ => (fun x => c x * f x) ∈ typeSubmodule ι ρ) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨T, hT, v, rfl⟩
    let T' : W →ₗ[ℂ] (G → ℂ) :=
      { toFun := fun v x => c x * T v x
        map_add' := fun v v' => by funext x; simp [mul_add]
        map_smul' := fun a v => by funext x; simp; ring }
    have hT' : IsRightEquivariant ι ρ T' := by
      intro k v x
      show c x * T (ρ k v) x = c (x * ι k) * T v (x * ι k)
      rw [hT k v x, hc]
    exact mem_typeSubmodule_of_isRightEquivariant hT' v
  · have : (fun x => c x * (0 : G → ℂ) x) = 0 := by funext x; simp
    show (fun x => c x * (0 : G → ℂ) x) ∈ _
    rw [this]; exact Submodule.zero_mem _
  · intro f g _ _ hf hg
    have : (fun x => c x * (f + g) x) = (fun x => c x * f x) + (fun x => c x * g x) := by
      funext x; simp [mul_add]
    rw [this]; exact Submodule.add_mem _ hf hg
  · intro a f _ hf
    have : (fun x => c x * (a • f) x) = a • (fun x => c x * f x) := by
      funext x; simp; ring
    rw [this]; exact Submodule.smul_mem _ a hf

theorem mul_mem_iSup_of_forall {G : Type*} (c : G → ℂ) {n : ℕ} (S : Fin n → Submodule ℂ (G → ℂ))
    (hS : ∀ i f, f ∈ S i → (fun x => c x * f x) ∈ S i)
    {f : G → ℂ} (hf : f ∈ ⨆ i, S i) : (fun x => c x * f x) ∈ ⨆ i, S i := by
  let L : (G → ℂ) →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun f x => c x * f x
      map_add' := fun f g => by funext x; simp [mul_add]
      map_smul' := fun a f => by funext x; simp; ring }
  have key : ∀ i, (S i).map L ≤ S i := by
    rintro i _ ⟨g, hg, rfl⟩
    exact hS i g hg
  have hmap : (⨆ i, S i).map L ≤ ⨆ i, S i := by
    rw [Submodule.map_iSup]; exact iSup_mono key
  exact hmap (Submodule.mem_map_of_mem hf)

theorem chiDet_mul_mem_archCutSubmodule (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (tys : ArchTypeFamily F)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ archCutSubmodule F tys) :
    (fun x => chiDet (𝓞 F) F η x * φ x) ∈ archCutSubmodule F tys := by
  rw [mem_archCutSubmodule_iff] at hφ ⊢
  intro w
  exact mul_mem_iSup_of_forall (chiDet (𝓞 F) F η) (fun i => archTypeSubmoduleAt F w (tys.rep w i))
    (fun i f hf => mul_mem_typeSubmodule _ _ (chiDet (𝓞 F) F η) (fun x k => chiDet_mul_rowIsometryInclAt₀ F η w k x) hf) (hφ w)

theorem chiDet_mul_mem_archDualCutSubmodule (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (tys : ArchTypeFamily F)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ archDualCutSubmodule F tys) :
    (fun x => chiDet (𝓞 F) F η x * φ x) ∈ archDualCutSubmodule F tys := by
  rw [mem_archDualCutSubmodule_iff] at hφ ⊢
  intro w
  exact mul_mem_iSup_of_forall (chiDet (𝓞 F) F η) (fun i => archDualTypeSubmoduleAt F w (tys.rep w i))
    (fun i f hf => mul_mem_typeSubmodule _ _ (chiDet (𝓞 F) F η) (fun x k => chiDet_mul_rowIsometryInclAt₀ F η w k x) hf) (hφ w)

theorem fnTwist_mem_archCutSubmodule (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (tys : ArchTypeFamily F)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ archCutSubmodule F tys) : fnTwist F η φ ∈ archCutSubmodule F tys :=
  chiDet_mul_mem_archCutSubmodule F η tys hφ

theorem isArchBiFinite_chiDet_mul (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (tys : ArchTypeFamily F)
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : IsArchBiFinite F tys f) :
    IsArchBiFinite F tys (fun x => chiDet (𝓞 F) F η x * f x) := by
  refine ⟨?_, chiDet_mul_mem_archDualCutSubmodule F η tys hf.2⟩
  have h : (fun x => (fun x => chiDet (𝓞 F) F η x * f x) x⁻¹) = fun x => chiDet (𝓞 F) F η⁻¹ x * (fun x => f x⁻¹) x := by
    funext x
    simp only [chiDet, map_inv, MonoidHom.inv_apply]
  rw [h]
  exact chiDet_mul_mem_archCutSubmodule F η⁻¹ tys hf.1

theorem isSmoothCuspAutomorphicFnAt_smul (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ) (c : ℂ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsSmoothCuspAutomorphicFnAt F pins ξ φ) :
    IsSmoothCuspAutomorphicFnAt F pins ξ (c • φ) := by
  obtain ⟨⟨haut, hcusp⟩, hkf⟩ := hφ
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := pins.mS
    have h := (lsXiMemberAt_iff (𝓞 F) F pins.μ pins.Z ξ pins.D φ).mp haut
    refine (lsXiMemberAt_iff (𝓞 F) F pins.μ pins.Z ξ pins.D (c • φ)).mpr ⟨⟨fun γ g => ?_, fun z g => ?_⟩, h.2.const_smul c⟩
    · simp only [Pi.smul_apply, h.1.left_invariant γ g]
    · simp only [Pi.smul_apply, h.1.central_transform z g, smul_eq_mul]; ring
  · letI : MeasurableSpace (AdeleRing (𝓞 F) F) := pins.nS
    intro g
    have hpt : ∀ q, constantTermIntegrand unipotentGL2 (c • φ) g q = c * constantTermIntegrand unipotentGL2 φ g q :=
      fun q => rfl
    unfold constantTerm
    rw [show (fun q => constantTermIntegrand unipotentGL2 (c • φ) g q) = fun q => c * constantTermIntegrand unipotentGL2 φ g q
      from funext hpt, integral_const_mul, show (∫ q, constantTermIntegrand unipotentGL2 φ g q ∂pins.ν) = 0 from hcusp g, mul_zero]
  · show IsKfSmooth F (fun g => c * φ g)
    exact isSmoothVector_rightTranslationFn_mul (isKfSmooth_const F c) hkf

theorem continuous_fnTwist {η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hη : Continuous η) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : Continuous φ) : Continuous (fnTwist F η φ) :=
  (Units.continuous_val.comp (hη.comp Matrix.GeneralLinearGroup.continuous_det)).mul hφ

theorem isCuspSubrep_map_twistLin
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F) (B : Set (AdeleRing (𝓞 F) F))
    (ξ : (productionPinsOf F D U gen B).Z →* ℂˣ)
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hη : HeckeCharacter.IsFiniteOrderHeckeChar F η)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hV : IsCuspSubrep F (productionPinsOf F D U gen B) ξ V) :
    IsCuspSubrep F (productionPinsOf F D U gen B) (twistedCentralChar F _ ξ η) (V.map (twistLin F η)) where
  le := by
    rintro _ ⟨φ, hφ, rfl⟩
    have hφK := hV.le hφ

    refine Submodule.span_induction
      (p := fun φ _ => twistLin F η φ ∈ cuspKFiniteSubmodule F (productionPinsOf F D U gen B) (twistedCentralChar F _ ξ η))
      ?_ ?_ ?_ ?_ hφK
    · rintro ψ ⟨hsat, hcont, tys, htys⟩
      refine Submodule.subset_span ⟨fun g => ?_, continuous_fnTwist F hη.continuous hcont, tys,
        fnTwist_mem_archCutSubmodule F η tys htys⟩
      rw [twistLin_apply, rightTranslate_fnTwist]
      exact isSmoothCuspAutomorphicFnAt_smul F _ _ _
        (AutomorphicForm.isSmoothCuspAutomorphicFnAt_twistedCentralChar_fnTwist_productionPinsOf F D U gen B ξ η hη _ (hsat g))
    · show twistLin F η 0 ∈ _
      rw [map_zero]; exact Submodule.zero_mem _
    · intro x y _ _ hx hy
      show twistLin F η (x + y) ∈ _
      rw [map_add]; exact Submodule.add_mem _ hx hy
    · intro c x _ hx
      show twistLin F η (c • x) ∈ _
      rw [map_smul]; exact Submodule.smul_mem _ c hx
  rightTranslate_fin_mem := by
    rintro g hg _ ⟨φ, hφ, rfl⟩
    rw [twistLin_apply, rightTranslate_fnTwist]
    exact Submodule.smul_mem _ _ ⟨rightTranslate F g φ, hV.rightTranslate_fin_mem g hg φ hφ, rfl⟩
  rightTranslate_arch_mem := by
    rintro w k _ ⟨φ, hφ, rfl⟩
    rw [twistLin_apply, rightTranslate_rowIsometryInclAt₀_fnTwist]
    exact ⟨_, hV.rightTranslate_arch_mem w k φ hφ, rfl⟩
  rightConv_mem := by
    rintro f tys hf hbi _ ⟨φ, hφ, rfl⟩
    rw [twistLin_apply, rightConv_fnTwist]
    exact ⟨_, hV.rightConv_mem _ tys
      (AutomorphicForm.isFactorizableTestFn_chiDet_mul_of_continuous_of_isOfFinOrder F η hη.continuous hη.isOfFinOrder f hf)
      (isArchBiFinite_chiDet_mul F η tys hbi) φ hφ, rfl⟩

end P2mS28R7
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_isCuspConstituent_twistedCentralChar_span_image_fnTwist.P2mS28R7"

end
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_isCuspConstituent_twistedCentralChar_span_image_fnTwist.P2mS28R7"

open P2mS28R7 in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F) (B : Set (AdeleRing (𝓞 F) F))
    (ξ : (productionPinsOf F D U gen B).Z →* ℂˣ)
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hη : HeckeCharacter.IsFiniteOrderHeckeChar F η)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hV : IsCuspConstituent F (productionPinsOf F D U gen B) ξ V) :
    IsCuspConstituent F (productionPinsOf F D U gen B) (twistedCentralChar F _ ξ η)
      (Submodule.span ℂ ((fun φ => fnTwist F η φ) '' (V : Set (AdelicGL2 (𝓞 F) F → ℂ)))) := by
  rw [span_image_fnTwist]
  refine ⟨isCuspSubrep_map_twistLin F D U gen B ξ η hη V hV.1, ?_, ?_⟩
  ·
    intro h
    apply hV.2.1
    rw [← map_twistLin_inv_map_twistLin F η V, h, Submodule.map_bot]
  ·
    intro W hW hWle
    have hW' : IsCuspSubrep F (productionPinsOf F D U gen B) ξ (W.map (twistLin F η⁻¹)) := by
      have := isCuspSubrep_map_twistLin F D U gen B (twistedCentralChar F _ ξ η) η⁻¹
        (isFiniteOrderHeckeChar_inv F hη) W hW
      rwa [twistedCentralChar_twistedCentralChar_inv] at this
    have hle : W.map (twistLin F η⁻¹) ≤ V := by
      rintro _ ⟨ψ, hψ, rfl⟩
      obtain ⟨φ, hφ, hφψ⟩ := hWle hψ
      rw [twistLin_apply, ← hφψ, twistLin_apply, fnTwist_inv_fnTwist]
      exact hφ
    rcases hV.2.2 _ hW' hle with h | h
    · left
      rw [← map_twistLin_map_twistLin_inv F η W, h, Submodule.map_bot]
    · right
      rw [← map_twistLin_map_twistLin_inv F η W, h]

end S_AutomorphicForm_CuspidalConstituent_isCuspConstituent_twistedCentralChar_span_image_fnTwist
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_isCuspConstituent_twistedCentralChar_span_image_fnTwist (solution)
