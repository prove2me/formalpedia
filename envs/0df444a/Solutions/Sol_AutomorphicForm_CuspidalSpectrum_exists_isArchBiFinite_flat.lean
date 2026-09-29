-- Prove2me | solution 1 for AutomorphicForm.CuspidalSpectrum.exists_isArchBiFinite_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/0a78a4e1-9bb1-5171-9120-053842048fc3

import Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_isArchBiFinite_flat

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace FlatBiFiniteProof

open Module

section General

variable {H G : Type*} [Group H] [Group G]
variable {W W' : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

private def transportRep (e : W ≃ₗ[ℂ] W') (ρ : Representation ℂ H W) : Representation ℂ H W' where
  toFun k := e.toLinearMap ∘ₗ ρ k ∘ₗ e.symm.toLinearMap
  map_one' := by ext v; simp
  map_mul' k k' := by ext v; simp

@[scoped simp] private theorem transportRep_apply (e : W ≃ₗ[ℂ] W') (ρ : Representation ℂ H W) (k : H) (v : W') :
    transportRep e ρ k v = e (ρ k (e.symm v)) := rfl

private theorem typeSubmodule_le_of_equiv (ι : H →* G) (ρ : Representation ℂ H W) (ρ' : Representation ℂ H W')
    (Ψ : W ≃ₗ[ℂ] W') (hΨ : ∀ (k : H) (v : W), Ψ (ρ k v) = ρ' k (Ψ v)) :
    typeSubmodule ι ρ ≤ typeSubmodule ι ρ' := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨T, hT, v, rfl⟩
  have hΨ' : ∀ (k : H) (u : W'), ρ k (Ψ.symm u) = Ψ.symm (ρ' k u) := fun k u => by
    apply Ψ.injective
    rw [hΨ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hT' : IsRightEquivariant ι ρ' (T ∘ₗ Ψ.symm.toLinearMap) := fun k u x => by
    show T (Ψ.symm (ρ' k u)) x = T (Ψ.symm u) (x * ι k)
    rw [← hΨ', hT]
  have : T v = (T ∘ₗ Ψ.symm.toLinearMap) (Ψ v) := by simp
  rw [this]
  exact mem_typeSubmodule_of_isRightEquivariant hT' _

end General

section Conj

variable {H G : Type*} [Group H] [Group G] {n : ℕ}

private def conjRep (ρ : Representation ℂ H (Fin n → ℂ)) : Representation ℂ H (Fin n → ℂ) where
  toFun k :=
    { toFun := fun v => star (ρ k (star v))
      map_add' := fun v w => by simp [star_add]
      map_smul' := fun c v => by simp [star_smul] }
  map_one' := by ext v i; simp
  map_mul' k k' := by ext v i; simp

@[scoped simp] private theorem conjRep_apply (ρ : Representation ℂ H (Fin n → ℂ)) (k : H) (v : Fin n → ℂ) :
    conjRep ρ k v = star (ρ k (star v)) := rfl

private theorem conj_mem_typeSubmodule_conjRep (ι : H →* G) (ρ : Representation ℂ H (Fin n → ℂ)) {f : G → ℂ}
    (hf : f ∈ typeSubmodule ι ρ) : (fun x => starRingEnd ℂ (f x)) ∈ typeSubmodule ι (conjRep ρ) := by
  refine Submodule.span_induction (p := fun f _ => (fun x => starRingEnd ℂ (f x)) ∈ typeSubmodule ι (conjRep ρ))
    ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨T, hT, v, rfl⟩
    let Tb : (Fin n → ℂ) →ₗ[ℂ] (G → ℂ) :=
      { toFun := fun u x => starRingEnd ℂ (T (star u) x)
        map_add' := fun u₁ u₂ => funext fun x => by simp [star_add, map_add]
        map_smul' := fun c u => funext fun x => by simp [star_smul, map_smul] }
    have hTb : IsRightEquivariant ι (conjRep ρ) Tb := fun k u x => by
      show starRingEnd ℂ (T (star (star (ρ k (star u)))) x) = starRingEnd ℂ (T (star u) (x * ι k))
      rw [star_star, hT]
    have : (fun x => starRingEnd ℂ (T v x)) = Tb (star v) := by
      funext x; show _ = starRingEnd ℂ (T (star (star v)) x); rw [star_star]
    rw [this]
    exact mem_typeSubmodule_of_isRightEquivariant hTb _
  · show (fun x => starRingEnd ℂ ((0 : G → ℂ) x)) ∈ typeSubmodule ι (conjRep ρ)
    have : (fun x => starRingEnd ℂ ((0 : G → ℂ) x)) = 0 := by funext x; simp
    rw [this]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb
    have : (fun x => starRingEnd ℂ ((a + b) x)) = (fun x => starRingEnd ℂ (a x)) + fun x => starRingEnd ℂ (b x) := by
      funext x; simp
    rw [this]; exact Submodule.add_mem _ ha hb
  · intro c a _ ha
    have : (fun x => starRingEnd ℂ ((c • a) x)) = starRingEnd ℂ c • fun x => starRingEnd ℂ (a x) := by
      funext x; simp
    rw [this]; exact Submodule.smul_mem _ _ ha

private def dualToPi (n : ℕ) : Module.Dual ℂ (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) := (Pi.basisFun ℂ (Fin n)).toDualEquiv.symm

private def pieceA (ρ : Representation ℂ H (Fin n → ℂ)) : Representation ℂ H (Fin n → ℂ) :=
  conjRep (transportRep (dualToPi n) ρ.dual)

private def pieceB (ρ : Representation ℂ H (Fin n → ℂ)) : Representation ℂ H (Fin n → ℂ) :=
  transportRep (dualToPi n) (conjRep ρ).dual

private theorem conj_mem_typeSubmodule_pieceA (ι : H →* G) (ρ : Representation ℂ H (Fin n → ℂ)) {f : G → ℂ}
    (hf : f ∈ typeSubmodule ι ρ.dual) : (fun x => starRingEnd ℂ (f x)) ∈ typeSubmodule ι (pieceA ρ) := by
  have h1 : f ∈ typeSubmodule ι (transportRep (dualToPi n) ρ.dual) :=
    typeSubmodule_le_of_equiv ι ρ.dual _ (dualToPi n) (fun k v => by simp) hf
  exact conj_mem_typeSubmodule_conjRep ι _ h1

private theorem typeSubmodule_le_pieceB_dual (ι : H →* G) (ρ : Representation ℂ H (Fin n → ℂ)) :
    typeSubmodule ι (conjRep ρ) ≤ typeSubmodule ι (pieceB ρ).dual := by
  set π : Representation ℂ H (Fin n → ℂ) := conjRep ρ

  let Ψ : (Fin n → ℂ) ≃ₗ[ℂ] Module.Dual ℂ (Fin n → ℂ) :=
    (Module.evalEquiv ℂ (Fin n → ℂ)).trans (dualToPi n).symm.dualMap
  refine typeSubmodule_le_of_equiv ι π (pieceB ρ).dual Ψ fun k v => ?_
  apply LinearMap.ext
  intro u
  simp only [Ψ, pieceB, LinearEquiv.trans_apply, LinearEquiv.dualMap_apply, Representation.dual_apply,
    Module.Dual.transpose_apply, LinearMap.comp_apply, transportRep_apply, LinearEquiv.symm_apply_apply, inv_inv]
  rfl

end Conj

section Det

variable {F : Type} [Field F] [NumberField F]

private theorem det_map_generalLinearGroup {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (g : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map φ g) = Units.map φ.toMonoidHom (Matrix.GeneralLinearGroup.det g) := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rfl

private theorem det_rowIsometryInclAt₀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    Matrix.GeneralLinearGroup.det (rowIsometryInclAt₀ F w k) = 1 := by
  have hk : ((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det = 1 :=
    ((mem_rowIsometrySubgroup₀_iff (K := w.Completion)).mp k.2).1

  have hfin : Units.map (adeleFin (𝓞 F) F).toMonoidHom (Matrix.GeneralLinearGroup.det (rowIsometryInclAt₀ F w k)) = 1 := by
    rw [← det_map_generalLinearGroup]
    show Matrix.GeneralLinearGroup.det (glFin (𝓞 F) F (rowIsometryInclAt₀ F w k)) = 1
    rw [glFin_rowIsometryInclAt₀, map_one]

  have harch : ∀ v : InfinitePlace F, Units.map ((archEval F v).comp (adeleArch (𝓞 F) F)).toMonoidHom
      (Matrix.GeneralLinearGroup.det (rowIsometryInclAt₀ F w k)) = 1 := by
    intro v
    rw [← det_map_generalLinearGroup]
    have : Matrix.GeneralLinearGroup.map ((archEval F v).comp (adeleArch (𝓞 F) F)) (rowIsometryInclAt₀ F w k)
        = archComponent F v (glArch (𝓞 F) F (rowIsometryInclAt₀ F w k)) := rfl
    rw [this, glArch_rowIsometryInclAt₀]
    by_cases hv : v = w
    · subst hv
      show Matrix.GeneralLinearGroup.det (archComponent F v (archGLIncl F v (k : GL (Fin 2) v.Completion))) = 1
      rw [archComponent_archGLIncl_self]
      exact Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply, hk, Units.val_one])
    · show Matrix.GeneralLinearGroup.det (archComponent F v (archGLIncl F w (k : GL (Fin 2) w.Completion))) = 1
      rw [archComponent_archGLIncl_of_ne F hv, map_one]
  refine Units.ext (Prod.ext (funext fun v => ?_) ?_)
  · have := congrArg (fun u : (v.Completion)ˣ => (u : v.Completion)) (harch v)
    simp at this
    exact this
  · have := congrArg (fun u : (FiniteAdeleRing (𝓞 F) F)ˣ => (u : FiniteAdeleRing (𝓞 F) F)) hfin
    simp at this
    exact this

private theorem weight_mul_rowIsometryInclAt₀ (σ : ℝ) (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion)
    (x : AdelicGL2 (𝓞 F) F) :
    ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (x * rowIsometryInclAt₀ F w k)) ^ (-σ) : ℝ) : ℂ)
      = ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ) := by
  rw [map_mul, det_rowIsometryInclAt₀, mul_one]

private theorem weight_inv_mul_rowIsometryInclAt₀ (σ : ℝ) (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion)
    (x : AdelicGL2 (𝓞 F) F) :
    ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (x * rowIsometryInclAt₀ F w k)⁻¹) ^ (-σ) : ℝ) : ℂ)
      = ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x⁻¹) ^ (-σ) : ℝ) : ℂ) := by
  rw [mul_inv_rev, map_mul, ← map_inv (rowIsometryInclAt₀ F w), det_rowIsometryInclAt₀, one_mul]

end Det

section Family

variable {F : Type} [Field F] [NumberField F]

private def newRep (tys : ArchTypeFamily F) (w : InfinitePlace F) : Fin (tys.card w + tys.card w) → ArchRepAt F w :=
  Fin.addCases (fun i => ⟨(tys.rep w i).n, pieceA (tys.rep w i).ρ⟩) (fun i => ⟨(tys.rep w i).n, pieceB (tys.rep w i).ρ⟩)

private def newFamily (tys : ArchTypeFamily F) : ArchTypeFamily F := ⟨fun w => tys.card w + tys.card w, newRep tys⟩

private theorem newFamily_rep_castAdd (tys : ArchTypeFamily F) (w : InfinitePlace F) (i : Fin (tys.card w)) :
    (newFamily tys).rep w (Fin.castAdd (tys.card w) i) = ⟨(tys.rep w i).n, pieceA (tys.rep w i).ρ⟩ := by
  simp [newFamily, newRep]

private theorem newFamily_rep_natAdd (tys : ArchTypeFamily F) (w : InfinitePlace F) (i : Fin (tys.card w)) :
    (newFamily tys).rep w (Fin.natAdd (tys.card w) i) = ⟨(tys.rep w i).n, pieceB (tys.rep w i).ρ⟩ :=
  Fin.addCases_right (m := tys.card w) (n := tys.card w) (motive := fun _ => ArchRepAt F w)
    (left := fun i => ⟨(tys.rep w i).n, pieceA (tys.rep w i).ρ⟩)
    (right := fun i => ⟨(tys.rep w i).n, pieceB (tys.rep w i).ρ⟩) i

end Family

end FlatBiFiniteProof
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_isArchBiFinite_flat.FlatBiFiniteProof"

end
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_isArchBiFinite_flat.FlatBiFiniteProof"

open FlatBiFiniteProof in
theorem solution
    (F : Type) [Field F] [NumberField F] (σ : ℝ) (tys : ArchTypeFamily F)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) (hft : IsArchBiFinite F tys f) :
    ∃ tys' : ArchTypeFamily F, IsArchBiFinite F tys' (flat F σ f) := by
  classical
  obtain ⟨hcut, hdual⟩ := hft
  refine ⟨newFamily tys, ?_, ?_⟩
  ·
    rw [mem_archCutSubmodule_iff]
    intro w
    have hw := (mem_archDualCutSubmodule_iff F tys f).mp hdual w
    have key : ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, φ ∈ (⨆ i : Fin (tys.card w), archDualTypeSubmoduleAt F w (tys.rep w i)) →
        (fun x => starRingEnd ℂ (φ x) *
          ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x⁻¹) ^ (-σ) : ℝ) : ℂ))
          ∈ ⨆ j : Fin ((newFamily tys).card w), archTypeSubmoduleAt F w ((newFamily tys).rep w j) := by
      intro φ hφ
      refine Submodule.iSup_induction _ (motive := fun φ => (fun x => starRingEnd ℂ (φ x) *
          ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x⁻¹) ^ (-σ) : ℝ) : ℂ))
          ∈ ⨆ j : Fin ((newFamily tys).card w), archTypeSubmoduleAt F w ((newFamily tys).rep w j)) hφ ?_ ?_ ?_
      · intro i φ hφi
        have h1 := conj_mem_typeSubmodule_pieceA (rowIsometryInclAt₀ F w) (tys.rep w i).ρ hφi
        have h2 : (fun x => starRingEnd ℂ (φ x) *
            ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x⁻¹) ^ (-σ) : ℝ) : ℂ))
            ∈ typeSubmodule (rowIsometryInclAt₀ F w) (pieceA (tys.rep w i).ρ) :=
          comp_mul_mem_typeSubmodule_of_hom (ι := rowIsometryInclAt₀ F w) (ι' := rowIsometryInclAt₀ F w)
            (MonoidHom.id (AdelicGL2 (𝓞 F) F)) (fun _ => rfl)
            (m := fun x => ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x⁻¹) ^ (-σ) : ℝ) : ℂ))
            (fun k x => weight_inv_mul_rowIsometryInclAt₀ σ w k x) h1
        refine le_iSup (fun j => archTypeSubmoduleAt F w ((newFamily tys).rep w j)) (Fin.castAdd (tys.card w) i) ?_
        show _ ∈ typeSubmodule (rowIsometryInclAt₀ F w) ((newFamily tys).rep w (Fin.castAdd (tys.card w) i)).ρ
        rw [newFamily_rep_castAdd]
        exact h2
      · show (fun x : AdelicGL2 (𝓞 F) F => starRingEnd ℂ ((0 : AdelicGL2 (𝓞 F) F → ℂ) x) *
            ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x⁻¹) ^ (-σ) : ℝ) : ℂ)) ∈ _
        have : (fun x : AdelicGL2 (𝓞 F) F => starRingEnd ℂ ((0 : AdelicGL2 (𝓞 F) F → ℂ) x) *
            ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x⁻¹) ^ (-σ) : ℝ) : ℂ)) = 0 := by
          funext x; simp
        rw [this]; exact Submodule.zero_mem _
      · intro a b ha hb
        have : (fun x : AdelicGL2 (𝓞 F) F => starRingEnd ℂ ((a + b) x) *
            ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x⁻¹) ^ (-σ) : ℝ) : ℂ))
            = (fun x => starRingEnd ℂ (a x) *
              ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x⁻¹) ^ (-σ) : ℝ) : ℂ))
              + fun x => starRingEnd ℂ (b x) *
              ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x⁻¹) ^ (-σ) : ℝ) : ℂ) := by
          funext x; simp [add_mul]
        rw [this]; exact Submodule.add_mem _ ha hb
    have hφ : (fun x => flat F σ f x⁻¹) = fun x => starRingEnd ℂ (f x) *
        ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x⁻¹) ^ (-σ) : ℝ) : ℂ) := by
      funext x; simp [flat, inv_inv]
    rw [hφ]
    exact key f hw
  ·
    rw [mem_archDualCutSubmodule_iff]
    intro w
    have hw := (mem_archCutSubmodule_iff F tys (fun x => f x⁻¹)).mp hcut w
    have key : ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, φ ∈ (⨆ i : Fin (tys.card w), archTypeSubmoduleAt F w (tys.rep w i)) →
        (fun x => starRingEnd ℂ (φ x) *
          ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ))
          ∈ ⨆ j : Fin ((newFamily tys).card w), archDualTypeSubmoduleAt F w ((newFamily tys).rep w j) := by
      intro φ hφ
      refine Submodule.iSup_induction _ (motive := fun φ => (fun x => starRingEnd ℂ (φ x) *
          ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ))
          ∈ ⨆ j : Fin ((newFamily tys).card w), archDualTypeSubmoduleAt F w ((newFamily tys).rep w j)) hφ ?_ ?_ ?_
      · intro i φ hφi
        have h1 := conj_mem_typeSubmodule_conjRep (rowIsometryInclAt₀ F w) (tys.rep w i).ρ hφi
        have h2 : (fun x => starRingEnd ℂ (φ x) *
            ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ))
            ∈ typeSubmodule (rowIsometryInclAt₀ F w) (conjRep (tys.rep w i).ρ) :=
          comp_mul_mem_typeSubmodule_of_hom (ι := rowIsometryInclAt₀ F w) (ι' := rowIsometryInclAt₀ F w)
            (MonoidHom.id (AdelicGL2 (𝓞 F) F)) (fun _ => rfl)
            (m := fun x => ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ))
            (fun k x => weight_mul_rowIsometryInclAt₀ σ w k x) h1
        have h3 := typeSubmodule_le_pieceB_dual (rowIsometryInclAt₀ F w) (tys.rep w i).ρ h2
        refine le_iSup (fun j => archDualTypeSubmoduleAt F w ((newFamily tys).rep w j)) (Fin.natAdd (tys.card w) i) ?_
        show _ ∈ typeSubmodule (rowIsometryInclAt₀ F w) ((newFamily tys).rep w (Fin.natAdd (tys.card w) i)).ρ.dual
        rw [newFamily_rep_natAdd]
        exact h3
      · show (fun x : AdelicGL2 (𝓞 F) F => starRingEnd ℂ ((0 : AdelicGL2 (𝓞 F) F → ℂ) x) *
            ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)) ∈ _
        have : (fun x : AdelicGL2 (𝓞 F) F => starRingEnd ℂ ((0 : AdelicGL2 (𝓞 F) F → ℂ) x) *
            ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)) = 0 := by
          funext x; simp
        rw [this]; exact Submodule.zero_mem _
      · intro a b ha hb
        have : (fun x : AdelicGL2 (𝓞 F) F => starRingEnd ℂ ((a + b) x) *
            ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ))
            = (fun x => starRingEnd ℂ (a x) *
              ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ))
              + fun x => starRingEnd ℂ (b x) *
              ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ) := by
          funext x; simp [add_mul]
        rw [this]; exact Submodule.add_mem _ ha hb
    have hφ : flat F σ f = fun x => starRingEnd ℂ ((fun y => f y⁻¹) x) *
        ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ) := by
      funext x; simp [flat]
    rw [hφ]
    exact key _ hw

end S_AutomorphicForm_CuspidalSpectrum_exists_isArchBiFinite_flat
end P2MW
export P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_isArchBiFinite_flat (solution)
