-- Prove2me | solution 1 for AutomorphicForm.exists_archTypeFamily_isArchFactorBiFinite_of_finiteDimensional_span_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/3295180c-46ea-548d-bfec-7f6905b7af26

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_archTypeFamily_isArchFactorBiFinite_of_finiteDimensional_span_range

set_option autoImplicit false

open NumberField

namespace RightFiniteTypes

noncomputable section

open AutomorphicForm

section Generic

variable {H G : Type*} [Group H] [Group G]

private def translateOn (ι : H →* G) (V : Submodule ℂ (G → ℂ))
    (hV : ∀ k : H, ∀ v ∈ V, (fun x => v (x * ι k)) ∈ V) (k : H) : V →ₗ[ℂ] V where
  toFun v := ⟨fun x => (v : G → ℂ) (x * ι k), hV k v v.2⟩
  map_add' _ _ := Subtype.ext (funext fun _ => rfl)
  map_smul' _ _ := Subtype.ext (funext fun _ => rfl)

private theorem translateOn_apply_coe (ι : H →* G) (V : Submodule ℂ (G → ℂ))
    (hV : ∀ k : H, ∀ v ∈ V, (fun x => v (x * ι k)) ∈ V) (k : H) (v : V) (x : G) :
    (translateOn ι V hV k v : G → ℂ) x = (v : G → ℂ) (x * ι k) :=
  rfl

private theorem translateOn_one (ι : H →* G) (V : Submodule ℂ (G → ℂ))
    (hV : ∀ k : H, ∀ v ∈ V, (fun x => v (x * ι k)) ∈ V) :
    translateOn ι V hV 1 = LinearMap.id :=
  LinearMap.ext fun v => Subtype.ext (funext fun x => by simp [translateOn_apply_coe])

private theorem translateOn_mul (ι : H →* G) (V : Submodule ℂ (G → ℂ))
    (hV : ∀ k : H, ∀ v ∈ V, (fun x => v (x * ι k)) ∈ V) (k₁ k₂ : H) :
    translateOn ι V hV (k₁ * k₂) = translateOn ι V hV k₁ ∘ₗ translateOn ι V hV k₂ :=
  LinearMap.ext fun v => Subtype.ext (funext fun x => by simp [translateOn_apply_coe, mul_assoc])

private def transportRep (ι : H →* G) (V : Submodule ℂ (G → ℂ))
    (hV : ∀ k : H, ∀ v ∈ V, (fun x => v (x * ι k)) ∈ V) {n : ℕ} (e : V ≃ₗ[ℂ] (Fin n → ℂ)) :
    Representation ℂ H (Fin n → ℂ) where
  toFun k := (e : V →ₗ[ℂ] (Fin n → ℂ)) ∘ₗ translateOn ι V hV k ∘ₗ (e.symm : (Fin n → ℂ) →ₗ[ℂ] V)
  map_one' := LinearMap.ext fun a => by simp [translateOn_one]
  map_mul' k₁ k₂ := LinearMap.ext fun a => by simp [translateOn_mul, Module.End.mul_apply]

private theorem transportRep_apply (ι : H →* G) (V : Submodule ℂ (G → ℂ))
    (hV : ∀ k : H, ∀ v ∈ V, (fun x => v (x * ι k)) ∈ V) {n : ℕ} (e : V ≃ₗ[ℂ] (Fin n → ℂ)) (k : H)
    (a : Fin n → ℂ) : transportRep ι V hV e k a = e (translateOn ι V hV k (e.symm a)) :=
  rfl

private theorem isRightEquivariant_subtype_comp_symm (ι : H →* G) (V : Submodule ℂ (G → ℂ))
    (hV : ∀ k : H, ∀ v ∈ V, (fun x => v (x * ι k)) ∈ V) {n : ℕ} (e : V ≃ₗ[ℂ] (Fin n → ℂ)) :
    IsRightEquivariant ι (transportRep ι V hV e)
      (V.subtype ∘ₗ (e.symm : (Fin n → ℂ) →ₗ[ℂ] V)) := by
  intro k a x
  simp [transportRep_apply, translateOn_apply_coe]

private theorem exists_rep_mem_typeSubmodule (ι : H →* G) {u : G → ℂ} (V : Submodule ℂ (G → ℂ))
    [FiniteDimensional ℂ V] (hu : u ∈ V) (hV : ∀ k : H, ∀ v ∈ V, (fun x => v (x * ι k)) ∈ V) :
    ∃ (n : ℕ) (ρ : Representation ℂ H (Fin n → ℂ)), u ∈ typeSubmodule ι ρ := by
  let e : V ≃ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ) := (Module.finBasis ℂ V).equivFun
  refine ⟨Module.finrank ℂ V, transportRep ι V hV e, ?_⟩
  have hmem := mem_typeSubmodule_of_isRightEquivariant (isRightEquivariant_subtype_comp_symm ι V hV e)
    (e ⟨u, hu⟩)
  simpa using hmem

private theorem comp_mul_mem_span_translates (ι : H →* G) (f : G → ℂ) (k : H) (v : G → ℂ)
    (hv : v ∈ Submodule.span ℂ (Set.range fun k : H => fun x => f (x * ι k))) :
    (fun x => v (x * ι k)) ∈ Submodule.span ℂ (Set.range fun k : H => fun x => f (x * ι k)) := by
  refine Submodule.span_induction
    (p := fun v _ => (fun x => v (x * ι k)) ∈ Submodule.span ℂ (Set.range fun k : H => fun x => f (x * ι k)))
    ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨k', rfl⟩
    refine Submodule.subset_span ⟨k * k', ?_⟩
    funext x
    simp only [map_mul, mul_assoc]
  · exact Submodule.zero_mem _
  · exact fun _ _ _ _ hu hw => Submodule.add_mem _ hu hw
  · exact fun c _ _ hu => Submodule.smul_mem _ c hu

private theorem self_mem_span_translates (ι : H →* G) (f : G → ℂ) :
    f ∈ Submodule.span ℂ (Set.range fun k : H => fun x => f (x * ι k)) := by
  have h1 : (fun x => f (x * ι 1)) ∈ Submodule.span ℂ (Set.range fun k : H => fun x => f (x * ι k)) :=
    Submodule.subset_span ⟨1, rfl⟩
  have e : (fun x => f (x * ι 1)) = f := by
    funext x
    rw [map_one, mul_one]
  rwa [e] at h1

private theorem exists_rep_mem_typeSubmodule_of_finiteDimensional (ι : H →* G) (u : G → ℂ)
    [FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : H => fun x => u (x * ι k)))] :
    ∃ (n : ℕ) (ρ : Representation ℂ H (Fin n → ℂ)), u ∈ typeSubmodule ι ρ :=
  exists_rep_mem_typeSubmodule ι _ (self_mem_span_translates ι u) (comp_mul_mem_span_translates ι u)

private def conjDualRep {n : ℕ} (ρ₀ : Representation ℂ H (Fin n → ℂ))
    (d : Module.Dual ℂ (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ)) : Representation ℂ H (Fin n → ℂ) where
  toFun k := (d : Module.Dual ℂ (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ∘ₗ ρ₀.dual k ∘ₗ
    (d.symm : (Fin n → ℂ) →ₗ[ℂ] Module.Dual ℂ (Fin n → ℂ))
  map_one' := LinearMap.ext fun a => by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, map_one, Module.End.one_apply, LinearEquiv.apply_symm_apply]
  map_mul' k₁ k₂ := LinearMap.ext fun a => by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, map_mul, Module.End.mul_apply, LinearEquiv.symm_apply_apply]

private theorem conjDualRep_apply {n : ℕ} (ρ₀ : Representation ℂ H (Fin n → ℂ))
    (d : Module.Dual ℂ (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ)) (k : H) (a : Fin n → ℂ) :
    conjDualRep ρ₀ d k a = d (ρ₀.dual k (d.symm a)) :=
  rfl

private def dualTransport {n : ℕ} (d : Module.Dual ℂ (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ))
    (S : (Fin n → ℂ) →ₗ[ℂ] (G → ℂ)) : Module.Dual ℂ (Fin n → ℂ) →ₗ[ℂ] (G → ℂ) :=
  S ∘ₗ (Module.evalEquiv ℂ (Fin n → ℂ)).symm.toLinearMap ∘ₗ
    (d : Module.Dual ℂ (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)).dualMap

omit [Group G] in
private theorem dualTransport_apply {n : ℕ} (d : Module.Dual ℂ (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ))
    (S : (Fin n → ℂ) →ₗ[ℂ] (G → ℂ)) (ψ : Module.Dual ℂ (Fin n → ℂ)) :
    dualTransport d S ψ =
      S ((Module.evalEquiv ℂ (Fin n → ℂ)).symm (ψ ∘ₗ (d : Module.Dual ℂ (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)))) :=
  rfl

private theorem evalEquiv_symm_comp_conjDualRep_dual {n : ℕ} (ρ₀ : Representation ℂ H (Fin n → ℂ))
    (d : Module.Dual ℂ (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ)) (k : H) (ψ : Module.Dual ℂ (Fin n → ℂ)) :
    (Module.evalEquiv ℂ (Fin n → ℂ)).symm
        ((conjDualRep ρ₀ d).dual k ψ ∘ₗ (d : Module.Dual ℂ (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))) =
      ρ₀ k ((Module.evalEquiv ℂ (Fin n → ℂ)).symm
        (ψ ∘ₗ (d : Module.Dual ℂ (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)))) := by
  rw [LinearEquiv.symm_apply_eq]
  ext φ
  simp only [Module.evalEquiv_apply, Module.Dual.eval_apply, LinearMap.comp_apply, Representation.dual_apply,
    Module.Dual.transpose_apply, conjDualRep_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, inv_inv]
  exact (Module.apply_evalEquiv_symm_apply ℂ (Fin n → ℂ) (φ ∘ₗ ρ₀ k)
    (ψ ∘ₗ (d : Module.Dual ℂ (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)))).symm

private theorem isRightEquivariant_dualTransport (ι : H →* G) {n : ℕ} (ρ₀ : Representation ℂ H (Fin n → ℂ))
    (d : Module.Dual ℂ (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ)) (S : (Fin n → ℂ) →ₗ[ℂ] (G → ℂ))
    (hS : IsRightEquivariant ι ρ₀ S) : IsRightEquivariant ι (conjDualRep ρ₀ d).dual (dualTransport d S) := by
  intro k ψ x
  rw [dualTransport_apply, dualTransport_apply, evalEquiv_symm_comp_conjDualRep_dual]
  exact hS k _ x

private theorem exists_rep_mem_typeSubmodule_dual_of_finiteDimensional (ι : H →* G) (u : G → ℂ)
    [FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : H => fun x => u (x * ι k)))] :
    ∃ (n : ℕ) (ρ : Representation ℂ H (Fin n → ℂ)), u ∈ typeSubmodule ι ρ.dual := by
  set V : Submodule ℂ (G → ℂ) := Submodule.span ℂ (Set.range fun k : H => fun x => u (x * ι k)) with hV
  have hstab : ∀ k : H, ∀ v ∈ V, (fun x => v (x * ι k)) ∈ V := fun k v hv =>
    comp_mul_mem_span_translates ι u k v hv
  let e : V ≃ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ) := (Module.finBasis ℂ V).equivFun
  let d : Module.Dual ℂ (Fin (Module.finrank ℂ V) → ℂ) ≃ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ) :=
    (Pi.basisFun ℂ (Fin (Module.finrank ℂ V))).dualBasis.equivFun
  let S : (Fin (Module.finrank ℂ V) → ℂ) →ₗ[ℂ] (G → ℂ) :=
    V.subtype ∘ₗ (e.symm : (Fin (Module.finrank ℂ V) → ℂ) →ₗ[ℂ] V)
  have hS : IsRightEquivariant ι (transportRep ι V hstab e) S :=
    isRightEquivariant_subtype_comp_symm ι V hstab e
  refine ⟨Module.finrank ℂ V, conjDualRep (transportRep ι V hstab e) d, ?_⟩
  set a : Fin (Module.finrank ℂ V) → ℂ := e ⟨u, self_mem_span_translates ι u⟩ with ha
  have hmem := mem_typeSubmodule_of_isRightEquivariant (isRightEquivariant_dualTransport ι _ d S hS)
    (Module.Dual.eval ℂ (Fin (Module.finrank ℂ V) → ℂ) a ∘ₗ
      (d.symm : (Fin (Module.finrank ℂ V) → ℂ) →ₗ[ℂ] Module.Dual ℂ (Fin (Module.finrank ℂ V) → ℂ)))
  convert hmem using 1
  rw [dualTransport_apply]
  have hcomp : (Module.Dual.eval ℂ (Fin (Module.finrank ℂ V) → ℂ) a ∘ₗ
      (d.symm : (Fin (Module.finrank ℂ V) → ℂ) →ₗ[ℂ] Module.Dual ℂ (Fin (Module.finrank ℂ V) → ℂ))) ∘ₗ
        (d : Module.Dual ℂ (Fin (Module.finrank ℂ V) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ)) =
      Module.Dual.eval ℂ (Fin (Module.finrank ℂ V) → ℂ) a := by
    ext φ
    simp
  rw [hcomp, ← Module.evalEquiv_apply, LinearEquiv.symm_apply_apply]
  simp [S, a]

end Generic

section Factor

variable (F : Type) [Field F]

private theorem exists_archRepAt_pair (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (hfin : ∀ w : InfinitePlace F,
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ w.Completion =>
        fun x : GL (Fin 2) (InfiniteAdeleRing F) => fa (x * archRowIsometryInclAt₀ F w k))) ∧
        FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ w.Completion =>
        fun x : GL (Fin 2) (InfiniteAdeleRing F) => fa (x * archRowIsometryInclAt₀ F w k)⁻¹)))
    (w : InfinitePlace F) :
    ∃ τ₁ τ₂ : ArchRepAt F w, (fun x => fa x⁻¹) ∈ archFactorTypeSubmoduleAt F w τ₁ ∧
      fa ∈ archFactorDualTypeSubmoduleAt F w τ₂ := by
  haveI h₁ := (hfin w).1
  haveI h₂ := (hfin w).2
  obtain ⟨n₁, ρ₁, hmem₁⟩ :=
    exists_rep_mem_typeSubmodule_of_finiteDimensional (archRowIsometryInclAt₀ F w) (fun x => fa x⁻¹)
  obtain ⟨n₂, ρ₂, hmem₂⟩ :=
    exists_rep_mem_typeSubmodule_dual_of_finiteDimensional (archRowIsometryInclAt₀ F w) fa
  exact ⟨⟨n₁, ρ₁⟩, ⟨n₂, ρ₂⟩, hmem₁, hmem₂⟩

end Factor

end

end RightFiniteTypes

open AutomorphicForm RightFiniteTypes in

theorem solution
    (F : Type) [Field F] (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (hfin : ∀ w : InfinitePlace F,
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ w.Completion =>
        fun x : GL (Fin 2) (InfiniteAdeleRing F) => fa (x * archRowIsometryInclAt₀ F w k))) ∧
        FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ w.Completion =>
        fun x : GL (Fin 2) (InfiniteAdeleRing F) => fa (x * archRowIsometryInclAt₀ F w k)⁻¹))) :
    ∃ tys : ArchTypeFamily F, IsArchFactorBiFinite F tys fa := by
  choose τ₁ τ₂ h₁ h₂ using exists_archRepAt_pair F fa hfin
  refine ⟨⟨fun _ => 2, fun w i => if i = 0 then τ₁ w else τ₂ w⟩, ?_, ?_⟩
  · refine (Submodule.mem_iInf _).2 fun w => ?_
    exact Submodule.mem_iSup_of_mem (0 : Fin 2) (by simpa using h₁ w)
  · refine (Submodule.mem_iInf _).2 fun w => ?_
    exact Submodule.mem_iSup_of_mem (1 : Fin 2) (by simpa using h₂ w)

end S_AutomorphicForm_exists_archTypeFamily_isArchFactorBiFinite_of_finiteDimensional_span_range
end P2MW
export P2MW.S_AutomorphicForm_exists_archTypeFamily_isArchFactorBiFinite_of_finiteDimensional_span_range (solution)
