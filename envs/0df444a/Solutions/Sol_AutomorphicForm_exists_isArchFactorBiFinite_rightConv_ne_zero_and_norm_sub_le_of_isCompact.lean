-- Prove2me | solution 1 for AutomorphicForm.exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/4457da2b-1013-51bf-896b-6bf3d0a3f021

import Mathlib
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

noncomputable section

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume

section ModConvHalf

set_option autoImplicit false

namespace ArchFiniteVector
namespace ConvHalf

variable (F : Type) [Field F] [NumberField F]

private theorem isFactorizableTestFn_mk (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (hfa : IsArchTestFactor F fa)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) (hff : IsFinTestFactor F ff) :
    IsFactorizableTestFn F (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) :=
  ⟨fa, ff, hfa, hff, fun _ => rfl⟩

end ArchFiniteVector.ConvHalf

end ModConvHalf

section ModKFinite

set_option autoImplicit false

open NumberField NumberField.AdelicHaar MeasureTheory
open AutomorphicForm

namespace ArchFiniteVector
namespace KFinite

variable (F : Type) [Field F] [NumberField F]

private theorem rightConv_mul_right (φ f : AdelicGL2 (𝓞 F) F → ℂ) (k g : AdelicGL2 (𝓞 F) F) :
    rightConv F φ f (g * k) = rightConv F φ (fun y => f (k⁻¹ * y)) g := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  rw [rightConv_apply, rightConv_apply]
  have key : (fun x => φ (g * k * x) * f x) =
      fun x => (fun y => φ (g * y) * f (k⁻¹ * y)) (k * x) := by
    funext x
    simp only [mul_assoc, inv_mul_cancel_left]
  rw [key]
  exact MeasureTheory.integral_mul_left_eq_self (fun y => φ (g * y) * f (k⁻¹ * y)) k

private theorem integrable_rightConv_integrand (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) (g : AdelicGL2 (𝓞 F) F) :
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
    Integrable (fun x => φ (g * x) * f x) (adelicGLHaar (Fin 2) (𝓞 F) F) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have hcont : Continuous fun x => φ (g * x) * f x := (hφ.comp (continuous_const_mul g)).mul hf
  have hsupp : HasCompactSupport fun x => φ (g * x) * f x := hfc.mul_left
  exact hcont.integrable_of_hasCompactSupport hsupp

private theorem rightConv_mem_span {n : ℕ} (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (fs : Fin n → AdelicGL2 (𝓞 F) F → ℂ) (hfs : ∀ i, Continuous (fs i)) (hfsc : ∀ i, HasCompactSupport (fs i))
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : f ∈ Submodule.span ℂ (Set.range fs)) :
    rightConv F φ f ∈ Submodule.span ℂ (Set.range fun i => rightConv F φ (fs i)) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  refine (Submodule.span_induction
    (p := fun f _ => (∀ g, Integrable (fun x => φ (g * x) * f x) (adelicGLHaar (Fin 2) (𝓞 F) F)) ∧
      rightConv F φ f ∈ Submodule.span ℂ (Set.range fun i => rightConv F φ (fs i)))
    ?_ ?_ ?_ ?_ hf).2
  · rintro _ ⟨i, rfl⟩
    exact ⟨fun g => integrable_rightConv_integrand F φ hφ (fs i) (hfs i) (hfsc i) g,
      Submodule.subset_span ⟨i, rfl⟩⟩
  · refine ⟨fun g => ?_, ?_⟩
    · have e : (fun x => φ (g * x) * (0 : AdelicGL2 (𝓞 F) F → ℂ) x) = fun _ => (0 : ℂ) := by
        funext x
        simp
      rw [e]
      exact integrable_zero _ _ _
    · have e : rightConv F φ (0 : AdelicGL2 (𝓞 F) F → ℂ) = 0 := by
        funext g
        simp [rightConv]
      rw [e]
      exact Submodule.zero_mem _
  · rintro f₁ f₂ - - ⟨h₁, m₁⟩ ⟨h₂, m₂⟩
    refine ⟨fun g => ?_, ?_⟩
    · have e : (fun x => φ (g * x) * (f₁ + f₂) x) = fun x => φ (g * x) * f₁ x + φ (g * x) * f₂ x := by
        funext x
        simp only [Pi.add_apply, mul_add]
      rw [e]
      exact (h₁ g).add (h₂ g)
    · have e : rightConv F φ (f₁ + f₂) = rightConv F φ f₁ + rightConv F φ f₂ := by
        funext g
        rw [Pi.add_apply, rightConv_apply, rightConv_apply, rightConv_apply]
        simp only [Pi.add_apply, mul_add]
        exact MeasureTheory.integral_add (h₁ g) (h₂ g)
      rw [e]
      exact Submodule.add_mem _ m₁ m₂
  · rintro a f₁ - ⟨h₁, m₁⟩
    refine ⟨fun g => ?_, ?_⟩
    · have e : (fun x => φ (g * x) * (a • f₁) x) = fun x => a * (φ (g * x) * f₁ x) := by
        funext x
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [e]
      exact (h₁ g).const_mul a
    · have e : rightConv F φ (a • f₁) = a • rightConv F φ f₁ := by
        funext g
        rw [Pi.smul_apply, smul_eq_mul, rightConv_apply, rightConv_apply, ← MeasureTheory.integral_const_mul]
        congr 1
        funext x
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [e]
      exact Submodule.smul_mem _ a m₁

private theorem exists_finiteDimensional_mem_of_forall_mem_span {n : ℕ} {H : Type} [Monoid H]
    (ι : H →* AdelicGL2 (𝓞 F) F) (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (fs : Fin n → AdelicGL2 (𝓞 F) F → ℂ) (hfs : ∀ i, Continuous (fs i)) (hfsc : ∀ i, HasCompactSupport (fs i))
    (f : AdelicGL2 (𝓞 F) F → ℂ)
    (hW : ∀ k : H, (fun y => f ((ι k)⁻¹ * y)) ∈ Submodule.span ℂ (Set.range fs)) :
    ∃ V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), FiniteDimensional ℂ V ∧ rightConv F φ f ∈ V ∧
      ∀ k : H, ∀ v ∈ V, (fun x => v (x * ι k)) ∈ V := by
  refine ⟨Submodule.span ℂ (Set.range fun k : H => fun x => rightConv F φ f (x * ι k)), ?_, ?_, ?_⟩
  · have hle : Submodule.span ℂ (Set.range fun k : H => fun x => rightConv F φ f (x * ι k)) ≤
        Submodule.span ℂ (Set.range fun i => rightConv F φ (fs i)) := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      show (fun x => rightConv F φ f (x * ι k)) ∈ Submodule.span ℂ (Set.range fun i => rightConv F φ (fs i))
      have e : (fun x => rightConv F φ f (x * ι k)) = rightConv F φ (fun y => f ((ι k)⁻¹ * y)) := by
        funext x
        exact rightConv_mul_right F φ f (ι k) x
      rw [e]
      exact rightConv_mem_span F φ hφ fs hfs hfsc _ (hW k)
    haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun i => rightConv F φ (fs i))) :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
    exact Submodule.finiteDimensional_of_le hle
  · have e : (fun x => rightConv F φ f (x * ι 1)) = rightConv F φ f := by
      funext x
      rw [map_one, mul_one]
    have h1 : (fun x => rightConv F φ f (x * ι 1)) ∈
        Submodule.span ℂ (Set.range fun k : H => fun x => rightConv F φ f (x * ι k)) :=
      Submodule.subset_span ⟨1, rfl⟩
    rwa [e] at h1
  · intro k v hv
    refine Submodule.span_induction
      (p := fun v _ => (fun x => v (x * ι k)) ∈
        Submodule.span ℂ (Set.range fun k : H => fun x => rightConv F φ f (x * ι k)))
      ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨k', rfl⟩
      refine Submodule.subset_span ⟨k * k', ?_⟩
      funext x
      simp only [map_mul, mul_assoc]
    · exact Submodule.zero_mem _
    · exact fun _ _ _ _ hu hw => Submodule.add_mem _ hu hw
    · exact fun c _ _ hu => Submodule.smul_mem _ c hu

end ArchFiniteVector.KFinite

end ModKFinite

section ModArchCut

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume

namespace ArchFiniteVector
namespace ArchCut

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

private theorem comp_inv_mem_span {N : ℕ} (b : Fin N → G → ℂ) {h : G → ℂ}
    (hh : h ∈ Submodule.span ℂ (Set.range b)) :
    (fun x => h x⁻¹) ∈ Submodule.span ℂ (Set.range fun i => fun x => b i x⁻¹) := by
  refine Submodule.span_induction
    (p := fun h _ => (fun x => h x⁻¹) ∈ Submodule.span ℂ (Set.range fun i => fun x => b i x⁻¹))
    ?_ ?_ ?_ ?_ hh
  · rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  · exact Submodule.zero_mem _
  · exact fun _ _ _ _ hu hw => Submodule.add_mem _ hu hw
  · exact fun c _ _ hu => Submodule.smul_mem _ c hu

private theorem exists_stable_of_translates_mem (ι : H →* G) (u : G → ℂ) (W : Submodule ℂ (G → ℂ))
    [FiniteDimensional ℂ W] (hW : ∀ k : H, (fun x => u (x * ι k)) ∈ W) :
    ∃ V : Submodule ℂ (G → ℂ), FiniteDimensional ℂ V ∧ u ∈ V ∧
      ∀ k : H, ∀ v ∈ V, (fun x => v (x * ι k)) ∈ V := by
  refine ⟨Submodule.span ℂ (Set.range fun k : H => fun x => u (x * ι k)), ?_, ?_, ?_⟩
  · have hle : Submodule.span ℂ (Set.range fun k : H => fun x => u (x * ι k)) ≤ W := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨k, rfl⟩
      exact hW k
    exact Submodule.finiteDimensional_of_le hle
  · have e : (fun x => u (x * ι 1)) = u := by
      funext x
      rw [map_one, mul_one]
    have h1 : (fun x => u (x * ι 1)) ∈ Submodule.span ℂ (Set.range fun k : H => fun x => u (x * ι k)) :=
      Submodule.subset_span ⟨1, rfl⟩
    rwa [e] at h1
  · intro k v hv
    refine Submodule.span_induction
      (p := fun v _ => (fun x => v (x * ι k)) ∈ Submodule.span ℂ (Set.range fun k : H => fun x => u (x * ι k)))
      ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨k', rfl⟩
      refine Submodule.subset_span ⟨k * k', ?_⟩
      funext x
      simp only [map_mul, mul_assoc]
    · exact Submodule.zero_mem _
    · exact fun _ _ _ _ hu hw => Submodule.add_mem _ hu hw
    · exact fun c _ _ hu => Submodule.smul_mem _ c hu

private def dualCarrierEquiv (n : ℕ) : (Fin n → ℂ) ≃ₗ[ℂ] Module.Dual ℂ (Fin n → ℂ) :=
  (Pi.basisFun ℂ (Fin n)).dualBasis.equivFun.symm

private def dualTransport {n : ℕ} (σ : Representation ℂ H (Fin n → ℂ)) : Representation ℂ H (Fin n → ℂ) where
  toFun k := ((dualCarrierEquiv n).symm : Module.Dual ℂ (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ∘ₗ σ.dual k ∘ₗ
    (dualCarrierEquiv n : (Fin n → ℂ) →ₗ[ℂ] Module.Dual ℂ (Fin n → ℂ))
  map_one' := LinearMap.ext fun a => by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, map_one, Module.End.one_apply,
      LinearEquiv.symm_apply_apply]
  map_mul' k₁ k₂ := LinearMap.ext fun a => by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, map_mul, Module.End.mul_apply,
      LinearEquiv.apply_symm_apply]

private theorem dualTransport_apply {n : ℕ} (σ : Representation ℂ H (Fin n → ℂ)) (k : H) (a : Fin n → ℂ) :
    dualTransport σ k a = (dualCarrierEquiv n).symm (σ.dual k (dualCarrierEquiv n a)) :=
  rfl

private def dualEquiv (n : ℕ) : Module.Dual ℂ (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) :=
  ((dualCarrierEquiv n).symm.dualMap).trans (Module.evalEquiv ℂ (Fin n → ℂ)).symm

private theorem apply_dualEquiv (n : ℕ) (φ ψ : Module.Dual ℂ (Fin n → ℂ)) :
    ψ (dualEquiv n φ) = φ ((dualCarrierEquiv n).symm ψ) := by
  simp only [dualEquiv, LinearEquiv.trans_apply, Module.apply_evalEquiv_symm_apply, LinearEquiv.dualMap_apply]

private theorem dualEquiv_dual_apply {n : ℕ} (σ : Representation ℂ H (Fin n → ℂ)) (k : H)
    (φ : Module.Dual ℂ (Fin n → ℂ)) :
    dualEquiv n ((dualTransport σ).dual k φ) = σ k (dualEquiv n φ) := by
  have key : ∀ ψ : Module.Dual ℂ (Fin n → ℂ),
      ψ (dualEquiv n ((dualTransport σ).dual k φ)) = ψ (σ k (dualEquiv n φ)) := by
    intro ψ
    rw [apply_dualEquiv]
    change φ (dualTransport σ k⁻¹ ((dualCarrierEquiv n).symm ψ)) = _
    rw [dualTransport_apply, LinearEquiv.apply_symm_apply]
    change φ ((dualCarrierEquiv n).symm (ψ ∘ₗ σ k⁻¹⁻¹)) = _
    rw [inv_inv, ← apply_dualEquiv n φ (ψ ∘ₗ σ k)]
    rfl
  exact (Module.evalEquiv ℂ (Fin n → ℂ)).injective (LinearMap.ext fun ψ => by
    simpa only [Module.evalEquiv_apply, Module.Dual.eval_apply] using key ψ)

private theorem exists_rep_mem_typeSubmodule_dual (ι : H →* G) {u : G → ℂ} (V : Submodule ℂ (G → ℂ))
    [FiniteDimensional ℂ V] (hu : u ∈ V) (hV : ∀ k : H, ∀ v ∈ V, (fun x => v (x * ι k)) ∈ V) :
    ∃ (n : ℕ) (ρ : Representation ℂ H (Fin n → ℂ)), u ∈ typeSubmodule ι ρ.dual := by
  let e : V ≃ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ) := (Module.finBasis ℂ V).equivFun
  refine ⟨Module.finrank ℂ V, dualTransport (transportRep ι V hV e), ?_⟩
  have hT : IsRightEquivariant ι (dualTransport (transportRep ι V hV e)).dual
      ((V.subtype ∘ₗ (e.symm : (Fin (Module.finrank ℂ V) → ℂ) →ₗ[ℂ] V)) ∘ₗ
        (dualEquiv (Module.finrank ℂ V) :
          Module.Dual ℂ (Fin (Module.finrank ℂ V) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ))) := by
    intro k φ x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, dualEquiv_dual_apply]
    exact isRightEquivariant_subtype_comp_symm ι V hV e k (dualEquiv _ φ) x
  have hmem := mem_typeSubmodule_of_isRightEquivariant hT ((dualEquiv (Module.finrank ℂ V)).symm (e ⟨u, hu⟩))
  simpa using hmem

end Generic

private theorem exists_archTypeFamily_mem_archCutSubmodule (F : Type) [Field F] [NumberField F]
    (u : AdelicGL2 (𝓞 F) F → ℂ)
    (hV : ∀ w : InfinitePlace F, ∃ V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ),
      FiniteDimensional ℂ V ∧ u ∈ V ∧
        ∀ k : rowIsometrySubgroup₀ w.Completion, ∀ v ∈ V, (fun x => v (x * rowIsometryInclAt₀ F w k)) ∈ V) :
    ∃ tys : ArchTypeFamily F, u ∈ archCutSubmodule F tys := by
  have h : ∀ w : InfinitePlace F, ∃ τ : ArchRepAt F w, u ∈ archTypeSubmoduleAt F w τ := by
    intro w
    obtain ⟨V, hfin, hu, hstab⟩ := hV w
    haveI := hfin
    obtain ⟨n, ρ, hmem⟩ := exists_rep_mem_typeSubmodule (rowIsometryInclAt₀ F w) V hu hstab
    exact ⟨⟨n, ρ⟩, hmem⟩
  choose τ hτ using h
  refine ⟨⟨fun _ => 1, fun w _ => τ w⟩, ?_⟩
  rw [mem_archCutSubmodule_iff]
  intro w
  exact Submodule.mem_iSup_of_mem (0 : Fin 1) (hτ w)

end ArchFiniteVector.ArchCut

end ModArchCut

section ModPoly

set_option autoImplicit false

open scoped Classical
open MeasureTheory

namespace ArchFiniteVector
namespace Poly

section Checks
end Checks

section SubstFinite

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

private def precomp (L : E →ₗ[ℝ] E) : (E → ℝ) →ₐ[ℝ] (E → ℝ) where
  toFun v := v ∘ L
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[scoped simp] private theorem precomp_apply (L : E →ₗ[ℝ] E) (v : E → ℝ) (x : E) :
    precomp L v x = v (L x) := rfl

private def IsSubstFinite (h : E → ℝ) : Prop :=
  ∃ V : Submodule ℝ (E → ℝ), FiniteDimensional ℝ V ∧ h ∈ V ∧
    ∀ L : E →ₗ[ℝ] E, ∀ v ∈ V, precomp L v ∈ V

private theorem IsSubstFinite.mul {h₁ h₂ : E → ℝ} (H₁ : IsSubstFinite h₁) (H₂ : IsSubstFinite h₂) :
    IsSubstFinite (h₁ * h₂) := by
  obtain ⟨V₁, hfd₁, hm₁, hs₁⟩ := H₁
  obtain ⟨V₂, hfd₂, hm₂, hs₂⟩ := H₂
  haveI := hfd₁
  haveI := hfd₂
  refine ⟨V₁ * V₂, ?_, Submodule.mul_mem_mul hm₁ hm₂, ?_⟩
  · exact Module.Finite.iff_fg.mpr
      ((Module.Finite.iff_fg.mp hfd₁).mul (Module.Finite.iff_fg.mp hfd₂))
  · intro L v hv
    refine Submodule.mul_induction_on hv ?_ ?_
    · intro m hm n hn
      rw [map_mul]
      exact Submodule.mul_mem_mul (hs₁ L m hm) (hs₂ L n hn)
    · intro x y hx hy
      rw [map_add]
      exact add_mem hx hy

private theorem IsSubstFinite.add {h₁ h₂ : E → ℝ} (H₁ : IsSubstFinite h₁) (H₂ : IsSubstFinite h₂) :
    IsSubstFinite (h₁ + h₂) := by
  obtain ⟨V₁, hfd₁, hm₁, hs₁⟩ := H₁
  obtain ⟨V₂, hfd₂, hm₂, hs₂⟩ := H₂
  haveI := hfd₁
  haveI := hfd₂
  refine ⟨V₁ ⊔ V₂, inferInstance, Submodule.add_mem_sup hm₁ hm₂, ?_⟩
  intro L v hv
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add]
  exact Submodule.add_mem_sup (hs₁ L y hy) (hs₂ L z hz)

private theorem IsSubstFinite.const (c : ℝ) : IsSubstFinite (fun _ : E => c) := by
  refine ⟨Submodule.span ℝ {fun _ : E => (1 : ℝ)}, ?_, ?_, ?_⟩
  · exact FiniteDimensional.span_of_finite ℝ (Set.finite_singleton _)
  · have h1 : (fun _ : E => c) = c • (fun _ : E => (1 : ℝ)) := by
      funext x
      simp
    rw [h1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · intro L v hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    have h2 : precomp L (a • fun _ : E => (1 : ℝ)) = a • fun _ : E => (1 : ℝ) := by
      funext x
      simp
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

variable (E) in
private def substFinite : Subalgebra ℝ (E → ℝ) where
  carrier := {h | IsSubstFinite h}
  mul_mem' := IsSubstFinite.mul
  add_mem' := IsSubstFinite.add
  algebraMap_mem' c := by
    have h : (algebraMap ℝ (E → ℝ) c) = fun _ => c := by
      funext x
      simp
    show IsSubstFinite (algebraMap ℝ (E → ℝ) c)
    rw [h]
    exact IsSubstFinite.const c

private theorem IsSubstFinite.linear [FiniteDimensional ℝ E] (ℓ : E →ₗ[ℝ] ℝ) :
    IsSubstFinite (ℓ : E → ℝ) := by
  let b := Module.finBasis ℝ E
  let V : Submodule ℝ (E → ℝ) :=
    Submodule.span ℝ (Set.range fun i => (b.coord i : E → ℝ))
  have key : ∀ f : E →ₗ[ℝ] ℝ, (f : E → ℝ) ∈ V := by
    intro f
    have hf : (f : E → ℝ) = ∑ i, f (b i) • (b.coord i : E → ℝ) := by
      funext m
      rw [Finset.sum_apply]
      conv_lhs => rw [← b.sum_repr m]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [map_smul, Pi.smul_apply, Module.Basis.coord_apply, smul_eq_mul]
      ring
    rw [hf]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨V, FiniteDimensional.span_of_finite ℝ (Set.finite_range _), key ℓ, ?_⟩
  intro L v hv
  have hle : V.map (precomp L).toLinearMap ≤ V := by
    refine (Submodule.map_span_le _ _ _).mpr ?_
    rintro _ ⟨i, rfl⟩
    exact key ((b.coord i).comp L)
  exact hle (Submodule.mem_map_of_mem hv)

end SubstFinite

section Poly

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private def smoothSubmodule : Submodule ℝ (E → ℝ) where
  carrier := {w | ContDiff ℝ (⊤ : ℕ∞) w}
  add_mem' {v w} (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hw : ContDiff ℝ (⊤ : ℕ∞) w) := by
    show ContDiff ℝ (⊤ : ℕ∞) (v + w)
    exact hv.add hw
  zero_mem' := by
    show ContDiff ℝ (⊤ : ℕ∞) (0 : E → ℝ)
    exact contDiff_const
  smul_mem' c w (hw : ContDiff ℝ (⊤ : ℕ∞) w) := by
    show ContDiff ℝ (⊤ : ℕ∞) (c • w)
    exact contDiff_const.smul hw

variable {E} in
private theorem IsSubstFinite.exists_smooth_span {p : E → ℝ} (hs : IsSubstFinite p) (hp : ContDiff ℝ (⊤ : ℕ∞) p) :
    ∃ (n : ℕ) (b : Fin n → E → ℝ), (∀ i, ContDiff ℝ (⊤ : ℕ∞) (b i)) ∧
      ∀ L : E →ₗ[ℝ] E, (p ∘ L) ∈ Submodule.span ℝ (Set.range b) := by
  obtain ⟨V, hfd, hpV, hst⟩ := hs
  haveI := hfd
  let W : Submodule ℝ (E → ℝ) := Submodule.span ℝ (Set.range fun L : E →ₗ[ℝ] E => precomp L p)
  have hWV : W ≤ V := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨L, rfl⟩
    exact hst L p hpV
  haveI : FiniteDimensional ℝ W := Submodule.finiteDimensional_of_le hWV
  have hWsmooth : W ≤ smoothSubmodule E := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨L, rfl⟩
    show ContDiff ℝ (⊤ : ℕ∞) (p ∘ L)
    exact hp.comp (LinearMap.toContinuousLinearMap L).contDiff
  let bW := Module.finBasis ℝ W
  refine ⟨Module.finrank ℝ W, fun i => (bW i : E → ℝ), fun i => hWsmooth (bW i).2, fun L => ?_⟩
  have hmem : precomp L p ∈ W := Submodule.subset_span ⟨L, rfl⟩
  have hrepr := bW.sum_repr ⟨precomp L p, hmem⟩
  have hsum : (p ∘ L : E → ℝ) = ∑ i, bW.repr ⟨precomp L p, hmem⟩ i • (bW i : E → ℝ) := by
    have h := congrArg (W.subtype) hrepr
    rw [map_sum] at h
    simp only [map_smul, Submodule.subtype_apply] at h
    exact h.symm
  rw [hsum]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

private def coordC (ℓ : E →ₗ[ℝ] ℝ) : C(E, ℝ) := ⟨ℓ, ℓ.continuous_of_finiteDimensional⟩

@[scoped simp] private theorem coordC_apply (ℓ : E →ₗ[ℝ] ℝ) (x : E) : coordC E ℓ x = ℓ x := rfl

private def polyAlg : Subalgebra ℝ C(E, ℝ) :=
  Algebra.adjoin ℝ (Set.range fun ℓ : E →ₗ[ℝ] ℝ => coordC E ℓ)

private def goodAlg : Subalgebra ℝ C(E, ℝ) where
  carrier := {p | ContDiff ℝ (⊤ : ℕ∞) (p : E → ℝ) ∧ IsSubstFinite (p : E → ℝ)}
  mul_mem' := fun {p q} hp hq => ⟨hp.1.mul hq.1, hp.2.mul hq.2⟩
  add_mem' := fun {p q} hp hq => ⟨hp.1.add hq.1, hp.2.add hq.2⟩
  algebraMap_mem' c := by
    have h : ((algebraMap ℝ C(E, ℝ) c : C(E, ℝ)) : E → ℝ) = fun _ => c := by
      funext x
      simp [Algebra.algebraMap_eq_smul_one]
    refine ⟨?_, ?_⟩
    · rw [h]
      exact contDiff_const
    · rw [h]
      exact IsSubstFinite.const c

private theorem polyAlg_le_goodAlg : polyAlg E ≤ goodAlg E := by
  refine Algebra.adjoin_le ?_
  rintro _ ⟨ℓ, rfl⟩
  refine ⟨?_, ?_⟩
  · have h : ((coordC E ℓ : C(E, ℝ)) : E → ℝ) = (LinearMap.toContinuousLinearMap ℓ : E → ℝ) := by
      funext x
      simp
    rw [h]
    exact (LinearMap.toContinuousLinearMap ℓ).contDiff
  · exact IsSubstFinite.linear ℓ

private theorem polyAlg_separatesPoints : (polyAlg E).SeparatesPoints := by
  intro x y hxy
  let b := Module.finBasis ℝ E
  have hex : ∃ i, b.repr x i ≠ b.repr y i :=
    not_forall.mp fun h => hxy (b.ext_elem_iff.mpr h)
  obtain ⟨i, hi⟩ := hex
  refine ⟨coordC E (b.coord i), ⟨coordC E (b.coord i), Algebra.subset_adjoin ⟨b.coord i, rfl⟩, rfl⟩,
    ?_⟩
  show b.coord i x ≠ b.coord i y
  simpa [Module.Basis.coord_apply] using hi

private theorem exists_poly_near (K : Set E) (hK : IsCompact K) (Φ : E → ℝ) (hΦ : Continuous Φ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) p ∧ IsSubstFinite p ∧ ∀ x ∈ K, ‖p x - Φ x‖ < ε := by
  obtain ⟨g, hg, happrox⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
      (polyAlg_separatesPoints E) (⟨Φ, hΦ⟩ : C(E, ℝ)) hK hε
  exact ⟨g, (polyAlg_le_goodAlg E hg).1, (polyAlg_le_goodAlg E hg).2, fun x hx => happrox x hx⟩

private theorem exists_poly_pair_near (K : Set E) (hK : IsCompact K) (Φ : E → ℂ) (hΦ : Continuous Φ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p q : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) p ∧ IsSubstFinite p ∧ ContDiff ℝ (⊤ : ℕ∞) q ∧
      IsSubstFinite q ∧ ∀ x ∈ K, ‖((p x : ℂ) + (q x : ℂ) * Complex.I) - Φ x‖ < ε := by
  obtain ⟨p, hp1, hp2, hp3⟩ := exists_poly_near E K hK (fun x => (Φ x).re)
    (Complex.continuous_re.comp hΦ) (ε / 2) (half_pos hε)
  obtain ⟨q, hq1, hq2, hq3⟩ := exists_poly_near E K hK (fun x => (Φ x).im)
    (Complex.continuous_im.comp hΦ) (ε / 2) (half_pos hε)
  refine ⟨p, q, hp1, hp2, hq1, hq2, fun x hx => ?_⟩
  have hre : |p x - (Φ x).re| < ε / 2 := by simpa [Real.norm_eq_abs] using hp3 x hx
  have him : |q x - (Φ x).im| < ε / 2 := by simpa [Real.norm_eq_abs] using hq3 x hx
  set z : ℂ := ((p x : ℂ) + (q x : ℂ) * Complex.I) - Φ x with hz
  have hzre : z.re = p x - (Φ x).re := by simp [hz]
  have hzim : z.im = q x - (Φ x).im := by simp [hz]
  calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ < ε / 2 + ε / 2 := by rw [hzre, hzim]; exact add_lt_add hre him
    _ = ε := by ring

end Poly

section Estimate

variable {G : Type*} [MeasurableSpace G] {μ : Measure G}

private theorem norm_integral_sub_integral_le {w a a' r : G → ℂ} {δ : ℝ}
    (hi : Integrable (fun y => w y * (a y * r y)) μ)
    (hi' : Integrable (fun y => w y * (a' y * r y)) μ)
    (hwr : Integrable (fun y => ‖w y‖ * ‖r y‖) μ)
    (hb : ∀ y, r y ≠ 0 → ‖a y - a' y‖ ≤ δ) :
    ‖(∫ y, w y * (a y * r y) ∂μ) - ∫ y, w y * (a' y * r y) ∂μ‖
      ≤ δ * ∫ y, ‖w y‖ * ‖r y‖ ∂μ := by
  rw [← integral_sub hi hi', ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hwr.const_mul δ) (Filter.Eventually.of_forall fun y => ?_)
  have h1 : w y * (a y * r y) - w y * (a' y * r y) = w y * ((a y - a' y) * r y) := by ring
  rw [h1, norm_mul, norm_mul]
  by_cases hr : r y = 0
  · simp [hr]
  · calc ‖w y‖ * (‖a y - a' y‖ * ‖r y‖) ≤ ‖w y‖ * (δ * ‖r y‖) := by
          gcongr
          exact hb y hr
      _ = δ * (‖w y‖ * ‖r y‖) := by ring

private theorem integral_ne_zero_of_close {w a a' r : G → ℂ} {δ : ℝ}
    (hi : Integrable (fun y => w y * (a y * r y)) μ)
    (hi' : Integrable (fun y => w y * (a' y * r y)) μ)
    (hwr : Integrable (fun y => ‖w y‖ * ‖r y‖) μ)
    (hb : ∀ y, r y ≠ 0 → ‖a y - a' y‖ ≤ δ)
    (hsmall : δ * ∫ y, ‖w y‖ * ‖r y‖ ∂μ < ‖∫ y, w y * (a' y * r y) ∂μ‖) :
    (∫ y, w y * (a y * r y) ∂μ) ≠ 0 := by
  intro h0
  have hle := norm_integral_sub_integral_le (μ := μ) hi hi' hwr hb
  rw [h0, zero_sub, norm_neg] at hle
  exact absurd (lt_of_le_of_lt hle hsmall) (lt_irrefl _)

end Estimate

end ArchFiniteVector.Poly
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.ArchFiniteVector P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.ArchFiniteVector.Poly"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.ArchFiniteVector"

end ModPoly
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.ArchFiniteVector P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.ArchFiniteVector.Poly"

section ModPlateau

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.InfinitePlace
p2m_open "NumberField.InfinitePlace.Completion IsDedekindDomain NumberField.InfiniteAdeleRing AutomorphicForm"
open AutomorphicForm.WindowedSiegel Metric Topology

open scoped Classical

namespace ArchFiniteVector
namespace Plateau

section PinChecks
end PinChecks
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.ArchFiniteVector P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.ArchFiniteVector.Poly"

section PerField

variable {K : Type*} [NormedField K]

private def HS (A : Matrix (Fin 2) (Fin 2) K) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

private theorem HS_eq_four (A : Matrix (Fin 2) (Fin 2) K) :
    HS A = ‖A 0 0‖ ^ 2 + ‖A 0 1‖ ^ 2 + (‖A 1 0‖ ^ 2 + ‖A 1 1‖ ^ 2) := by
  simp [HS, Fin.sum_univ_two]

private theorem HS_eq (g : GL (Fin 2) K) :
    HS (g : Matrix (Fin 2) (Fin 2) K) =
      ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ ^ 2 *
        (topNormSq ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) +
          rowNormSq ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero g
  have hinv : ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (g : Matrix (Fin 2) (Fin 2) K).det⁻¹ • (g : Matrix (Fin 2) (Fin 2) K).adjugate := by
    rw [Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv]
  have hn : ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ ≠ 0 := norm_ne_zero_iff.mpr hdet
  rw [hinv, Matrix.adjugate_fin_two, HS_eq_four]
  simp [topNormSq, rowNormSq, Matrix.smul_apply, norm_mul, norm_inv, norm_neg]
  field_simp
  ring

private theorem HS_rowIsometry_mul (k g : GL (Fin 2) K) (hk : IsRowIsometry k) :
    HS ((k * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = HS (g : Matrix (Fin 2) (Fin 2) K) := by
  rw [HS_eq, HS_eq, _root_.mul_inv_rev, topNormSq_mul_rowIsometry _ hk.inv,
    rowNormSq_mul_rowIsometry _ hk.inv, Units.val_mul, Matrix.det_mul, norm_mul, hk.1, one_mul]

private theorem HS_mul_rowIsometry (g k : GL (Fin 2) K) (hk : IsRowIsometry k) :
    HS ((g * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = HS (g : Matrix (Fin 2) (Fin 2) K) := by
  rw [HS_eq_four, HS_eq_four, Units.val_mul]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  rw [hk.2, hk.2]

end PerField
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.ArchFiniteVector P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.ArchFiniteVector.Poly"

section EntrySpace

variable (F : Type) [Field F] [NumberField F]

private abbrev E : Type := Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F

private def q (m : mixedEmbedding.mixedSpace F) : ℝ := (∑ v, ‖m.1 v‖ ^ 2) + ∑ v, ‖m.2 v‖ ^ 2

private theorem q_nonneg (m : mixedEmbedding.mixedSpace F) : 0 ≤ q F m :=
  add_nonneg (Finset.sum_nonneg fun _ _ => by positivity) (Finset.sum_nonneg fun _ _ => by positivity)

private theorem sq_fst_le_q (m : mixedEmbedding.mixedSpace F) (v : {w : InfinitePlace F // IsReal w}) :
    ‖m.1 v‖ ^ 2 ≤ q F m :=
  le_add_of_le_of_nonneg
    (Finset.single_le_sum (f := fun v => ‖m.1 v‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ v))
    (Finset.sum_nonneg fun _ _ => by positivity)

private theorem sq_snd_le_q (m : mixedEmbedding.mixedSpace F) (v : {w : InfinitePlace F // IsComplex w}) :
    ‖m.2 v‖ ^ 2 ≤ q F m :=
  le_add_of_nonneg_of_le (Finset.sum_nonneg fun _ _ => by positivity)
    (Finset.single_le_sum (f := fun v => ‖m.2 v‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ v))

private theorem contDiff_q : ContDiff ℝ (⊤ : ℕ∞) (q F) := by
  unfold q
  refine ContDiff.add ?_ ?_
  · exact ContDiff.sum fun v _ => ((contDiff_apply ℝ ℝ v).comp contDiff_fst).norm_sq (𝕜 := ℝ)
  · exact ContDiff.sum fun v _ => ((contDiff_apply ℝ ℂ v).comp contDiff_snd).norm_sq (𝕜 := ℂ)

private theorem q_ringEquiv (x : InfiniteAdeleRing F) :
    q F (InfiniteAdeleRing.ringEquiv_mixedSpace F x) = ∑ w, ‖x w‖ ^ 2 := by
  have h1 : ∀ v : {w : InfinitePlace F // IsReal w},
      ‖extensionEmbeddingOfIsReal v.2 (x v.1)‖ = ‖x v.1‖ := fun v =>
    (isometry_extensionEmbeddingOfIsReal v.2).norm_map_of_map_zero (map_zero _) _
  have h2 : ∀ v : {w : InfinitePlace F // IsComplex w},
      ‖extensionEmbedding v.1 (x v.1)‖ = ‖x v.1‖ := fun v =>
    (isometry_extensionEmbedding v.1).norm_map_of_map_zero (map_zero _) _
  simp only [q, InfiniteAdeleRing.ringEquiv_mixedSpace_apply, h1, h2]
  rw [← Fintype.sum_subtype_add_sum_subtype IsReal (fun w => ‖x w‖ ^ 2)]
  congr 1
  exact (Fintype.sum_equiv (Equiv.subtypeEquivRight fun _ => not_isReal_iff_isComplex)
    (fun v => ‖x v.1‖ ^ 2) (fun v => ‖x v.1‖ ^ 2) fun _ => rfl).symm

private def N (M : E F) : ℝ := ∑ i, ∑ j, q F (M i j)

private theorem q_le_N (M : E F) (i j : Fin 2) : q F (M i j) ≤ N F M := by
  unfold N
  calc q F (M i j) ≤ ∑ j', q F (M i j') :=
        Finset.single_le_sum (f := fun j' => q F (M i j')) (fun _ _ => q_nonneg F _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', q F (M i' j') :=
        Finset.single_le_sum (f := fun i' => ∑ j', q F (M i' j'))
          (fun _ _ => Finset.sum_nonneg fun _ _ => q_nonneg F _) (Finset.mem_univ i)

private theorem contDiff_N : ContDiff ℝ (⊤ : ℕ∞) (N F) := by
  unfold N
  exact ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
    (contDiff_q F).comp ((contDiff_apply ℝ (mixedEmbedding.mixedSpace F) j).comp
      (contDiff_apply ℝ (Fin 2 → mixedEmbedding.mixedSpace F) i))

private theorem norm_le_sqrt_N (M : E F) : ‖M‖ ≤ Real.sqrt (N F M) := by
  have key : ∀ (a : ℝ), 0 ≤ a → a ^ 2 ≤ N F M → a ≤ Real.sqrt (N F M) := fun a ha h =>
    calc a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
      _ ≤ Real.sqrt (N F M) := Real.sqrt_le_sqrt h
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun j => ?_
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun v => ?_
    exact key _ (norm_nonneg _) ((sq_fst_le_q F _ v).trans (q_le_N F M i j))
  · refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun v => ?_
    exact key _ (norm_nonneg _) ((sq_snd_le_q F _ v).trans (q_le_N F M i j))

private def detE (M : E F) : mixedEmbedding.mixedSpace F := M 0 0 * M 1 1 - M 0 1 * M 1 0

omit [NumberField F] in
private theorem detE_eq_det (M : E F) :
    detE F M = Matrix.det (M : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F)) := by
  rw [Matrix.det_fin_two]
  rfl

private theorem contDiff_detE : ContDiff ℝ (⊤ : ℕ∞) (detE F) := by
  have hc : ∀ i j : Fin 2, ContDiff ℝ (⊤ : ℕ∞) fun M : E F => M i j := fun i j =>
    (contDiff_apply ℝ (mixedEmbedding.mixedSpace F) j).comp
      (contDiff_apply ℝ (Fin 2 → mixedEmbedding.mixedSpace F) i)
  unfold detE
  exact ((hc 0 0).mul (hc 1 1)).sub ((hc 0 1).mul (hc 1 0))

private def PD (M : E F) : ℝ := (∏ v, ‖(detE F M).1 v‖ ^ 2) * ∏ v, ‖(detE F M).2 v‖ ^ 2

private theorem PD_nonneg (M : E F) : 0 ≤ PD F M :=
  mul_nonneg (Finset.prod_nonneg fun _ _ => by positivity) (Finset.prod_nonneg fun _ _ => by positivity)

private theorem contDiff_PD : ContDiff ℝ (⊤ : ℕ∞) (PD F) := by
  unfold PD
  refine ContDiff.mul ?_ ?_
  · exact contDiff_prod fun v _ =>
      ((contDiff_apply ℝ ℝ v).comp (contDiff_fst.comp (contDiff_detE F))).norm_sq (𝕜 := ℝ)
  · exact contDiff_prod fun v _ =>
      ((contDiff_apply ℝ ℂ v).comp (contDiff_snd.comp (contDiff_detE F))).norm_sq (𝕜 := ℂ)

private theorem isUnit_detE_of_PD_ne_zero {M : E F} (h : PD F M ≠ 0) : IsUnit (detE F M) := by
  have h1 : ∀ v, (detE F M).1 v ≠ 0 := fun v hv => by
    apply h
    unfold PD
    rw [Finset.prod_eq_zero (Finset.mem_univ v) (by rw [hv, norm_zero, zero_pow two_ne_zero]), zero_mul]
  have h2 : ∀ v, (detE F M).2 v ≠ 0 := fun v hv => by
    apply h
    unfold PD
    rw [Finset.prod_eq_zero (Finset.mem_univ v) (by rw [hv, norm_zero, zero_pow two_ne_zero]), mul_zero]
  refine IsUnit.of_mul_eq_one ⟨fun v => ((detE F M).1 v)⁻¹, fun v => ((detE F M).2 v)⁻¹⟩ ?_
  refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
  · show (detE F M).1 v * ((detE F M).1 v)⁻¹ = 1
    exact mul_inv_cancel₀ (h1 v)
  · show (detE F M).2 v * ((detE F M).2 v)⁻¹ = 1
    exact mul_inv_cancel₀ (h2 v)

end EntrySpace
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.ArchFiniteVector P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.ArchFiniteVector.Poly"

section Bridges

variable (F : Type) [Field F] [NumberField F]

omit [NumberField F] in
private theorem archEntries_eq_mapMatrix (y : GL (Fin 2) (InfiniteAdeleRing F)) :
    (archEntries F y : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F)) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.mapMatrix
        (y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) := by
  funext i j
  rfl

omit [NumberField F] in
private theorem archComponent_coe (w : InfinitePlace F) (y : GL (Fin 2) (InfiniteAdeleRing F)) :
    ((archComponent F w y : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) =
      (archEval F w).mapMatrix (y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) := by
  ext i j
  rfl

private theorem N_archEntries (y : GL (Fin 2) (InfiniteAdeleRing F)) :
    N F (archEntries F y) =
      ∑ w : InfinitePlace F, HS ((archComponent F w y : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) := by
  unfold N HS
  simp only [archEntries_apply, q_ringEquiv]
  calc (∑ i, ∑ j, ∑ w, ‖(y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j w‖ ^ 2)
        = ∑ i, ∑ w, ∑ j, ‖(y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j w‖ ^ 2 :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ w, ∑ i, ∑ j, ‖(y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j w‖ ^ 2 := Finset.sum_comm
    _ = _ := by rfl

omit [NumberField F] in
private theorem detE_archEntries (y : GL (Fin 2) (InfiniteAdeleRing F)) :
    detE F (archEntries F y) =
      InfiniteAdeleRing.ringEquiv_mixedSpace F (y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)).det := by
  rw [detE_eq_det, archEntries_eq_mapMatrix]
  exact (RingHom.map_det _ _).symm

omit [NumberField F] in
private theorem norm_detE_fst (y : GL (Fin 2) (InfiniteAdeleRing F)) (v : {w : InfinitePlace F // IsReal w}) :
    ‖(detE F (archEntries F y)).1 v‖ =
      ‖((archComponent F v.1 y : GL (Fin 2) v.1.Completion) : Matrix (Fin 2) (Fin 2) v.1.Completion).det‖ := by
  rw [detE_archEntries, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  show ‖extensionEmbeddingOfIsReal v.2 ((y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)).det v.1)‖ = _
  rw [(isometry_extensionEmbeddingOfIsReal v.2).norm_map_of_map_zero (map_zero _), archComponent_coe,
    ← RingHom.map_det]
  rfl

omit [NumberField F] in
private theorem norm_detE_snd (y : GL (Fin 2) (InfiniteAdeleRing F)) (v : {w : InfinitePlace F // IsComplex w}) :
    ‖(detE F (archEntries F y)).2 v‖ =
      ‖((archComponent F v.1 y : GL (Fin 2) v.1.Completion) : Matrix (Fin 2) (Fin 2) v.1.Completion).det‖ := by
  rw [detE_archEntries, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  show ‖extensionEmbedding v.1 ((y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)).det v.1)‖ = _
  rw [(isometry_extensionEmbedding v.1).norm_map_of_map_zero (map_zero _), archComponent_coe,
    ← RingHom.map_det]
  rfl

private theorem PD_archEntries_pos (y : GL (Fin 2) (InfiniteAdeleRing F)) : 0 < PD F (archEntries F y) := by
  unfold PD
  refine mul_pos (Finset.prod_pos fun v _ => ?_) (Finset.prod_pos fun v _ => ?_)
  · rw [norm_detE_fst]
    exact pow_pos (norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero _)) 2
  · rw [norm_detE_snd]
    exact pow_pos (norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero _)) 2

variable {F}

omit [NumberField F] in
private theorem norm_det_archComponent_mul (w : InfinitePlace F) (k : GL (Fin 2) w.Completion)
    (hk : IsRowIsometry k) (y : GL (Fin 2) (InfiniteAdeleRing F)) (v : InfinitePlace F) :
    ‖((archComponent F v (archGLIncl F w k * y) : GL (Fin 2) v.Completion) :
        Matrix (Fin 2) (Fin 2) v.Completion).det‖ =
      ‖((archComponent F v y : GL (Fin 2) v.Completion) : Matrix (Fin 2) (Fin 2) v.Completion).det‖ := by
  rw [map_mul]
  by_cases h : v = w
  · subst h
    rw [archComponent_archGLIncl_self, Units.val_mul, Matrix.det_mul, norm_mul, hk.1, one_mul]
  · rw [archComponent_archGLIncl_of_ne F h, one_mul]

private theorem N_archEntries_mul (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) (hk : IsRowIsometry k)
    (y : GL (Fin 2) (InfiniteAdeleRing F)) :
    N F (archEntries F (archGLIncl F w k * y)) = N F (archEntries F y) := by
  rw [N_archEntries, N_archEntries]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_mul]
  by_cases h : v = w
  · subst h
    rw [archComponent_archGLIncl_self]
    exact HS_rowIsometry_mul k _ hk
  · rw [archComponent_archGLIncl_of_ne F h, one_mul]

private theorem PD_archEntries_mul (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) (hk : IsRowIsometry k)
    (y : GL (Fin 2) (InfiniteAdeleRing F)) :
    PD F (archEntries F (archGLIncl F w k * y)) = PD F (archEntries F y) := by
  unfold PD
  simp only [norm_detE_fst, norm_detE_snd, norm_det_archComponent_mul w k hk y]

omit [NumberField F] in
private theorem norm_det_archComponent_mul_right (w : InfinitePlace F) (k : GL (Fin 2) w.Completion)
    (hk : IsRowIsometry k) (y : GL (Fin 2) (InfiniteAdeleRing F)) (v : InfinitePlace F) :
    ‖((archComponent F v (y * archGLIncl F w k) : GL (Fin 2) v.Completion) :
        Matrix (Fin 2) (Fin 2) v.Completion).det‖ =
      ‖((archComponent F v y : GL (Fin 2) v.Completion) : Matrix (Fin 2) (Fin 2) v.Completion).det‖ := by
  rw [map_mul]
  by_cases h : v = w
  · subst h
    rw [archComponent_archGLIncl_self, Units.val_mul, Matrix.det_mul, norm_mul, hk.1, mul_one]
  · rw [archComponent_archGLIncl_of_ne F h, mul_one]

private theorem N_archEntries_mul_right (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) (hk : IsRowIsometry k)
    (y : GL (Fin 2) (InfiniteAdeleRing F)) :
    N F (archEntries F (y * archGLIncl F w k)) = N F (archEntries F y) := by
  rw [N_archEntries, N_archEntries]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_mul]
  by_cases h : v = w
  · subst h
    rw [archComponent_archGLIncl_self]
    exact HS_mul_rowIsometry _ k hk
  · rw [archComponent_archGLIncl_of_ne F h, mul_one]

private theorem PD_archEntries_mul_right (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) (hk : IsRowIsometry k)
    (y : GL (Fin 2) (InfiniteAdeleRing F)) :
    PD F (archEntries F (y * archGLIncl F w k)) = PD F (archEntries F y) := by
  unfold PD
  simp only [norm_detE_fst, norm_detE_snd, norm_det_archComponent_mul_right w k hk y]

end Bridges
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.ArchFiniteVector P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.ArchFiniteVector.Poly"

section Plateau

private def θup (R t : ℝ) : ℝ := Real.smoothTransition (R + 1 - t)

private def θlow (ε t : ℝ) : ℝ := Real.smoothTransition (2 / ε * t - 1)

private theorem contDiff_θup (R : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (θup R) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

private theorem contDiff_θlow (ε : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (θlow ε) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

private theorem θup_eq_one {R t : ℝ} (h : t ≤ R) : θup R t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

private theorem θup_eq_zero {R t : ℝ} (h : R + 1 ≤ t) : θup R t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

private theorem θlow_eq_one {ε t : ℝ} (hε : 0 < ε) (h : ε ≤ t) : θlow ε t = 1 := by
  refine Real.smoothTransition.one_of_one_le ?_
  have : 2 / ε * t ≥ 2 / ε * ε := mul_le_mul_of_nonneg_left h (by positivity)
  have h2 : 2 / ε * ε = 2 := by field_simp
  linarith

private theorem θlow_eq_zero {ε t : ℝ} (hε : 0 < ε) (h : t ≤ ε / 2) : θlow ε t = 0 := by
  refine Real.smoothTransition.zero_of_nonpos ?_
  have : 2 / ε * t ≤ 2 / ε * (ε / 2) := mul_le_mul_of_nonneg_left h (by positivity)
  have h2 : 2 / ε * (ε / 2) = 1 := by field_simp
  linarith

variable (F : Type) [Field F] [NumberField F]

private def plateau (R ε : ℝ) (M : E F) : ℝ := θup R (N F M) * θlow ε (PD F M)

private theorem contDiff_plateau (R ε : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (plateau F R ε) :=
  ((contDiff_θup R).comp (contDiff_N F)).mul ((contDiff_θlow ε).comp (contDiff_PD F))

private theorem plateau_eq_one {R ε : ℝ} (hε : 0 < ε) {M : E F} (hN : N F M ≤ R) (hP : ε ≤ PD F M) :
    plateau F R ε M = 1 := by
  rw [plateau, θup_eq_one hN, θlow_eq_one hε hP, one_mul]

private theorem N_lt_of_plateau_ne_zero {R ε : ℝ} {M : E F} (h : plateau F R ε M ≠ 0) : N F M < R + 1 := by
  by_contra hc
  exact h (by rw [plateau, θup_eq_zero (not_lt.mp hc), zero_mul])

private theorem PD_gt_of_plateau_ne_zero {R ε : ℝ} (hε : 0 < ε) {M : E F} (h : plateau F R ε M ≠ 0) :
    ε / 2 < PD F M := by
  by_contra hc
  exact h (by rw [plateau, θlow_eq_zero hε (not_lt.mp hc), mul_zero])

private def ZE (R ε : ℝ) : Set (E F) := {M | N F M ≤ R + 1 ∧ ε / 2 ≤ PD F M}

private theorem plateau_ne_zero_subset_ZE (R ε : ℝ) (hε : 0 < ε) :
    {M : E F | plateau F R ε M ≠ 0} ⊆ ZE F R ε := fun _ h =>
  ⟨(N_lt_of_plateau_ne_zero F h).le, (PD_gt_of_plateau_ne_zero F hε h).le⟩

private theorem isClosed_ZE (R ε : ℝ) : IsClosed (ZE F R ε) :=
  (isClosed_le (contDiff_N F).continuous continuous_const).inter
    (isClosed_le continuous_const (contDiff_PD F).continuous)

private theorem isCompact_ZE (R ε : ℝ) : IsCompact (ZE F R ε) := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_ZE F R ε)
    ((Metric.isBounded_closedBall (x := (0 : E F)) (r := Real.sqrt (R + 1))).subset fun M hM => ?_)
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (norm_le_sqrt_N F M).trans (Real.sqrt_le_sqrt hM.1)

private theorem isUnit_detE_of_mem_ZE {R ε : ℝ} (hε : 0 < ε) {M : E F} (hM : M ∈ ZE F R ε) :
    IsUnit (detE F M) :=
  isUnit_detE_of_PD_ne_zero F (lt_of_lt_of_le (half_pos hε) hM.2).ne'

private theorem plateau_archEntries_mul (R ε : ℝ) (w : InfinitePlace F) (k : GL (Fin 2) w.Completion)
    (hk : IsRowIsometry k) (y : GL (Fin 2) (InfiniteAdeleRing F)) :
    plateau F R ε (archEntries F (archGLIncl F w k * y)) = plateau F R ε (archEntries F y) := by
  rw [plateau, plateau, N_archEntries_mul w k hk, PD_archEntries_mul w k hk]

private theorem plateau_archEntries_mul_right (R ε : ℝ) (w : InfinitePlace F) (k : GL (Fin 2) w.Completion)
    (hk : IsRowIsometry k) (y : GL (Fin 2) (InfiniteAdeleRing F)) :
    plateau F R ε (archEntries F (y * archGLIncl F w k)) = plateau F R ε (archEntries F y) := by
  rw [plateau, plateau, N_archEntries_mul_right w k hk, PD_archEntries_mul_right w k hk]

end Plateau
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.ArchFiniteVector P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.ArchFiniteVector.Poly"

section Topology

variable (F : Type) [Field F] [NumberField F]

omit [NumberField F] in
private theorem continuous_ringEquiv_mixedSpace : Continuous (ringEquiv_mixedSpace F) := by
  refine continuous_prodMk.2 ⟨continuous_pi fun v => ?_, continuous_pi fun v => ?_⟩
  · exact (isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

omit [NumberField F] in
private theorem continuous_ringEquiv_mixedSpace_symm : Continuous (ringEquiv_mixedSpace F).symm := by
  apply continuous_pi
  intro v
  by_cases hv : IsReal v
  · have key : (fun y : mixedEmbedding.mixedSpace F => (ringEquiv_mixedSpace F).symm y v)
        = fun y => (isometryEquivRealOfIsReal hv).symm (y.1 ⟨v, hv⟩) := by
      funext y
      apply (isometryEquivRealOfIsReal hv).injective
      rw [IsometryEquiv.apply_symm_apply]
      exact congrArg (fun z : mixedEmbedding.mixedSpace F => z.1 ⟨v, hv⟩)
        ((ringEquiv_mixedSpace F).apply_symm_apply y)
    rw [key]
    exact (isometryEquivRealOfIsReal hv).symm.continuous.comp
      ((continuous_apply _).comp continuous_fst)
  · have hc : IsComplex v := not_isReal_iff_isComplex.1 hv
    have key : (fun y : mixedEmbedding.mixedSpace F => (ringEquiv_mixedSpace F).symm y v)
        = fun y => (isometryEquivComplexOfIsComplex hc).symm (y.2 ⟨v, hc⟩) := by
      funext y
      apply (isometryEquivComplexOfIsComplex hc).injective
      rw [IsometryEquiv.apply_symm_apply]
      exact congrArg (fun z : mixedEmbedding.mixedSpace F => z.2 ⟨v, hc⟩)
        ((ringEquiv_mixedSpace F).apply_symm_apply y)
    rw [key]
    exact (isometryEquivComplexOfIsComplex hc).symm.continuous.comp
      ((continuous_apply _).comp continuous_snd)

omit [NumberField F] in
private def mixedHomeo : InfiniteAdeleRing F ≃ₜ mixedEmbedding.mixedSpace F where
  toEquiv := (ringEquiv_mixedSpace F).toEquiv
  continuous_toFun := continuous_ringEquiv_mixedSpace F
  continuous_invFun := continuous_ringEquiv_mixedSpace_symm F

omit [NumberField F] in
private def matHomeo : (Fin 2 → Fin 2 → InfiniteAdeleRing F) ≃ₜ E F :=
  Homeomorph.piCongrRight fun _ => Homeomorph.piCongrRight fun _ => mixedHomeo F

omit [NumberField F] in
private def pairHomeo :
    (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) × (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))ᵐᵒᵖ)
      ≃ₜ (E F × E F) :=
  Homeomorph.prodCongr (matHomeo F) (MulOpposite.opHomeomorph.symm.trans (matHomeo F))

omit [NumberField F] in
private def J (g : GL (Fin 2) (InfiniteAdeleRing F)) : E F × E F :=
  pairHomeo F (Units.embedProduct _ g)

omit [NumberField F] in
private theorem J_apply (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    J F g = (archEntries F g, archEntries F g⁻¹) := rfl

omit [NumberField F] in
private theorem isClosedEmbedding_J : IsClosedEmbedding (J F) :=
  (pairHomeo F).isClosedEmbedding.comp Units.isClosedEmbedding_embedProduct

omit [NumberField F] in
private theorem continuous_archEntries : Continuous (archEntries F) := by
  have : archEntries F = fun g => (J F g).1 := funext fun g => rfl
  rw [this]
  exact continuous_fst.comp (isClosedEmbedding_J F).continuous

private def Ψinv (m : E F) : E F :=
  fun i j => (Ring.inverse (Matrix.det (m : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F))) •
    Matrix.adjugate (m : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F))) i j

omit [NumberField F] in
private theorem Ψinv_archEntries (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    Ψinv F (archEntries F g) = archEntries F g⁻¹ := by
  set A := (ringEquiv_mixedSpace F).toRingHom.mapMatrix
    (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) with hA
  have hAinv : (ringEquiv_mixedSpace F).toRingHom.mapMatrix
      ((g⁻¹ : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) = A⁻¹ := by
    symm
    apply Matrix.inv_eq_left_inv
    rw [hA, ← map_mul, Units.inv_mul, map_one]
  have h1 : (archEntries F g⁻¹ : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F)) = A⁻¹ := by
    rw [archEntries_eq_mapMatrix, hAinv]
  funext i j
  show (Ring.inverse (Matrix.det (archEntries F g : Matrix (Fin 2) (Fin 2) _)) •
      Matrix.adjugate (archEntries F g : Matrix (Fin 2) (Fin 2) _)) i j = archEntries F g⁻¹ i j
  have h2 : archEntries F g⁻¹ i j = (archEntries F g⁻¹ : Matrix (Fin 2) (Fin 2) _) i j := rfl
  rw [h2, h1, archEntries_eq_mapMatrix, ← hA, Matrix.inv_def]

private theorem continuousOn_Ψinv {R ε : ℝ} (hε : 0 < ε) : ContinuousOn (Ψinv F) (ZE F R ε) := by
  intro m hm
  have hunit : IsUnit (Matrix.det (m : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F))) := by
    rw [← detE_eq_det]
    exact isUnit_detE_of_mem_ZE F hε hm
  obtain ⟨u, hu⟩ := hunit
  apply ContinuousAt.continuousWithinAt
  have hdet : Continuous fun m : E F =>
      Matrix.det (m : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F)) :=
    Continuous.matrix_det continuous_id
  have h1 : ContinuousAt (fun m : E F =>
      Ring.inverse (Matrix.det (m : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F)))) m := by
    have hi : ContinuousAt Ring.inverse
        (Matrix.det (m : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F))) :=
      hu ▸ NormedRing.inverse_continuousAt u
    exact hi.comp hdet.continuousAt
  have h2 : Continuous fun m : E F =>
      Matrix.adjugate (m : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F)) :=
    Continuous.matrix_adjugate continuous_id
  rw [continuousAt_pi]
  intro i
  rw [continuousAt_pi]
  intro j
  have h3 : ContinuousAt (fun m : E F =>
      Ring.inverse (Matrix.det (m : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F))) *
        Matrix.adjugate (m : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F)) i j) m :=
    h1.mul (h2.matrix_elem i j).continuousAt
  have e : (fun y : E F => Ψinv F y i j) = fun m : E F =>
      Ring.inverse (Matrix.det (m : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F))) *
        Matrix.adjugate (m : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F)) i j := by
    funext y
    simp only [Ψinv, Matrix.smul_apply, smul_eq_mul]
  rw [e]
  exact h3

private theorem hasCompactSupport_of_plateau {R ε : ℝ} (hε : 0 < ε)
    (f : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (hf : ∀ y, plateau F R ε (archEntries F y) = 0 → f y = 0) : HasCompactSupport f := by
  set T : Set (E F × E F) := ZE F R ε ×ˢ (Ψinv F '' ZE F R ε) with hT
  have hTc : IsCompact T :=
    (isCompact_ZE F R ε).prod ((isCompact_ZE F R ε).image_of_continuousOn (continuousOn_Ψinv F hε))
  have hpre : IsCompact (J F ⁻¹' T) := (isClosedEmbedding_J F).isCompact_preimage hTc
  refine HasCompactSupport.intro' hpre (hTc.isClosed.preimage (isClosedEmbedding_J F).continuous) ?_
  intro y hy
  apply hf
  by_contra hne
  apply hy
  have hZ : archEntries F y ∈ ZE F R ε := plateau_ne_zero_subset_ZE F R ε hε hne
  show J F y ∈ T
  rw [J_apply, hT, Set.mem_prod]
  exact ⟨hZ, ⟨archEntries F y, hZ, Ψinv_archEntries F y⟩⟩

end Topology
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.ArchFiniteVector P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.ArchFiniteVector.Poly"

section Parameters

variable (F : Type) [Field F] [NumberField F]

private theorem exists_R (C : Set (GL (Fin 2) (InfiniteAdeleRing F))) (hC : IsCompact C) :
    ∃ R : ℝ, ∀ y ∈ C, N F (archEntries F y) ≤ R := by
  obtain ⟨R, hR⟩ := hC.bddAbove_image
    (f := fun y => N F (archEntries F y)) ((contDiff_N F).continuous.comp (continuous_archEntries F)).continuousOn
  exact ⟨R, fun y hy => hR ⟨y, hy, rfl⟩⟩

private theorem exists_eps (C : Set (GL (Fin 2) (InfiniteAdeleRing F))) (hC : IsCompact C) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ C, ε ≤ PD F (archEntries F y) := by
  by_cases hne : C.Nonempty
  · obtain ⟨y₀, hy₀, hmin⟩ := hC.exists_isMinOn hne
      ((contDiff_PD F).continuous.comp (continuous_archEntries F)).continuousOn
    exact ⟨PD F (archEntries F y₀), PD_archEntries_pos F y₀, fun y hy => hmin hy⟩
  · exact ⟨1, one_pos, fun y hy => (hne ⟨y, hy⟩).elim⟩

private theorem exists_plateau (C : Set (GL (Fin 2) (InfiniteAdeleRing F))) (hC : IsCompact C) :
    ∃ Ψ₀ : E F → ℝ, ContDiff ℝ (⊤ : ℕ∞) Ψ₀ ∧ (∀ y ∈ C, Ψ₀ (archEntries F y) = 1) ∧
      (∀ (w : InfinitePlace F) (k : GL (Fin 2) w.Completion), IsRowIsometry k →
        ∀ y, Ψ₀ (archEntries F (archGLIncl F w k * y)) = Ψ₀ (archEntries F y)) ∧
      (∀ (w : InfinitePlace F) (k : GL (Fin 2) w.Completion), IsRowIsometry k →
        ∀ y, Ψ₀ (archEntries F (y * archGLIncl F w k)) = Ψ₀ (archEntries F y)) ∧
      (∀ f : GL (Fin 2) (InfiniteAdeleRing F) → ℂ,
        (∀ y, Ψ₀ (archEntries F y) = 0 → f y = 0) → HasCompactSupport f) ∧
      (∃ Kc : Set (E F), IsCompact Kc ∧ ∀ M, Ψ₀ M ≠ 0 → M ∈ Kc) := by
  obtain ⟨R, hR⟩ := exists_R F C hC
  obtain ⟨ε, hε, hP⟩ := exists_eps F C hC
  exact ⟨plateau F R ε, contDiff_plateau F R ε, fun y hy => plateau_eq_one F hε (hR y hy) (hP y hy),
    fun w k hk y => plateau_archEntries_mul F R ε w k hk y,
    fun w k hk y => plateau_archEntries_mul_right F R ε w k hk y,
    fun f hf => hasCompactSupport_of_plateau F hε f hf,
    ⟨ZE F R ε, isCompact_ZE F R ε, fun M hM => plateau_ne_zero_subset_ZE F R ε hε hM⟩⟩

end Parameters
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.ArchFiniteVector P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.ArchFiniteVector.Poly"

end ArchFiniteVector.Plateau
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.ArchFiniteVector P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.ArchFiniteVector.Poly"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.ArchFiniteVector P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.ArchFiniteVector.Poly"

end ModPlateau
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.ArchFiniteVector P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.ArchFiniteVector.Poly"

section ModAssembly

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume

open scoped Classical

namespace ArchFiniteVector
namespace Assembly

section PinChecks
end PinChecks
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.ArchFiniteVector P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.ArchFiniteVector.Poly"

variable (F : Type) [Field F] [NumberField F]

private abbrev E : Type := Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F

private def Lsub (A : E F) : E F →ₗ[ℝ] E F where
  toFun M := fun i j => ∑ l, A i l * M l j
  map_add' M M' := by
    funext i j
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c M := by
    funext i j
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, mul_smul_comm]

omit [NumberField F] in
private theorem Lsub_apply (A M : E F) (i j : Fin 2) : Lsub F A M i j = ∑ l, A i l * M l j := rfl

omit [NumberField F] in
private theorem archEntries_mul (a z : GL (Fin 2) (InfiniteAdeleRing F)) :
    archEntries F (a * z) = Lsub F (archEntries F a) (archEntries F z) := by
  funext i j
  rw [Lsub_apply]
  simp only [archEntries_apply, Units.val_mul, Matrix.mul_apply, map_sum, map_mul]

omit [NumberField F] in
private theorem isRowIsometry_coe_inv {w : InfinitePlace F} (k : rowIsometrySubgroup₀ w.Completion) :
    IsRowIsometry ((k⁻¹ : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) :=
  ((mem_rowIsometrySubgroup₀_iff w.Completion).mp (k⁻¹).2).2

private theorem glFin_inv_mul (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion)
    (y : AdelicGL2 (𝓞 F) F) :
    glFin (𝓞 F) F ((rowIsometryInclAt₀ F w k)⁻¹ * y) = glFin (𝓞 F) F y := by
  rw [map_mul, map_inv, glFin_rowIsometryInclAt₀, inv_one, one_mul]

private theorem glArch_inv_mul (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion)
    (y : AdelicGL2 (𝓞 F) F) :
    glArch (𝓞 F) F ((rowIsometryInclAt₀ F w k)⁻¹ * y) =
      archGLIncl F w ((k⁻¹ : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) *
        glArch (𝓞 F) F y := by
  rw [map_mul, ← map_inv, glArch_rowIsometryInclAt₀]
  rfl

private def Tfix (r : AdelicGL2 (𝓞 F) F → ℂ) : (E F → ℝ) →ₗ[ℝ] (AdelicGL2 (𝓞 F) F → ℂ) where
  toFun v := fun y => (v (archEntries F (glArch (𝓞 F) F y)) : ℂ) * r y
  map_add' v v' := by
    funext y
    simp only [Pi.add_apply, Complex.ofReal_add, add_mul]
  map_smul' c v := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply, Complex.real_smul,
      mul_assoc]

private theorem Tfix_apply (r : AdelicGL2 (𝓞 F) F → ℂ) (v : E F → ℝ) (y : AdelicGL2 (𝓞 F) F) :
    Tfix F r v y = (v (archEntries F (glArch (𝓞 F) F y)) : ℂ) * r y := rfl

private theorem Tfix_mem_span (r : AdelicGL2 (𝓞 F) F → ℂ) {n : ℕ} (b : Fin n → E F → ℝ) {v : E F → ℝ}
    (hv : v ∈ Submodule.span ℝ (Set.range b)) :
    Tfix F r v ∈ Submodule.span ℂ (Set.range fun i => Tfix F r (b i)) := by
  have h1 : Tfix F r v ∈ (Submodule.span ℝ (Set.range b)).map (Tfix F r) := Submodule.mem_map_of_mem hv
  rw [Submodule.map_span, ← Set.range_comp] at h1
  exact Submodule.span_le_restrictScalars ℝ ℂ _ h1

private theorem isArchTestFactor_mul_plateau (Ψ₀ : E F → ℝ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ₀)
    (hkill : ∀ f : GL (Fin 2) (InfiniteAdeleRing F) → ℂ,
      (∀ y, Ψ₀ (archEntries F y) = 0 → f y = 0) → HasCompactSupport f)
    (h : E F → ℂ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    IsArchTestFactor F (fun z => h (archEntries F z) * (Ψ₀ (archEntries F z) : ℂ)) := by
  refine ⟨⟨fun M => h M * (Ψ₀ M : ℂ), hh.mul (Complex.ofRealCLM.contDiff.comp hΨ), fun _ => rfl⟩, ?_⟩
  exact hkill _ fun y hy => by simp only [hy, Complex.ofReal_zero, mul_zero]

private theorem contDiff_ofReal_comp {p : E F → ℝ} (hp : ContDiff ℝ (⊤ : ℕ∞) p) :
    ContDiff ℝ (⊤ : ℕ∞) fun M => (p M : ℂ) :=
  Complex.ofRealCLM.contDiff.comp hp

private theorem contDiff_pair {p q : E F → ℝ} (hp : ContDiff ℝ (⊤ : ℕ∞) p) (hq : ContDiff ℝ (⊤ : ℕ∞) q) :
    ContDiff ℝ (⊤ : ℕ∞) fun M => (p M : ℂ) + (q M : ℂ) * Complex.I :=
  (contDiff_ofReal_comp F hp).add ((contDiff_ofReal_comp F hq).mul contDiff_const)

private theorem continuous_and_hasCompactSupport_tensor (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (hfa : IsArchTestFactor F fa) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) (hff : IsFinTestFactor F ff) :
    Continuous (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) ∧
      HasCompactSupport (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) :=
  continuous_and_hasCompactSupport_of_isFactorizableTestFn F _
    (ArchFiniteVector.ConvHalf.isFactorizableTestFn_mk F fa hfa ff hff)

section Translate

variable {F}
variable (Ψ₀ p q : E F → ℝ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ)

private def rfun : AdelicGL2 (𝓞 F) F → ℂ :=
  fun y => (Ψ₀ (archEntries F (glArch (𝓞 F) F y)) : ℂ) * ff (glFin (𝓞 F) F y)

private def ffun : AdelicGL2 (𝓞 F) F → ℂ :=
  fun y => ((p (archEntries F (glArch (𝓞 F) F y)) : ℂ) +
      (q (archEntries F (glArch (𝓞 F) F y)) : ℂ) * Complex.I) *
    (Ψ₀ (archEntries F (glArch (𝓞 F) F y)) : ℂ) * ff (glFin (𝓞 F) F y)

private theorem ffun_eq_tensor : ffun Ψ₀ p q ff = fun g =>
    (fun z => ((p (archEntries F z) : ℂ) + (q (archEntries F z) : ℂ) * Complex.I) *
      (Ψ₀ (archEntries F z) : ℂ)) (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g) := rfl

variable (hΨinv : ∀ (w : InfinitePlace F) (k : GL (Fin 2) w.Completion), IsRowIsometry k →
  ∀ y, Ψ₀ (archEntries F (archGLIncl F w k * y)) = Ψ₀ (archEntries F y))

include hΨinv in
private theorem ffun_translate (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (y : AdelicGL2 (𝓞 F) F) :
    ffun Ψ₀ p q ff ((rowIsometryInclAt₀ F w k)⁻¹ * y) =
      Tfix F (rfun Ψ₀ ff) (p ∘ Lsub F (archEntries F (archGLIncl F w
          ((k⁻¹ : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion)))) y +
        Complex.I * Tfix F (rfun Ψ₀ ff) (q ∘ Lsub F (archEntries F (archGLIncl F w
          ((k⁻¹ : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion)))) y := by
  rw [Tfix_apply, Tfix_apply]
  unfold ffun rfun
  rw [glFin_inv_mul, glArch_inv_mul, hΨinv w _ (isRowIsometry_coe_inv F k), archEntries_mul]
  simp only [Function.comp_apply]
  ring

include hΨinv in
private theorem ffun_translate_mem_span {n m : ℕ} (bp : Fin n → E F → ℝ) (bq : Fin m → E F → ℝ)
    (hp : ∀ L : E F →ₗ[ℝ] E F, (p ∘ L) ∈ Submodule.span ℝ (Set.range bp))
    (hq : ∀ L : E F →ₗ[ℝ] E F, (q ∘ L) ∈ Submodule.span ℝ (Set.range bq))
    (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    (fun y => ffun Ψ₀ p q ff ((rowIsometryInclAt₀ F w k)⁻¹ * y)) ∈
      Submodule.span ℂ (Set.range (Fin.append (fun i => Tfix F (rfun Ψ₀ ff) (bp i))
        (fun j => Tfix F (rfun Ψ₀ ff) (bq j)))) := by
  have key : (fun y => ffun Ψ₀ p q ff ((rowIsometryInclAt₀ F w k)⁻¹ * y)) =
      Tfix F (rfun Ψ₀ ff) (p ∘ Lsub F (archEntries F (archGLIncl F w
          ((k⁻¹ : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion)))) +
        Complex.I • Tfix F (rfun Ψ₀ ff) (q ∘ Lsub F (archEntries F (archGLIncl F w
          ((k⁻¹ : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion)))) := by
    funext y
    rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact ffun_translate Ψ₀ p q ff hΨinv w k y
  rw [key]
  have hl : Set.range (fun i => Tfix F (rfun Ψ₀ ff) (bp i)) ⊆
      Set.range (Fin.append (fun i => Tfix F (rfun Ψ₀ ff) (bp i)) (fun j => Tfix F (rfun Ψ₀ ff) (bq j))) := by
    rintro _ ⟨i, rfl⟩
    exact ⟨Fin.castAdd m i, by rw [Fin.append_left]⟩
  have hr : Set.range (fun j => Tfix F (rfun Ψ₀ ff) (bq j)) ⊆
      Set.range (Fin.append (fun i => Tfix F (rfun Ψ₀ ff) (bp i)) (fun j => Tfix F (rfun Ψ₀ ff) (bq j))) := by
    rintro _ ⟨j, rfl⟩
    exact ⟨Fin.natAdd n j, by rw [Fin.append_right]⟩
  refine add_mem ?_ (Submodule.smul_mem _ _ ?_)
  · exact Submodule.span_mono hl (Tfix_mem_span F (rfun Ψ₀ ff) bp (hp _))
  · exact Submodule.span_mono hr (Tfix_mem_span F (rfun Ψ₀ ff) bq (hq _))

end Translate
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.ArchFiniteVector P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.ArchFiniteVector.Poly"

private theorem rightConv_ffun_ne_zero (u₀ : AdelicGL2 (𝓞 F) F → ℂ) (hu₀ : Continuous u₀)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) (hff : IsFinTestFactor F ff)
    (fa₀ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (Φ₀ : E F → ℂ) (hΦ₀ : ∀ z, fa₀ z = Φ₀ (archEntries F z))
    (hfa₀ : IsArchTestFactor F fa₀)
    (Ψ₀ : E F → ℝ) (hΨs : ContDiff ℝ (⊤ : ℕ∞) Ψ₀) (hΨ1 : ∀ z ∈ tsupport fa₀, Ψ₀ (archEntries F z) = 1)
    (hkill : ∀ f : GL (Fin 2) (InfiniteAdeleRing F) → ℂ,
      (∀ y, Ψ₀ (archEntries F y) = 0 → f y = 0) → HasCompactSupport f)
    (Kc : Set (E F)) (hKc : ∀ M, Ψ₀ M ≠ 0 → M ∈ Kc)
    (p q : E F → ℝ) (hp : ContDiff ℝ (⊤ : ℕ∞) p) (hq : ContDiff ℝ (⊤ : ℕ∞) q) (δ : ℝ)
    (hclose : ∀ M ∈ Kc, ‖((p M : ℂ) + (q M : ℂ) * Complex.I) - Φ₀ M‖ < δ)
    (g₀ : AdelicGL2 (𝓞 F) F)
    (hsmall : letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
      δ * ∫ y, ‖u₀ (g₀ * y)‖ * ‖rfun Ψ₀ ff y‖ ∂(adelicGLHaar (Fin 2) (𝓞 F) F) <
        ‖rightConv F u₀ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g₀‖) :
    rightConv F u₀ (ffun Ψ₀ p q ff) g₀ ≠ 0 := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  have hΨarch : IsArchTestFactor F
      (fun z => (fun _ : E F => (1 : ℂ)) (archEntries F z) * (Ψ₀ (archEntries F z) : ℂ)) :=
    isArchTestFactor_mul_plateau F Ψ₀ hΨs hkill (fun _ => (1 : ℂ)) contDiff_const
  have hr := continuous_and_hasCompactSupport_tensor F _ hΨarch ff hff
  have hr_eq : (fun g => (fun z => (fun _ : E F => (1 : ℂ)) (archEntries F z) * (Ψ₀ (archEntries F z) : ℂ))
      (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) = rfun Ψ₀ ff := by
    funext g
    simp only [rfun, one_mul]
  rw [hr_eq] at hr
  have hfarch : IsArchTestFactor F (fun z => ((p (archEntries F z) : ℂ) + (q (archEntries F z) : ℂ) *
      Complex.I) * (Ψ₀ (archEntries F z) : ℂ)) :=
    isArchTestFactor_mul_plateau F Ψ₀ hΨs hkill _ (contDiff_pair F hp hq)
  have hf := continuous_and_hasCompactSupport_tensor F _ hfarch ff hff
  rw [← ffun_eq_tensor] at hf
  have hf₀ := continuous_and_hasCompactSupport_tensor F fa₀ hfa₀ ff hff
  have hint := ArchFiniteVector.KFinite.integrable_rightConv_integrand F u₀ hu₀ _ hf.1 hf.2 g₀
  have hint₀ := ArchFiniteVector.KFinite.integrable_rightConv_integrand F u₀ hu₀ _ hf₀.1 hf₀.2 g₀
  have hintr := ArchFiniteVector.KFinite.integrable_rightConv_integrand F u₀ hu₀ _ hr.1 hr.2 g₀
  have e1 : (fun y => u₀ (g₀ * y) * ffun Ψ₀ p q ff y) = fun y => u₀ (g₀ * y) *
      ((fun y => (p (archEntries F (glArch (𝓞 F) F y)) : ℂ) +
        (q (archEntries F (glArch (𝓞 F) F y)) : ℂ) * Complex.I) y * rfun Ψ₀ ff y) := by
    funext y
    simp only [ffun, rfun]
    ring
  have e0 : (fun y => u₀ (g₀ * y) * (fa₀ (glArch (𝓞 F) F y) * ff (glFin (𝓞 F) F y))) = fun y => u₀ (g₀ * y) *
      (Φ₀ (archEntries F (glArch (𝓞 F) F y)) * rfun Ψ₀ ff y) := by
    funext y
    simp only [rfun]
    by_cases h0 : fa₀ (glArch (𝓞 F) F y) = 0
    · rw [h0, ← hΦ₀, h0]
      ring
    · rw [hΨ1 _ (subset_tsupport _ h0), ← hΦ₀]
      push_cast
      ring
  have hne : rightConv F u₀ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g₀ =
      ∫ y, u₀ (g₀ * y) * (Φ₀ (archEntries F (glArch (𝓞 F) F y)) * rfun Ψ₀ ff y)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
    rw [rightConv_apply, ← e0]
  have hgoal : rightConv F u₀ (ffun Ψ₀ p q ff) g₀ =
      ∫ y, u₀ (g₀ * y) * ((fun y => (p (archEntries F (glArch (𝓞 F) F y)) : ℂ) +
        (q (archEntries F (glArch (𝓞 F) F y)) : ℂ) * Complex.I) y * rfun Ψ₀ ff y)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
    rw [rightConv_apply, ← e1]
  rw [hgoal]
  refine ArchFiniteVector.Poly.integral_ne_zero_of_close (μ := adelicGLHaar (Fin 2) (𝓞 F) F)
    (w := fun y => u₀ (g₀ * y))
    (a := fun y => (p (archEntries F (glArch (𝓞 F) F y)) : ℂ) + (q (archEntries F (glArch (𝓞 F) F y)) : ℂ) *
      Complex.I) (a' := fun y => Φ₀ (archEntries F (glArch (𝓞 F) F y))) (r := rfun Ψ₀ ff) (δ := δ)
    (e1 ▸ hint) (e0 ▸ hint₀) ?_ ?_ ?_
  · simpa only [norm_mul] using hintr.norm
  · intro y hy
    have hΨne : Ψ₀ (archEntries F (glArch (𝓞 F) F y)) ≠ 0 := fun h0 => hy (by simp only [rfun, h0,
      Complex.ofReal_zero, zero_mul])
    exact (hclose _ (hKc _ hΨne)).le
  · have h := hsmall
    rw [hne] at h
    exact h

private theorem rightConv_ffun_sub_le (u₀ : AdelicGL2 (𝓞 F) F → ℂ) (hu₀ : Continuous u₀)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) (hff : IsFinTestFactor F ff)
    (fa₀ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (Φ₀ : E F → ℂ) (hΦ₀ : ∀ z, fa₀ z = Φ₀ (archEntries F z))
    (hfa₀ : IsArchTestFactor F fa₀)
    (Ψ₀ : E F → ℝ) (hΨs : ContDiff ℝ (⊤ : ℕ∞) Ψ₀) (hΨ1 : ∀ z ∈ tsupport fa₀, Ψ₀ (archEntries F z) = 1)
    (hkill : ∀ f : GL (Fin 2) (InfiniteAdeleRing F) → ℂ,
      (∀ y, Ψ₀ (archEntries F y) = 0 → f y = 0) → HasCompactSupport f)
    (Kc : Set (E F)) (hKc : ∀ M, Ψ₀ M ≠ 0 → M ∈ Kc)
    (p q : E F → ℝ) (hp : ContDiff ℝ (⊤ : ℕ∞) p) (hq : ContDiff ℝ (⊤ : ℕ∞) q) (δ : ℝ)
    (hclose : ∀ M ∈ Kc, ‖((p M : ℂ) + (q M : ℂ) * Complex.I) - Φ₀ M‖ < δ)
    (g₀ : AdelicGL2 (𝓞 F) F) :
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
    ‖rightConv F u₀ (ffun Ψ₀ p q ff) g₀ - rightConv F u₀ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g₀‖ ≤
      δ * ∫ y, ‖u₀ (g₀ * y)‖ * ‖rfun Ψ₀ ff y‖ ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  have hΨarch : IsArchTestFactor F
      (fun z => (fun _ : E F => (1 : ℂ)) (archEntries F z) * (Ψ₀ (archEntries F z) : ℂ)) :=
    isArchTestFactor_mul_plateau F Ψ₀ hΨs hkill (fun _ => (1 : ℂ)) contDiff_const
  have hr := continuous_and_hasCompactSupport_tensor F _ hΨarch ff hff
  have hr_eq : (fun g => (fun z => (fun _ : E F => (1 : ℂ)) (archEntries F z) * (Ψ₀ (archEntries F z) : ℂ))
      (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) = rfun Ψ₀ ff := by
    funext g
    simp only [rfun, one_mul]
  rw [hr_eq] at hr
  have hfarch : IsArchTestFactor F (fun z => ((p (archEntries F z) : ℂ) + (q (archEntries F z) : ℂ) *
      Complex.I) * (Ψ₀ (archEntries F z) : ℂ)) :=
    isArchTestFactor_mul_plateau F Ψ₀ hΨs hkill _ (contDiff_pair F hp hq)
  have hf := continuous_and_hasCompactSupport_tensor F _ hfarch ff hff
  rw [← ffun_eq_tensor] at hf
  have hf₀ := continuous_and_hasCompactSupport_tensor F fa₀ hfa₀ ff hff
  have hint := ArchFiniteVector.KFinite.integrable_rightConv_integrand F u₀ hu₀ _ hf.1 hf.2 g₀
  have hint₀ := ArchFiniteVector.KFinite.integrable_rightConv_integrand F u₀ hu₀ _ hf₀.1 hf₀.2 g₀
  have hintr := ArchFiniteVector.KFinite.integrable_rightConv_integrand F u₀ hu₀ _ hr.1 hr.2 g₀
  have e1 : (fun y => u₀ (g₀ * y) * ffun Ψ₀ p q ff y) = fun y => u₀ (g₀ * y) *
      ((fun y => (p (archEntries F (glArch (𝓞 F) F y)) : ℂ) +
        (q (archEntries F (glArch (𝓞 F) F y)) : ℂ) * Complex.I) y * rfun Ψ₀ ff y) := by
    funext y
    simp only [ffun, rfun]
    ring
  have e0 : (fun y => u₀ (g₀ * y) * (fa₀ (glArch (𝓞 F) F y) * ff (glFin (𝓞 F) F y))) = fun y => u₀ (g₀ * y) *
      (Φ₀ (archEntries F (glArch (𝓞 F) F y)) * rfun Ψ₀ ff y) := by
    funext y
    simp only [rfun]
    by_cases h0 : fa₀ (glArch (𝓞 F) F y) = 0
    · rw [h0, ← hΦ₀, h0]
      ring
    · rw [hΨ1 _ (subset_tsupport _ h0), ← hΦ₀]
      push_cast
      ring
  have hne : rightConv F u₀ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g₀ =
      ∫ y, u₀ (g₀ * y) * (Φ₀ (archEntries F (glArch (𝓞 F) F y)) * rfun Ψ₀ ff y)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
    rw [rightConv_apply, ← e0]
  have hgoal : rightConv F u₀ (ffun Ψ₀ p q ff) g₀ =
      ∫ y, u₀ (g₀ * y) * ((fun y => (p (archEntries F (glArch (𝓞 F) F y)) : ℂ) +
        (q (archEntries F (glArch (𝓞 F) F y)) : ℂ) * Complex.I) y * rfun Ψ₀ ff y)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
    rw [rightConv_apply, ← e1]
  show ‖rightConv F u₀ (ffun Ψ₀ p q ff) g₀ -
      rightConv F u₀ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g₀‖ ≤ _
  rw [hgoal, hne]
  refine ArchFiniteVector.Poly.norm_integral_sub_integral_le (μ := adelicGLHaar (Fin 2) (𝓞 F) F)
    (w := fun y => u₀ (g₀ * y))
    (a := fun y => (p (archEntries F (glArch (𝓞 F) F y)) : ℂ) + (q (archEntries F (glArch (𝓞 F) F y)) : ℂ) *
      Complex.I) (a' := fun y => Φ₀ (archEntries F (glArch (𝓞 F) F y))) (r := rfun Ψ₀ ff) (δ := δ)
    (e1 ▸ hint) (e0 ▸ hint₀) ?_ ?_
  · simpa only [norm_mul] using hintr.norm
  · intro y hy
    have hΨne : Ψ₀ (archEntries F (glArch (𝓞 F) F y)) ≠ 0 := fun h0 => hy (by simp only [rfun, h0,
      Complex.ofReal_zero, zero_mul])
    exact (hclose _ (hKc _ hΨne)).le

section BiFinite

private def Rsub (A : E F) : E F →ₗ[ℝ] E F where
  toFun M := fun i j => ∑ l, M i l * A l j
  map_add' M M' := by
    funext i j
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c M := by
    funext i j
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, smul_mul_assoc]

omit [NumberField F] in
private theorem Rsub_apply (A M : E F) (i j : Fin 2) : Rsub F A M i j = ∑ l, M i l * A l j := rfl

omit [NumberField F] in
private theorem archEntries_mul_right (z a : GL (Fin 2) (InfiniteAdeleRing F)) :
    archEntries F (z * a) = Rsub F (archEntries F a) (archEntries F z) := by
  funext i j
  rw [Rsub_apply]
  simp only [archEntries_apply, Units.val_mul, Matrix.mul_apply, map_sum, map_mul]

section FactorTranslate

variable {F}

omit [NumberField F] in
private theorem isRowIsometry_coe {w : InfinitePlace F} (k : rowIsometrySubgroup₀ w.Completion) :
    IsRowIsometry (k : GL (Fin 2) w.Completion) :=
  ((mem_rowIsometrySubgroup₀_iff w.Completion).mp k.2).2

omit [NumberField F] in
private theorem archRowIsometryInclAt₀_eq (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    archRowIsometryInclAt₀ F w k = archGLIncl F w (k : GL (Fin 2) w.Completion) :=
  rfl

private def TfixA (r : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) :
    (E F → ℝ) →ₗ[ℝ] (GL (Fin 2) (InfiniteAdeleRing F) → ℂ) where
  toFun v := fun z => (v (archEntries F z) : ℂ) * r z
  map_add' v v' := by
    funext z
    simp only [Pi.add_apply, Complex.ofReal_add, add_mul]
  map_smul' c v := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply, Complex.real_smul,
      mul_assoc]

omit [NumberField F] in
private theorem TfixA_apply (r : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (v : E F → ℝ)
    (z : GL (Fin 2) (InfiniteAdeleRing F)) : TfixA r v z = (v (archEntries F z) : ℂ) * r z :=
  rfl

omit [NumberField F] in
private theorem TfixA_mem_span (r : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) {n : ℕ} (b : Fin n → E F → ℝ)
    {v : E F → ℝ} (hv : v ∈ Submodule.span ℝ (Set.range b)) :
    TfixA r v ∈ Submodule.span ℂ (Set.range fun i => TfixA r (b i)) := by
  have h1 : TfixA r v ∈ (Submodule.span ℝ (Set.range b)).map (TfixA r) := Submodule.mem_map_of_mem hv
  rw [Submodule.map_span, ← Set.range_comp] at h1
  exact Submodule.span_le_restrictScalars ℝ ℂ _ h1

variable (Ψ₀ p q : E F → ℝ)

private def rA : GL (Fin 2) (InfiniteAdeleRing F) → ℂ := fun z => (Ψ₀ (archEntries F z) : ℂ)

private def afun : GL (Fin 2) (InfiniteAdeleRing F) → ℂ :=
  fun z => ((p (archEntries F z) : ℂ) + (q (archEntries F z) : ℂ) * Complex.I) * (Ψ₀ (archEntries F z) : ℂ)

private theorem ffun_eq_afun (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) :
    ffun Ψ₀ p q ff = fun g => afun Ψ₀ p q (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g) :=
  rfl

private def BA {n m : ℕ} (bp : Fin n → E F → ℝ) (bq : Fin m → E F → ℝ) :
    Fin (n + m) → GL (Fin 2) (InfiniteAdeleRing F) → ℂ :=
  Fin.append (fun i => TfixA (rA Ψ₀) (bp i)) (fun j => TfixA (rA Ψ₀) (bq j))

private def BAinv {n m : ℕ} (bp : Fin n → E F → ℝ) (bq : Fin m → E F → ℝ) :
    Fin (n + m) → GL (Fin 2) (InfiniteAdeleRing F) → ℂ :=
  fun i => fun x => BA Ψ₀ bp bq i x⁻¹

omit [NumberField F] in
private theorem mem_span_BA_of_eq {n m : ℕ} (bp : Fin n → E F → ℝ) (bq : Fin m → E F → ℝ) {vp vq : E F → ℝ}
    (hvp : vp ∈ Submodule.span ℝ (Set.range bp)) (hvq : vq ∈ Submodule.span ℝ (Set.range bq))
    {g : GL (Fin 2) (InfiniteAdeleRing F) → ℂ}
    (hg : ∀ z, g z = TfixA (rA Ψ₀) vp z + Complex.I * TfixA (rA Ψ₀) vq z) :
    g ∈ Submodule.span ℂ (Set.range (BA Ψ₀ bp bq)) := by
  have key : g = TfixA (rA Ψ₀) vp + Complex.I • TfixA (rA Ψ₀) vq := by
    funext z
    rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact hg z
  rw [key]
  have hl : Set.range (fun i => TfixA (rA Ψ₀) (bp i)) ⊆ Set.range (BA Ψ₀ bp bq) := by
    rintro _ ⟨i, rfl⟩
    refine ⟨Fin.castAdd m i, ?_⟩
    unfold BA
    rw [Fin.append_left]
  have hr : Set.range (fun j => TfixA (rA Ψ₀) (bq j)) ⊆ Set.range (BA Ψ₀ bp bq) := by
    rintro _ ⟨j, rfl⟩
    refine ⟨Fin.natAdd n j, ?_⟩
    unfold BA
    rw [Fin.append_right]
  refine add_mem ?_ (Submodule.smul_mem _ _ ?_)
  · exact Submodule.span_mono hl (TfixA_mem_span (rA Ψ₀) bp hvp)
  · exact Submodule.span_mono hr (TfixA_mem_span (rA Ψ₀) bq hvq)

variable (hΨinv : ∀ (w : InfinitePlace F) (k : GL (Fin 2) w.Completion), IsRowIsometry k →
  ∀ y, Ψ₀ (archEntries F (archGLIncl F w k * y)) = Ψ₀ (archEntries F y))
variable (hΨinvR : ∀ (w : InfinitePlace F) (k : GL (Fin 2) w.Completion), IsRowIsometry k →
  ∀ y, Ψ₀ (archEntries F (y * archGLIncl F w k)) = Ψ₀ (archEntries F y))

omit [NumberField F] in
include hΨinv in
private theorem afun_mul_left (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) (hk : IsRowIsometry k)
    (z : GL (Fin 2) (InfiniteAdeleRing F)) :
    afun Ψ₀ p q (archGLIncl F w k * z) =
      TfixA (rA Ψ₀) (p ∘ Lsub F (archEntries F (archGLIncl F w k))) z +
        Complex.I * TfixA (rA Ψ₀) (q ∘ Lsub F (archEntries F (archGLIncl F w k))) z := by
  rw [TfixA_apply, TfixA_apply]
  unfold afun rA
  rw [hΨinv w k hk z, archEntries_mul]
  simp only [Function.comp_apply]
  ring

omit [NumberField F] in
include hΨinvR in
private theorem afun_mul_right (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) (hk : IsRowIsometry k)
    (z : GL (Fin 2) (InfiniteAdeleRing F)) :
    afun Ψ₀ p q (z * archGLIncl F w k) =
      TfixA (rA Ψ₀) (p ∘ Rsub F (archEntries F (archGLIncl F w k))) z +
        Complex.I * TfixA (rA Ψ₀) (q ∘ Rsub F (archEntries F (archGLIncl F w k))) z := by
  rw [TfixA_apply, TfixA_apply]
  unfold afun rA
  rw [hΨinvR w k hk z, archEntries_mul_right]
  simp only [Function.comp_apply]
  ring

omit [NumberField F] in
include hΨinv in
private theorem afun_mul_left_mem_span {n m : ℕ} (bp : Fin n → E F → ℝ) (bq : Fin m → E F → ℝ)
    (hp : ∀ L : E F →ₗ[ℝ] E F, (p ∘ L) ∈ Submodule.span ℝ (Set.range bp))
    (hq : ∀ L : E F →ₗ[ℝ] E F, (q ∘ L) ∈ Submodule.span ℝ (Set.range bq))
    (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    (fun z => afun Ψ₀ p q (archRowIsometryInclAt₀ F w k * z)) ∈ Submodule.span ℂ (Set.range (BA Ψ₀ bp bq)) :=
  mem_span_BA_of_eq Ψ₀ bp bq (hp _) (hq _) fun z => by
    rw [archRowIsometryInclAt₀_eq]
    exact afun_mul_left Ψ₀ p q hΨinv w _ (isRowIsometry_coe k) z

omit [NumberField F] in
include hΨinvR in
private theorem afun_mul_right_mem_span {n m : ℕ} (bp : Fin n → E F → ℝ) (bq : Fin m → E F → ℝ)
    (hp : ∀ L : E F →ₗ[ℝ] E F, (p ∘ L) ∈ Submodule.span ℝ (Set.range bp))
    (hq : ∀ L : E F →ₗ[ℝ] E F, (q ∘ L) ∈ Submodule.span ℝ (Set.range bq))
    (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    (fun z => afun Ψ₀ p q (z * archRowIsometryInclAt₀ F w k)) ∈ Submodule.span ℂ (Set.range (BA Ψ₀ bp bq)) :=
  mem_span_BA_of_eq Ψ₀ bp bq (hp _) (hq _) fun z => by
    rw [archRowIsometryInclAt₀_eq]
    exact afun_mul_right Ψ₀ p q hΨinvR w _ (isRowIsometry_coe k) z

omit [NumberField F] in
include hΨinv in
private theorem afun_inv_mul_mem_span {n m : ℕ} (bp : Fin n → E F → ℝ) (bq : Fin m → E F → ℝ)
    (hp : ∀ L : E F →ₗ[ℝ] E F, (p ∘ L) ∈ Submodule.span ℝ (Set.range bp))
    (hq : ∀ L : E F →ₗ[ℝ] E F, (q ∘ L) ∈ Submodule.span ℝ (Set.range bq))
    (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    (fun x => afun Ψ₀ p q (x * archRowIsometryInclAt₀ F w k)⁻¹) ∈
      Submodule.span ℂ (Set.range (BAinv Ψ₀ bp bq)) := by
  have h := afun_mul_left_mem_span Ψ₀ p q hΨinv bp bq hp hq w k⁻¹
  have e : (fun x => afun Ψ₀ p q (x * archRowIsometryInclAt₀ F w k)⁻¹) =
      fun x => (fun z => afun Ψ₀ p q (archRowIsometryInclAt₀ F w k⁻¹ * z)) x⁻¹ := by
    funext x
    simp only [_root_.mul_inv_rev, map_inv]
  rw [e]
  exact ArchFiniteVector.ArchCut.comp_inv_mem_span (BA Ψ₀ bp bq) h

end FactorTranslate
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.ArchFiniteVector P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.ArchFiniteVector.Poly"

omit [NumberField F] in
private theorem exists_archRepAt_of_translates (w : InfinitePlace F) (u : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (W : Submodule ℂ (GL (Fin 2) (InfiniteAdeleRing F) → ℂ)) [FiniteDimensional ℂ W]
    (hW : ∀ k : rowIsometrySubgroup₀ w.Completion, (fun x => u (x * archRowIsometryInclAt₀ F w k)) ∈ W) :
    ∃ τ : ArchRepAt F w, u ∈ archFactorTypeSubmoduleAt F w τ := by
  obtain ⟨V, hfin, hu, hV⟩ :=
    ArchFiniteVector.ArchCut.exists_stable_of_translates_mem (archRowIsometryInclAt₀ F w) u W hW
  haveI := hfin
  obtain ⟨n, ρ, hmem⟩ := ArchFiniteVector.ArchCut.exists_rep_mem_typeSubmodule (archRowIsometryInclAt₀ F w) V hu hV
  exact ⟨⟨n, ρ⟩, hmem⟩

omit [NumberField F] in
private theorem exists_archRepAt_dual_of_translates (w : InfinitePlace F) (u : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (W : Submodule ℂ (GL (Fin 2) (InfiniteAdeleRing F) → ℂ)) [FiniteDimensional ℂ W]
    (hW : ∀ k : rowIsometrySubgroup₀ w.Completion, (fun x => u (x * archRowIsometryInclAt₀ F w k)) ∈ W) :
    ∃ τ : ArchRepAt F w, u ∈ archFactorDualTypeSubmoduleAt F w τ := by
  obtain ⟨V, hfin, hu, hV⟩ :=
    ArchFiniteVector.ArchCut.exists_stable_of_translates_mem (archRowIsometryInclAt₀ F w) u W hW
  haveI := hfin
  obtain ⟨n, ρ, hmem⟩ :=
    ArchFiniteVector.ArchCut.exists_rep_mem_typeSubmodule_dual (archRowIsometryInclAt₀ F w) V hu hV
  exact ⟨⟨n, ρ⟩, hmem⟩

private def tripleFamily (τ₁ τ₂ τ₃ : ∀ w : InfinitePlace F, ArchRepAt F w) : ArchTypeFamily F where
  card := fun _ => 3
  rep := fun w => ![τ₁ w, τ₂ w, τ₃ w]

omit [NumberField F] in
private theorem mem_archFactorCut_tripleFamily (τ₁ τ₂ τ₃ : ∀ w : InfinitePlace F, ArchRepAt F w)
    {u : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (h : ∀ w, u ∈ archFactorTypeSubmoduleAt F w (τ₁ w)) :
    u ∈ archFactorCutSubmodule F (tripleFamily F τ₁ τ₂ τ₃) :=
  (Submodule.mem_iInf _).mpr fun w => Submodule.mem_iSup_of_mem (0 : Fin 3) (h w)

omit [NumberField F] in
private theorem mem_archFactorDualCut_tripleFamily (τ₁ τ₂ τ₃ : ∀ w : InfinitePlace F, ArchRepAt F w)
    {u : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (h : ∀ w, u ∈ archFactorDualTypeSubmoduleAt F w (τ₂ w)) :
    u ∈ archFactorDualCutSubmodule F (tripleFamily F τ₁ τ₂ τ₃) :=
  (Submodule.mem_iInf _).mpr fun w => Submodule.mem_iSup_of_mem (1 : Fin 3) (h w)

private theorem mem_archCut_tripleFamily (τ₁ τ₂ τ₃ : ∀ w : InfinitePlace F, ArchRepAt F w)
    {v : AdelicGL2 (𝓞 F) F → ℂ} (h : ∀ w, v ∈ archTypeSubmoduleAt F w (τ₃ w)) :
    v ∈ archCutSubmodule F (tripleFamily F τ₁ τ₂ τ₃) :=
  (Submodule.mem_iInf _).mpr fun w => Submodule.mem_iSup_of_mem (2 : Fin 3) (h w)

private theorem exists_archFiniteVector (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (fa₀ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (hfa₀ : IsArchTestFactor F fa₀)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) (hff : IsFinTestFactor F ff) (g₀ : AdelicGL2 (𝓞 F) F)
    (hg₀ : rightConv F φ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g₀ ≠ 0) :
    ∃ (tys : ArchTypeFamily F) (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ),
      IsArchTestFactor F fa ∧ IsArchFactorBiFinite F tys fa ∧
        rightConv F φ (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) ≠ 0 ∧
        rightConv F φ (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) ∈ archCutSubmodule F tys := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  obtain ⟨⟨Φ₀, hΦ₀, hfaΦ⟩, hfa₀c⟩ := id hfa₀
  obtain ⟨Ψ₀, hΨs, hΨ1, hΨinv, hΨinvR, hkill, Kc, hKc, hKcΨ⟩ :=
    ArchFiniteVector.Plateau.exists_plateau F (tsupport fa₀) hfa₀c
  obtain ⟨δ, hδpos, hsmall⟩ : ∃ δ : ℝ, 0 < δ ∧
      δ * (∫ y, ‖φ (g₀ * y)‖ * ‖rfun Ψ₀ ff y‖ ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) <
        ‖rightConv F φ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g₀‖ := by
    set M : ℝ := ∫ y, ‖φ (g₀ * y)‖ * ‖rfun Ψ₀ ff y‖ ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
    set cc : ℝ := ‖rightConv F φ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g₀‖
    have hMnn : 0 ≤ M := integral_nonneg fun y => by positivity
    have hccpos : 0 < cc := norm_pos_iff.mpr hg₀
    have h2 : 0 < 2 * (M + 1) := by linarith
    refine ⟨cc / (2 * (M + 1)), div_pos hccpos h2, ?_⟩
    rw [div_mul_eq_mul_div, div_lt_iff₀ h2]
    nlinarith
  obtain ⟨p, q, hp, hps, hq, hqs, hclose⟩ :=
    ArchFiniteVector.Poly.exists_poly_pair_near (E F) Kc hKc Φ₀ hΦ₀.continuous δ hδpos
  obtain ⟨n, bp, hbp, hpspan⟩ := hps.exists_smooth_span hp
  obtain ⟨m, bq, hbq, hqspan⟩ := hqs.exists_smooth_span hq
  have hfarch : IsArchTestFactor F (afun Ψ₀ p q) :=
    isArchTestFactor_mul_plateau F Ψ₀ hΨs hkill _ (contDiff_pair F hp hq)
  have hune : rightConv F φ (fun g => afun Ψ₀ p q (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) ≠ 0 := fun h0 =>
    rightConv_ffun_ne_zero F φ hφ ff hff fa₀ Φ₀ hfaΦ hfa₀ Ψ₀ hΨs hΨ1 hkill Kc hKcΨ p q hp hq δ hclose g₀ hsmall
      (by rw [ffun_eq_afun Ψ₀ p q ff, h0]; rfl)
  have hfs : ∀ i, Continuous (Fin.append (fun i => Tfix F (rfun Ψ₀ ff) (bp i))
      (fun j => Tfix F (rfun Ψ₀ ff) (bq j)) i) ∧ HasCompactSupport (Fin.append
        (fun i => Tfix F (rfun Ψ₀ ff) (bp i)) (fun j => Tfix F (rfun Ψ₀ ff) (bq j)) i) := by
    have key : ∀ (b : E F → ℝ), ContDiff ℝ (⊤ : ℕ∞) b →
        Continuous (Tfix F (rfun Ψ₀ ff) b) ∧ HasCompactSupport (Tfix F (rfun Ψ₀ ff) b) := by
      intro b hb
      have harch : IsArchTestFactor F (fun z => (fun M => (b M : ℂ)) (archEntries F z) *
          (Ψ₀ (archEntries F z) : ℂ)) :=
        isArchTestFactor_mul_plateau F Ψ₀ hΨs hkill _ (contDiff_ofReal_comp F hb)
      have h := continuous_and_hasCompactSupport_tensor F _ harch ff hff
      have e : (fun g => (fun z => (fun M => (b M : ℂ)) (archEntries F z) * (Ψ₀ (archEntries F z) : ℂ))
          (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) = Tfix F (rfun Ψ₀ ff) b := by
        funext g
        rw [Tfix_apply]
        simp only [rfun]
        ring
      rw [e] at h
      exact h
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · rw [Fin.append_left]
      exact key _ (hbp i)
    · rw [Fin.append_right]
      exact key _ (hbq j)
  have hV : ∀ w : InfinitePlace F, ∃ V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ),
      FiniteDimensional ℂ V ∧ rightConv F φ (ffun Ψ₀ p q ff) ∈ V ∧
        ∀ k : rowIsometrySubgroup₀ w.Completion, ∀ v ∈ V, (fun x => v (x * rowIsometryInclAt₀ F w k)) ∈ V :=
    fun w => ArchFiniteVector.KFinite.exists_finiteDimensional_mem_of_forall_mem_span F (rowIsometryInclAt₀ F w) φ
      hφ _ (fun i => (hfs i).1) (fun i => (hfs i).2) (ffun Ψ₀ p q ff)
      (ffun_translate_mem_span Ψ₀ p q ff hΨinv bp bq hpspan hqspan w)
  have hτ₃ : ∀ w : InfinitePlace F, ∃ τ : ArchRepAt F w,
      rightConv F φ (ffun Ψ₀ p q ff) ∈ archTypeSubmoduleAt F w τ := by
    intro w
    obtain ⟨V, hfin, hu, hstab⟩ := hV w
    haveI := hfin
    obtain ⟨n', ρ, hmem⟩ :=
      ArchFiniteVector.ArchCut.exists_rep_mem_typeSubmodule (rowIsometryInclAt₀ F w) V hu hstab
    exact ⟨⟨n', ρ⟩, hmem⟩
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range (BA Ψ₀ bp bq))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range (BAinv Ψ₀ bp bq))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hτ₂ : ∀ w : InfinitePlace F, ∃ τ : ArchRepAt F w, afun Ψ₀ p q ∈ archFactorDualTypeSubmoduleAt F w τ :=
    fun w => exists_archRepAt_dual_of_translates F w (afun Ψ₀ p q) _
      (fun k => afun_mul_right_mem_span Ψ₀ p q hΨinvR bp bq hpspan hqspan w k)
  have hτ₁ : ∀ w : InfinitePlace F, ∃ τ : ArchRepAt F w,
      (fun x => afun Ψ₀ p q x⁻¹) ∈ archFactorTypeSubmoduleAt F w τ :=
    fun w => exists_archRepAt_of_translates F w (fun x => afun Ψ₀ p q x⁻¹) _
      (fun k => afun_inv_mul_mem_span Ψ₀ p q hΨinv bp bq hpspan hqspan w k)
  choose τ₁ hτ₁ using hτ₁
  choose τ₂ hτ₂ using hτ₂
  choose τ₃ hτ₃ using hτ₃
  refine ⟨tripleFamily F τ₁ τ₂ τ₃, afun Ψ₀ p q, hfarch,
    ⟨mem_archFactorCut_tripleFamily F τ₁ τ₂ τ₃ hτ₁, mem_archFactorDualCut_tripleFamily F τ₁ τ₂ τ₃ hτ₂⟩, hune, ?_⟩
  have h3 := mem_archCut_tripleFamily F τ₁ τ₂ τ₃ hτ₃
  rwa [ffun_eq_afun] at h3

open scoped Pointwise in

private theorem exists_archFiniteVector_uniformOn (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (fa₀ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (hfa₀ : IsArchTestFactor F fa₀)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) (hff : IsFinTestFactor F ff) (g₀ : AdelicGL2 (𝓞 F) F)
    (hg₀ : rightConv F φ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g₀ ≠ 0)
    (C : Set (AdelicGL2 (𝓞 F) F)) (hC : IsCompact C) (η : ℝ) (hη : 0 < η) :
    ∃ (tys : ArchTypeFamily F) (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ),
      IsArchTestFactor F fa ∧ IsArchFactorBiFinite F tys fa ∧
        rightConv F φ (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) ≠ 0 ∧
        rightConv F φ (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) ∈ archCutSubmodule F tys ∧
        ∀ g ∈ C, ‖rightConv F φ (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g -
            rightConv F φ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g‖ ≤ η := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  obtain ⟨⟨Φ₀, hΦ₀, hfaΦ⟩, hfa₀c⟩ := id hfa₀
  obtain ⟨Ψ₀, hΨs, hΨ1, hΨinv, hΨinvR, hkill, Kc, hKc, hKcΨ⟩ :=
    ArchFiniteVector.Plateau.exists_plateau F (tsupport fa₀) hfa₀c

  have hΨarch' : IsArchTestFactor F
      (fun z => (fun _ : E F => (1 : ℂ)) (archEntries F z) * (Ψ₀ (archEntries F z) : ℂ)) :=
    isArchTestFactor_mul_plateau F Ψ₀ hΨs hkill (fun _ => (1 : ℂ)) contDiff_const
  have hr' := continuous_and_hasCompactSupport_tensor F _ hΨarch' ff hff
  have hr_eq' : (fun g => (fun z => (fun _ : E F => (1 : ℂ)) (archEntries F z) * (Ψ₀ (archEntries F z) : ℂ))
      (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) = rfun Ψ₀ ff := by
    funext g
    simp only [rfun, one_mul]
  rw [hr_eq'] at hr'
  obtain ⟨Bφ, hBφ⟩ : ∃ B : ℝ, ∀ z ∈ C * tsupport (rfun Ψ₀ ff), ‖φ z‖ ≤ B :=
    (hC.mul hr'.2).exists_bound_of_continuousOn hφ.continuousOn
  set Bst : ℝ := max Bφ 0 with hBst
  set Ir : ℝ := ∫ y, ‖rfun Ψ₀ ff y‖ ∂(adelicGLHaar (Fin 2) (𝓞 F) F) with hIr
  have hIr0 : 0 ≤ Ir := integral_nonneg fun _ => norm_nonneg _
  have hBI0 : 0 ≤ Bst * Ir := mul_nonneg (le_max_right _ _) hIr0
  have hM_le : ∀ g ∈ C, (∫ y, ‖φ (g * y)‖ * ‖rfun Ψ₀ ff y‖ ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) ≤ Bst * Ir := by
    intro g hg
    have hi1 : Integrable (fun y => ‖φ (g * y)‖ * ‖rfun Ψ₀ ff y‖) (adelicGLHaar (Fin 2) (𝓞 F) F) := by
      simpa only [norm_mul] using
        (ArchFiniteVector.KFinite.integrable_rightConv_integrand F φ hφ _ hr'.1 hr'.2 g).norm
    have hi2 : Integrable (fun y => Bst * ‖rfun Ψ₀ ff y‖) (adelicGLHaar (Fin 2) (𝓞 F) F) :=
      ((hr'.1.norm).integrable_of_hasCompactSupport hr'.2.norm).const_mul Bst
    rw [hIr, ← integral_const_mul]
    refine integral_mono hi1 hi2 fun y => ?_
    by_cases hy : y ∈ tsupport (rfun Ψ₀ ff)
    · exact mul_le_mul_of_nonneg_right ((hBφ _ (Set.mul_mem_mul hg hy)).trans (le_max_left _ _)) (norm_nonneg _)
    · have h0 : rfun Ψ₀ ff y = 0 := by
        by_contra h
        exact hy (subset_tsupport _ h)
      simp only [h0, norm_zero, mul_zero, le_refl]
  obtain ⟨δ₁, hδ₁pos, hsmall₁⟩ : ∃ δ : ℝ, 0 < δ ∧
      δ * (∫ y, ‖φ (g₀ * y)‖ * ‖rfun Ψ₀ ff y‖ ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) <
        ‖rightConv F φ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g₀‖ := by
    set M : ℝ := ∫ y, ‖φ (g₀ * y)‖ * ‖rfun Ψ₀ ff y‖ ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
    set cc : ℝ := ‖rightConv F φ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g₀‖
    have hMnn : 0 ≤ M := integral_nonneg fun y => by positivity
    have hccpos : 0 < cc := norm_pos_iff.mpr hg₀
    have h2 : 0 < 2 * (M + 1) := by linarith
    refine ⟨cc / (2 * (M + 1)), div_pos hccpos h2, ?_⟩
    rw [div_mul_eq_mul_div, div_lt_iff₀ h2]
    nlinarith
  set δ : ℝ := min δ₁ (η / (Bst * Ir + 1)) with hδdef
  have hδpos : 0 < δ := lt_min hδ₁pos (div_pos hη (by linarith))
  have hδle₁ : δ ≤ δ₁ := min_le_left _ _
  have hδle₂ : δ ≤ η / (Bst * Ir + 1) := min_le_right _ _
  have hsmall : δ * (∫ y, ‖φ (g₀ * y)‖ * ‖rfun Ψ₀ ff y‖ ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) <
      ‖rightConv F φ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g₀‖ :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hδle₁ (integral_nonneg fun y => by positivity)) hsmall₁
  obtain ⟨p, q, hp, hps, hq, hqs, hclose⟩ :=
    ArchFiniteVector.Poly.exists_poly_pair_near (E F) Kc hKc Φ₀ hΦ₀.continuous δ hδpos
  obtain ⟨n, bp, hbp, hpspan⟩ := hps.exists_smooth_span hp
  obtain ⟨m, bq, hbq, hqspan⟩ := hqs.exists_smooth_span hq
  have hfarch : IsArchTestFactor F (afun Ψ₀ p q) :=
    isArchTestFactor_mul_plateau F Ψ₀ hΨs hkill _ (contDiff_pair F hp hq)
  have hune : rightConv F φ (fun g => afun Ψ₀ p q (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) ≠ 0 := fun h0 =>
    rightConv_ffun_ne_zero F φ hφ ff hff fa₀ Φ₀ hfaΦ hfa₀ Ψ₀ hΨs hΨ1 hkill Kc hKcΨ p q hp hq δ hclose g₀ hsmall
      (by rw [ffun_eq_afun Ψ₀ p q ff, h0]; rfl)
  have hfs : ∀ i, Continuous (Fin.append (fun i => Tfix F (rfun Ψ₀ ff) (bp i))
      (fun j => Tfix F (rfun Ψ₀ ff) (bq j)) i) ∧ HasCompactSupport (Fin.append
        (fun i => Tfix F (rfun Ψ₀ ff) (bp i)) (fun j => Tfix F (rfun Ψ₀ ff) (bq j)) i) := by
    have key : ∀ (b : E F → ℝ), ContDiff ℝ (⊤ : ℕ∞) b →
        Continuous (Tfix F (rfun Ψ₀ ff) b) ∧ HasCompactSupport (Tfix F (rfun Ψ₀ ff) b) := by
      intro b hb
      have harch : IsArchTestFactor F (fun z => (fun M => (b M : ℂ)) (archEntries F z) *
          (Ψ₀ (archEntries F z) : ℂ)) :=
        isArchTestFactor_mul_plateau F Ψ₀ hΨs hkill _ (contDiff_ofReal_comp F hb)
      have h := continuous_and_hasCompactSupport_tensor F _ harch ff hff
      have e : (fun g => (fun z => (fun M => (b M : ℂ)) (archEntries F z) * (Ψ₀ (archEntries F z) : ℂ))
          (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) = Tfix F (rfun Ψ₀ ff) b := by
        funext g
        rw [Tfix_apply]
        simp only [rfun]
        ring
      rw [e] at h
      exact h
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · rw [Fin.append_left]
      exact key _ (hbp i)
    · rw [Fin.append_right]
      exact key _ (hbq j)
  have hV : ∀ w : InfinitePlace F, ∃ V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ),
      FiniteDimensional ℂ V ∧ rightConv F φ (ffun Ψ₀ p q ff) ∈ V ∧
        ∀ k : rowIsometrySubgroup₀ w.Completion, ∀ v ∈ V, (fun x => v (x * rowIsometryInclAt₀ F w k)) ∈ V :=
    fun w => ArchFiniteVector.KFinite.exists_finiteDimensional_mem_of_forall_mem_span F (rowIsometryInclAt₀ F w) φ
      hφ _ (fun i => (hfs i).1) (fun i => (hfs i).2) (ffun Ψ₀ p q ff)
      (ffun_translate_mem_span Ψ₀ p q ff hΨinv bp bq hpspan hqspan w)
  have hτ₃ : ∀ w : InfinitePlace F, ∃ τ : ArchRepAt F w,
      rightConv F φ (ffun Ψ₀ p q ff) ∈ archTypeSubmoduleAt F w τ := by
    intro w
    obtain ⟨V, hfin, hu, hstab⟩ := hV w
    haveI := hfin
    obtain ⟨n', ρ, hmem⟩ :=
      ArchFiniteVector.ArchCut.exists_rep_mem_typeSubmodule (rowIsometryInclAt₀ F w) V hu hstab
    exact ⟨⟨n', ρ⟩, hmem⟩
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range (BA Ψ₀ bp bq))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range (BAinv Ψ₀ bp bq))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hτ₂ : ∀ w : InfinitePlace F, ∃ τ : ArchRepAt F w, afun Ψ₀ p q ∈ archFactorDualTypeSubmoduleAt F w τ :=
    fun w => exists_archRepAt_dual_of_translates F w (afun Ψ₀ p q) _
      (fun k => afun_mul_right_mem_span Ψ₀ p q hΨinvR bp bq hpspan hqspan w k)
  have hτ₁ : ∀ w : InfinitePlace F, ∃ τ : ArchRepAt F w,
      (fun x => afun Ψ₀ p q x⁻¹) ∈ archFactorTypeSubmoduleAt F w τ :=
    fun w => exists_archRepAt_of_translates F w (fun x => afun Ψ₀ p q x⁻¹) _
      (fun k => afun_inv_mul_mem_span Ψ₀ p q hΨinv bp bq hpspan hqspan w k)
  choose τ₁ hτ₁ using hτ₁
  choose τ₂ hτ₂ using hτ₂
  choose τ₃ hτ₃ using hτ₃
  refine ⟨tripleFamily F τ₁ τ₂ τ₃, afun Ψ₀ p q, hfarch,
    ⟨mem_archFactorCut_tripleFamily F τ₁ τ₂ τ₃ hτ₁, mem_archFactorDualCut_tripleFamily F τ₁ τ₂ τ₃ hτ₂⟩, hune, ?_, ?_⟩
  · have h3 := mem_archCut_tripleFamily F τ₁ τ₂ τ₃ hτ₃
    rwa [ffun_eq_afun] at h3
  · intro g hg
    have hle := rightConv_ffun_sub_le F φ hφ ff hff fa₀ Φ₀ hfaΦ hfa₀ Ψ₀ hΨs hΨ1 hkill Kc hKcΨ p q hp hq δ hclose g
    rw [ffun_eq_afun Ψ₀ p q ff] at hle
    refine hle.trans ?_
    calc δ * (∫ y, ‖φ (g * y)‖ * ‖rfun Ψ₀ ff y‖ ∂(adelicGLHaar (Fin 2) (𝓞 F) F))
        ≤ δ * (Bst * Ir) := mul_le_mul_of_nonneg_left (hM_le g hg) hδpos.le
      _ ≤ η / (Bst * Ir + 1) * (Bst * Ir) := mul_le_mul_of_nonneg_right hδle₂ hBI0
      _ ≤ η := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
          nlinarith

end BiFinite
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.ArchFiniteVector P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.ArchFiniteVector.Poly"

theorem bifin_export (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (fa₀ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (hfa₀ : IsArchTestFactor F fa₀)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) (hff : IsFinTestFactor F ff) (g₀ : AdelicGL2 (𝓞 F) F)
    (hg₀ : rightConv F φ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g₀ ≠ 0)
    (C : Set (AdelicGL2 (𝓞 F) F)) (hC : IsCompact C) (η : ℝ) (hη : 0 < η) :
    ∃ (tys : ArchTypeFamily F) (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ),
      IsArchTestFactor F fa ∧ IsArchFactorBiFinite F tys fa ∧
        rightConv F φ (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) ≠ 0 ∧
        rightConv F φ (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) ∈ archCutSubmodule F tys ∧
        ∀ g ∈ C, ‖rightConv F φ (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g -
            rightConv F φ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g‖ ≤ η :=
  exists_archFiniteVector_uniformOn F φ hφ fa₀ hfa₀ ff hff g₀ hg₀ C hC η hη

end ArchFiniteVector.Assembly
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.ArchFiniteVector P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.ArchFiniteVector.Poly"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.ArchFiniteVector P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.ArchFiniteVector.Poly"

end ModAssembly
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.ArchFiniteVector P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.ArchFiniteVector.Poly"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.ArchFiniteVector P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.ArchFiniteVector.Poly"

open NumberField NumberField.AdelicLevel AutomorphicForm IsDedekindDomain in

theorem solution
    (F : Type) [Field F] [NumberField F]
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (fa₀ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (hfa₀ : IsArchTestFactor F fa₀)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) (hff : IsFinTestFactor F ff) (g₀ : AdelicGL2 (𝓞 F) F)
    (hg₀ : rightConv F φ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g₀ ≠ 0)
    (C : Set (AdelicGL2 (𝓞 F) F)) (hC : IsCompact C) (η : ℝ) (hη : 0 < η) :
    ∃ (tys : ArchTypeFamily F) (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ),
      IsArchTestFactor F fa ∧ IsArchFactorBiFinite F tys fa ∧
        rightConv F φ (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) ≠ 0 ∧
        rightConv F φ (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) ∈ archCutSubmodule F tys ∧
        ∀ g ∈ C, ‖rightConv F φ (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g -
            rightConv F φ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g‖ ≤ η :=
  ArchFiniteVector.Assembly.bifin_export F φ hφ fa₀ hfa₀ ff hff g₀ hg₀ C hC η hη

end S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact
end P2MW
export P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact (solution)
