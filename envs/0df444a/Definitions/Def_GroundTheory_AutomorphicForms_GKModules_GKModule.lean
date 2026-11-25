-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_GKModules_GKModule
-- name    : GroundTheory_AutomorphicForms_GKModules_GKModule
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T00:03:22.839917+00:00
-- url     : https://prove2.me/theorems/8f449505-d020-457c-88b2-d42420b9edc1
-- title:
--   GKModule
-- statement:
--   Definitions and structural lemmas for GKModule, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/GKModule.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_SmoothVectors
import Theorems.Thm_GroundTheory_Automorphic_BanachRep_continuous_orbit
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivEnd_smoothOp
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivOp_map
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.AdL_apply
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.Ad_one
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_Ad
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_bracket
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.derivLie_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a


set_option autoImplicit false
namespace GroundTheory.Automorphic
open NormedSpace Set Filter Topology
open scoped Manifold ContDiff
set_option linter.unusedSectionVars false
attribute [local instance 100] LieRing.ofAssociativeRing
section KHom
variable {K : Type*} [Monoid K]
variable {W : Type*} [AddCommGroup W] [Module ℂ W] {V : Type*} [AddCommGroup V] [Module ℂ V]
def kHom (τ : Representation ℂ K W) (σ : Representation ℂ K V) : Submodule ℂ (W →ₗ[ℂ] V) where
  carrier := {T | ∀ k : K, T ∘ₗ τ k = σ k ∘ₗ T}
  zero_mem' k := by simp
  add_mem' {S T} hS hT k := by
    simp only [mem_setOf_eq] at *
    rw [LinearMap.add_comp, LinearMap.comp_add, hS k, hT k]
  smul_mem' c T hT k := by
    simp only [mem_setOf_eq] at *
    rw [LinearMap.smul_comp, LinearMap.comp_smul, hT k]
end KHom
def Representation.HasContinuousCoeff {K : Type*} [Monoid K] [TopologicalSpace K]
    {W : Type*} [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ K W) : Prop :=
  ∀ (φ : Module.Dual ℂ W) (w : W), Continuous fun k => φ (τ k w)
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
namespace IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
structure GKModule (K : Subgroup G) (V : Type*) [AddCommGroup V] [Module ℂ V] where

  ρ : h.lieSubalgebra →ₗ⁅ℝ⁆ Module.End ℂ V

  σ : Representation ℂ K V

  locallyFinite : ∀ v : V, FiniteDimensional ℂ (Submodule.span ℂ (range fun k : K => σ k v))

  hasContinuousCoeff : Representation.HasContinuousCoeff σ

  hasDerivAt_coeff : ∀ (X : 𝔤) (hX : ∀ t : ℝ, h.expG (t • X) ∈ K) (φ : Module.Dual ℂ V) (v : V),
    HasDerivAt (fun t : ℝ => φ (σ ⟨h.expG (t • X), hX t⟩ v)) (φ (ρ (h.toLie X) v)) 0

  map_ρ : ∀ (k : K) (X : 𝔤) (v : V), σ k (ρ (h.toLie X) v) = ρ (h.toLie (h.Ad k X)) (σ k v)
def GKModule.IsAdmissible {K : Subgroup G} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (M : h.GKModule K V) : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (τ : Representation ℂ K W),
    τ.IsIrreducible → Representation.HasContinuousCoeff τ → FiniteDimensional ℂ (kHom τ M.σ)
end IsExpLieAlgebra
namespace BanachRep
variable {K' : Type*} [Group K'] [TopologicalSpace K']
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
noncomputable def toRepresentation (π : BanachRep K' E) : Representation ℂ K' E where
  toFun k := (π k : E →ₗ[ℂ] E)
  map_one' := by ext v; simp
  map_mul' k k' := by ext v; simp [map_mul_apply]
@[simp] theorem toRepresentation_apply (π : BanachRep K' E) (k : K') (v : E) :
    π.toRepresentation k v = π k v := rfl
noncomputable def restrict (π : BanachRep K' E) (K : Subgroup K') : BanachRep K E where
  toHom := π.toHom.comp K.subtype
  continuous_orbit' v := (π.continuous_orbit v).comp continuous_subtype_val
@[simp] theorem restrict_apply (π : BanachRep K' E) (K : Subgroup K') (k : K) :
    π.restrict K k = π k := rfl
def IsAdmissible (π : BanachRep K' E) (K : Subgroup K') : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (τ : Representation ℂ K W),
    τ.IsIrreducible → Representation.HasContinuousCoeff τ →
      FiniteDimensional ℂ (kHom τ (π.restrict K).toRepresentation)
variable (π : BanachRep K' E) (K : Subgroup K')
def kSpan (v : E) : Submodule ℂ E := Submodule.span ℂ (range fun k : K => π k v)
def IsKFinite (v : E) : Prop := FiniteDimensional ℂ (π.kSpan K v)
theorem mem_kSpan_self (v : E) : v ∈ π.kSpan K v :=
  Submodule.subset_span ⟨1, by simp⟩
theorem map_mem_kSpan (v : E) (k : K) : π k v ∈ π.kSpan K v :=
  Submodule.subset_span ⟨k, rfl⟩
theorem map_mem_kSpan_of_mem {v w : E} (hw : w ∈ π.kSpan K v) (k : K) : π k w ∈ π.kSpan K v := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k', rfl⟩ := hx
    rw [← map_mul_apply]
    exact Submodule.subset_span ⟨k * k', by simp⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
theorem kSpan_le_of_mem {v w : E} (hw : w ∈ π.kSpan K v) : π.kSpan K w ≤ π.kSpan K v := by
  rw [kSpan, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  exact π.map_mem_kSpan_of_mem K hw k
theorem isKFinite_of_mem {v w : E} (hv : π.IsKFinite K v) (hw : w ∈ π.kSpan K v) :
    π.IsKFinite K w :=
  haveI : FiniteDimensional ℂ (π.kSpan K v) := hv
  Submodule.finiteDimensional_of_le (π.kSpan_le_of_mem K hw)
theorem isKFinite_map {v : E} (hv : π.IsKFinite K v) (k : K) : π.IsKFinite K (π k v) :=
  π.isKFinite_of_mem K hv (π.map_mem_kSpan K v k)
def kFiniteVectors : Submodule ℂ E where
  carrier := {v | π.IsKFinite K v}
  zero_mem' := by
    show FiniteDimensional ℂ (π.kSpan K 0)
    have : π.kSpan K 0 = ⊥ := by
      rw [kSpan, Submodule.span_eq_bot]
      rintro _ ⟨k, rfl⟩; simp
    rw [this]; infer_instance
  add_mem' {v w} hv hw := by
    change FiniteDimensional ℂ (π.kSpan K v) at hv
    change FiniteDimensional ℂ (π.kSpan K w) at hw
    show FiniteDimensional ℂ (π.kSpan K (v + w))
    haveI := hv; haveI := hw
    refine Submodule.finiteDimensional_of_le (S₂ := π.kSpan K v ⊔ π.kSpan K w) ?_
    rw [kSpan, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    show π k (v + w) ∈ _
    rw [map_add]
    exact Submodule.add_mem_sup (π.map_mem_kSpan K v k) (π.map_mem_kSpan K w k)
  smul_mem' c v hv := by
    change FiniteDimensional ℂ (π.kSpan K v) at hv
    show FiniteDimensional ℂ (π.kSpan K (c • v))
    haveI := hv
    refine Submodule.finiteDimensional_of_le (S₂ := π.kSpan K v) ?_
    rw [kSpan, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    show π k (c • v) ∈ _
    rw [map_smul]
    exact Submodule.smul_mem _ c (π.map_mem_kSpan K v k)
end BanachRep
namespace IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E) (K : Subgroup G)
noncomputable def derivEndL : 𝔤 →ₗ[ℝ] Module.End ℂ (h.smoothVectors π) where
  toFun X := h.derivEnd π X
  map_add' X Y := by ext v; exact h.derivOp_add_left π _ _ _
  map_smul' r X := by ext v; exact h.derivOp_smul_left π r _ _
theorem isKFinite_derivOp {v : E} (hv : h.IsSmoothVector π v) (hK : π.IsKFinite K v) (X : 𝔤) :
    π.IsKFinite K (h.derivOp π X v) := by
  set M := h.smoothVectors π
  set v' : M := ⟨v, hv⟩
  set S : Submodule ℂ M := Submodule.span ℂ (range fun k : K => h.smoothOp π k v')
  have hSmap : S.map M.subtype = π.kSpan K v := by
    rw [Submodule.map_span, BanachRep.kSpan, ← range_comp]
    rfl
  haveI : FiniteDimensional ℂ (S.map M.subtype) := by rw [hSmap]; exact hK
  haveI : FiniteDimensional ℂ S :=
    (Submodule.equivMapOfInjective M.subtype M.injective_subtype S).symm.finiteDimensional
  let b := Module.finBasis ℝ 𝔤
  set S' : Submodule ℂ M := ⨆ i, S.map (h.derivEnd π (b i))
  have hmem : ∀ (Y : 𝔤) (w : M), w ∈ S → h.derivEnd π Y w ∈ S' := by
    intro Y w hw
    have e : h.derivEnd π Y = ∑ i, b.repr Y i • h.derivEnd π (b i) := by
      conv_lhs => rw [← b.sum_repr Y]
      show h.derivEndL π (∑ i, b.repr Y i • b i) = _
      rw [map_sum]
      simp only [map_smul]
      rfl
    rw [e, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [LinearMap.smul_apply]
    exact Submodule.smul_of_tower_mem _ _
      ((le_iSup (fun i => S.map (h.derivEnd π (b i))) i) (Submodule.mem_map_of_mem hw))
  have hle : π.kSpan K (h.derivOp π X v) ≤ S'.map M.subtype := by
    rw [BanachRep.kSpan, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    have e : h.smoothOp π k (h.derivEnd π X v') = h.derivEnd π (h.Ad k X) (h.smoothOp π k v') :=
      (LinearMap.congr_fun (h.derivEnd_smoothOp π k X) v').symm
    have hk : h.smoothOp π k (h.derivEnd π X v') ∈ S' := by
      rw [e]; exact hmem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    exact ⟨_, hk, rfl⟩
  exact Submodule.finiteDimensional_of_le hle
def gkVectors : Submodule ℂ E := h.smoothVectors π ⊓ π.kFiniteVectors K
theorem map_mem_gkVectors {v : E} (hv : v ∈ h.gkVectors π K) (k : K) :
    π k v ∈ h.gkVectors π K :=
  ⟨h.isSmoothVector_map π hv.1 k, π.isKFinite_map K hv.2 k⟩
theorem derivOp_mem_gkVectors {v : E} (hv : v ∈ h.gkVectors π K) (X : 𝔤) :
    h.derivOp π X v ∈ h.gkVectors π K :=
  ⟨h.isSmoothVector_derivOp π hv.1 X, h.isKFinite_derivOp π K hv.1 hv.2 X⟩
theorem kSpan_le_gkVectors {v : E} (hv : v ∈ h.gkVectors π K) :
    π.kSpan K v ≤ h.gkVectors π K := by
  rw [BanachRep.kSpan, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  exact h.map_mem_gkVectors π K hv k
noncomputable def derivGK (X : 𝔤) : Module.End ℂ (h.gkVectors π K) where
  toFun v := ⟨h.derivOp π X v, h.derivOp_mem_gkVectors π K v.2 X⟩
  map_add' v w := by ext; exact h.derivOp_add π v.2.1 w.2.1 X
  map_smul' c v := by ext; exact h.derivOp_smul π v.2.1 c X
@[simp] theorem coe_derivGK (X : 𝔤) (v : h.gkVectors π K) :
    ((h.derivGK π K X v : h.gkVectors π K) : E) = h.derivOp π X v := rfl
noncomputable def kRepGK : Representation ℂ K (h.gkVectors π K) where
  toFun k :=
    { toFun := fun v => ⟨π k v, h.map_mem_gkVectors π K v.2 k⟩
      map_add' := fun v w => by ext; simp
      map_smul' := fun c v => by ext; simp }
  map_one' := by ext v; simp
  map_mul' k k' := by ext v; simp [BanachRep.map_mul_apply]
@[simp] theorem coe_kRepGK (k : K) (v : h.gkVectors π K) :
    ((h.kRepGK π K k v : h.gkVectors π K) : E) = π k v := rfl
theorem exists_strongDual_eq [CompleteSpace E] (φ : Module.Dual ℂ (h.gkVectors π K))
    (v : h.gkVectors π K) :
    ∃ Φ : E →L[ℂ] ℂ, ∀ (w : E) (hw : w ∈ π.kSpan K v),
      Φ w = φ ⟨w, h.kSpan_le_gkVectors π K v.2 hw⟩ := by
  set W := π.kSpan K (v : E)
  haveI : FiniteDimensional ℂ W := v.2.2
  let ψ : W →ₗ[ℂ] ℂ := φ ∘ₗ Submodule.inclusion (h.kSpan_le_gkVectors π K v.2)
  let ψc : StrongDual ℂ W := ⟨ψ, ψ.continuous_of_finiteDimensional⟩
  obtain ⟨Φ, hΦ, -⟩ := exists_extension_norm_eq W ψc
  exact ⟨Φ, fun w hw => hΦ ⟨w, hw⟩⟩
theorem derivOp_mem_kSpan [CompleteSpace E] {v : E} (hv : h.IsSmoothVector π v)
    (hK : π.IsKFinite K v) (X : 𝔤) (hX : ∀ t : ℝ, h.expG (t • X) ∈ K) :
    h.derivOp π X v ∈ π.kSpan K v := by
  haveI : FiniteDimensional ℂ (π.kSpan K v) := hK
  have hcl : IsClosed (π.kSpan K v : Set E) := Submodule.closed_of_finiteDimensional _
  have hlim := hasDerivAt_iff_tendsto_slope.1 (h.hasDerivAt_derivOp π hv X)
  refine hcl.mem_of_tendsto hlim (Eventually.of_forall fun t => ?_)
  rw [slope_def_module]
  refine Submodule.smul_of_tower_mem _ _ (Submodule.sub_mem _ ?_ ?_)
  · exact π.map_mem_kSpan K v ⟨h.expG (t • X), hX t⟩
  · simp only [zero_smul, expG_zero, BanachRep.map_one_apply]
    exact π.mem_kSpan_self K v
noncomputable def gkModule [CompleteSpace E] : h.GKModule K (h.gkVectors π K) where
  ρ :=
    { toFun := fun X => h.derivGK π K (h.ofLie X)
      map_add' := fun X Y => by ext v; exact h.derivOp_add_left π _ _ _
      map_smul' := fun r X => by ext v; exact h.derivOp_smul_left π r _ _
      map_lie' := fun {X Y} => by
        ext v
        rw [h.ofLie_lie, Ring.lie_def]
        exact h.derivOp_bracket π v.2.1 _ _ }
  σ := h.kRepGK π K
  locallyFinite v := by
    set S := Submodule.span ℂ (range fun k : K => h.kRepGK π K k v)
    have hS : S.map (h.gkVectors π K).subtype = π.kSpan K v := by
      rw [Submodule.map_span, BanachRep.kSpan, ← range_comp]
      rfl
    haveI : FiniteDimensional ℂ (π.kSpan K v) := v.2.2
    haveI : FiniteDimensional ℂ (S.map (h.gkVectors π K).subtype) := by rw [hS]; infer_instance
    exact (Submodule.equivMapOfInjective _ (h.gkVectors π K).injective_subtype S).symm.finiteDimensional
  hasContinuousCoeff φ v := by
    obtain ⟨Φ, hΦ⟩ := h.exists_strongDual_eq π K φ v
    have e : (fun k : K => φ (h.kRepGK π K k v)) = fun k : K => Φ (π k v) := by
      funext k
      rw [hΦ _ (π.map_mem_kSpan K v k)]
      rfl
    rw [e]
    exact Φ.continuous.comp ((π.continuous_orbit v).comp (continuous_subtype_val))
  hasDerivAt_coeff X hX φ v := by
    obtain ⟨Φ, hΦ⟩ := h.exists_strongDual_eq π K φ v
    have hd := (Φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (h.hasDerivAt_derivOp π v.2.1 X)
    have hmem := h.derivOp_mem_kSpan π K v.2.1 v.2.2 X hX
    have e1 : (Φ.restrictScalars ℝ) (h.derivOp π X v) = φ (h.derivGK π K (h.ofLie (h.toLie X)) v) := by
      rw [ContinuousLinearMap.coe_restrictScalars', hΦ _ hmem]
      rfl
    rw [e1] at hd
    refine hd.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars']
    rw [hΦ _ (π.map_mem_kSpan K v ⟨h.expG (t • X), hX t⟩)]
    rfl
  map_ρ k X v := by
    ext
    exact (h.derivOp_map π v.2.1 k X).symm
end IsExpLieAlgebra
end GroundTheory.Automorphic


