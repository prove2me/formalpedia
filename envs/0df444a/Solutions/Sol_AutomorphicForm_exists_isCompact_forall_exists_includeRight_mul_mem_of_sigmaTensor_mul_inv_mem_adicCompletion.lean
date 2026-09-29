-- Prove2me | solution 1 for AutomorphicForm.exists_isCompact_forall_exists_includeRight_mul_mem_of_sigmaTensor_mul_inv_mem_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/d980b40c-140e-53f1-9ee4-0cbcd4082e83

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_ConstantTerm
import Theorems.Thm_AutomorphicForm_exists_units_mul_sigmaTensor_eq_of_norm_eq_one
import Theorems.Thm_AutomorphicForm_exists_finset_forall_eq_mul_algebraMap_mul_of_sigmaTensor_eq_mul
import Theorems.Thm_AutomorphicForm_exists_isCompact_isOpen_one_mem_mul_mem_norm_eq_one_tensor_adicCompletion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isCompact_forall_exists_includeRight_mul_mem_of_sigmaTensor_mul_inv_mem_adicCompletion

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace H90P

open AutomorphicForm

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
  [IsGalois K L] (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K))

local notation "E" => (L ⊗[K] v.adicCompletion K)
local notation "Kv" => (v.adicCompletion K)
local notation "σE" => AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ

theorem sigmaTensor_tmul (τ : L ≃ₐ[K] L) (l : L) (a : Kv) :
    AutomorphicForm.sigmaTensor K L Kv τ (l ⊗ₜ[K] a) = τ l ⊗ₜ[K] a := by
  show (Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id K Kv)) (l ⊗ₜ[K] a) = τ l ⊗ₜ[K] a
  rw [Algebra.TensorProduct.map_tmul]; rfl

theorem sigmaTensor_mul_apply (τ τ' : L ≃ₐ[K] L) (x : E) :
    AutomorphicForm.sigmaTensor K L Kv (τ * τ') x =
      AutomorphicForm.sigmaTensor K L Kv τ (AutomorphicForm.sigmaTensor K L Kv τ' x) := by
  induction x with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  | tmul l a => rw [sigmaTensor_tmul, sigmaTensor_tmul, sigmaTensor_tmul]; rfl

theorem sigmaTensor_one_apply (x : E) : AutomorphicForm.sigmaTensor K L Kv 1 x = x := by
  induction x with
  | zero => simp
  | add x y hx hy => rw [map_add, hx, hy]
  | tmul l a => rw [sigmaTensor_tmul]; rfl

theorem sigmaTensor_algebraMap (a : Kv) : σE (algebraMap Kv E a) = algebraMap Kv E a := by
  show σE ((1 : L) ⊗ₜ[K] a) = (1 : L) ⊗ₜ[K] a
  rw [sigmaTensor_tmul, map_one]

def sigmaRingEquiv : E ≃+* E where
  toFun := σE
  invFun := AutomorphicForm.sigmaTensor K L Kv σ⁻¹
  left_inv x := by
    show AutomorphicForm.sigmaTensor K L Kv σ⁻¹ (σE x) = x
    rw [← sigmaTensor_mul_apply, inv_mul_cancel, sigmaTensor_one_apply]
  right_inv x := by
    show σE (AutomorphicForm.sigmaTensor K L Kv σ⁻¹ x) = x
    rw [← sigmaTensor_mul_apply, mul_inv_cancel, sigmaTensor_one_apply]
  map_mul' := map_mul σE
  map_add' := map_add σE

def sigmaAlgEquiv : E ≃ₐ[Kv] E :=
  AlgEquiv.ofRingEquiv (f := sigmaRingEquiv K L σ v) (fun a => sigmaTensor_algebraMap K L σ v a)

theorem sigmaAlgEquiv_apply (x : E) : sigmaAlgEquiv K L σ v x = σE x := rfl

theorem norm_sigma (x : E) : Algebra.norm Kv (σE x) = Algebra.norm Kv x := by
  rw [← sigmaAlgEquiv_apply K L σ v x]
  exact Algebra.norm_eq_of_algEquiv (sigmaAlgEquiv K L σ v) x

theorem norm_twist (a : Eˣ) :
    Algebra.norm Kv ((Units.map (σE).toMonoidHom a * a⁻¹ : Eˣ) : E) = 1 := by
  rw [Units.val_mul, map_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, norm_sigma]
  rw [← map_mul, Units.mul_inv, map_one]

theorem continuous_norm_E : Continuous (fun x : E => Algebra.norm Kv x) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L Kv
  let b := Module.Free.chooseBasis Kv E
  have h : (fun x : E => Algebra.norm Kv x) = fun x => (Algebra.leftMulMatrix b x).det := by
    funext x; exact Algebra.norm_eq_matrix_det b x
  rw [h]
  have hc : Continuous (fun x : E => Algebra.leftMulMatrix b x) :=
    IsModuleTopology.continuous_of_linearMap ((Algebra.leftMulMatrix b : E →ₐ[Kv] _).toLinearMap)
  exact hc.matrix_det

end H90P

end

set_option maxHeartbeats 3200000 in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (C : Set (L ⊗[K] v.adicCompletion K)ˣ) (hC : IsCompact C) :
    ∃ C' : Set (L ⊗[K] v.adicCompletion K)ˣ, IsCompact C' ∧
      ∀ a : (L ⊗[K] v.adicCompletion K)ˣ,
        Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ).toMonoidHom a * a⁻¹ ∈ C →
        ∃ p : (v.adicCompletion K)ˣ,
          Units.map ((Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) :
              v.adicCompletion K →* L ⊗[K] v.adicCompletion K) p * a ∈ C'  := by
  classical
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := AutomorphicForm.t2Space_tensor K L (v.adicCompletion K)

  obtain ⟨G₀, hG₀c, hG₀o, hG₀1, hG₀m, hG₀i, -⟩ :=
    AutomorphicForm.exists_isCompact_isOpen_one_mem_mul_mem_norm_eq_one_tensor_adicCompletion K L v
  obtain ⟨Fs, hFsU, hFs⟩ :=
    AutomorphicForm.exists_finset_forall_eq_mul_algebraMap_mul_of_sigmaTensor_eq_mul K L σ hgen v G₀ hG₀c hG₀o hG₀1 hG₀m hG₀i

  let q : (L ⊗[K] v.adicCompletion K)ˣ → (L ⊗[K] v.adicCompletion K)ˣ := fun a => Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ).toMonoidHom a * a⁻¹
  have hqE : ∀ a : (L ⊗[K] v.adicCompletion K)ˣ, ((q a : (L ⊗[K] v.adicCompletion K)ˣ) : (L ⊗[K] v.adicCompletion K)) = AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ a * ((a⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : (L ⊗[K] v.adicCompletion K)) := fun a => rfl

  have h90 : ∀ u : (L ⊗[K] v.adicCompletion K)ˣ, Algebra.norm (v.adicCompletion K) (u : (L ⊗[K] v.adicCompletion K)) = 1 → ∃ c : (L ⊗[K] v.adicCompletion K)ˣ, q c = u := by
    intro u hu
    have hu' : Algebra.norm (v.adicCompletion K) ((u⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : (L ⊗[K] v.adicCompletion K)) = 1 := by
      have := congrArg (Algebra.norm (v.adicCompletion K)) (show (u : (L ⊗[K] v.adicCompletion K)) * ((u⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : (L ⊗[K] v.adicCompletion K)) = 1 from by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
      rw [map_mul, hu, one_mul, map_one] at this
      exact this
    obtain ⟨y, hy⟩ := AutomorphicForm.exists_units_mul_sigmaTensor_eq_of_norm_eq_one K L σ hgen v _ hu'
    refine ⟨y, Units.ext ?_⟩
    rw [hqE]

    have : AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ (y : (L ⊗[K] v.adicCompletion K)) = (u : (L ⊗[K] v.adicCompletion K)) * (y : (L ⊗[K] v.adicCompletion K)) := by
      have := congrArg (fun z => (u : (L ⊗[K] v.adicCompletion K)) * z) hy
      simpa [← mul_assoc] using this
    rw [this, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

  let V : (L ⊗[K] v.adicCompletion K)ˣ → Set (L ⊗[K] v.adicCompletion K)ˣ := fun u =>
    if Algebra.norm (v.adicCompletion K) (u : (L ⊗[K] v.adicCompletion K)) = 1 then {w | (w : (L ⊗[K] v.adicCompletion K)) * ((u⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : (L ⊗[K] v.adicCompletion K)) ∈ G₀}
    else {w | Algebra.norm (v.adicCompletion K) (w : (L ⊗[K] v.adicCompletion K)) ≠ 1}
  have hV : ∀ u ∈ C, V u ∈ nhds u := by
    intro u _
    by_cases hu : Algebra.norm (v.adicCompletion K) (u : (L ⊗[K] v.adicCompletion K)) = 1
    · simp only [V, hu, if_true]
      refine ((hG₀o.preimage (Units.continuous_val.mul continuous_const))).mem_nhds ?_
      show (u : (L ⊗[K] v.adicCompletion K)) * ((u⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : (L ⊗[K] v.adicCompletion K)) ∈ G₀
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]; exact hG₀1
    · simp only [V, hu, if_false]
      exact ((isOpen_ne.preimage ((H90P.continuous_norm_E K L v).comp Units.continuous_val))).mem_nhds hu
  obtain ⟨tC, htC, hcov⟩ := hC.elim_nhds_subcover V hV

  have hrep : ∀ u : (L ⊗[K] v.adicCompletion K)ˣ, ∃ c : (L ⊗[K] v.adicCompletion K)ˣ, Algebra.norm (v.adicCompletion K) (u : (L ⊗[K] v.adicCompletion K)) = 1 → q c = u := by
    intro u
    by_cases hu : Algebra.norm (v.adicCompletion K) (u : (L ⊗[K] v.adicCompletion K)) = 1
    · obtain ⟨c, hc⟩ := h90 u hu; exact ⟨c, fun _ => hc⟩
    · exact ⟨1, fun h => absurd h hu⟩
  choose cu hcu using hrep

  let G₀U : Set (L ⊗[K] v.adicCompletion K)ˣ := {g | (g : (L ⊗[K] v.adicCompletion K)) ∈ G₀ ∧ ((g⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : (L ⊗[K] v.adicCompletion K)) ∈ G₀}
  have hG₀Uc : IsCompact G₀U := by
    have hce : Topology.IsClosedEmbedding (Units.embedProduct (L ⊗[K] v.adicCompletion K)) := Units.isClosedEmbedding_embedProduct
    have : G₀U = Units.embedProduct (L ⊗[K] v.adicCompletion K) ⁻¹' (G₀ ×ˢ (MulOpposite.op '' G₀)) := by
      ext g
      simp only [G₀U, Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod, Set.mem_image,
        MulOpposite.op_inj, exists_eq_right]
    rw [this]
    exact hce.isCompact_preimage (hG₀c.prod (hG₀c.image MulOpposite.continuous_op))

  let fU : (L ⊗[K] v.adicCompletion K) → (L ⊗[K] v.adicCompletion K)ˣ := fun f => if h : IsUnit f then h.unit else 1
  have hfU : ∀ f ∈ Fs, ((fU f : (L ⊗[K] v.adicCompletion K)ˣ) : (L ⊗[K] v.adicCompletion K)) = f := fun f hf => by simp only [fU, dif_pos (hFsU f hf), IsUnit.unit_spec]

  let C' : Set (L ⊗[K] v.adicCompletion K)ˣ := ⋃ u ∈ tC, ⋃ f ∈ Fs, (fun g : (L ⊗[K] v.adicCompletion K)ˣ => fU f * g * cu u) '' G₀U
  have hC'c : IsCompact C' := by
    refine tC.finite_toSet.isCompact_biUnion fun u _ => Fs.finite_toSet.isCompact_biUnion fun f _ => ?_
    exact hG₀Uc.image ((continuous_const.mul continuous_id).mul continuous_const)
  refine ⟨C', hC'c, fun a ha => ?_⟩

  obtain ⟨u, huT, hau⟩ : ∃ u ∈ tC, q a ∈ V u := by simpa only [Set.mem_iUnion, exists_prop] using hcov ha
  have hNu : Algebra.norm (v.adicCompletion K) (u : (L ⊗[K] v.adicCompletion K)) = 1 := by
    by_contra hNu
    simp only [V, hNu, if_false, Set.mem_setOf_eq] at hau
    exact hau (H90P.norm_twist K L σ v a)
  simp only [V, hNu, if_true, Set.mem_setOf_eq] at hau

  have hquu : q (cu u) = u := hcu u hNu
  let σU : (L ⊗[K] v.adicCompletion K)ˣ →* (L ⊗[K] v.adicCompletion K)ˣ := Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ).toMonoidHom
  have hq : ∀ b : (L ⊗[K] v.adicCompletion K)ˣ, q b = σU b * b⁻¹ := fun b => rfl
  have e1U : σU a = q a * a := by rw [hq, inv_mul_cancel_right]
  have e2U : σU (cu u) = u * cu u := by
    have h := hq (cu u)
    rw [hquu] at h
    exact (eq_mul_inv_iff_mul_eq.mp h).symm
  set c : (L ⊗[K] v.adicCompletion K)ˣ := a * (cu u)⁻¹ with hc
  have hcU : σU c = c * (q a * u⁻¹) := by
    rw [hc, map_mul, map_inv, e1U, e2U, mul_inv_rev]
    apply Units.ext
    simp only [Units.val_mul]
    ring
  have hσc : AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ (c : (L ⊗[K] v.adicCompletion K)) = (c : (L ⊗[K] v.adicCompletion K)) * (((q a) : (L ⊗[K] v.adicCompletion K)) * ((u⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : (L ⊗[K] v.adicCompletion K))) := by
    have h := congrArg Units.val hcU
    simpa only [σU, Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] using h
  obtain ⟨f, hfF, x, hx, g, hgG, hcfg⟩ := hFs (c : (L ⊗[K] v.adicCompletion K)) c.isUnit ⟨_, hau, hσc⟩

  refine ⟨(Units.mk0 x hx)⁻¹, ?_⟩

  obtain ⟨h, hhG, hgh⟩ := hG₀i g hgG
  let gU : (L ⊗[K] v.adicCompletion K)ˣ := ⟨g, h, hgh, by rw [mul_comm]; exact hgh⟩
  have hgU : gU ∈ G₀U := ⟨hgG, hhG⟩
  refine Set.mem_iUnion₂.2 ⟨u, huT, Set.mem_iUnion₂.2 ⟨f, hfF, ⟨gU, hgU, ?_⟩⟩⟩

  apply Units.ext
  have hι : ((Units.map ((Algebra.TensorProduct.includeRight : (v.adicCompletion K) →ₐ[K] (L ⊗[K] v.adicCompletion K)) : (v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K)) (Units.mk0 x hx)⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : (L ⊗[K] v.adicCompletion K)) =
      algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) x⁻¹ := by
    rw [Units.coe_map, MonoidHom.coe_coe, Units.val_inv_eq_inv_val, Units.val_mk0]
    rfl
  rw [Units.val_mul, Units.val_mul, hfU f hfF, Units.val_mul, hι]
  show f * g * ((cu u : (L ⊗[K] v.adicCompletion K)ˣ) : (L ⊗[K] v.adicCompletion K)) = algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) x⁻¹ * (a : (L ⊗[K] v.adicCompletion K))
  have ha' : (a : (L ⊗[K] v.adicCompletion K)) = (c : (L ⊗[K] v.adicCompletion K)) * ((cu u : (L ⊗[K] v.adicCompletion K)ˣ) : (L ⊗[K] v.adicCompletion K)) := by
    rw [hc, Units.val_mul, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  rw [ha', hcfg]
  calc f * g * ((cu u : (L ⊗[K] v.adicCompletion K)ˣ) : (L ⊗[K] v.adicCompletion K))
      = algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) (x⁻¹ * x) * (f * g * ((cu u : (L ⊗[K] v.adicCompletion K)ˣ) : (L ⊗[K] v.adicCompletion K))) := by
        rw [inv_mul_cancel₀ hx, map_one, one_mul]
    _ = algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) x⁻¹ * (f * algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) x * g * ((cu u : (L ⊗[K] v.adicCompletion K)ˣ) : (L ⊗[K] v.adicCompletion K))) := by
        rw [map_mul]; ring

end S_AutomorphicForm_exists_isCompact_forall_exists_includeRight_mul_mem_of_sigmaTensor_mul_inv_mem_adicCompletion
end P2MW
export P2MW.S_AutomorphicForm_exists_isCompact_forall_exists_includeRight_mul_mem_of_sigmaTensor_mul_inv_mem_adicCompletion (solution)
