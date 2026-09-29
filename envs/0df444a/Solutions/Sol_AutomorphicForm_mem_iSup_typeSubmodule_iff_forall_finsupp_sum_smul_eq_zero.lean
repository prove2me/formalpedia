-- Prove2me | solution 1 for AutomorphicForm.mem_iSup_typeSubmodule_iff_forall_finsupp_sum_smul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/365fbffa-0e02-5aaa-ae43-75f283415fd5

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_mem_iSup_typeSubmodule_iff_forall_finsupp_sum_smul_eq_zero

set_option autoImplicit false

p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_mem_iSup_typeSubmodule_iff_forall_finsupp_sum_smul_eq_zero.AutomorphicForm"

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsRightEquivariant typeSubmodule mem_typeSubmodule_of_isRightEquivariant"
namespace TypeAnnAux
p2m_open "AutomorphicForm"

section Coset

variable {H G : Type*} [Group H] [Group G] (ι : H →* G)

noncomputable def rep (x : G) : G := (QuotientGroup.mk x : G ⧸ ι.range).out

theorem rep_mul (x : G) (k : H) : rep ι (x * ι k) = rep ι x := by
  unfold rep
  rw [QuotientGroup.mk_mul_of_mem x (MonoidHom.mem_range.mpr ⟨k, rfl⟩)]

theorem rep_inv_mul_mem (x : G) : (rep ι x)⁻¹ * x ∈ ι.range :=
  QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk x : G ⧸ ι.range))

theorem exists_hpart (x : G) : ∃ h : H, ι h = (rep ι x)⁻¹ * x :=
  MonoidHom.mem_range.mp (rep_inv_mul_mem ι x)

noncomputable def hpart (x : G) : H := (exists_hpart ι x).choose

theorem hpart_spec (x : G) : ι (hpart ι x) = (rep ι x)⁻¹ * x :=
  (exists_hpart ι x).choose_spec

theorem rep_mul_hpart (x : G) : rep ι x * ι (hpart ι x) = x := by
  rw [hpart_spec, mul_inv_cancel_left]

theorem hpart_mul (hι : Function.Injective ι) (x : G) (k : H) :
    hpart ι (x * ι k) = hpart ι x * k := by
  apply hι
  rw [map_mul, hpart_spec, hpart_spec, rep_mul, mul_assoc]

end Coset

theorem linearCombination_mapDomain {α R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (v : α → M) (g : α → α) (L : M →ₗ[R] M) (hv : ∀ a, v (g a) = L (v a)) (l : α →₀ R) :
    Finsupp.linearCombination R v (Finsupp.mapDomain g l) =
      L (Finsupp.linearCombination R v l) := by
  induction l using Finsupp.induction_linear with
  | zero => simp
  | add l₁ l₂ h₁ h₂ => rw [Finsupp.mapDomain_add, map_add, map_add, map_add, h₁, h₂]
  | single a b => rw [Finsupp.mapDomain_single, Finsupp.linearCombination_single,
      Finsupp.linearCombination_single, hv, map_smul]

section Ext

variable {H G : Type*} [Group H] [Group G] (ι : H →* G)
variable {I : Type*} {W : I → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable (ρ : ∀ i, Representation ℂ H (W i)) {J : I → Type*}

def act (k : H) : (∀ i, J i → W i) →ₗ[ℂ] (∀ i, J i → W i) where
  toFun m := fun i j => ρ i k (m i j)
  map_add' m m' := by funext i j; simp
  map_smul' c m := by funext i j; simp

@[scoped simp] theorem act_apply (k : H) (m : ∀ i, J i → W i) (i : I) (j : J i) :
    act ρ (J := J) k m i j = ρ i k (m i j) := rfl

theorem act_mul (k k' : H) (m : ∀ i, J i → W i) :
    act ρ (J := J) (k * k') m = act ρ k (act ρ k' m) := by
  funext i j
  simp [map_mul]

theorem act_single [DecidableEq I] [∀ i, DecidableEq (J i)] (k : H) (i : I) (j : J i) (v : W i) :
    act ρ (J := J) k (Pi.single i (Pi.single j v)) = Pi.single i (Pi.single j (ρ i k v)) := by
  funext i' j'
  rw [act_apply]
  rcases eq_or_ne i' i with rfl | hi
  · rw [Pi.single_eq_same, Pi.single_eq_same]
    rcases eq_or_ne j' j with rfl | hj
    · rw [Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, map_zero]
  · simp [Pi.single_eq_of_ne hi]

private noncomputable def _root_.AutomorphicForm.TypeAnnAux.ext (L : (∀ i, J i → W i) →ₗ[ℂ] (G → ℂ)) :
    (∀ i, J i → W i) →ₗ[ℂ] (G → ℂ) where
  toFun m := fun x => L (act ρ (hpart ι x) m) (rep ι x)
  map_add' m m' := by funext x; simp
  map_smul' c m := by funext x; simp

p2m_export "AutomorphicForm.TypeAnnAux" "ext"
theorem ext_apply (L : (∀ i, J i → W i) →ₗ[ℂ] (G → ℂ)) (m : ∀ i, J i → W i) (x : G) :
    ext ι ρ L m x = L (act ρ (hpart ι x) m) (rep ι x) := rfl

theorem ext_act (hι : Function.Injective ι) (L : (∀ i, J i → W i) →ₗ[ℂ] (G → ℂ))
    (k : H) (m : ∀ i, J i → W i) (x : G) :
    ext ι ρ L (act ρ k m) x = ext ι ρ L m (x * ι k) := by
  rw [ext_apply, ext_apply, ← act_mul, hpart_mul ι hι, rep_mul]

theorem isRightEquivariant_ext_single [DecidableEq I] [∀ i, DecidableEq (J i)]
    (hι : Function.Injective ι) (L : (∀ i, J i → W i) →ₗ[ℂ] (G → ℂ)) (i : I) (j : J i) :
    IsRightEquivariant ι (ρ i)
      (ext ι ρ L ∘ₗ LinearMap.single ℂ (fun i => J i → W i) i ∘ₗ
        LinearMap.single ℂ (fun _ : J i => W i) j) := by
  intro k v x
  simp only [LinearMap.comp_apply, LinearMap.coe_single]
  rw [← act_single ρ k i j v, ext_act ι ρ hι]

theorem ext_mem_iSup [Fintype I] [∀ i, Fintype (J i)] [DecidableEq I] [∀ i, DecidableEq (J i)]
    (hι : Function.Injective ι) (L : (∀ i, J i → W i) →ₗ[ℂ] (G → ℂ)) (m : ∀ i, J i → W i) :
    ext ι ρ L m ∈ ⨆ i, typeSubmodule ι (ρ i) := by
  rw [← Finset.univ_sum_single m, map_sum]
  refine Submodule.sum_mem_iSup fun i => ?_
  have hmi : Pi.single (M := fun i => J i → W i) i (m i) =
      ∑ j, LinearMap.single ℂ (fun i => J i → W i) i
        (LinearMap.single ℂ (fun _ : J i => W i) j (m i j)) := by
    rw [← map_sum, ← LinearMap.coe_single (R := ℂ)]
    congr 1
    simp only [LinearMap.coe_single]
    exact (Finset.univ_sum_single (m i)).symm
  rw [hmi, map_sum]
  exact (typeSubmodule ι (ρ i)).sum_mem fun j _ =>
    mem_typeSubmodule_of_isRightEquivariant (isRightEquivariant_ext_single ι ρ hι L i j) (m i j)

end Ext

section GroupRing

variable {H G : Type*} [Group H] [Group G] (ι : H →* G)
variable {I : Type*} {W : I → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable (ρ : ∀ i, Representation ℂ H (W i)) {J : I → Type*} (b : ∀ i, J i → W i) (f : G → ℂ)

noncomputable def Φ : (H →₀ ℂ) →ₗ[ℂ] (∀ i, J i → W i) :=
  Finsupp.linearCombination ℂ fun k => fun i j => ρ i k (b i j)

noncomputable def Ψ : (H →₀ ℂ) →ₗ[ℂ] (G → ℂ) :=
  Finsupp.linearCombination ℂ fun k => fun x => f (x * ι k)

theorem Φ_apply (a : H →₀ ℂ) (i : I) (j : J i) :
    Φ ρ b a i j = (a.sum fun k c => c • ρ i k) (b i j) := by
  simp only [Φ, Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply,
    LinearMap.sum_apply, LinearMap.smul_apply]

theorem Ψ_apply (a : H →₀ ℂ) :
    Ψ ι f a = fun x => a.sum fun k c => c * f (x * ι k) := by
  funext x
  simp only [Ψ, Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]

theorem Ψ_single_one : Ψ ι f (Finsupp.single 1 1) = f := by
  rw [Ψ, Finsupp.linearCombination_single, one_smul]
  funext x
  rw [map_one, mul_one]

theorem Φ_mapDomain (k : H) (a : H →₀ ℂ) :
    Φ ρ b (Finsupp.mapDomain (k * ·) a) = act ρ k (Φ ρ b a) := by
  unfold Φ
  refine linearCombination_mapDomain _ _ _ (fun k' => ?_) a
  funext i j
  simp [map_mul]

theorem Ψ_mapDomain (k : H) (a : H →₀ ℂ) :
    Ψ ι f (Finsupp.mapDomain (k * ·) a) = LinearMap.funLeft ℂ ℂ (· * ι k) (Ψ ι f a) := by
  unfold Ψ
  refine linearCombination_mapDomain _ _ _ (fun k' => ?_) a
  funext x
  simp [map_mul, mul_assoc]

theorem ext_Φ (L : (∀ i, J i → W i) →ₗ[ℂ] (G → ℂ)) (hL : ∀ a, L (Φ ρ b a) = Ψ ι f a)
    (a : H →₀ ℂ) : ext ι ρ L (Φ ρ b a) = Ψ ι f a := by
  funext x
  rw [ext_apply, ← Φ_mapDomain, hL, Ψ_mapDomain, LinearMap.funLeft_apply, rep_mul_hpart]

theorem ker_Φ_le_ker_Ψ (hb : ∀ i, ∃ B : Module.Basis (J i) ℂ (W i), ⇑B = b i)
    (hann : ∀ a : H →₀ ℂ, (∀ i, (a.sum fun k c => c • (ρ i k)) = 0) →
      (fun x : G => a.sum fun k c => c * f (x * ι k)) = 0) :
    LinearMap.ker (Φ ρ b) ≤ LinearMap.ker (Ψ ι f) := by
  intro a ha
  rw [LinearMap.mem_ker] at ha ⊢
  rw [Ψ_apply]
  refine hann a fun i => ?_
  obtain ⟨B, hB⟩ := hb i
  refine B.ext fun j => ?_
  rw [LinearMap.zero_apply, hB, ← Φ_apply ρ b a i j, ha]
  rfl

theorem exists_factor (hker : LinearMap.ker (Φ ρ b) ≤ LinearMap.ker (Ψ ι f)) :
    ∃ L : (∀ i, J i → W i) →ₗ[ℂ] (G → ℂ), ∀ a, L (Φ ρ b a) = Ψ ι f a := by
  obtain ⟨L, hL⟩ := LinearMap.exists_extend
    ((LinearMap.ker (Φ ρ b)).liftQ (Ψ ι f) hker ∘ₗ (Φ ρ b).quotKerEquivRange.symm.toLinearMap)
  refine ⟨L, fun a => ?_⟩
  have h := congrArg (fun T => T ⟨Φ ρ b a, LinearMap.mem_range_self _ a⟩) hL
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_toLinearMap,
    LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply,
    Submodule.liftQ_apply] at h
  exact h

end GroupRing

end AutomorphicForm.TypeAnnAux
p2m_reactivate "P2MW.S_AutomorphicForm_mem_iSup_typeSubmodule_iff_forall_finsupp_sum_smul_eq_zero.AutomorphicForm P2MW.S_AutomorphicForm_mem_iSup_typeSubmodule_iff_forall_finsupp_sum_smul_eq_zero.AutomorphicForm.TypeAnnAux"
p2m_reactivate "P2MW.S_AutomorphicForm_mem_iSup_typeSubmodule_iff_forall_finsupp_sum_smul_eq_zero.AutomorphicForm"

open AutomorphicForm.TypeAnnAux in
theorem solution
    {H G : Type*} [Group H] [Group G] (ι : H →* G) (hι : Function.Injective ι)
    {I : Type*} [Fintype I] {W : I → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    [∀ i, FiniteDimensional ℂ (W i)]
    (ρ : ∀ i, Representation ℂ H (W i))
    (f : G → ℂ) :
    f ∈ (⨆ i, typeSubmodule ι (ρ i)) ↔
      ∀ a : H →₀ ℂ, (∀ i, (a.sum fun k c => c • (ρ i k)) = 0) →
        (fun x : G => a.sum fun k c => c * f (x * ι k)) = 0 := by
  classical
  constructor
  ·
    intro hf a hann
    suffices h : (⨆ i, typeSubmodule ι (ρ i)) ≤
        LinearMap.ker (Finsupp.linearCombination ℂ (fun k : H =>
          LinearMap.funLeft ℂ ℂ (fun x : G => x * ι k)) a) by
      have := h hf
      rw [LinearMap.mem_ker] at this
      rw [← this]
      funext x
      simp only [Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sum_apply,
        LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, LinearMap.funLeft_apply,
        smul_eq_mul]
    refine iSup_le fun i => Submodule.span_le.mpr ?_
    rintro _ ⟨T, hT, v, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    funext x
    have h1 : (Finsupp.linearCombination ℂ (fun k : H =>
          LinearMap.funLeft ℂ ℂ (fun x : G => x * ι k)) a) (T v) x =
        T ((a.sum fun k c => c • (ρ i k)) v) x := by
      simp only [Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sum_apply,
        LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, LinearMap.funLeft_apply,
        map_sum, map_smul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hT k v x]
    rw [h1, hann i, LinearMap.zero_apply, map_zero]
  ·
    intro hann
    let J : I → Type _ := fun i => Fin (Module.finrank ℂ (W i))
    let b : ∀ i, J i → W i := fun i => ⇑(Module.finBasis ℂ (W i))
    have hb : ∀ i, ∃ B : Module.Basis (J i) ℂ (W i), ⇑B = b i := fun i => ⟨_, rfl⟩
    have hker := ker_Φ_le_ker_Ψ ι ρ b f hb hann
    obtain ⟨L, hL⟩ := exists_factor ι ρ b f hker
    rw [← Ψ_single_one ι f, ← ext_Φ ι ρ b f L hL]
    exact ext_mem_iSup ι ρ hι L _

end S_AutomorphicForm_mem_iSup_typeSubmodule_iff_forall_finsupp_sum_smul_eq_zero
end P2MW
export P2MW.S_AutomorphicForm_mem_iSup_typeSubmodule_iff_forall_finsupp_sum_smul_eq_zero (solution)
