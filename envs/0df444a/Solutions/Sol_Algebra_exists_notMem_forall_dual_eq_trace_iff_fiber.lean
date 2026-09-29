-- Prove2me | solution 1 for Algebra.exists_notMem_forall_dual_eq_trace_iff_fiber
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/5ed678ab-8972-5621-8880-2e37e7745dbc

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_exists_notMem_forall_dual_eq_trace_iff_fiber

set_option autoImplicit false

open scoped TensorProduct

namespace L2aDAux

section Generic

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]

@[reducible] def dualModule : Module B (Module.Dual A B) where
  smul b φ := φ ∘ₗ LinearMap.mulLeft A b
  one_smul φ := by
    refine LinearMap.ext fun y => ?_
    change φ (1 * y) = φ y
    rw [one_mul]
  mul_smul b c φ := by
    refine LinearMap.ext fun y => ?_
    change φ (b * c * y) = φ (c * (b * y))
    congr 1
    ring
  smul_zero b := by
    refine LinearMap.ext fun y => ?_
    change (0 : Module.Dual A B) (b * y) = 0
    rfl
  smul_add b φ ψ := by
    refine LinearMap.ext fun y => ?_
    change (φ + ψ) (b * y) = φ (b * y) + ψ (b * y)
    rfl
  add_smul b c φ := by
    refine LinearMap.ext fun y => ?_
    change φ ((b + c) * y) = φ (b * y) + φ (c * y)
    rw [add_mul, map_add]
  zero_smul φ := by
    refine LinearMap.ext fun y => ?_
    change φ (0 * y) = 0
    rw [zero_mul, map_zero]

attribute [local instance] dualModule

theorem smul_dual_apply (b : B) (φ : Module.Dual A B) (y : B) : (b • φ) y = φ (b * y) := rfl

scoped instance : IsScalarTower A B (Module.Dual A B) where
  smul_assoc a b φ := by
    refine LinearMap.ext fun y => ?_
    rw [smul_dual_apply, LinearMap.smul_apply, smul_dual_apply, smul_mul_assoc, map_smul]

noncomputable def theta : B →ₗ[B] Module.Dual A B where
  toFun x := Algebra.traceForm A B x
  map_add' x y := by rw [map_add]
  map_smul' b x := by
    refine LinearMap.ext fun y => ?_
    rw [RingHom.id_apply, smul_dual_apply, Algebra.traceForm_apply, Algebra.traceForm_apply,
      smul_eq_mul]
    congr 1
    ring

theorem theta_apply (x y : B) : theta A B x y = Algebra.trace A B (x * y) := rfl

abbrev Coker : Type _ := Module.Dual A B ⧸ LinearMap.range (theta A B)

scoped instance [Module.Free A B] [Module.Finite A B] : Module.Finite B (Module.Dual A B) :=
  Module.Finite.of_restrictScalars_finite A B (Module.Dual A B)

theorem cond_iff_not_annihilator_le (P : Ideal B) :
    (∃ s ∉ P, ∀ φ : Module.Dual A B, ∃ x : B, ∀ y : B, φ (s * y) = Algebra.trace A B (x * y)) ↔
      ¬ Module.annihilator B (Coker A B) ≤ P := by
  rw [SetLike.not_le_iff_exists]
  refine exists_congr fun s => ?_
  rw [and_comm (a := s ∈ Module.annihilator B (Coker A B))]
  refine and_congr_right fun _ => ?_
  rw [Module.mem_annihilator]
  constructor
  · intro h n
    obtain ⟨φ, rfl⟩ := Submodule.Quotient.mk_surjective _ n
    obtain ⟨x, hx⟩ := h φ
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨x, LinearMap.ext fun y => by rw [theta_apply, smul_dual_apply, hx]⟩
  · intro h φ
    have := h (Submodule.Quotient.mk φ)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this
    obtain ⟨x, hx⟩ := this
    exact ⟨x, fun y => by rw [← theta_apply, hx, smul_dual_apply]⟩

theorem cond_iff_subsingleton [Module.Free A B] [Module.Finite A B] (P : Ideal B) [P.IsPrime] :
    (∃ s ∉ P, ∀ φ : Module.Dual A B, ∃ x : B, ∀ y : B, φ (s * y) = Algebra.trace A B (x * y)) ↔
      Subsingleton (P.ResidueField ⊗[B] Coker A B) := by
  rw [cond_iff_not_annihilator_le, ← not_nontrivial_iff_subsingleton,
    ← Module.mem_support_iff_nontrivial_residueField_tensorProduct (p := ⟨P, inferInstance⟩),
    Module.mem_support_iff_of_finite]

end Generic

section Bridge

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Free A B]
variable (κ : Type*) [CommRing κ] [Algebra A κ]

attribute [local instance] dualModule Algebra.TensorProduct.rightAlgebra

local notation "T" => κ ⊗[A] B
local notation "DB" => Module.Dual A B
local notation "DT" => Module.Dual κ (κ ⊗[A] B)

@[reducible] noncomputable def dualTModuleB : Module B DT := Module.compHom DT (algebraMap B T)

attribute [local instance] dualTModuleB

scoped instance : IsScalarTower B T DT := IsScalarTower.of_algebraMap_smul fun _ _ => rfl

theorem smul_dualT_B (b : B) (ψ : DT) : b • ψ = (algebraMap B T b) • ψ := rfl

theorem ibcB : IsBaseChange κ (TensorProduct.mk A κ B 1) := TensorProduct.isBaseChange A B κ

noncomputable def beta : DB →ₗ[B] DT where
  toFun f := (ibcB A B κ).toDual f
  map_add' f g := by rw [map_add]
  map_smul' b f := by
    refine (ibcB A B κ).algHom_ext _ _ fun v => ?_
    rw [RingHom.id_apply, IsBaseChange.toDual_comp_apply, smul_dual_apply, smul_dualT_B,
      smul_dual_apply]
    change _ = (ibcB A B κ).toDual f ((1 ⊗ₜ[A] b) * (1 ⊗ₜ[A] v))
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact ((ibcB A B κ).toDual_comp_apply f (b * v)).symm

theorem beta_apply (f : DB) : beta A B κ f = (ibcB A B κ).toDual f := rfl

noncomputable def Phi : T ⊗[B] DB →ₗ[T] DT :=
  (TensorProduct.isBaseChange B DB T).lift (beta A B κ)

theorem Phi_tmul (t : T) (f : DB) : Phi A B κ (t ⊗ₜ[B] f) = t • beta A B κ f := by
  have h : Phi A B κ ((TensorProduct.mk B T DB 1) f) = beta A B κ f :=
    (TensorProduct.isBaseChange B DB T).lift_eq (beta A B κ) f
  rw [TensorProduct.mk_apply] at h
  rw [show t ⊗ₜ[B] f = t • ((1 : T) ⊗ₜ[B] f) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
    map_smul, h]

theorem Phi_bijective : Function.Bijective (Phi A B κ) := by
  let G : T ⊗[B] DB ≃ₗ[κ] κ ⊗[A] DB := Algebra.IsPushout.cancelBaseChange A κ B T DB
  let E : κ ⊗[A] DB ≃ₗ[κ] DT := (ibcB A B κ).dual.equiv
  have key : ∀ z, Phi A B κ z = E (G z) := by
    intro z
    obtain ⟨w, rfl⟩ := G.symm.surjective z
    rw [LinearEquiv.apply_symm_apply]
    induction w using TensorProduct.induction_on with
    | zero => rw [G.symm.map_zero, (Phi A B κ).map_zero, E.map_zero]
    | add x y hx hy => rw [G.symm.map_add, (Phi A B κ).map_add, E.map_add, hx, hy]
    | tmul s f =>
      rw [Algebra.IsPushout.cancelBaseChange_symm_tmul, Phi_tmul, IsBaseChange.equiv_tmul,
        beta_apply]
      refine LinearMap.ext fun t => ?_
      rw [smul_dual_apply, LinearMap.smul_apply, ← Algebra.smul_def, map_smul]
  have : (Phi A B κ : T ⊗[B] DB → DT) = E ∘ G := funext key
  rw [this]
  exact E.bijective.comp G.bijective

noncomputable def PhiEquiv : T ⊗[B] DB ≃ₗ[T] DT := LinearEquiv.ofBijective (Phi A B κ) (Phi_bijective A B κ)

end Bridge

section Bridge2

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Free A B]
variable (κ : Type*) [CommRing κ] [Algebra A κ]

attribute [local instance] dualModule Algebra.TensorProduct.rightAlgebra dualTModuleB

local notation "T" => κ ⊗[A] B
local notation "DB" => Module.Dual A B
local notation "DT" => Module.Dual κ (κ ⊗[A] B)

theorem trace_one_tmul (z : B) :
    Algebra.trace κ T ((1 : κ) ⊗ₜ[A] z) = algebraMap A κ (Algebra.trace A B z) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange]
  congr 1
  refine TensorProduct.AlgebraTensorModule.ext fun a b => ?_
  rw [LinearMap.baseChange_tmul]
  change ((1 : κ) ⊗ₜ[A] z) * (a ⊗ₜ[A] b) = a ⊗ₜ[A] (Algebra.lmul A B z) b
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rfl

theorem beta_theta (x : B) : beta A B κ (theta A B x) = theta κ T ((1 : κ) ⊗ₜ[A] x) := by
  refine (ibcB A B κ).algHom_ext _ _ fun v => ?_
  rw [beta_apply, IsBaseChange.toDual_comp_apply, TensorProduct.mk_apply, theta_apply, theta_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, trace_one_tmul]

noncomputable abbrev Q1 : Submodule T (T ⊗[B] DB) :=
  LinearMap.range (TensorProduct.AlgebraTensorModule.lTensor T T
    ((LinearMap.range (theta A B)).subtype.restrictScalars B))

theorem map_Q1 : (Q1 A B κ).map (PhiEquiv A B κ).toLinearMap = LinearMap.range (theta κ T) := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.map_le_iff_le_comap, LinearMap.range_le_iff_comap, Submodule.eq_top_iff']
    intro w
    rw [Submodule.mem_comap, Submodule.mem_comap]
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]; exact Submodule.zero_mem _
    | add x y hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy
    | tmul t d =>
      obtain ⟨_, ⟨x, rfl⟩⟩ := d
      rw [TensorProduct.AlgebraTensorModule.lTensor_tmul]
      change PhiEquiv A B κ (t ⊗ₜ[B] theta A B x) ∈ LinearMap.range (theta κ T)
      rw [show (PhiEquiv A B κ) (t ⊗ₜ[B] theta A B x) = Phi A B κ (t ⊗ₜ[B] theta A B x) from rfl,
        Phi_tmul, beta_theta, ← map_smul]
      exact ⟨_, rfl⟩
  · rintro _ ⟨t, rfl⟩
    refine ⟨t ⊗ₜ[B] theta A B 1, ?_, ?_⟩
    · exact ⟨t ⊗ₜ[B] ⟨theta A B 1, ⟨1, rfl⟩⟩, by
        rw [TensorProduct.AlgebraTensorModule.lTensor_tmul]; rfl⟩
    · change Phi A B κ (t ⊗ₜ[B] theta A B 1) = theta κ T t
      rw [Phi_tmul, beta_theta, ← Algebra.TensorProduct.one_def, ← map_smul, smul_eq_mul, mul_one]

end Bridge2

section Final

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Free A B]
variable (κ : Type*) [CommRing κ] [Algebra A κ]

attribute [local instance] dualModule Algebra.TensorProduct.rightAlgebra dualTModuleB

noncomputable def PhiN : (κ ⊗[A] B) ⊗[B] Coker A B ≃ₗ[κ ⊗[A] B] Coker κ (κ ⊗[A] B) :=
  (TensorProduct.AlgebraTensorModule.tensorQuotientEquiv (κ ⊗[A] B) B (κ ⊗[A] B)
      (LinearMap.range (theta A B))).trans
    (Submodule.Quotient.equiv (Q1 A B κ) (LinearMap.range (theta κ (κ ⊗[A] B))) (PhiEquiv A B κ)
      (map_Q1 A B κ))

end Final

end L2aDAux
p2m_reactivate "P2MW.S_Algebra_exists_notMem_forall_dual_eq_trace_iff_fiber.L2aDAux"

attribute [local instance] L2aDAux.dualModule Algebra.TensorProduct.rightAlgebra L2aDAux.dualTModuleB

open L2aDAux in
theorem solution
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Free A B]
    (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    (P' : Ideal (p.Fiber B)) [P'.IsPrime]
    (hP' : P = P'.comap Algebra.TensorProduct.includeRight.toRingHom) :
    (∃ s ∉ P, ∀ φ : Module.Dual A B, ∃ x : B, ∀ y : B, φ (s * y) = Algebra.trace A B (x * y)) ↔
      (∃ s ∉ P', ∀ φ : Module.Dual p.ResidueField (p.Fiber B), ∃ x : p.Fiber B, ∀ y : p.Fiber B,
        φ (s * y) = Algebra.trace p.ResidueField (p.Fiber B) (x * y)) := by
  rw [cond_iff_subsingleton A B P, cond_iff_subsingleton p.ResidueField (p.Fiber B) P']

  let g : P.ResidueField →ₐ[B] P'.ResidueField :=
    Ideal.ResidueField.mapₐ P P' (Algebra.ofId B (p.Fiber B)) hP'
  letI : Algebra P.ResidueField P'.ResidueField := g.toRingHom.toAlgebra
  haveI : IsScalarTower B P.ResidueField P'.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun b => (g.commutes b).symm
  let e1 : P'.ResidueField ⊗[p.Fiber B] Coker p.ResidueField (p.Fiber B) ≃ₗ[P'.ResidueField]
      P'.ResidueField ⊗[p.Fiber B] ((p.Fiber B) ⊗[B] Coker A B) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl P'.ResidueField P'.ResidueField)
      (PhiN A B p.ResidueField).symm
  let e2 : P'.ResidueField ⊗[p.Fiber B] ((p.Fiber B) ⊗[B] Coker A B) ≃ₗ[P'.ResidueField]
      P'.ResidueField ⊗[B] Coker A B :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange B (p.Fiber B) P'.ResidueField
      P'.ResidueField (Coker A B)
  let e3 : P'.ResidueField ⊗[B] Coker A B ≃ₗ[P'.ResidueField]
      P'.ResidueField ⊗[P.ResidueField] (P.ResidueField ⊗[B] Coker A B) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange B P.ResidueField P'.ResidueField
      P'.ResidueField (Coker A B)).symm
  rw [((e1.trans e2).trans e3).toEquiv.subsingleton_congr,
    Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right P.ResidueField P'.ResidueField]

end S_Algebra_exists_notMem_forall_dual_eq_trace_iff_fiber
end P2MW
export P2MW.S_Algebra_exists_notMem_forall_dual_eq_trace_iff_fiber (solution)
