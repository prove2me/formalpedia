-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LocalTrilinearFormUnique
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LocalTrilinearFormUnique
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T20:42:39.948576+00:00
-- url     : https://prove2.me/theorems/ce9cd219-3c87-4f44-b110-c1f9c8bd95d3
-- title:
--   Local Trilinear Form Unique
-- statement:
--   Definitions and structural lemmas for Local Trilinear Form Unique, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/LocalTrilinearFormUnique.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IndicatorFunctionIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_KernelsCommuteTwistedStatement
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity ValuativeRel IsLocalRing
noncomputable section
namespace GlobalTheory.KernelTri
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
def rmul (g : GL n k) : Matrix m n k ≃ₜ Matrix m n k where
  toFun x := x * g.val
  invFun x := x * (g⁻¹ : GL n k).val
  left_inv x := by simp [Matrix.mul_assoc]
  right_inv x := by simp [Matrix.mul_assoc]
  continuous_toFun := Continuous.matrix_mul continuous_id continuous_const
  continuous_invFun := Continuous.matrix_mul continuous_id continuous_const
def rt (g : GL n k) : SB (Matrix m n k) →ₗ[ℂ] SB (Matrix m n k) where
  toFun Ψ := ⟨fun x => Ψ.1 (x * g.val),
    ⟨Ψ.2.1.comp_continuous (rmul (m := m) g).continuous, Ψ.2.2.comp_homeomorph (rmul (m := m) g)⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
@[simp] theorem rt_apply (g : GL n k) (Ψ : SB (Matrix m n k)) (x : Matrix m n k) :
    (rt g Ψ).1 x = Ψ.1 (x * g.val) := rfl
theorem rt_one (Ψ : SB (Matrix m n k)) : rt (1 : GL n k) Ψ = Ψ := by
  apply Subtype.ext; funext x; simp
theorem rt_rt (a b : GL n k) (Ψ : SB (Matrix m n k)) : rt a (rt b Ψ) = rt (a * b) Ψ := by
  apply Subtype.ext; funext x; simp [Matrix.mul_assoc]
variable {m' : Type} [Fintype m'] [DecidableEq m']
variable {V : Type} [AddCommGroup V] [Module ℂ V]
def Mid (l'' : kˣ →* ℂˣ) (π : Representation ℂ (GL m' k) V) : Submodule ℂ (SB (Matrix m' n k) →ₗ[ℂ] V) where
  carrier := {f | ∀ (h : GL m' k) (Ψ Ψ' : SB (Matrix m' n k)), (∀ x, Ψ'.1 x = Ψ.1 ((h⁻¹ : GL m' k).val * x)) →
    (l'' (Matrix.GeneralLinearGroup.det h) : ℂ) • f Ψ' = π h (f Ψ)}
  add_mem' {a b} ha hb h Ψ Ψ' e := by
    simp only [LinearMap.add_apply, smul_add, map_add, ha h Ψ Ψ' e, hb h Ψ Ψ' e]
  zero_mem' h Ψ Ψ' e := by simp
  smul_mem' c a ha h Ψ Ψ' e := by
    simp only [LinearMap.smul_apply, map_smul]
    rw [smul_comm, ha h Ψ Ψ' e]
theorem rt_mem_Mid (l'' : kˣ →* ℂˣ) (π : Representation ℂ (GL m' k) V) (g : GL n k)
    (f : SB (Matrix m' n k) →ₗ[ℂ] V) (hf : f ∈ Mid l'' π) : f ∘ₗ rt g ∈ Mid l'' π := by
  intro h Ψ Ψ' e
  simp only [LinearMap.comp_apply]
  exact hf h _ _ (fun x => by simp [e, Matrix.mul_assoc])
def piM (l'' : kˣ →* ℂˣ) (π : Representation ℂ (GL m' k) V) : Representation ℂ (GL n k) (Mid (n := n) l'' π) where
  toFun g :=
    { toFun := fun f => ⟨f.1 ∘ₗ rt g⁻¹, rt_mem_Mid l'' π g⁻¹ f.1 f.2⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_one' := by
    ext f Ψ
    simp [rt_one]
  map_mul' a b := by
    ext f Ψ
    simp [rt_rt]
@[simp] theorem piM_apply (l'' : kˣ →* ℂˣ) (π : Representation ℂ (GL m' k) V) (g : GL n k)
    (f : Mid (n := n) l'' π) (Ψ : SB (Matrix m' n k)) : (piM l'' π g f).1 Ψ = f.1 (rt g⁻¹ Ψ) := rfl
end GlobalTheory.KernelTri
noncomputable section
namespace GlobalTheory.KernelTri
def th1 {V' A B V : Type} [AddCommGroup V'] [Module ℂ V'] [AddCommGroup A] [Module ℂ A] [AddCommGroup B]
    [Module ℂ B] [AddCommGroup V] [Module ℂ V] (θ : V' →ₗ[ℂ] A →ₗ[ℂ] B →ₗ[ℂ] V) (p : Submodule ℂ (B →ₗ[ℂ] V))
    (hmem : ∀ v a, θ v a ∈ p) : V' →ₗ[ℂ] A →ₗ[ℂ] p :=
  LinearMap.mk₂ ℂ (fun v a => ⟨θ v a, hmem v a⟩) (fun _ _ _ => by ext; simp) (fun _ _ _ => by ext; simp)
    (fun _ _ _ => by ext; simp) (fun _ _ _ => by ext; simp)
end GlobalTheory.KernelTri


