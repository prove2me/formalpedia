-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FontaineFormalismTensorEquiv
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FontaineFormalismTensorEquiv
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T03:50:10.334193+00:00
-- url     : https://prove2.me/theorems/63c7b2c3-e3ed-4686-9e93-2ffef6161f44
-- title:
--   Fontaine Formalism Tensor Equiv
-- statement:
--   Definitions and structural lemmas for Fontaine Formalism Tensor Equiv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FontaineFormalismTensorEquiv.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorMultiplication
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FontCmp
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct GlobalTheory.IndefiniteRowSideFullHecke
section Generic
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
section Tools
variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
variable (LL) in

def mB (b : B) : V ⊗[Qp] B →ₗ[LL] V ⊗[Qp] B :=
  AlgebraTensorModule.map LinearMap.id (LinearMap.mulLeft Qp b)
@[simp] theorem mB_tmul (b b' : B) (v : V) : mB LL b (v ⊗ₜ[Qp] b') = v ⊗ₜ[Qp] (b * b') := by
  simp [mB]
theorem mulVB_eq (c : K₀) (x : V ⊗[Qp] B) :
    mulVB (K₀ := K₀) (LL := LL) c x = mB LL (algebraMap K₀ B c) x := rfl
theorem mB_add (b b' : B) (x : V ⊗[Qp] B) : mB LL (b + b') x = mB LL b x + mB LL b' x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp [add_mul, tmul_add]
  | add a c ha hc => simp only [map_add, ha, hc]; abel
def mK (ρ : Representation LL G V) (c : K₀) : ↥(Dcris PD ρ) →ₗ[LL] ↥(Dcris PD ρ) :=
  (mB LL (algebraMap K₀ B c)).restrict (fun x hx => by
    rw [CrystallineSubrepresentation.mem_Dcris] at hx ⊢
    intro g
    rw [← mulVB_eq, CrystallineSubrepresentation.actVB_mulVB, hx])
@[simp] theorem coe_mK (ρ : Representation LL G V) (c : K₀) (d : ↥(Dcris PD ρ)) :
    (mK PD ρ c d : V ⊗[Qp] B) = mB LL (algebraMap K₀ B c) d := rfl
variable (LL V) in

def actKK (τ : K₀ →ₐ[Qp] LL) : K₀ ⊗[Qp] K₀ →+ (V ⊗[Qp] B →ₗ[LL] V ⊗[Qp] B) :=
  liftAddHom (AddMonoidHom.mk' (fun a => AddMonoidHom.mk'
      (fun c => τ a • mB LL (algebraMap K₀ B c))
      (fun c c' => by ext x; simp [mB_add, add_mul, tmul_add]))
      (fun a a' => by ext c x; simp [add_smul]))
    (fun r a c => by
      ext v b
      simp only [AddMonoidHom.mk'_apply, map_smul, AlgebraTensorModule.curry_apply,
        LinearMap.restrictScalars_self, curry_apply, LinearMap.coe_restrictScalars,
        LinearMap.smul_apply, mB_tmul]
      rw [smul_assoc, smul_comm r, ← tmul_smul, ← smul_mul_assoc, Algebra.smul_def r c, map_mul,
        ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def])
end Tools
variable (LL : Type) [Field LL] [Algebra Qp LL]
end Generic
variable (l : ℕ) [Fact l.Prime] (P : LocPrime l)
end GlobalTheory.FontCmp


