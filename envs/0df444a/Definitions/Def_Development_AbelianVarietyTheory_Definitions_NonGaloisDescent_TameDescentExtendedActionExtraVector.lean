-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TameDescentExtendedActionExtraVector
-- name    : Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TameDescentExtendedActionExtraVector
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T19:58:52.635749+00:00
-- url     : https://prove2.me/theorems/9f140f10-937e-4312-8370-490838cc1b65
-- title:
--   Tame Descent Extended Action Extra Vector
-- statement:
--   Definitions and structural lemmas for Tame Descent Extended Action Extra Vector, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/TameDescentExtendedActionExtraVector.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
import Theorems.Thm_GlobalTheory_BK_Descent_act_E_pow_smul
import Theorems.Thm_GlobalTheory_BK_Descent_act_mem_Mext
import Theorems.Thm_GlobalTheory_BK_Descent_plus_act_join
import Theorems.Thm_GlobalTheory_BK_Hom_app_comp
import Theorems.Thm_GlobalTheory_BK_Hom_app_scalar
import Theorems.Thm_GlobalTheory_BK_Hom_onPol_cls
import Theorems.Thm_GlobalTheory_BK_PhiMod_M_le_Man
import Theorems.Thm_GlobalTheory_BK_PhiMod_cls_eq_zero_iff
import Theorems.Thm_GlobalTheory_BK_PhiMod_mem_M_of_mem_Man
import Theorems.Thm_GlobalTheory_BK_PhiMod_plusInl_app
import Theorems.Thm_GlobalTheory_BK_Rot_invL
import Theorems.Thm_GlobalTheory_BK_coe_Eunit
import Theorems.Thm_GlobalTheory_BK_hat_coe
import Theorems.Thm_GlobalTheory_BK_mem_divE
import Theorems.Thm_GlobalTheory_BK_rot_R
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BK.Hom.onPol_cls
attribute [local simp] GlobalTheory.BK.coe_Eunit
attribute [local simp] GlobalTheory.BK.hat_coe


set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype μ] [DecidableEq μ] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
  [TameDescentExponentData K l e a]
namespace Descent
variable {P : PhiMod O K l e a ι} (Δ : Descent P)
theorem act_mem_Man (g : TameGal K l e a) {v : Vec K a ι} (hv : v ∈ P.Man) : Δ.act g v ∈ P.Man :=
  Δ.act_mem_Mext g (A_le_Rpi l e) (rot_R _) hv
omit [NeZero e] in
theorem act_mem_EM (g : TameGal K l e a) {η : ℕ} {v : Vec K a ι} (hv : v ∈ P.EM η) :
    Δ.act g v ∈ P.EM η := by
  rw [mem_divE, ← act_E_pow_smul]
  exact Δ.act_mem_M g _ hv
def actPol : Representation K (TameGal K l e a) P.Pol :=
  Δ.act.quotient P.Man fun g _ => Δ.act_mem_Man g
@[simp] theorem actPol_cls (g : TameGal K l e a) (v : Vec K a ι) :
    Δ.actPol g (P.cls v) = P.cls (Δ.act g v) := rfl
def invOf {B : Subalgebra O K⟦X⟧} (W : Submodule B (Vec K a ι)) : Submodule O (Vec K a ι) :=
  W.restrictScalars O ⊓ Δ.inv.restrictScalars O
abbrev Minv : Submodule O (Vec K a ι) := Δ.invOf P.M
abbrev Linv : Submodule O (Vec K a ι) := Δ.invOf P.L
abbrev Y (η : ℕ) : Submodule O (Vec K a ι) := Δ.invOf (P.EM η)
def Y' (η : ℕ) : Submodule O (Vec K a ι) := (Δ.Y η).map ((mulV K a ι (X ^ e)).restrictScalars O)
abbrev Yl (η : ℕ) : Submodule O (Vec K a ι) := Δ.invOf (divE l e η (P.Mext (invL l (A O K))))
def Z (η : ℕ) : Submodule O P.Pol :=
  ((P.EM η).restrictScalars O).map (P.cls.restrictScalars O) ⊓ Δ.actPol.invariants.restrictScalars O
def Zl (η : ℕ) : Submodule K P.Pol := P.PolEta η ⊓ Δ.actPol.invariants
def actO : Representation O (TameGal K l e a) (Vec K a ι) where
  toFun g := (Δ.act g).restrictScalars O
  map_one' := LinearMap.ext fun v => by simp
  map_mul' g h := LinearMap.ext fun v => by simp
omit [NeZero e] in
@[simp] theorem actO_apply (g : TameGal K l e a) (v : Vec K a ι) : Δ.actO g v = Δ.act g v := rfl
def actEM (η : ℕ) : Representation O (TameGal K l e a) ((P.EM η).restrictScalars O) :=
  Δ.actO.subrepresentation _ fun g v hv => by
    rw [Submodule.mem_comap, actO_apply]
    exact Δ.act_mem_EM g hv
omit [NeZero e] in
theorem coe_actEM (η : ℕ) (g : TameGal K l e a) (v : (P.EM η).restrictScalars O) :
    (Δ.actEM η g v : Vec K a ι) = Δ.act g v := rfl
def actQuot (η : ℕ) : Representation O (TameGal K l e a)
    ((P.EM η).restrictScalars O ⧸ (P.M.restrictScalars O).submoduleOf ((P.EM η).restrictScalars O)) :=
  (Δ.actEM η).quotient _ fun g v hv => by
    have h : Δ.act g v ∈ P.M := Δ.act_mem_M g _ hv
    rw [← coe_actEM] at h
    exact h
variable (P) in

def quotToPol (η : ℕ) : ((P.EM η).restrictScalars O ⧸
    (P.M.restrictScalars O).submoduleOf ((P.EM η).restrictScalars O)) →ₗ[O] P.Pol :=
  Submodule.liftQ _ (P.cls.restrictScalars O ∘ₗ Submodule.subtype _)
    fun _ hv => P.cls_eq_zero_iff.2 (P.M_le_Man hv)
theorem quotToPol_act (η : ℕ) (g : TameGal K l e a) (w) :
    quotToPol P η (Δ.actQuot η g w) = Δ.actPol g (quotToPol P η w) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rfl
variable [CompleteSpace K]
omit [NeZero a] [TameDescentExponentData K l e a] in
theorem quotToPol_injective (η : ℕ) : Function.Injective (quotToPol P η) :=
  LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _
    fun y hy => P.mem_M_of_mem_Man y.2 (P.cls_eq_zero_iff.1 hy))
theorem map_invariants_actQuot (η : ℕ) :
    (Δ.actQuot η).invariants.map (quotToPol P η) = Δ.Z η := by
  ext w
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨?_, fun g => by rw [← quotToPol_act, hw g]⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    exact ⟨y, y.2, rfl⟩
  · rintro ⟨⟨y, hy, rfl⟩, h⟩
    exact ⟨Submodule.Quotient.mk ⟨y, hy⟩, fun g => quotToPol_injective η
      ((Δ.quotToPol_act η g _).trans (h g)), rfl⟩
def quotInvEquiv (η : ℕ) : (Δ.actQuot η).invariants ≃ₗ[O] Δ.Z η :=
  (Submodule.equivMapOfInjective _ (quotToPol_injective η) _).trans
    (LinearEquiv.ofEq _ _ (Δ.map_invariants_actQuot η))
end Descent
namespace Descent
variable {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {T : PhiMod O K l e a μ}
structure Hom (Δ₁ : Descent P) (Δ₂ : Descent Q) extends BK.Hom P Q where
  app_act : ∀ g v, toHom.app (Δ₁.act g v) = Δ₂.act g (toHom.app v)
namespace Hom
variable {Δ₁ : Descent P} {Δ₂ : Descent Q} {Δ₃ : Descent T} (F : Hom Δ₁ Δ₂)
variable (Δ₁) in

def scalar (c : O) : Hom Δ₁ Δ₁ where
  toHom := BK.Hom.scalar P c
  app_act g v := by
    simp only [BK.Hom.app_scalar, algebraMap_smul]
    exact (map_smul (Δ₁.actO g) c v).symm
def comp (G : Hom Δ₂ Δ₃) (F : Hom Δ₁ Δ₂) : Hom Δ₁ Δ₃ where
  toHom := G.toHom.comp F.toHom
  app_act g v := by rw [BK.Hom.app_comp, BK.Hom.app_comp, F.app_act, G.app_act]
end Hom
variable (Δ : Descent P) {y : Vec K a ι} (hy : y ∈ P.Mext (invE l e (A O K))) (hinv : y ∈ Δ.inv)
def plusInl : Hom Δ (Δ.plus hy hinv) where
  toHom := P.plusInl hy
  app_act g v := by rw [P.plusInl_app, P.plusInl_app, plus_act_join, map_zero]
end Descent
omit [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] in

structure IsExactTriple {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {T : PhiMod O K l e a μ}
    (F : Hom P Q) (G : Hom Q T) : Prop where
  inj : ∀ v ∈ P.M, F.app v = 0 → v = 0
  exact : ∀ v ∈ Q.M, G.app v = 0 ↔ v ∈ F.imM
  finiteLength : IsFiniteLength (A O K) G.coker
namespace PhiMod
omit [NeZero a] [TameDescentExponentData K l e a]
variable (P : PhiMod O K l e a ι)
variable {y : Vec K a ι} (hy : y ∈ P.Mext (invE l e (A O K)))
omit [NormedAlgebra ℚ_[l] K] [NeZero e]
end PhiMod
end GlobalTheory.BK


