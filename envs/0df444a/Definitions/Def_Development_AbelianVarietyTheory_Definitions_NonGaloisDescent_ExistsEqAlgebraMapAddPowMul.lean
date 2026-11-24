-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
-- name    : Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T18:38:06.365624+00:00
-- url     : https://prove2.me/theorems/7ccd298d-be63-4d1c-907b-4b29e37f607c
-- title:
--   Exists Eq Algebra Map Add Pow Mul
-- statement:
--   Definitions and structural lemmas for Exists Eq Algebra Map Add Pow Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsEqAlgebraMapAddPowMul.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InstTameDescentExponentDataPadicThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlgebraMapMemNonZeroDivisorsAdicCompletion
import Theorems.Thm_GlobalTheory_BK_Hom_app_mem_Mext
import Theorems.Thm_GlobalTheory_BK_PhiMod_smul_tot_mem_Mext
import Theorems.Thm_GlobalTheory_BK_Rot_invL
import Theorems.Thm_GlobalTheory_BK_coe_Eunit
import Theorems.Thm_GlobalTheory_BK_hat_coe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BK.coe_Eunit
attribute [local simp] GlobalTheory.BK.hat_coe


set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
section Scalars
variable (l e) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]
variable (K) in

def Ezpow (i : ℤ) : K⟦X⟧ := (((isUnit_E (K := K) l e).unit ^ i : K⟦X⟧ˣ) : K⟦X⟧)
omit [IsUltrametricDist K] [CompleteSpace K]
@[simp] theorem Ezpow_natCast (n : ℕ) : Ezpow K l e n = E K l e ^ n := by simp [Ezpow]
end Scalars
section DivE
variable {R : Type} [Semiring R] [Module R (Vec K a ι)] [SMulCommClass R K⟦X⟧ (Vec K a ι)]
variable (l e) in

def divE (n : ℕ) (W : Submodule R (Vec K a ι)) : Submodule R (Vec K a ι) where
  carrier := {y | E K l e ^ n • y ∈ W}
  add_mem' hv hw := by simpa only [Set.mem_ofPred_eq, smul_add] using W.add_mem hv hw
  zero_mem' := by simp
  smul_mem' c y hy := by simpa only [Set.mem_ofPred_eq, smul_comm c] using W.smul_mem c hy
variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
variable (l e) in

def shiftE (i : ℤ) (W : Submodule R (Vec K a ι)) : Submodule R (Vec K a ι) where
  carrier := {y | Ezpow K l e (-i) • y ∈ W}
  add_mem' hv hw := by simpa only [Set.mem_ofPred_eq, smul_add] using W.add_mem hv hw
  zero_mem' := by simp
  smul_mem' c y hy := by simpa only [Set.mem_ofPred_eq, smul_comm c] using W.smul_mem c hy
end DivE
variable (K a ι) in

def mulV (f : K⟦X⟧) : Module.End K (Vec K a ι) where
  toFun v := f • v
  map_add' := smul_add f
  map_smul' c v := smul_comm f c v
omit [IsUltrametricDist K] [Fintype ι] [DecidableEq ι] in
@[simp] theorem mulV_apply (f : K⟦X⟧) (v : Vec K a ι) : mulV K a ι f v = f • v := rfl
namespace PhiMod
variable (P : PhiMod O K l e a ι)
abbrev EM (η : ℕ) : Submodule (A O K) (Vec K a ι) := divE l e η P.M
def Man : Submodule K (Vec K a ι) := (P.Mext (Rpi O K l e)).restrictScalars K
theorem smul_mem_Man {f : K⟦X⟧} (hf : f ∈ Rpi O K l e) {v : Vec K a ι} (hv : v ∈ P.Man) :
    f • v ∈ P.Man := P.smul_tot_mem_Mext (f := fun _ => f) (fun _ => hf) hv
abbrev Pol : Type := Vec K a ι ⧸ P.Man
abbrev cls : Vec K a ι →ₗ[K] P.Pol := P.Man.mkQ
def PolEta (η : ℕ) : Submodule K P.Pol := (divE l e η P.Man).map P.cls
def mulPol (f : Rpi O K l e) : Module.End K P.Pol :=
  P.Man.mapQ P.Man (mulV K a ι f) fun _ => P.smul_mem_Man f.2
@[simp] theorem mulPol_cls (f : Rpi O K l e) (v : Vec K a ι) :
    P.mulPol f (P.cls v) = P.cls ((f : K⟦X⟧) • v) := rfl
def vPol : Module.End K P.Pol := P.mulPol (uIn _ ^ e)
@[simp] theorem vPol_cls (v : Vec K a ι) : P.vPol (P.cls v) = P.cls ((X : K⟦X⟧) ^ e • v) := rfl
variable [Fact l.Prime]
def EN : Module.End K (Vec K a ι) := mulV K a ι (E K l e) * P.conn
def Mon : Vec K a ι →ₗ[K] P.Pol := P.cls ∘ₗ (P.EN - mulV K a ι (E K l e) * P.zeta)
variable [NormedAlgebra ℚ_[l] K] [NeZero e]
def filL (i : ℤ) : Submodule (invL l (A O K)) (Vec K a ι) :=
  (P.ext (invL l (A O K)) ⊓ shiftE l e i (P.Mext (invL l (A O K)))) ⊔
    shiftE l e 1 (P.ext (invL l (A O K)))
def jumps : Set ℤ := {i | P.filL (i + 1) ≠ P.filL i}
variable [CompleteSpace K]
def connHat (w : ZMod a → ι → AhatE O K l e) : ZMod a → ι → AhatE O K l e :=
  fun τ i => NHatE O K l e (w τ i) + ∑ j, w τ j * P.hatTot (P.conn (bas j)) τ i
end PhiMod
namespace Hom
variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
  {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : Hom P Q)
def onPol : P.Pol →ₗ[K] Q.Pol :=
  P.Man.mapQ Q.Man (F.app.restrictScalars K) fun _ => F.app_mem_Mext (A_le_Rpi l e)
omit [NormedAlgebra ℚ_[l] K] [NeZero e]
def imM : Submodule (A O K) (Vec K a κ) := P.M.map (F.app.restrictScalars (A O K))
def imL : Submodule (A O K) (Vec K a κ) := P.L.map (F.app.restrictScalars (A O K))
abbrev coker : Type := Q.M ⧸ F.imM.submoduleOf Q.M
abbrev cokerL : Type := Q.L ⧸ F.imL.submoduleOf Q.L
end Hom
end GlobalTheory.BK


