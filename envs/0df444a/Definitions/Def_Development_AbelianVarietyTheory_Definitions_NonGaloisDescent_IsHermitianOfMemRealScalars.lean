-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsHermitianOfMemRealScalars
-- name    : Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsHermitianOfMemRealScalars
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:26:21.827534+00:00
-- url     : https://prove2.me/theorems/e3e45f0e-4a98-434e-b180-843a2226e221
-- title:
--   Is Hermitian Of Mem Real Scalars
-- statement:
--   Definitions and structural lemmas for Is Hermitian Of Mem Real Scalars, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Theorems.Thm_GlobalTheory_Tw_Model_Phi_mul_transpose
import Theorems.Thm_GlobalTheory_Tw_Model_transpose_mul_Phi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
namespace GlobalTheory.Tw
section Theta
variable {n : ℕ} {R : Type} [CommRing R] [StarRing R]
def PhiGL (n : ℕ) (R : Type) [CommRing R] : GL (Fin n) R :=
  ⟨Phi n R, (Phi n R)ᵀ, Model.Phi_mul_transpose, Model.transpose_mul_Phi⟩
omit [StarRing R] in
@[simp] theorem PhiGL_val : (PhiGL n R).val = Phi n R := rfl
omit [StarRing R] in
@[simp] theorem PhiGL_inv_val : (PhiGL n R)⁻¹.val = (Phi n R)ᵀ := rfl
def thetaGL (g : GL (Fin n) R) : GL (Fin n) R := PhiGL n R * star g⁻¹ * (PhiGL n R)⁻¹
end Theta
structure PFlag (n : ℕ) (k : Type) [CommRing k] where

  carrier : Set (Submodule k (Fin n → k))
  chain : IsChain (· ≤ ·) carrier
  bot_mem : ⊥ ∈ carrier
  top_mem : ⊤ ∈ carrier
namespace PFlag
section Ring
variable {n : ℕ} {k : Type} [CommRing k] (F : PFlag n k)
def triv (n : ℕ) (k : Type) [CommRing k] : PFlag n k where
  carrier := {⊥, ⊤}
  chain := by
    rintro _ (rfl | rfl) _ (rfl | rfl) _ <;> simp
  bot_mem := by simp
  top_mem := by simp
def single (V : Submodule k (Fin n → k)) : PFlag n k where
  carrier := {⊥, V, ⊤}
  chain := by
    rintro _ (rfl | rfl | rfl) _ (rfl | rfl | rfl) _ <;> simp
  bot_mem := by simp
  top_mem := by simp
def pred (V : Submodule k (Fin n → k)) : Submodule k (Fin n → k) := sSup {V' | V' ∈ F.carrier ∧ V' < V}
theorem le_pred {V V' : Submodule k (Fin n → k)} (h : V' ∈ F.carrier) (hlt : V' < V) : V' ≤ F.pred V :=
  le_sSup ⟨h, hlt⟩
def lieQ : Submodule k (Matrix (Fin n) (Fin n) k) where
  carrier := {X | ∀ V ∈ F.carrier, ∀ v ∈ V, X *ᵥ v ∈ V}
  add_mem' hX hY V hV v hv := by rw [add_mulVec]; exact V.add_mem (hX V hV v hv) (hY V hV v hv)
  zero_mem' V _ v _ := by simp
  smul_mem' c X hX V hV v hv := by rw [smul_mulVec]; exact V.smul_mem c (hX V hV v hv)
def lieN : Submodule k (Matrix (Fin n) (Fin n) k) where
  carrier := {X | ∀ V ∈ F.carrier, ∀ v ∈ V, X *ᵥ v ∈ F.pred V}
  add_mem' hX hY V hV v hv := by rw [add_mulVec]; exact (F.pred V).add_mem (hX V hV v hv) (hY V hV v hv)
  zero_mem' V _ v _ := by simp
  smul_mem' c X hX V hV v hv := by rw [smul_mulVec]; exact (F.pred V).smul_mem c (hX V hV v hv)
variable {F}
theorem one_mem_lieQ : (1 : Matrix (Fin n) (Fin n) k) ∈ F.lieQ := fun V _ v hv => by simpa using hv
theorem mul_mem_lieQ {X Y : Matrix (Fin n) (Fin n) k} (hX : X ∈ F.lieQ) (hY : Y ∈ F.lieQ) : X * Y ∈ F.lieQ :=
  fun V hV v hv => by rw [← mulVec_mulVec]; exact hX V hV _ (hY V hV v hv)
theorem mulVec_mem_pred {X : Matrix (Fin n) (Fin n) k} (hX : X ∈ F.lieQ) (V : Submodule k (Fin n → k)) {v : Fin n → k}
    (hv : v ∈ F.pred V) : X *ᵥ v ∈ F.pred V := by
  have : F.pred V ≤ (F.pred V).comap X.mulVecLin :=
    sSup_le fun V' h w hw => F.le_pred h.1 h.2 (hX V' h.1 w hw)
  exact this hv
theorem lieQ_mul_lieN {X Y : Matrix (Fin n) (Fin n) k} (hX : X ∈ F.lieQ) (hY : Y ∈ F.lieN) : X * Y ∈ F.lieN :=
  fun V hV v hv => by rw [← mulVec_mulVec]; exact mulVec_mem_pred hX V (hY V hV v hv)
theorem lieN_mul_lieQ {X Y : Matrix (Fin n) (Fin n) k} (hX : X ∈ F.lieN) (hY : Y ∈ F.lieQ) : X * Y ∈ F.lieN :=
  fun V hV v hv => by rw [← mulVec_mulVec]; exact hX V hV _ (hY V hV v hv)
variable (F)
def stab : Subgroup (GL (Fin n) k) where
  carrier := {g | g.val ∈ F.lieQ ∧ g⁻¹.val ∈ F.lieQ}
  mul_mem' hg hh := ⟨mul_mem_lieQ hg.1 hh.1, by rw [_root_.mul_inv_rev]; exact mul_mem_lieQ hh.2 hg.2⟩
  one_mem' := ⟨one_mem_lieQ, one_mem_lieQ⟩
  inv_mem' hg := ⟨hg.2, hg.1⟩
def unip : Subgroup (GL (Fin n) k) where
  carrier := {g | g ∈ F.stab ∧ g.val - 1 ∈ F.lieN}
  mul_mem' {g h} hg hh := ⟨mul_mem hg.1 hh.1, by
    have : (g * h).val - 1 = (g.val - 1) * h.val + (h.val - 1) := by rw [Units.val_mul]; noncomm_ring
    rw [this]; exact add_mem (lieN_mul_lieQ hg.2 hh.1.1) hh.2⟩
  one_mem' := ⟨one_mem _, by simp⟩
  inv_mem' {g} hg := ⟨inv_mem hg.1, by
    have : g⁻¹.val - 1 = -(g⁻¹.val * (g.val - 1)) := by rw [mul_sub, Units.inv_mul]; simp
    rw [this]; exact neg_mem (lieQ_mul_lieN hg.1.2 hg.2)⟩
variable {F}
end Ring
section Field
variable {n : ℕ} {k : Type} [Field k] {F : PFlag n k}
end Field
section Complex
variable {n : ℕ} (F : PFlag n ℂ)
end Complex
end PFlag
def perp {n : ℕ} (V : Submodule ℂ (Fin n → ℂ)) : Submodule ℂ (Fin n → ℂ) where
  carrier := {w | ∀ v ∈ V, w ⬝ᵥ star v = 0}
  add_mem' hw hw' v hv := by rw [add_dotProduct, hw v hv, hw' v hv, add_zero]
  zero_mem' v _ := by simp
  smul_mem' c w hw v hv := by rw [smul_dotProduct, hw v hv, smul_zero]
def PFlag.summand {n : ℕ} (F : PFlag n ℂ) (V : Submodule ℂ (Fin n → ℂ)) : Submodule ℂ (Fin n → ℂ) := V ⊓ perp (F.pred V)
section Perp
variable {n : ℕ}
namespace PFlag
variable {F : PFlag n ℂ}
def realScalars (F : PFlag n ℂ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {X | ∀ V ∈ F.carrier, ∃ c : ℝ, ∀ v ∈ F.summand V, X *ᵥ v = c • v}
  add_mem' hX hY V hV := by
    obtain ⟨c, hc⟩ := hX V hV
    obtain ⟨d, hd⟩ := hY V hV
    exact ⟨c + d, fun v hv => by rw [add_mulVec, hc v hv, hd v hv, add_smul]⟩
  zero_mem' V _ := ⟨0, fun v _ => by simp⟩
  smul_mem' r X hX V hV := by
    obtain ⟨c, hc⟩ := hX V hV
    exact ⟨r * c, fun v hv => by rw [smul_mulVec, hc v hv, mul_smul]⟩
end PFlag
end Perp
end GlobalTheory.Tw


