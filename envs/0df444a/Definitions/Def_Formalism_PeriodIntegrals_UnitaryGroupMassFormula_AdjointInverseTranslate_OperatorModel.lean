-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OperatorModel
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OperatorModel
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T18:16:49.440495+00:00
-- url     : https://prove2.me/theorems/63d85022-b989-48a1-a703-8d49bc236582
-- title:
--   Operator Model
-- statement:
--   Definitions and structural lemmas for Operator Model, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/OperatorModel.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OpModel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_Imports
import Theorems.Thm_AAInvW_ana_mul
import Theorems.Thm_AAInvW_eab_h_linear
import Theorems.Thm_AAInvW_eab_h_local
import Theorems.Thm_AAInvW_eab_h_smooth
import Theorems.Thm_AAInvW_smooth_local
import Theorems.Thm_P2M_AAInvW_smooth_linear__4ce59117e344
import Theorems.Thm_P2M_AAInvW_smooth_right__23e71241d98e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
namespace AAInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3
open scoped Classical
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section Model
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ}
def mExt (φ : {x : Matrix (Fin n) (Fin n) ℂ // inUH H x} → E) : Matrix (Fin n) (Fin n) ℂ → E :=
  fun x => if h : inUH H x then φ ⟨x, h⟩ else 0
lemma mExt_pos {φ : {x : Matrix (Fin n) (Fin n) ℂ // inUH H x} → E} {x : Matrix (Fin n) (Fin n) ℂ}
    (hx : inUH H x) : mExt φ x = φ ⟨x, hx⟩ := by
  unfold mExt
  rw [dif_pos hx]
lemma m_smooth_zero : SmoothOnH H (fun _ : Matrix (Fin n) (Fin n) ℂ => (0 : E)) := by
  unfold SmoothOnH
  intro g₀ _
  exact ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩
lemma m_eabH_zero (a b : Fin n) (x : Matrix (Fin n) (Fin n) ℂ) :
    EabH H a b (fun _ : Matrix (Fin n) (Fin n) ℂ => (0 : E)) x = 0 := by
  simp [EabH, RdV]
def mSub {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] : Submodule ℂ ({x : Matrix (Fin n) (Fin n) ℂ // inUH H x} → E) where
  carrier := {φ | SmoothOnH H (mExt φ)}
  zero_mem' := smooth_local n H E (fun _ => 0) _ (fun x hx => by rw [mExt_pos hx]; rfl) m_smooth_zero
  add_mem' := by
    intro φ ψ hφ hψ
    exact smooth_local n H E _ _ (fun x hx => by
      rw [mExt_pos hx, mExt_pos hx, mExt_pos hx, one_smul]; rfl) (smooth_linear' n H E _ _ 1 hφ hψ)
  smul_mem' := by
    intro c φ hφ
    exact smooth_local n H E _ _ (fun x hx => by
      rw [mExt_pos hx, mExt_pos hx, zero_add]; rfl) (smooth_linear' n H E _ _ c m_smooth_zero hφ)
def mCls (f : Matrix (Fin n) (Fin n) ℂ → E) : mSub H E :=
  if hf : SmoothOnH H f then
    ⟨fun x => f x.1, smooth_local n H E f _ (fun _ hx => (mExt_pos (φ := fun x => f x.1) hx).symm) hf⟩
  else 0
def mE (hH : HInvol H) (a b : Fin n) : Module.End ℂ (mSub H E) where
  toFun φ := ⟨fun x => EabH H a b (mExt φ.1) x.1,
    smooth_local n H E (EabH H a b (mExt φ.1)) _
      (fun x hx => (mExt_pos (φ := fun x => EabH H a b (mExt φ.1) x.1) hx).symm)
      (eab_h_smooth n H E _ a b hH φ.2)⟩
  map_add' φ ψ := by
    apply Subtype.ext; funext x
    show EabH H a b (mExt (φ.1 + ψ.1)) x.1 = EabH H a b (mExt φ.1) x.1 + EabH H a b (mExt ψ.1) x.1
    rw [eab_h_local n H E (mExt (φ.1 + ψ.1)) (fun y => mExt φ.1 y + (1 : ℂ) • mExt ψ.1 y) a b x.1 hH
      (fun y hy => by rw [mExt_pos hy, mExt_pos hy, mExt_pos hy, one_smul]; rfl) x.2,
      eab_h_linear n H E _ _ 1 a b x.1 hH φ.2 ψ.2 x.2, one_smul]
  map_smul' c φ := by
    apply Subtype.ext; funext x
    show EabH H a b (mExt (c • φ.1)) x.1 = c • EabH H a b (mExt φ.1) x.1
    rw [eab_h_local n H E (mExt (c • φ.1)) (fun y => (fun _ => (0 : E)) y + c • mExt φ.1 y) a b x.1 hH
      (fun y hy => by rw [mExt_pos hy, mExt_pos hy, zero_add]; rfl) x.2,
      eab_h_linear n H E _ _ c a b x.1 hH m_smooth_zero φ.2 x.2, m_eabH_zero, zero_add]
def mRel (G : Matrix (Fin n) (Fin n) ℂ → E) (ψ : mSub H E) : Prop :=
  SmoothOnH H G ∧ ∀ (y : Matrix (Fin n) (Fin n) ℂ) (hy : inUH H y), G y = ψ.1 ⟨y, hy⟩
def mRho (hH : HInvol H) (s : Matrix (Fin n) (Fin n) ℂ) (hs : inUH H s) : Module.End ℂ (mSub H E) where
  toFun φ := ⟨fun x => φ.1 ⟨x.1 * s, ana_mul x.2 hs⟩,
    smooth_local n H E (fun y => mExt φ.1 (y * s)) _
      (fun y hy => by rw [mExt_pos (ana_mul hy hs), mExt_pos hy])
      (smooth_right' n H E (mExt φ.1) s hH hs φ.2)⟩
  map_add' φ ψ := rfl
  map_smul' c φ := rfl
end Model
end AAInvW


