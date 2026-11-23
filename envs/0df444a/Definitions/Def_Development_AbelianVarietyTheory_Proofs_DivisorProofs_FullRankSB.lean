-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankSB
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankSB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:16:46.300925+00:00
-- url     : https://prove2.me/theorems/114f4a7a-58f0-4fcf-987f-54b1df01c74b
-- title:
--   Full Rank SB
-- statement:
--   Definitions and structural lemmas for Full Rank SB, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FullRankSB.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.WeilM
namespace GlobalTheory.RankFibre
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable (k) in

def fullRankSB (a d : ℕ) : Submodule ℂ (Matrix (Fin a) (Fin d) k → ℂ) where
  carrier := {Ψ | Ψ ∈ SB (Matrix (Fin a) (Fin d) k) ∧ ∀ Y : Matrix (Fin a) (Fin d) k, Y.rank ≠ a → Ψ Y = 0}
  zero_mem' := ⟨(SB _).zero_mem, fun _ _ => rfl⟩
  add_mem' := fun hΦ hΨ => ⟨(SB _).add_mem hΦ.1 hΨ.1, fun Y hY => by simp [hΦ.2 Y hY, hΨ.2 Y hY]⟩
  smul_mem' := fun c Φ hΦ => ⟨(SB _).smul_mem c hΦ.1, fun Y hY => by simp [hΦ.2 Y hY]⟩
def coinv (ν β : kˣ →* ℂˣ) (a d : ℕ) : Submodule ℂ (Matrix (Fin a) (Fin d) k → ℂ) :=
  Submodule.span ℂ {z | ∃ (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin d) k → ℂ),
    Ψ ∈ SB (Matrix (Fin a) (Fin d) k) ∧ z = omA ν β g 1 Ψ - Ψ}
abbrev blocks (a b : ℕ) : (Σ x, Two (Fin a) (Fin b) x) ≃ Fin (a + b) := two (stdSum (rfl : a + b = a + b))
def parChar (ν β : kˣ →* ℂˣ) (a b : ℕ) : parab k (blocks a b) →* ℂˣ :=
  (deltaHalf k (Two (Fin a) (Fin b)) * ((detChar (Fin a) (ν * β)).comp (MonoidHom.fst _ _)).comp
      (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom *
    ((detChar (Fin b) β).comp (MonoidHom.snd _ _)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom).comp
    (leviProj k (blocks a b))
def indScal (ν β : kˣ →* ℂˣ) (a b : ℕ) : Submodule ℂ (GL (Fin (a + b)) k → ℂ) :=
  smoothPart (rightReg ℂ (GL (Fin (a + b)) k) ℂ) ⊓ indSpace (parab k (blocks a b)) (ofChar (parChar ν β a b))
variable [MeasurableSpace k] [BorelSpace k]
def fibre (ν β : kˣ →* ℂˣ) (a b : ℕ) (Φ : Matrix (Fin a) (Fin (a + b)) k → ℂ) (x : GL (Fin (a + b)) k) : ℂ :=
  ∫ g : GL (Fin a) k, omA ν β 1 x Φ (g.val * X0 k finSumFinEquiv) * (ν (gdet g) : ℂ) *
    apow (gdet g) (((a + b : ℕ) : ℂ) / 2) ∂(haarVol (GlobalTheory.SplitWeil.KO k (Fin a)))
end GlobalTheory.RankFibre


