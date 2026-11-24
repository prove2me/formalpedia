-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WEMulNUMulTD
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_WEMulNUMulTD
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:50:57.466801+00:00
-- url     : https://prove2.me/theorems/764155f9-b113-4c02-87dc-4dc5f5b350f1
-- title:
--   WEMul NUMul TD
-- statement:
--   Definitions and structural lemmas for WEMul NUMul TD, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WEMulNUMulTD.lean

import Mathlib
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
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct
namespace GlobalTheory.PrinTwo
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def bor (a d : kˣ) (x : k) : GL (Fin (1 + 1)) k :=
  GeneralLinearGroup.mkOfDetNeZero !![(a : k), x; 0, (d : k)] (by simp)
def nU (x : k) : GL (Fin (1 + 1)) k := bor 1 1 x
def nL (x : k) : GL (Fin (1 + 1)) k := GeneralLinearGroup.mkOfDetNeZero !![1, 0; x, 1] (by simp)
def wE : GL (Fin (1 + 1)) k := GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 0] (by simp)
def tD (a d : kˣ) : GL (Fin (1 + 1)) k := bor a d 0
abbrev PSp (μ₁ μ₂ : kˣ →* ℂˣ) : Type :=
  IndSp (two (stdSum (rfl : 1 + 1 = 1 + 1)))
    ((extTensor (detRep (Fin 1) μ₁) (detRep (Fin 1) μ₂)).comp (leviTwo k (Fin 1) (Fin 1)).symm.toMonoidHom)
abbrev psRep (μ₁ μ₂ : kˣ →* ℂˣ) : Representation ℂ (GL (Fin (1 + 1)) k) (PSp μ₁ μ₂) :=
  prod₂ (detRep (Fin 1) μ₁) (detRep (Fin 1) μ₂)
def ev {μ₁ μ₂ : kˣ →* ℂˣ} (f : PSp μ₁ μ₂) (g : GL (Fin (1 + 1)) k) : ℂ := TensorProduct.lid ℂ ℂ (f.1.1 g)
def coord {μ₁ μ₂ : kˣ →* ℂˣ} (f : PSp μ₁ μ₂) (x : k) : ℂ := ev f (wE * nU x)
def bchar (μ₁ μ₂ : kˣ →* ℂˣ) (a d : kˣ) : ℂ :=
  ((μ₁ a * μ₂ d * absPow k (1 / 2) a * absPow k (-1 / 2) d : ℂˣ) : ℂ)
theorem ev_add {μ₁ μ₂ : kˣ →* ℂˣ} (f f' : PSp μ₁ μ₂) (g : GL (Fin (1 + 1)) k) :
    ev (f + f') g = ev f g + ev f' g := by
  show TensorProduct.lid ℂ ℂ (f.1.1 g + f'.1.1 g) = _
  rw [map_add]; rfl
theorem ev_smul {μ₁ μ₂ : kˣ →* ℂˣ} (c : ℂ) (f : PSp μ₁ μ₂) (g : GL (Fin (1 + 1)) k) :
    ev (c • f) g = c * ev f g := by
  show TensorProduct.lid ℂ ℂ (c • f.1.1 g) = _
  rw [map_smul]; rfl
def evL (μ₁ μ₂ : kˣ →* ℂˣ) (g : GL (Fin (1 + 1)) k) : PSp μ₁ μ₂ →ₗ[ℂ] ℂ where
  toFun f := ev f g
  map_add' f f' := ev_add f f' g
  map_smul' c f := ev_smul c f g
def coordL (μ₁ μ₂ : kˣ →* ℂˣ) : PSp μ₁ μ₂ →ₗ[ℂ] (k → ℂ) where
  toFun f := coord f
  map_add' f f' := funext fun x => ev_add f f' _
  map_smul' c f := funext fun x => ev_smul c f _
def ball (c : k) (r : kˣ) : Set k := {z | valuation k (z - c) ≤ valuation k (r : k)}
def elemDiff (c c' : k) (r : kˣ) : k → ℂ := (ball c r).indicator 1 - (ball c' r).indicator 1
variable (k) in

def elemSpan : Submodule ℂ (k → ℂ) :=
  Submodule.span ℂ (Set.range fun p : k × k × kˣ => elemDiff p.1 p.2.1 p.2.2)
def IsLC (Φ : k → ℂ) : Prop := ∃ r : kˣ, ∀ x y : k, valuation k y ≤ valuation k (r : k) → Φ (x + y) = Φ x
def IsCS (Φ : k → ℂ) : Prop := ∃ R : kˣ, ∀ x : k, valuation k (R : k) < valuation k x → Φ x = 0
def IsEvRad (Φ : k → ℂ) : Prop :=
  ∃ R : kˣ, ∀ x y : k, valuation k (R : k) < valuation k x → valuation k x = valuation k y → Φ x = Φ y
end GlobalTheory.PrinTwo


