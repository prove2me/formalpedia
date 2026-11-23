-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_IsParahoricVec
-- name    : Development_AbelianVarietyTheory_Definitions_GaloisGeometry_IsParahoricVec
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:28:18.243739+00:00
-- url     : https://prove2.me/theorems/19c426c4-ac43-4077-aea2-268bc18a1aa2
-- title:
--   Is Parahoric Vec
-- statement:
--   Definitions and structural lemmas for Is Parahoric Vec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/IsParahoricVec.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel
open scoped TensorProduct
namespace GlobalTheory.ThetaGL
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
def ThetaPair (μ : kˣ →* ℂˣ) (σ : Representation ℂ (GL (Fin r) k) V) (π : Representation ℂ (GL (Fin n) k) W) :
    Prop :=
  ∃ B : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] W →ₗ[ℂ] V, B ≠ 0 ∧
    ∀ (g : GL (Fin r) k) (h : GL (Fin n) k) (Φ Φ' : SB (Matrix (Fin n) (Fin r) k)),
      (Φ' : Matrix (Fin n) (Fin r) k → ℂ) = om μ g h Φ → ∀ F : W, B Φ' (π h F) = σ g (B Φ F)
def OmQuot (μ : kˣ →* ℂˣ) (σ : Representation ℂ (GL (Fin r) k) V) (τ : Representation ℂ (GL (Fin n) k) W) :
    Prop :=
  ∃ f : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] V ⊗[ℂ] W, f ≠ 0 ∧
    ∀ (g : GL (Fin r) k) (h : GL (Fin n) k) (Φ Φ' : SB (Matrix (Fin n) (Fin r) k)),
      (Φ' : Matrix (Fin n) (Fin r) k → ℂ) = om μ g h Φ → f Φ' = TensorProduct.map (σ g) (τ h) (f Φ)
def IsParahoricVec {t : ℕ} (χ : kˣ →* ℂˣ) (π : Representation ℂ (GL (Fin (r + t)) k) W) (v : W) : Prop :=
  ∀ h ∈ KO k (Fin (r + t)),
    (∀ (i : Fin t) (j : Fin r), valuation k (h.val (Fin.natAdd r i) (Fin.castAdd t j)) < 1) →
    ∀ u : kˣ, (u : k) = (h.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det → π h v = (χ u : ℂ) • v
end GlobalTheory.ThetaGL


