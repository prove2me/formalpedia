-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisGeometry__HoweDualityGL_c4f3064dc8a43034
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisGeometry__HoweDualityGL_c4f3064dc8a43034
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:39:35.28383+00:00
-- url     : https://prove2.me/theorems/be6aeb64-b3e0-427c-ade5-e634fe5303da
-- title:
--   Howe Duality GL
-- statement:
--   Definitions and structural lemmas for Howe Duality GL, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisGeometry₂/HoweDualityGL.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_IsParahoricVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.ThetaGL
namespace GlobalTheory.Published
def HoweDualityGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r n : ℕ)
    (μ : kˣ →* ℂˣ), IsSmoothChar μ →
    (∀ (V W W' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
      (σ : Representation ℂ (GL (Fin r) k) V) (τ : Representation ℂ (GL (Fin n) k) W)
      (τ' : Representation ℂ (GL (Fin n) k) W'), IsSmooth σ → σ.IsIrreducible → IsSmooth τ → τ.IsIrreducible →
      IsSmooth τ' → τ'.IsIrreducible → OmQuot μ σ τ → OmQuot μ σ τ' → Nonempty (τ.Equiv τ')) ∧
    (∀ (V V' W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W] [Module ℂ W]
      (σ : Representation ℂ (GL (Fin r) k) V) (σ' : Representation ℂ (GL (Fin r) k) V')
      (τ : Representation ℂ (GL (Fin n) k) W), IsSmooth σ → σ.IsIrreducible → IsSmooth σ' → σ'.IsIrreducible →
      IsSmooth τ → τ.IsIrreducible → OmQuot μ σ τ → OmQuot μ σ' τ → Nonempty (σ.Equiv σ'))
end GlobalTheory.Published


