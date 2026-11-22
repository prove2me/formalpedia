-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieFrame
-- name    : Formalism_SharpRestriction_Divisibility_HookProducts_RBTieFrame
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:22:34.655733+00:00
-- url     : https://prove2.me/theorems/bd02bf2d-4825-4b3a-9846-0fb9a7b15303
-- title:
--   RBTie Frame
-- statement:
--   Definitions and structural lemmas for RBTie Frame, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/HookProducts/RBTieFrame.lean

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField Module
noncomputable section
namespace Formalism.MainNotions.DIV.HookProducts.RBTie
section Vec
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
end Vec
section Comparison₂
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ}
def cP (b : Basis ι K V) (e : (Fin d → K) ≃ₗ[K] V) (v : InfinitePlace K) : Matrix ι (Fin d) ℂ :=
  (LinearMap.toMatrix (Pi.basisFun K (Fin d)) b e.toLinearMap).map v.embedding
def cQ (b : Basis ι K V) (e : (Fin d → K) ≃ₗ[K] V) (v : InfinitePlace K) : Matrix (Fin d) ι ℂ :=
  (LinearMap.toMatrix b (Pi.basisFun K (Fin d)) e.symm.toLinearMap).map v.embedding
def cU (b : Basis ι K V) (XA : InfinitePlace K → Matrix ι ι ℂ) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (e : (Fin d → K) ≃ₗ[K] V) (v : InfinitePlace K) : Matrix ι (Fin d) ℂ :=
  (XA v)⁻¹ * cP b e v * X v
def cV (b : Basis ι K V) (XA : InfinitePlace K → Matrix ι ι ℂ) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (e : (Fin d → K) ≃ₗ[K] V) (v : InfinitePlace K) : Matrix (Fin d) ι ℂ :=
  (X v)⁻¹ * cQ b e v * XA v
variable (b : Basis ι K V) (XA : InfinitePlace K → Matrix ι ι ℂ) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
  (e : (Fin d → K) ≃ₗ[K] V) (v : InfinitePlace K)
end Comparison₂
section Norm
end Norm
end Formalism.MainNotions.DIV.HookProducts.RBTie


