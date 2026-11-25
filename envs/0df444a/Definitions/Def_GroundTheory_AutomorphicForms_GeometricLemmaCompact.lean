-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCompact
-- name    : GroundTheory_AutomorphicForms_GeometricLemmaCompact
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T11:22:24.671429+00:00
-- url     : https://prove2.me/theorems/c56475cf-6bcc-4e80-bb38-539e21c03b89
-- title:
--   Geometric Lemma Compact
-- statement:
--   Definitions and structural lemmas for Geometric Lemma Compact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCompact.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaFiltration
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Automorphic
namespace Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
section Bounds
variable (F) in

abbrev EntryBound (e : ℕ) (A : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ i j, (uniformizer F : F) ^ e * A i j ∈ 𝒪[F]
end Bounds
section UnipotentCompact
variable (γ : Fin n → ℕ)
def unipotentCompactG (e : ℕ) : Subgroup (GL (Fin n) F) :=
  (unipotentCompact F n γ e).map (unipotentRadical F n γ).subtype
variable {γ}
end UnipotentCompact
section Support
variable {β γ : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (levi F n β) W}
variable (w : Equiv.Perm (Fin n))
end Support
end Parabolic
end GroundTheory.Automorphic


