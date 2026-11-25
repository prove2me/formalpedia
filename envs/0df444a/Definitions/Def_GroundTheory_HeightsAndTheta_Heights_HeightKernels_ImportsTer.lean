-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsTer
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsTer
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T10:30:00.706043+00:00
-- url     : https://prove2.me/theorems/8e7a0a2c-8342-5494-9795-1e1edd9638f5
-- title:
--   Imports Ter
-- statement:
--   Definitions and structural lemmas for Imports Ter, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ImportsTer.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_LatticeBundleObjects
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
open NumberField NumberField.ComplexEmbedding Matrix GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors
noncomputable section
def S6.QuotExtension.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (a : Fin n → FractionalIdeal (𝓞 K)⁰ K)
    (d : (K →+* ℂ) → Fin n → ℝ) (hd : ∀ σ x, 0 < d σ x) (hc : ∀ σ x, d (conjugate σ) x = d σ x),
    (∀ x, a x ≠ 0) →
    ∀ (m k : ℕ) (b : Fin m → Fin n → K) (c : Fin k → Fin n → K)
      (hli : LinearIndependent K (Sum.elim b c)) (hmk : m + k = n),
      ∃ X : HermitianExtension (subBundle a d hd hc b) (latticeBundle a d hd hc)
          (quotBundle a d hd hc b c hli hmk),
        X.incl = (subLattice a b).subtype ∧ X.proj = quotProj a b c hli hmk
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels


