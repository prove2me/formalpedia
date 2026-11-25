-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsBis
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsBis
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T10:34:10.917418+00:00
-- url     : https://prove2.me/theorems/8a00d828-c569-51cb-b6f5-ba2ef2743599
-- title:
--   Imports Bis
-- statement:
--   Definitions and structural lemmas for Imports Bis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ImportsBis.lean

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
def S6.QuotDegree.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (a : Fin n → FractionalIdeal (𝓞 K)⁰ K)
    (d : (K →+* ℂ) → Fin n → ℝ), (∀ x, a x ≠ 0) → (∀ σ x, 0 < d σ x) →
    ∀ (m k : ℕ) (b : Fin m → Fin n → K) (c : Fin k → Fin n → K)
      (hli : LinearIndependent K (Sum.elim b c)) (hmk : m + k = n),
      Submodule.span K (quotLattice a b c hli hmk : Set (Fin k → K)) = ⊤ ∧
        subDegree (quotLattice a b c hli hmk) (schurMetric d b c)
            (fun j : Fin k => (Pi.single j 1 : Fin k → K)) =
          quotDegree (idealLattice a) (diagMetric d) b c
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels


