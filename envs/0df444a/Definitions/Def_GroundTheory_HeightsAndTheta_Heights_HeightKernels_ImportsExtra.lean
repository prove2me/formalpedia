-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsExtra
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsExtra
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:27:21.110886+00:00
-- url     : https://prove2.me/theorems/6c7820cf-3fea-4524-a2fb-2cae42d0a292
-- title:
--   Imports Extra
-- statement:
--   Definitions and structural lemmas for Imports Extra, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ImportsExtra.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardInnerSingleNe
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
open NumberField NumberField.ComplexEmbedding GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors
noncomputable section
def S6.BundleCoordinates.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (X : Type) [Fintype X]
    [DecidableEq X] (L : X → Submodule (𝓞 K) E.carrier),
    DirectSum.IsInternal L → (∀ x, E.rank (L x) = 1) → IsOrthogonalFamily E L →
    ∀ (E' E'' : HermitianBundle.{0} K), HermitianExtension E' E E'' →
    ∃ (n : ℕ) (e : Fin n ≃ X) (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) (d : (K →+* ℂ) → Fin n → ℝ),
      (∀ i, a i ≠ 0) ∧ (∀ σ i, 0 < d σ i) ∧ (∀ σ i, d (conjugate σ) i = d σ i) ∧
      (∀ i, GroundTheory.Heights₂.Heights.normalise K
        (GroundTheory.Heights₂.Heights.subDegree (GroundTheory.Heights₂.Heights.idealLattice a)
          (GroundTheory.Heights₂.Heights.diagMetric d) (fun _ : Fin 1 => (Pi.single i 1 : Fin n → K))) =
        E.normDegree (L (e i))) ∧
      ∃ (m k : ℕ) (b : Fin m → Fin n → K) (c : Fin k → Fin n → K),
        LinearIndependent K (Sum.elim b c) ∧ m + k = n ∧ k = E''.rank ⊤ ∧
        GroundTheory.Heights₂.Heights.normalise K
          (GroundTheory.Heights₂.Heights.quotDegree (GroundTheory.Heights₂.Heights.idealLattice a)
            (GroundTheory.Heights₂.Heights.diagMetric d) b c) = E''.normDegree ⊤
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels


