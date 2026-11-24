-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsRest
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsRest
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:30.757898+00:00
-- url     : https://prove2.me/theorems/61648429-5c23-4588-9bef-1e0d1da7f793
-- title:
--   Imports Rest
-- statement:
--   Definitions and structural lemmas for Imports Rest, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ImportsRest.lean

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
def S6.LatticeAsBundle.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (a : Fin n → FractionalIdeal (𝓞 K)⁰ K)
    (d : (K →+* ℂ) → Fin n → ℝ),
    (∀ x, a x ≠ 0) → (∀ σ x, 0 < d σ x) → (∀ σ x, d (conjugate σ) x = d σ x) →
    ∃ (E : HermitianBundle.{0} K) (L : Fin n → Submodule (𝓞 K) E.carrier),
      DirectSum.IsInternal L ∧ (∀ x, E.rank (L x) = 1) ∧ IsOrthogonalFamily E L ∧
      (∀ x, E.normDegree (L x) = GroundTheory.Heights₂.Heights.normalise K
        (GroundTheory.Heights₂.Heights.subDegree (GroundTheory.Heights₂.Heights.idealLattice a)
          (GroundTheory.Heights₂.Heights.diagMetric d) (fun _ : Fin 1 => (Pi.single x 1 : Fin n → K)))) ∧
      ∀ (m k : ℕ) (b : Fin m → Fin n → K) (c : Fin k → Fin n → K),
        LinearIndependent K (Sum.elim b c) → m + k = n →
        ∃ (E' E'' : HermitianBundle.{0} K), Nonempty (HermitianExtension E' E E'') ∧
          E''.rank ⊤ = k ∧
          E''.normDegree ⊤ = GroundTheory.Heights₂.Heights.normalise K
            (GroundTheory.Heights₂.Heights.quotDegree (GroundTheory.Heights₂.Heights.idealLattice a)
              (GroundTheory.Heights₂.Heights.diagMetric d) b c)
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels


