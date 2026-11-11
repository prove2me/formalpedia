-- Prove2me | Definitions.Def_InterleavedUnitaryNOF_LowerBound_Haar
-- name    : InterleavedUnitaryNOF_LowerBound_Haar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:07:06.660035+00:00
-- url     : https://prove2.me/theorems/414c18b3-a6ab-440e-8ed9-f80bb8bc3f4c
-- title:
--   Actual special-unitary group and normalized Borel Haar measure
-- statement:
--   Use Mathlib's actual group $SU(m)$ of complex unitary matrices with determinant one, its inherited matrix topology, and the Borel measurable structure. For every $m\ge1$, compactness is established from closedness and the unitary norm bound; the entire group is used as the Haar normalizing compact set.
--
--   $$\nu(SU(m))=1.$$
--
--   Probability and Haar instances are constructed, not supplied as source-result certificates. The singleton group at $m=1$ is included.
-- source:
--   Haoyu Wang, Pei Wu, Guangxu Yang, STOC 2027 submission #1513 (October 2026), §2 Notation, p.6; §4, pp.9–10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1513.pdf

import Mathlib
import Definitions.Def_InterleavedUnitaryNOF_LowerBound_Input

open scoped ComplexOrder
open MeasureTheory TopologicalSpace

namespace InterleavedUnitaryNOF.LowerBound

abbrev SU (m : ℕ) := Matrix.specialUnitaryGroup (Fin m) ℂ

instance matrixSecondCountable (m : ℕ) : SecondCountableTopology (Mat m) :=
  inferInstanceAs (SecondCountableTopology (Fin m → Fin m → ℂ))
instance suSecondCountable (m : ℕ) : SecondCountableTopology (SU m) :=
  (Topology.IsInducing.subtypeVal : Topology.IsInducing (Subtype.val : SU m → Mat m)).secondCountableTopology

noncomputable instance suMeasurable (m : ℕ) : MeasurableSpace (SU m) := borel (SU m)
instance suBorel (m : ℕ) : BorelSpace (SU m) := ⟨rfl⟩
instance suContinuousMul (m : ℕ) : ContinuousMul (SU m) where
  continuous_mul := continuous_induced_rng.mpr
    ((continuous_subtype_val.comp continuous_fst).matrix_mul (continuous_subtype_val.comp continuous_snd))
instance suContinuousInv (m : ℕ) : ContinuousInv (SU m) where
  continuous_inv := continuous_induced_rng.mpr continuous_subtype_val.star
instance suTopologicalGroup (m : ℕ) : IsTopologicalGroup (SU m) where

/-- Compactness is obtained in the C*-matrix norm. Its topology is precisely
Mathlib's entrywise matrix topology, so this does not change the Borel structure. -/
instance suCompact (m : ℕ) [NeZero m] : CompactSpace (SU m) := by
  have hclosed : IsClosed (Matrix.specialUnitaryGroup (Fin m) ℂ : Set (Mat m)) :=
    isClosed_unitary.inter (isClosed_eq continuous_id.matrix_det continuous_const)
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0 : ℂ) 1).matrix.of_isClosed_subset hclosed
  intro a ha i j
  rw [Metric.mem_closedBall, dist_zero_right]
  let a' : CStarMatrix (Fin m) (Fin m) ℂ := CStarMatrix.ofMatrix a
  have hu : a' ∈ unitary (CStarMatrix (Fin m) (Fin m) ℂ) := ha.1
  exact CStarMatrix.norm_entry_le_norm.trans
    (le_of_eq (CStarRing.norm_of_mem_unitary hu))

/-- The compact set used to normalize Haar is the entire actual SU(m). -/
def haarNormalizingSet (m : ℕ) [NeZero m] : PositiveCompacts (SU m) :=
  ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

noncomputable def haar (m : ℕ) [NeZero m] : Measure (SU m) :=
  Measure.haarMeasure (haarNormalizingSet m)

instance haarProbability (m : ℕ) [NeZero m] : IsProbabilityMeasure (haar m) :=
  ⟨by simpa [haar, haarNormalizingSet] using Measure.haarMeasure_self (K₀ := haarNormalizingSet m)⟩

instance haarInvariance (m : ℕ) [NeZero m] : (haar m).IsHaarMeasure :=
  Measure.isHaarMeasure_haarMeasure _

end InterleavedUnitaryNOF.LowerBound


