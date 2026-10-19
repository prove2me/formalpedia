-- Prove2me | Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
-- name    : QAlgorithms_Defs_SchurUnitaryEnsembles
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:38:03.889592+00:00
-- url     : https://prove2.me/theorems/dc3bc33d-cace-4408-90a0-160b417e2811
-- title:
--   SchurUnitaryEnsembles
-- statement:
--   SchurUnitaryEnsembles
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\SchurUnitaryEnsembles.lean

import Definitions.Def_QAlgorithms_Defs_SchurShapes
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open MeasureTheory TopologicalSpace
open scoped Matrix.Norms.Elementwise

namespace QAlgorithms.Schur

/-- Borel unitary outcomes, as used by both continuous tomography measurements
(1508.01797 p.6; 1508.01907 pp.7-8). -/
instance unitaryMeasurable (d : ℕ) : MeasurableSpace (Matrix.unitaryGroup (Fin d) ℂ) := borel _

/-- Borel convention for the exact unitary group (1508.01907 p.7). -/
instance unitaryBorel (d : ℕ) : BorelSpace (Matrix.unitaryGroup (Fin d) ℂ) := ⟨rfl⟩

/-- Compactness of finite-dimensional unitary outcomes permits whole-group
probability Haar normalization (1508.01797 p.6; 1508.01907 p.7). -/
instance unitaryCompact (d : ℕ) : CompactSpace (Matrix.unitaryGroup (Fin d) ℂ) := by
  have hc : IsClosed (Matrix.unitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ)) :=
    isClosed_unitary
  have hb : Bornology.IsBounded
      (Matrix.unitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ)) :=
    (show Bornology.IsBounded (Metric.closedBall (0 : Matrix (Fin d) (Fin d) ℂ) 1) from Metric.isBounded_closedBall).subset (by
      intro U hU
      simp only [Metric.mem_closedBall, dist_zero_right]
      exact entrywise_sup_norm_bound_of_unitary hU)
  exact isCompact_iff_compactSpace.mp (Metric.isCompact_of_isClosed_isBounded hc hb)

/-- Exact probability Haar measure, normalized on the entire compact U(d).
This reference law is distinct from the state-dependent Born outcome law
(1508.01797 p.6; 1508.01907 pp.7-8). -/
def unitaryHaar (d : ℕ) : Measure (Matrix.unitaryGroup (Fin d) ℂ) :=
  Measure.haarMeasure (⟨⟨Set.univ,isCompact_univ⟩,by simp⟩ : PositiveCompacts _)

example (d : ℕ) : unitaryHaar d Set.univ = 1 := Measure.haarMeasure_self

end QAlgorithms.Schur


