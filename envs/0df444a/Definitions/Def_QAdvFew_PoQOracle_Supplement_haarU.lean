-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_Supplement_haarU
-- name    : QAdvFew_PoQOracle_Supplement_haarU
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:10:47.339123+00:00
-- url     : https://prove2.me/theorems/98ef1760-127c-4685-a6d8-6587dc1824c3
-- title:
--   Normalized Haar measure on the unitary group
-- statement:
--   For a finite index set $S$, $\mathrm{Haar}(S)$ is the **Haar probability measure** on the unitary group $U(\mathcal H(S))$ of $\mathcal H(S)=\mathbb C^S$: the unique left-invariant Borel probability measure on this compact group. The paper writes $U\leftarrow\mathrm{Haar}(S)$ for a Haar-random unitary and $|\phi\rangle\leftarrow\mathrm{HaarSt}(S)$ for a Haar-random state, which is distributed as $U|0\rangle$ with $U\leftarrow\mathrm{Haar}(S)$.
--
--   The random unitaries and random states of the oracle distribution of §5.1 and of Appendix A are drawn from this measure.
--
--   **Formalization Note** The module proves that the unitary group of a finite-dimensional space is compact and takes Mathlib's Haar measure normalized on the whole group, so it has total mass $1$. Haar-random states are represented by the unitary $V$ with $|\phi\rangle=V|0\rangle$.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, §3.3, p. 16 (PDF p. 18); §5.1, p. 32 (PDF p. 34)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity

open QAlgorithms.Complexity MeasureTheory Matrix

namespace QAdvFew.PoQOracle.Supplement

/-- The unitary group of a finite-dimensional Hilbert space is compact (closed and entrywise
bounded by `1`); needed to normalize its Haar measure. -/
instance instCompactUnitaryGroup (ι : Type) [Fintype ι] [DecidableEq ι] :
    CompactSpace (Matrix.unitaryGroup ι ℂ) := by
  refine isCompact_iff_compactSpace.mp ?_
  have hK : IsCompact (Set.univ.pi fun _ : ι => Set.univ.pi fun _ : ι => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hC : IsClosed ((Matrix.unitaryGroup ι ℂ : Set (Matrix ι ι ℂ))) := by
    have : ((Matrix.unitaryGroup ι ℂ : Set (Matrix ι ι ℂ))) = {A | star A * A = 1} := by
      ext A; exact Matrix.mem_unitaryGroup_iff'
    rw [this]
    exact isClosed_eq (continuous_star.matrix_mul continuous_id) continuous_const
  refine hK.of_isClosed_subset hC ?_
  intro U hU i _ j _
  simpa using entry_norm_bound_of_unitary hU i j

/-- The Borel σ-algebra on the unitary group. -/
noncomputable instance instMeasurableUnitaryGroup (ι : Type) [Fintype ι] [DecidableEq ι] :
    MeasurableSpace (Matrix.unitaryGroup ι ℂ) := borel _

instance instBorelUnitaryGroup (ι : Type) [Fintype ι] [DecidableEq ι] :
    BorelSpace (Matrix.unitaryGroup ι ℂ) := ⟨rfl⟩

/-- The **Haar measure** `Haar(S)` on the unitary group `U(H(S))` of `H(S) = ℂ^S` (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1, §3.1 and
§3.3, pp. 11, 16 (PDF pp. 13, 18): "`U ← Haar(S)`"; §5.1, p. 32 (PDF p. 34): "random unitaries"),
normalized to a probability measure: Mathlib's Haar measure of the compact group normalized so the
whole group has measure `1`.

**Formalization Note** A Haar-random state `HaarSt(S)` is the law of `U|0⟩` for `U ← Haar(S)`;
the definitions sample such states as `U|0⟩` from `haarU` rather than through a separate
measure on state vectors. -/
noncomputable def haarU (ι : Type) [Fintype ι] [DecidableEq ι] :
    Measure (Matrix.unitaryGroup ι ℂ) :=
  Measure.haarMeasure ⊤

instance instProbHaarU (ι : Type) [Fintype ι] [DecidableEq ι] : IsProbabilityMeasure (haarU ι) :=
  ⟨by unfold haarU; exact Measure.haarMeasure_self⟩

end QAdvFew.PoQOracle.Supplement


