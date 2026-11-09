-- Prove2me | Definitions.Def_ConstGapCircuits_compactGroups
-- name    : ConstGapCircuits_compactGroups
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:42:56.654195+00:00
-- url     : https://prove2.me/theorems/9bb0f571-d41f-4aaa-b75c-c40c3a8594c6
-- title:
--   Compact quantum groups and normalized subgroup Haar measure (Definitions 1.1–1.2)
-- statement:
--   Let $\mathcal Q_n=\{0,1\}^{\{0,\ldots,n-1\}}$ be the computational basis of $n$ qubits. The ambient group is the full determinant-one unitary group $\mathrm{SU}(2^n)$ on $\mathbb C^{\mathcal Q_n}$, with its usual matrix topology and Borel sets. For a compact Hausdorff topological group $G$, let $\mu_G$ be Haar measure normalized on the whole group. For a closed subgroup $H\le G$, write
--   $$\mu_H^G=(\iota_H)_*\mu_H,$$
--   where $\iota_H:H\hookrightarrow G$ is inclusion. Thus both measures have total mass one.
--
--   This supplies a reusable Haar interface, as well as proved topological-group and compactness instances for the special unitary groups. There is no fallback branch for noncompact subgroups: the subgroup interface requires closedness in a compact group.
-- source:
--   Baer, Haah, Random unitary circuits with constant spectral gap, STOC 2027 submission #15 (preprint), p. 2–3, Definitions 1.1–1.2; §1.4, (1.12)

import Mathlib

noncomputable section

namespace ConstGapCircuits

abbrev Qubits (n : ℕ) := Fin n → Fin 2
abbrev Mat (n : ℕ) := Matrix (Qubits n) (Qubits n) ℂ
abbrev SU (n : ℕ) := Matrix.specialUnitaryGroup (Qubits n) ℂ

instance suContinuousInv (n : ℕ) : ContinuousInv (SU n) where
  continuous_inv := continuous_induced_rng.mpr continuous_subtype_val.star

instance suTopologicalGroup (n : ℕ) : IsTopologicalGroup (SU n) where

instance suMeasurableSpace (n : ℕ) : MeasurableSpace (SU n) := borel _
instance suBorelSpace (n : ℕ) : BorelSpace (SU n) := ⟨rfl⟩

/-- Closedness is structural: unitarity and determinant one are closed equations. -/
lemma su_isClosed (n : ℕ) : IsClosed (Matrix.specialUnitaryGroup (Qubits n) ℂ : Set (Mat n)) := by
  exact (isClosed_unitary).inter (isClosed_eq continuous_id.matrix_det continuous_const)

instance suCompactSpace (n : ℕ) : CompactSpace (SU n) := by
  open scoped Matrix.Norms.Elementwise in
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0 : Mat n) 1).of_isClosed_subset (su_isClosed n)
  intro U hU
  simpa [Metric.mem_closedBall, dist_zero_right] using entrywise_sup_norm_bound_of_unitary hU.1

section Haar
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

instance closedSubgroupTopologicalGroup (H : ClosedSubgroup G) : IsTopologicalGroup H where
  continuous_mul := continuous_induced_rng.mpr ((continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd))
  continuous_inv := continuous_induced_rng.mpr continuous_subtype_val.inv

/-- Haar measure normalized on the whole compact group, with no zero branch. -/
def haarProbability : MeasureTheory.Measure G :=
  MeasureTheory.Measure.haarMeasure ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

instance haarProbability_isProbability : MeasureTheory.IsProbabilityMeasure (haarProbability (G := G)) := by
  constructor
  exact MeasureTheory.Measure.haarMeasure_self

/-- Haar on a closed subgroup, pushed forward by its inclusion. -/
def haarOn (H : ClosedSubgroup G) : MeasureTheory.Measure G :=
  (haarProbability (G := H)).map ((↑) : H → G)

instance haarOn_isProbability (H : ClosedSubgroup G) : MeasureTheory.IsProbabilityMeasure (haarOn H) := by
  unfold haarOn
  exact MeasureTheory.Measure.isProbabilityMeasure_map (continuous_subtype_val : Continuous ((↑) : H → G)).measurable.aemeasurable
end Haar

end ConstGapCircuits


