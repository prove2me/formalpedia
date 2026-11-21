-- Prove2me | Definitions.Def_YM_canonicalFamily
-- name    : YM_canonicalFamily
-- status  : Definition
-- author  : @LG
-- created : 2026-11-20T17:30:39.465002+00:00
-- url     : https://prove2.me/theorems/80766fa3-e788-4953-8a0b-5cfa39e8d782
-- title:
--   Canonical Wilson lattice family for a compact matrix gauge group
-- statement:
--   An explicit Wilson lattice family attached to each compact matrix gauge group $G$. The lattice at refinement $N$ and volume index $p$ has mesh $1/(N+1)$ and physical period $p+1$; the bare inverse coupling is $\beta(N,p)=\log(N+1)$, so $\beta/\log(1/\mathrm{mesh})\to 1$. The prior is the normalized Haar probability measure of the compact group $G$. Insertion tokens are finite lists of oriented plaquette directions, and the corresponding insertion is the product of the traces of the plaquette holonomies based at the insertion site; these generate the local gauge-invariant observable algebra. This canonical family anchors the decomposition of the joint Yang–Mills existence challenge into a lattice-regularity part and a continuum-construction part.
--
--   **Formalization Note.** Compactness of $G$ follows because it is a closed subgroup of the compact unitary group; the Haar probability measure is `Measure.haarMeasure` normalized on the whole group. The family is a `YangMills.WilsonFamily` in the public challenge specification.
-- source:
--   https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/PublicWilson.lean (WilsonFamily); standard Wilson lattice regularization, Wilson 1974 Phys. Rev. D 10 2445

import Definitions.Def_YM_ChallengeSpec

/-! The canonical Wilson lattice family used to anchor the joint-existence decomposition.
One explicit family per gauge group: mesh `1/(N+1)`, physical period `p+1`, running bare
coupling `beta N p = log (N+1)`, normalized Haar prior, and insertions given by finite
products of plaquette traces (the local gauge-invariant observable algebra). -/
set_option autoImplicit false
noncomputable section

namespace YangMills

open MeasureTheory TopologicalSpace
open scoped Matrix.Norms.Elementwise

/-- The ambient unitary group is compact (closed and bounded in matrix space). -/
instance ymUnitaryCompact (n : ℕ) : CompactSpace (Matrix.unitaryGroup (Fin (n + 1)) ℂ) := by
  have hc : IsClosed (Matrix.unitaryGroup (Fin (n + 1)) ℂ :
      Set (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) := isClosed_unitary
  have hb : Bornology.IsBounded (Matrix.unitaryGroup (Fin (n + 1)) ℂ :
      Set (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) :=
    (show Bornology.IsBounded
        (Metric.closedBall (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) 1) from
      Metric.isBounded_closedBall).subset (by
      intro U hU
      simp only [Metric.mem_closedBall, dist_zero_right]
      exact entrywise_sup_norm_bound_of_unitary hU)
  exact isCompact_iff_compactSpace.mp (Metric.isCompact_of_isClosed_isBounded hc hb)

/-- A closed matrix gauge group is compact. -/
instance ymImageCompact (g : GaugeGroup) : CompactSpace g.image :=
  isCompact_iff_compactSpace.mp g.imageClosed.isCompact

/-- The whole compact group as a positive compact set. -/
def posCompactsImage (g : GaugeGroup) : PositiveCompacts g.image :=
  ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

/-- Normalized Haar probability measure on the compact gauge group. -/
def probHaar (g : GaugeGroup) : Measure g.image :=
  Measure.haarMeasure (posCompactsImage g)

instance ymProbHaar (g : GaugeGroup) : IsProbabilityMeasure (probHaar g) where
  measure_univ := by
    have h := Measure.haarMeasure_self (K₀ := posCompactsImage g)
    simpa [probHaar, posCompactsImage] using h

instance ymHaar (g : GaugeGroup) : (probHaar g).IsHaarMeasure :=
  Measure.isHaarMeasure_haarMeasure _

/-- The canonical Wilson family: one explicit lattice regularization per gauge group. -/
noncomputable def canonicalFamily (g : GaugeGroup) : WilsonFamily g where
  period := fun p => ⟨p + 1, Nat.succ_pos p⟩
  denominator := fun N => ⟨N + 1, Nat.succ_pos N⟩
  periodStrict := fun _ _ hab => Nat.add_lt_add_right hab 1
  denominatorStrict := fun _ _ hab => Nat.add_lt_add_right hab 1
  beta := fun N _ => Real.log (N + 1)
  haar := probHaar g
  probability := inferInstance
  invariantHaar := inferInstance
  Token := List (Axis × Axis)
  insertion := fun _ _ v x U =>
    (v.map (fun ij => (plaquette U x ij.1 ij.2).val.val.trace)).prod

end YangMills


