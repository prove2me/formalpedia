-- Prove2me | Definitions.Def_SP4TauCeti
-- name    : SP4TauCeti
-- status  : Definition
-- author  : @loader3229
-- created : 2026-11-26T12:50:04.981318+00:00
-- url     : https://prove2.me/theorems/a2bfb7af-fc72-4361-abad-57819cb4cbb5
-- title:
--   Characteristic map of a CW cell as a continuous map
-- statement:
--   The characteristic map of an $n$-cell of a relative CW complex $(\mathcal{C},D)$ is the continuous map $\Phi_j : \overline{B}^n \to \mathcal{C}$ from the closed unit ball of $\mathbb{R}^n$ (sup norm) into the complex, obtained by restricting the characteristic partial equivalence `map n j` to the closed ball. It carries the boundary sphere $S^{n-1}$ into the $(n-1)$-skeleton. This is the Mathlib rendering of TauCeti's `cellMap`, used to state the compression lemma's cell-by-cell hypotheses.
-- source:
--   A. Hatcher, Algebraic Topology, Cambridge University Press (2002), §4.1 Lemma 4.6 (compression lemma) and the compression criterion; TauCetiProject/TauCeti, TauCeti.exists_homotopicRel_cellMap, TauCeti.exists_homotopicRel_forall_mapsTo_skeletonLT, TauCeti.exists_homotopicRel_range_subset (https://github.com/TauCetiProject/TauCeti).

import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.CWComplex.Classical.Basic

set_option autoImplicit false

open scoped ContinuousMap
open ContinuousMap Metric Set Topology Topology.RelCWComplex

universe u v

namespace SP4TauCeti

variable {X : Type u} [TopologicalSpace X] [T2Space X] {C D : Set X} [RelCWComplex C D]

/-- The characteristic map of an `n`-cell as a continuous map from the closed unit ball
of `Fin n → ℝ` (sup norm) into the complex `C`.  Mathlib stores `map n j` as a
`PartialEquiv`; this is its continuous restriction to the closed ball, landing in `C`. -/
def cellMap {n : ℕ} (j : cell C n) : C(closedBall (0 : Fin n → ℝ) 1, C) :=
  ⟨fun y ↦ ⟨map n j y, closedCell_subset_complex n j ⟨y, y.property, rfl⟩⟩,
    ((continuousOn n j).comp_continuous continuous_subtype_val fun y ↦ y.property).subtype_mk _⟩

@[simp] lemma coe_cellMap_apply {n : ℕ} (j : cell C n) (y : closedBall (0 : Fin n → ℝ) 1) :
    (cellMap j y : X) = map n j y := rfl

/-- A map `C(C, Y)` sends the closed `n`-cell `j` to `Y` by precomposing with `cellMap j`. -/
abbrev cellMapComp (n : ℕ) (j : cell C n) (Y : Type v) [TopologicalSpace Y]
    (f : C(C, Y)) : C(closedBall (0 : Fin n → ℝ) 1, Y) := f.comp (cellMap j)

end SP4TauCeti


