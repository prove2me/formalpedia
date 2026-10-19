-- Prove2me | Definitions.Def_QAlgorithms_Papers_RoadmapO18_Model
-- name    : QAlgorithms_Papers_RoadmapO18_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:02:36.363248+00:00
-- url     : https://prove2.me/theorems/93ccd2f1-89bf-4f9b-8531-197cb63a9777
-- title:
--   Computed lightcone ansatz and proved positive-domain prerequisites
-- statement:
--   Supporting mathematical objects and conventions for the selected original paper results. Exact source hypotheses and labels are documented in the Lean declarations.
-- source:
--   Performance guarantees of light-cone variational quantum algorithms for the maximum cut problem, arXiv:2504.12896v4, https://arxiv.org/abs/2504.12896v4. Exact locators in declaration docstrings.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_ZYLocalCertificates
noncomputable section

open Filter

namespace QAlgorithms.Papers.RoadmapO18

open QAlgorithms QAlgorithms.ZY

attribute [local instance] Classical.propDecidable


theorem cubic_domains {N : ℕ} (G : SimpleGraph (Fin N)) (connected : G.Connected)
    (nonempty : 0 < N) (cubic : ∀ v, (Finset.univ.filter fun u => G.Adj v u).card = 3)
    (O : Orientation G) (S : GateSequence O) :
    0 < @maximumCut N G (Classical.decRel _) ∧ 0 < S.edges.length := by
  classical
  let v : Fin N := ⟨0, nonempty⟩
  have hneighbors : (Finset.univ.filter fun u => G.Adj v u).Nonempty := by
    apply Finset.card_pos.mp
    rw [cubic v]
    omega
  obtain ⟨u, hu⟩ := hneighbors
  have hvu : G.Adj v u := (Finset.mem_filter.mp hu).2
  have hordered : ∃ a b : Fin N, a < b ∧ G.Adj a b := by
    rcases lt_or_gt_of_ne (G.ne_of_adj hvu) with h | h
    · exact ⟨v, u, h, hvu⟩
    · exact ⟨u, v, h, hvu.symm⟩
  obtain ⟨a, b, hab, hadj⟩ := hordered
  constructor
  · let z : Qubits N := fun i => decide (i = a)
    have hz : z a ≠ z b := by
      simp [z, (ne_of_lt hab).symm]
    have hcut : 0 < cutValue G z := by
      apply Finset.card_pos.mpr
      exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hadj, hz⟩⟩
    exact lt_of_lt_of_le hcut (Finset.le_sup (f := cutValue G) (Finset.mem_univ z))
  · have hex : ∃ e, e ∈ directedEdges O := by
      rcases (O.faithful a b).mp hadj with h | h
      · exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
      · exact ⟨(b, a), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
    obtain ⟨e, he⟩ := hex
    have hmem : e ∈ S.edges := List.mem_toFinset.mp (S.exhaustive.symm ▸ he)
    by_contra hlen
    have hempty : S.edges = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_not_pos hlen)
    simpa [hempty] using hmem

/-- The source's recursive BFS construction (PDF p.15, Supplementary Note A).
The frozen construction fixes the unspecified ties by the vertex labels. Its edge list
is chronological, reversing the paper's reverse-time, sink-first presentation. -/
def sourceAnsatz {N : ℕ} (G : SimpleGraph (Fin N)) (connected : G.Connected)
    (nonempty : 0 < N) (cubic : ∀ v, (Finset.univ.filter fun u => G.Adj v u).card = 3)
    (root : Fin N) : CubicAnsatz where
  N := N
  nonempty := nonempty
  G := G
  connected := connected
  cubic := cubic
  orientation := lightconeOrientation G connected root
  sequence := lightconeGateSequence G connected root
  positiveCut := (cubic_domains G connected nonempty cubic
    (lightconeOrientation G connected root) (lightconeGateSequence G connected root)).1






end QAlgorithms.Papers.RoadmapO18


