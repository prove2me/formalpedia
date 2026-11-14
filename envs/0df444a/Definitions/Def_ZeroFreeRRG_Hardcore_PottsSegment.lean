-- Prove2me | Definitions.Def_ZeroFreeRRG_Hardcore_PottsSegment
-- name    : ZeroFreeRRG_Hardcore_PottsSegment
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T08:57:57.692206+00:00
-- url     : https://prove2.me/theorems/d44e05dc-738b-4dd6-ba1c-9300e6d2050a
-- title:
--   Potts edge weights on a common segment
-- statement:
--   Every edge interaction entry lies on the complex segment from $1$ to $\beta$.
-- source:
--   Auxiliary definition for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Lemma 5.7.

import Definitions.Def_ZeroFreeRRG_Hardcore_PottsWeighted
import Mathlib
open Set
namespace ZeroFreeRRG.Hardcore

open Classical in
/-- Every edge interaction entry lies on the segment from one to beta. -/
noncomputable def pottsSegmentWeights {V : Type} [Fintype V] (q : ℕ) (G : SimpleGraph V) (β : ℂ)
    (W : Sym2 V → Fin q → Fin q → ℂ) : Prop :=
  ∀ e ∈ G.edgeFinset, ∀ i j, ∃ t : ℝ, t ∈ Icc 0 1 ∧ W e i j = 1+(t:ℂ)*(β-1)

end ZeroFreeRRG.Hardcore


