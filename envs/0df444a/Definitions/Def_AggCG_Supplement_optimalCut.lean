-- Prove2me | Definitions.Def_AggCG_Supplement_optimalCut
-- name    : AggCG_Supplement_optimalCut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T23:22:47.129969+00:00
-- url     : https://prove2.me/theorems/8fa0c6b3-9c04-4dc6-870e-5b29b6b83572
-- title:
--   Deterministically tie-broken minimum cut
-- statement:
--   Given a finite feasible cut family and edge weights, the selected optimal cut minimizes the sum of the weights of its edges. A fixed deterministic tie rule chooses one cut whenever several cuts attain the minimum.
-- source:
--   Sharma, STOC 2027 submission (manuscript sha256 f7ea0248…), §E.4, p.33, PDF p.34

import Mathlib

namespace AggCG.Supplement

/-- A deterministic tie rule for minimum cuts: it returns one member of any nonempty set of tied cuts
(Sharma, *Computational Complexity of Data-Driven Configuration for Integer Programming, Clustering, and
Learning Algorithms*, STOC 2027 submission (manuscript sha256 f7ea0248…), §E.4, p.33, PDF p.34: "with
deterministic tie breaking").

**Formalization Note** The rule depends only on the set of tied cuts, not on the parameter `s`. -/
structure CutTieRule (E : Type*) where
  /-- The chosen cut. -/
  pick : Finset (Finset E) → Finset E
  /-- It is one of the tied cuts. -/
  pick_mem : ∀ S, S.Nonempty → pick S ∈ S

open Classical in
/-- The optimal cut `C_s ∈ argmin_{C ∈ 𝒞} W_C(s)` for the edge weights `w`, with `W_C = Σ_{e∈C} w_e`,
chosen by the tie rule among all minimizers (§E.4, p.33). -/
noncomputable def optimalCut {E : Type*} (𝒞 : Finset (Finset E)) (tie : CutTieRule E) (w : E → ℝ) :
    Finset E :=
  if h : 𝒞.Nonempty then
    tie.pick (𝒞.filter fun C => ∑ e ∈ C, w e = 𝒞.inf' h fun C' => ∑ e ∈ C', w e)
  else ∅

end AggCG.Supplement


