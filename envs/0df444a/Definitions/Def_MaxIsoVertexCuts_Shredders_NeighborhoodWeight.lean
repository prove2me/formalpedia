-- Prove2me | Definitions.Def_MaxIsoVertexCuts_Shredders_NeighborhoodWeight
-- name    : MaxIsoVertexCuts_Shredders_NeighborhoodWeight
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:49:01.281318+00:00
-- url     : https://prove2.me/theorems/d1a02ffd-67d4-42f4-ae19-295f678314fe
-- title:
--   NeighborhoodWeight
-- statement:
--   For finite labelled vertices, the open neighbourhood is the published HypRecov.nbhd. The closed neighbourhood is X ∪ N(X), the exterior is V minus that closed neighbourhood, and weight and boundary weight are sums of vertex weights. Positive means every vertex has strictly positive real weight. Section 2 and Proposition 3.3, printed pp.16–17 (PDF 18–19).
-- source:
--   Fischer and Yingchareonthawornchai, Maximal Isolating Vertex Cuts and Shredders: Structure and Applications, STOC 2027 submission, Sections 2–5; machine conventions specified in the mission.

import Mathlib
import Definitions.Def_HypRecov_IsCompOf

open Classical
open scoped BigOperators
noncomputable section

namespace MaxIsoVertexCuts.Shredders

abbrev VSet (n : ℕ) := Finset (Fin n)
noncomputable def closedNbhd {n : ℕ} (G : SimpleGraph (Fin n)) (X : VSet n) : VSet n :=
  X ∪ HypRecov.nbhd G X
noncomputable def exterior {n : ℕ} (G : SimpleGraph (Fin n)) (X : VSet n) : VSet n :=
  Finset.univ \ closedNbhd G X
noncomputable def weight {n : ℕ} (w : Fin n → ℝ) (X : VSet n) : ℝ := ∑ v ∈ X, w v
noncomputable def boundaryWeight {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℝ)
    (X : VSet n) : ℝ := weight w (HypRecov.nbhd G X)
def Positive {n : ℕ} (w : Fin n → ℝ) : Prop := ∀ v, 0 < w v

end MaxIsoVertexCuts.Shredders


