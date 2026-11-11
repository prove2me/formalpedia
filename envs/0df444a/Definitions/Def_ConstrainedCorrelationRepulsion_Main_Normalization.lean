-- Prove2me | Definitions.Def_ConstrainedCorrelationRepulsion_Main_Normalization
-- name    : ConstrainedCorrelationRepulsion_Main_Normalization
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:28:47.825191+00:00
-- url     : https://prove2.me/theorems/738561b0-472b-42f8-a202-53a38c4a7b44
-- title:
--   Fixed-cost relabelling, vertex removal and restoration
-- statement:
--   The fixed-cost step relabels positive cannot-link pairs as negative and records their number. Full normalization then removes zero-positive-degree vertices and relabels the remaining vertices in increasing order. Restoration gives removed vertices their own singleton clusters and transports all other labels back through that explicit enumeration.
--
--   Full normalization is invoked only in the no-must-link regime. At the end of preclustering only the relabelling step is used, so units and the entire vertex set are retained. The auxiliary normalization identity states the exact additive partition-cost and optimum identities.
-- source:
--   Yixin Cao, Ying Xu, Optimal Approximation for Constrained Correlation Clustering via Repulsion, STOC 2027 submission #869 (October 2026), Definition 3.1 and §4.2, printed pp.13, 20–21 (PDF pp.14, 21–22)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Repulsion

namespace ConstrainedCorrelationRepulsion.Main

open Classical

/-- Fixed-cost relabelling, retaining every vertex and unit. This is the normalization step
used at the end of Figure 4, and is different from full normalization below. -/
def relabelOnly {n : ℕ} (I : Instance n) : Instance n :=
  {I with positive := I.positive ⊓ I.cannotLinkᶜ}

noncomputable def remainingVertices {n : ℕ} (I : Instance n) : Finset (Fin n) :=
  Finset.univ.filter (fun v => 0 < positiveDegree (relabelOnly I) v Finset.univ)

/-- Increasing vertex enumeration: no arbitrary relabelling or choice of a partition. -/
noncomputable def retainedVertex {n : ℕ} (I : Instance n) :
    Fin (remainingVertices I).card → Fin n := fun v =>
  ((remainingVertices I).orderIsoOfFin rfl v : Fin n)

/-- Definition 3.1. Removal of zero-positive-degree vertices is used only in the no-must-link
regime; its domain is enforced at every invocation of full normalization in the pipeline. -/
noncomputable def normalize {n : ℕ} (I : Instance n) : Instance (remainingVertices I).card :=
  {positive := (relabelOnly I).positive.comap (retainedVertex I),
   mustLink := (relabelOnly I).mustLink.comap (retainedVertex I),
   cannotLink := (relabelOnly I).cannotLink.comap (retainedVertex I)}

noncomputable def restore {n : ℕ} (I : Instance n)
    (P : Partition (remainingVertices I).card) : Partition n := fun v =>
  if h : v ∈ remainingVertices I then
    retainedVertex I (P (((remainingVertices I).orderIsoOfFin rfl).symm ⟨v,h⟩))
  else v

noncomputable def normalizationCost {n : ℕ} (I : Instance n) : ℝ :=
  pairSum (fun u v => if I.positive.Adj u v ∧ I.cannotLink.Adj u v then 1 else 0)

end ConstrainedCorrelationRepulsion.Main


