-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingConversion__MatchingAffineLift
-- name    : OAI_Combinatorics_MatchingPSD_MatchingConversion__MatchingAffineLift
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T14:04:01.173368+00:00
-- url     : https://prove2.me/theorems/71b75cbe-49fa-46da-8fc2-b8bd58f29563
-- title:
--   From fixed-point-free involutions of $\{0,\dots,n-1\}$ to perfect matchings
-- statement:
--   This file converts pairings of the vertex set $\{0,\dots,n-1\}$ into perfect matchings in the edge-set form used in the slack matrix.
--
--   **Perfect matchings of $K_n$.** An *edge* on the vertex set $\{0,\dots,n-1\}$ is a pair $(u,v)$ with $u<v$, and a *perfect matching* is a set $\mathcal M$ of edges such that every vertex lies in exactly one edge of $\mathcal M$. A *pairing* of a set $X$ is a permutation $M$ of $X$ with $M(M(a))=a$ and $M(a)\neq a$ for every $a\in X$, that is, a perfect matching of $X$ in which every $a$ is matched to its partner $M(a)$.
--
--   1. **The edge at a vertex.** For a pairing $M$ of $\{0,\dots,n-1\}$ and a vertex $v$,
--   $$
--   e_M(v)=\bigl(\min(v,M(v)),\ \max(v,M(v))\bigr),
--   $$
--   the edge joining $v$ and its partner (well defined since $M(v)\neq v$). One has $e_M(M(v))=e_M(v)$, $v$ is an endpoint of $e_M(v)$, $M$ maps the first endpoint of $e_M(v)$ to the second, and every edge $(u,u')$ with $M(u)=u'$ that contains $v$ equals $e_M(v)$.
--   2. **The perfect matching of a pairing.**
--   $$
--   \mathcal M(M)=\{(u,u'):\ u<u',\ M(u)=u'\},
--   $$
--   which is a perfect matching: the edges of $\mathcal M(M)$ containing a vertex $v$ are exactly $e_M(v)$. Membership is characterised by $(u,u')\in\mathcal M(M)\Leftrightarrow M(u)=u'$.
--
--   Pairings are convenient for symmetrisation, because permutations act on them by conjugation; this conversion translates statements about pairings back into the language of the slack matrix, whose columns are perfect matchings. Since $M$ and $\mathcal M(M)$ have the same edges, the number of edges of $\mathcal M(M)$ crossing a vertex set $U$ equals the number of vertices of $U$ whose partner lies outside $U$.
--
--   **Formalization Note** `Edge n` is the subtype of `Fin n × Fin n` with first component smaller than the second, and `PerfectMatching n` is the subtype of `Finset (Edge n)` in which each vertex lies in exactly one edge. The Lean names are `pairingEdge` and `fromPairing`; `pairingEdge_partner`, `pairingEdge_incident`, `pairingEdge_mem`, `eq_pairingEdge` and `mem_fromPairing` are the lemmas listed in item 1 and the membership criterion.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/MatchingConversion.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/MatchingConversion.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MatchingAffineLift mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PSDEvaluation
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Model
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SpectralContraction__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EquivariantCompression__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialSpaces__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_FiberAverages__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ScalarSmoothing__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeMonomials__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PartialColorings__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableCoordinates__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TablePolynomials__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PermutationSmoothing__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingFibers__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_GlobalGeometry__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_AdmissibleTables__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CutGeometry__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CellAverages__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SequentialTests__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatrixAverages__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialInterpolation__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatrixInterpolation__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_GoodCells__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CellDecoder__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_AffineSlacks

namespace OAI

namespace PerfectMatchingPSD
open MatchingSmoothing
attribute [local instance] Classical.propDecidable

noncomputable def pairingEdge {n : ℕ} (M : Pairing (Fin n)) (v : Fin n) : Edge n :=
  if h : v < M.1 v then ⟨(v,M.1 v),h⟩ else
    ⟨(M.1 v,v),lt_of_le_of_ne (le_of_not_gt h) (M.partner_ne v)⟩

lemma pairingEdge_partner {n : ℕ} (M : Pairing (Fin n)) (v : Fin n) :
    pairingEdge M (M.1 v) = pairingEdge M v := by
  by_cases h : v < M.1 v
  · simp [pairingEdge, h, M.partner_partner, not_lt.mpr h.le]
  · have h' : M.1 v < v := lt_of_le_of_ne (le_of_not_gt h) (M.partner_ne v)
    simp [pairingEdge, h, h', M.partner_partner]

lemma pairingEdge_incident {n : ℕ} (M : Pairing (Fin n)) (v : Fin n) :
    (pairingEdge M v).1.1 = v ∨ (pairingEdge M v).1.2 = v := by
  unfold pairingEdge
  split_ifs <;> simp

lemma pairingEdge_mem {n : ℕ} (M : Pairing (Fin n)) (v : Fin n) :
    M.1 (pairingEdge M v).1.1 = (pairingEdge M v).1.2 := by
  unfold pairingEdge
  split_ifs <;> simp

lemma eq_pairingEdge {n : ℕ} (M : Pairing (Fin n)) (e : Edge n) (hM : M.1 e.1.1 = e.1.2)
    (v : Fin n) (hv : e.1.1 = v ∨ e.1.2 = v) : e = pairingEdge M v := by
  have he : e = pairingEdge M e.1.1 := by
    simp only [pairingEdge, hM, e.2, dite_true]
  rcases hv with rfl | rfl
  · exact he
  · rw [← hM, pairingEdge_partner]
    exact he

noncomputable def fromPairing {n : ℕ} (M : Pairing (Fin n)) : PerfectMatching n :=
  ⟨Finset.univ.filter (fun e : Edge n => M.1 e.1.1 = e.1.2), by
    intro v
    apply Finset.card_eq_one.mpr
    refine ⟨pairingEdge M v, ?_⟩
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨hM,hv⟩
      exact eq_pairingEdge M e hM v hv
    · rintro rfl
      exact ⟨pairingEdge_mem M v, pairingEdge_incident M v⟩⟩

@[simp] lemma mem_fromPairing {n : ℕ} (M : Pairing (Fin n)) (e : Edge n) :
    e ∈ (fromPairing M).1 ↔ M.1 e.1.1 = e.1.2 := by
  simp [fromPairing]

end PerfectMatchingPSD

end OAI


