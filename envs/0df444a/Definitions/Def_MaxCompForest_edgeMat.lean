-- Prove2me | Definitions.Def_MaxCompForest_edgeMat
-- name    : MaxCompForest_edgeMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:22.446244+00:00
-- url     : https://prove2.me/theorems/98892075-f07f-4f43-8e9c-f2ecdbb74106
-- title:
--   The edge form $C^{1/2}B^{\top}MBC^{1/2}$
-- statement:
--   For a matrix $M$ indexed by vertices, the matrix indexed by edge labels
--   $$
--   C_E^{1/2}\,B^{\top}MB\,C_E^{1/2},
--   $$
--   where $B$ is the oriented incidence matrix (vertices $\times$ edges) and $C_E=\mathrm{diag}(c_e)$. With $M=L^{+}$ it is the transfer-current kernel; with $M=D^{-1}+R$ it is the slow-response approximation.
--
--   **Formalization Note** Lean's published incidence matrix is indexed edges $\times$ vertices, so it plays the role of $B^\top$. The form does not change when an edge is reoriented.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), (3.2) p.14, (E.7)–(E.8) p.39

import Mathlib
import Definitions.Def_EffResSparsify_ResistanceSketch_Graph
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- **The edge-indexed form** `C_E^{1/2} Bᵀ M B C_E^{1/2}` of a vertex matrix `M`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), (3.2) p.14, (E.7)–(E.8) p.39, (E.15) p.40.

**Formalization Note.** In the paper `B` is vertices × edges. The published `incidence` is
edges × vertices, so the paper's `Bᵀ` is `G.incidence` here. The form does not depend on the orientation
chosen for an edge. -/
noncomputable def edgeMat (G : WGraph V E) (M : Matrix V V ℝ) : Matrix E E ℝ :=
  Matrix.diagonal (fun e => Real.sqrt (G.w e)) * G.incidence * M * G.incidence.transpose *
    Matrix.diagonal (fun e => Real.sqrt (G.w e))

end MaxCompForest


