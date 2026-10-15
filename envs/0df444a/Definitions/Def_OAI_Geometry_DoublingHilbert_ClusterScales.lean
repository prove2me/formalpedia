-- Prove2me | Definitions.Def_OAI_Geometry_DoublingHilbert_ClusterScales
-- name    : OAI_Geometry_DoublingHilbert_ClusterScales
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T07:03:39.218558+00:00
-- url     : https://prove2.me/theorems/71598735-8bf1-4e34-a53a-02b141c58c27
-- title:
--   Dyadic cluster scales $\sigma_j=2^{-(j+1)}$
-- statement:
--   For $j\in\mathbb{N}$ the cluster scale is
--   $$
--   \sigma_j=\Bigl(\frac12\Bigr)^{j+1}=2^{-(j+1)},
--   $$
--   so $\sigma_0=1/2$, $\sigma_{j+1}=\sigma_j/2$, and $\sigma_j\to0$ as $j\to\infty$.
--
--   These are the distances from the origin at which the successive finite clusters of the compact doubling set are placed: the $j$-th cluster lies within distance $\sigma_j/100$ of the point $\sigma_jv$ on the ray spanned by a fixed unit vector $v$. Because consecutive scales differ by the factor $2$, only boundedly many clusters are relevant at any given radius, which gives a uniform doubling constant for the union of the clusters, while $\sigma_j\to0$ makes that union together with the origin compact.
--
--   **Formalization Note** The scale is `clusterScale j = (1 / 2 : ℝ) ^ (j + 1)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/ClusterScales.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/ClusterScales.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CompactBanach mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CompactBanach
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids
import Definitions.Def_OAI_Geometry_DoublingHilbert_SelectedSheets
import Definitions.Def_OAI_Geometry_DoublingHilbert_Energy
import Definitions.Def_OAI_Geometry_DoublingHilbert_Crossings
import Definitions.Def_OAI_Geometry_DoublingHilbert_Doubling
import Definitions.Def_OAI_Geometry_DoublingHilbert_CoordinateSupport
import Definitions.Def_OAI_Geometry_DoublingHilbert_CoordinateMap
import Definitions.Def_OAI_Geometry_DoublingHilbert_IntrinsicCovers

namespace OAI

open Set Metric
open scoped BigOperators
open Filter
open scoped Topology
noncomputable section
namespace CompactBanach

def clusterScale (j : ℕ) : ℝ := (1 / 2 : ℝ) ^ (j + 1)

                                            
                                                                               
                                                                           
                                                                             
end CompactBanach
end

end OAI


