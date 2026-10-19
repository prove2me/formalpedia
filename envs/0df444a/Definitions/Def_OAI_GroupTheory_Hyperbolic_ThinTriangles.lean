-- Prove2me | Definitions.Def_OAI_GroupTheory_Hyperbolic_ThinTriangles
-- name    : OAI_GroupTheory_Hyperbolic_ThinTriangles
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T07:16:52.29779+00:00
-- url     : https://prove2.me/theorems/3296934e-3aaf-41b7-89e9-980f4259528a
-- title:
--   Geodesic discrete spaces and paths outside a ball
-- statement:
--   Two notions for discrete metrics $d:V\times V\to\mathbb N$ with discrete paths.
--
--   1. **Geodesic spaces.** A discrete metric is geodesic if every pair of points is joined by a geodesic path, i.e. a path of length exactly $d(a,b)$. In that case a fixed choice of geodesic $\gamma_{a,b}$ is made for every pair, and
--   $$
--   \mathrm{length}(\gamma_{a,b})=d(a,b).
--   $$
--   2. **Outside a ball.** A path stays outside the open ball of radius $T$ around $o$ if every point $x$ on it satisfies
--   $$
--   d(o,x)\ge T .
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/ThinTriangles.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/ThinTriangles.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TorsionFreeHyperbolic mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation
import Definitions.Def_OAI_GroupTheory_Hyperbolic_WordPaths
import Definitions.Def_OAI_GroupTheory_Hyperbolic_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Planarity
import Definitions.Def_OAI_GroupTheory_Hyperbolic_RePairing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_TriangleFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Words
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Dipoles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Ribbons
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Links
import Definitions.Def_OAI_GroupTheory_Hyperbolic_LiftedFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Spheres
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullGluing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Chains
import Definitions.Def_OAI_GroupTheory_Hyperbolic_CyclicAction
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullChains
import Definitions.Def_OAI_GroupTheory_Hyperbolic_BasedWords
import Definitions.Def_OAI_GroupTheory_Hyperbolic_DiscreteMetric

namespace OAI

namespace Release075.Discrete
variable {V : Type} {M : Metric V}

def GeodesicSpace (M : Metric V) : Prop := ∀ a b, ∃ p : Path M a b, p.Geodesic

noncomputable def shortPath (h : GeodesicSpace M) (a b : V) : Path M a b := (h a b).choose

theorem shortPath_geodesic (h : GeodesicSpace M) (a b : V) : (shortPath h a b).Geodesic :=
  (h a b).choose_spec

@[simp] theorem shortPath_length (h : GeodesicSpace M) (a b : V) :
    (shortPath h a b).length = M.dist a b := shortPath_geodesic h a b

namespace Path
variable {a b c : V}

def Outside (p : Path M a b) (o : V) (T : ℕ) : Prop := ∀ x, p.Mem x → T ≤ M.dist o x

end Path

namespace Path
variable {a b c : V}

end Path
end Release075.Discrete

end OAI


