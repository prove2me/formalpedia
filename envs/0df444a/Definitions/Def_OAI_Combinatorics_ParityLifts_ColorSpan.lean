-- Prove2me | Definitions.Def_OAI_Combinatorics_ParityLifts_ColorSpan
-- name    : OAI_Combinatorics_ParityLifts_ColorSpan
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:27:51.887983+00:00
-- url     : https://prove2.me/theorems/a2ae334d-a871-489a-ac94-75f29595402a
-- title:
--   Atomic types and Weisfeiler–Leman colours of tuples from two graphs on a common domain
-- statement:
--   Let $G$ and $H$ be simple graphs on finite sets $V$ and $W$, and let $\mathcal T_k=V^k\sqcup W^k$. For a $k$-tuple $x$ of vertices of a graph $G$, the atomic type $\operatorname{atp}_G(x)$ records, for every ordered pair of positions $i,j<k$, the truth values of $x_i=x_j$ and of $x_ix_j\in E(G)$. For $r\ge0$ the joint and the separate colours are defined recursively by $\chi^{\mathrm J}_{0}=\chi^{\mathrm S}_{0}=\operatorname{atp}_G$ and
--   $$
--   \chi^{\mathrm J}_{r+1}(x)=\Bigl(\chi^{\mathrm J}_{r}(x),\ \{\!\{(\chi^{\mathrm J}_{r}(x[i\mapsto y]))_{i<k} : y\in V\}\!\}\Bigr),\qquad\chi^{\mathrm S}_{r+1}(x)=\Bigl(\chi^{\mathrm S}_{r}(x),\ \bigl(\{\!\{\chi^{\mathrm S}_{r}(x[i\mapsto y]) : y\in V\}\!\}\bigr)_{i<k}\Bigr),
--   $$
--   where $\{\!\{\cdots\}\!\}$ denotes a multiset and $x[i\mapsto y]$ replaces the $i$-th entry of $x$ by $y$. These are the folklore and the oblivious variants of $k$-dimensional Weisfeiler–Leman refinement. This module evaluates the invariants on both graphs at once:
--
--   1. **Atomic type of a tuple of either graph.** The map $\operatorname{atp}$ on $\mathcal T_k$ equals $\operatorname{atp}_G$ on $V^k$ and $\operatorname{atp}_H$ on $W^k$.
--
--   2. **Joint colour.** For each round $r$, the map $\chi^{\mathrm J}_r$ on $\mathcal T_k$ is the joint colouring of $G$ on $V^k$ and that of $H$ on $W^k$; both take values in the same set of round-$r$ joint colours.
--
--   3. **Separate colour.** For each round $r$, the map $\chi^{\mathrm S}_r$ on $\mathcal T_k$ is defined in the same way from the separate colourings.
--
--   4. **Boolean indicator.** The rational number $[b]$ of a truth value $b$ is $1$ if $b$ is true and $0$ otherwise.
--
--   Because the colours of both graphs live in one set, the two colour histograms can be compared through indicator functions on the common domain $\mathcal T_k$: the histograms of $G$ and $H$ agree as soon as every colour-class indicator lies in a space of functions whose sums over $V^k$ and over $W^k$ coincide. The parity reduction applies this to the span of rooted homomorphism counts.
--
--   **Formalization Note** The maps are `pairAtomic`, `pairJoint k r` and `pairSeparate k r`, defined by `Sum.elim` from `atomicType`, `jointColor` and `separateColor`; `boolIndicator` is the indicator of a `Bool` in $\mathbb{Q}$. The colour types `JointColor k r` and `SeparateColor k r` are defined recursively by round, with multisets taken over `Finset.univ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/ColorSpan.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/ColorSpan.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ParityLifts mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts
import Definitions.Def_OAI_Combinatorics_ParityLifts_WeightedDual
import Definitions.Def_OAI_Combinatorics_ParityLifts_Masses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BaseLabels
import Definitions.Def_OAI_Combinatorics_ParityLifts_BalancedBags
import Definitions.Def_OAI_Combinatorics_ParityLifts_DecompositionCuts
import Definitions.Def_OAI_Combinatorics_ParityLifts_Witnesses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BagTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_TagSizes
import Definitions.Def_OAI_Combinatorics_ParityLifts_Detection
import Definitions.Def_OAI_Combinatorics_ParityLifts_RankedTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_RootedTests
import Definitions.Def_OAI_Combinatorics_ParityLifts_GlueTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_GlueVertices
import Definitions.Def_OAI_Combinatorics_ParityLifts_Rerooting
import Definitions.Def_OAI_Combinatorics_ParityLifts_TestAlgebra
import Definitions.Def_OAI_Combinatorics_ParityLifts_Interpolation

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace ParityWL

open scoped BigOperators

section ColorSpan

open scoped Classical

variable {V W : Type} [Fintype V] [Fintype W]
variable (G : SimpleGraph V) (H : SimpleGraph W)

noncomputable def pairAtomic {k : ℕ} : TuplePair V W k → AtomicType k :=
  Sum.elim (atomicType G) (atomicType H)

noncomputable def pairJoint (k r : ℕ) : TuplePair V W k → JointColor k r :=
  Sum.elim (jointColor G k r) (jointColor H k r)

noncomputable def pairSeparate (k r : ℕ) : TuplePair V W k → SeparateColor k r :=
  Sum.elim (separateColor G k r) (separateColor H k r)

def boolIndicator (b : Bool) : ℚ := if b then 1 else 0

end ColorSpan

section SpanHistograms

open scoped Classical

variable {V W X Y D : Type} [Fintype V] [Fintype W] [Fintype X] [Fintype Y]
variable (G : SimpleGraph V) (H : SimpleGraph W) {k t : ℕ}
variable (l : X → TuplePair V W k) (r : Y → TuplePair V W k)

end SpanHistograms

end ParityWL

end OAI


