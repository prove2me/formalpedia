-- Prove2me | Definitions.Def_ProEtale_Topology_SpectralSpace_WLocal_ClosedPoints
-- name    : ProEtale_Topology_SpectralSpace_WLocal_ClosedPoints
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:40:44.885406+00:00
-- url     : https://prove2.me/theorems/5ca49f76-ae81-50f5-8e35-27b8014dbeb3
-- title:
--   The closed points of a w-local space form a compact spectral T1 space
-- statement:
--   Let $X$ be a topological space and $X^c \subseteq X$ its subspace of closed points.
--
--   Principal results:
--   1. If $X$ is w-local, then $X^c$ is a spectral space, since it is a closed subspace of a spectral space.
--   2. For any topological space $X$, the subspace $X^c$ is $T_1$.
--   3. If $X$ is w-local, then $X^c$ is compact.
--
--   Combined with the fact that $T_1$ spectral spaces are totally separated, this shows that the closed points of a w-local space form a profinite space, as the module title says. That profinite space is used in constructing w-contractible covers.
--
--   **Formalization Note** The instances are `WLocalSpace.spectralSpace_closedPoints`, `WLocalSpace.t1Space_closedPoints` (no hypothesis on $X$) and `WLocalSpace.CompactSpace_closedPoints`, all for the subtype `closedPoints X`. `WLocalSpace` is the project class from the published w-local spaces file. Profiniteness itself is not stated as a single declaration here.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Topology/SpectralSpace/WLocal/ClosedPoints.lean (declarations needed by the transplanted proofs, unused ones removed).

/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Mathlib.Data.Set.Card
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Inseparable
import Mathlib.Topology.JacobsonSpace
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.QuasiSeparated
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Sober
import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Spectral.ConstructibleTopology
import Mathlib.Topology.Spectral.Prespectral
import Definitions.Def_ProEtale_Mathlib_Topology_Inseparable
import Definitions.Def_ProEtale_Mathlib_Topology_JacobsonSpace
import Definitions.Def_ProEtale_Mathlib_Topology_QuasiSeparated
import Definitions.Def_ProEtale_Mathlib_Topology_Separation_Basic
import Definitions.Def_ProEtale_Mathlib_Topology_Sober
import Definitions.Def_ProEtale_Mathlib_Topology_Spectral_Basic
import Definitions.Def_ProEtale_Mathlib_Topology_Spectral_ConstructibleTopology
import Definitions.Def_ProEtale_Mathlib_Topology_Spectral_Prespectral
import Definitions.Def_ProEtale_Topology_SpectralSpace_Constructible
import Definitions.Def_ProEtale_Topology_SpectralSpace_WLocal_Basic
import Definitions.Def_ProEtale_Topology_SpectralSpace_WLocal_Basic_Lib

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Closed Points of w-local spaces is profinite

-/

variable {X : Type*} [TopologicalSpace X]

namespace WLocalSpace

instance spectralSpace_closedPoints [WLocalSpace X] : SpectralSpace (closedPoints X) :=
  SpectralSpace.of_isClosed X

instance t1Space_closedPoints : T1Space (closedPoints X) where
  t1 := closedPoints.isClosed_singleton

instance CompactSpace_closedPoints [WLocalSpace X] :
    CompactSpace (closedPoints X) :=
  (IsClosed.isClosedEmbedding_subtypeVal inferInstance).compactSpace

end WLocalSpace


