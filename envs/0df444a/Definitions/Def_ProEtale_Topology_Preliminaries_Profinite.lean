-- Prove2me | Definitions.Def_ProEtale_Topology_Preliminaries_Profinite
-- name    : ProEtale_Topology_Preliminaries_Profinite
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:01:28.051504+00:00
-- url     : https://prove2.me/theorems/e31dbfad-2259-4ed4-88b9-61d4d19d43b8
-- title:
--   Profinite spaces are prespectral and spectral
-- statement:
--   Let $T$ be a profinite space, i.e. a compact, Hausdorff, totally disconnected topological space. Then:
--   1. $T$ is prespectral: its compact open subsets form a basis (indeed the clopen subsets form a basis and are compact).
--   2. $T$ is a spectral space.
--
--   This allows profinite sets to be treated as spectral spaces, for instance in products $T \times X$ with a w-local space $X$.
--
--   **Formalization Note** The results are the instances `Prespectral.of_profinite` and `Spectral.of_profinite`, stated under `[T2Space T] [CompactSpace T] [TotallyDisconnectedSpace T]` with Mathlib's `PrespectralSpace` and `SpectralSpace`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Topology/Preliminaries/Profinite.lean (declarations needed by the transplanted proofs, unused ones removed).

/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.Spectral.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Profinite spaces are spectral

-/

instance Prespectral.of_profinite {T : Type*} [TopologicalSpace T] [T2Space T] [CompactSpace T]
  [TotallyDisconnectedSpace T] : PrespectralSpace T := by
  refine PrespectralSpace.of_isTopologicalBasis (B := { U : Set T | IsClopen U })
    (basis := isTopologicalBasis_isClopen (X := T)) ?_
  intro U hU
  exact hU.1.isCompact

instance Spectral.of_profinite {T : Type*} [TopologicalSpace T] [T2Space T] [CompactSpace T]
  [TotallyDisconnectedSpace T] : SpectralSpace T where


