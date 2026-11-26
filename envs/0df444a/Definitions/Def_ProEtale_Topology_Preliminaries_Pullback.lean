-- Prove2me | Definitions.Def_ProEtale_Topology_Preliminaries_Pullback
-- name    : ProEtale_Topology_Preliminaries_Pullback
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:39:16.673323+00:00
-- url     : https://prove2.me/theorems/3c57f752-f64a-48b4-8656-c3ba4a223c75
-- title:
--   Fibre products of spectral spaces over a Hausdorff space are spectral
-- statement:
--   Let $f : X \to S$ and $g : Y \to S$ be continuous maps of topological spaces and $X \times_S Y$ their fibre product in the category of topological spaces, i.e. the subspace $\{(x,y) : f(x) = g(y)\}$ of $X \times Y$. This file records instances on separation and spectrality of the fibre product:
--
--   1. if $X$ and $Y$ are $T_0$, so is $X \times_S Y$ (no assumption on $S$);
--
--   and, assuming $S$ is Hausdorff (so that $X \times_S Y$ is closed in $X \times Y$):
--
--   2. if $X$ and $Y$ are quasi-sober, so is $X \times_S Y$;
--   3. if $X$ and $Y$ are compact, so is $X \times_S Y$;
--   4. if $X$ and $Y$ are prespectral, so is $X \times_S Y$;
--   5. if $X$ and $Y$ are **spectral**, so is $X \times_S Y$.
--
--   Each follows from the corresponding property of $X \times Y$ and the fact that a closed embedding inherits it.
--
--   These are used when forming fibre products of spectra over profinite (Hausdorff) spaces, e.g. of $\pi_0$ of spectral spaces.
--
--   **Formalization Note** All spaces are in `Type u` and the fibre product is `pullback (ofHom f) (ofHom g)` in `TopCat`. Instances: `T0Space.pullback`, `QuasiSober.pullback`, `CompactSpace.pullback`, `PrespectralSpace.pullback` and `SpectralSpace.pullback`. Items 2–5 assume `[T2Space S]`. The section also declares the variable `pb` for an arbitrary pullback square, which no declaration in this file uses.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Topology/Preliminaries/Pullback.lean (declarations needed by the transplanted proofs, unused ones removed).

/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Mathlib.Topology.Inseparable
import Mathlib.Topology.QuasiSeparated
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sober
import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Spectral.Prespectral
import Definitions.Def_ProEtale_Mathlib_Topology_Category_TopCat_Limits_Pullbacks
import Definitions.Def_ProEtale_Mathlib_Topology_Inseparable
import Definitions.Def_ProEtale_Mathlib_Topology_QuasiSeparated
import Definitions.Def_ProEtale_Mathlib_Topology_Separation_Hausdorff
import Definitions.Def_ProEtale_Mathlib_Topology_Sober
import Definitions.Def_ProEtale_Mathlib_Topology_Spectral_Basic
import Definitions.Def_ProEtale_Mathlib_Topology_Spectral_Prespectral

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
universe u

open CategoryTheory TopCat Limits

variable {X Y S : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace S]
variable (f : C(X, S)) (g : C(Y, S))

variable {P : Type u} [TopologicalSpace P] {f' : C(P, Y)} {g' : C(P, X)}
    (pb : IsPullback (ofHom g') (ofHom f') (ofHom f) (ofHom g))

section pullback

instance T0Space.pullback [T0Space X] [T0Space Y] (f : C(X, S)) (g : C(Y, S)) :
    T0Space (pullback (ofHom f) (ofHom g) : TopCat) :=
  (homeoOfIso (pullbackIsoProdSubtype (ofHom f) (ofHom g))).symm.t0Space

variable [T2Space S]

instance QuasiSober.pullback [QuasiSober X] [QuasiSober Y] (f : C(X, S)) (g : C(Y, S)) :
    QuasiSober (pullback (ofHom f) (ofHom g) : TopCat) :=
  let _ := (homeoOfIso (prodIsoProd (of X) (of Y))).symm.quasiSober
  (isClosedEmbedding_pullback_to_prod (ofHom f) (ofHom g)).quasiSober

instance CompactSpace.pullback [CompactSpace X] [CompactSpace Y] (f : C(X, S)) (g : C(Y, S)) :
    CompactSpace (pullback (ofHom f) (ofHom g) : TopCat) :=
  let _ := (homeoOfIso (prodIsoProd (of X) (of Y))).symm.compactSpace
  (isClosedEmbedding_pullback_to_prod (ofHom f) (ofHom g)).compactSpace

instance PrespectralSpace.pullback [PrespectralSpace X] [PrespectralSpace Y]
    (f : C(X, S)) (g : C(Y, S)) :
    PrespectralSpace (pullback (ofHom f) (ofHom g) : TopCat) :=
  let _ := (homeoOfIso (prodIsoProd (of X) (of Y))).symm.prespectralSpace
  PrespectralSpace.of_isClosedEmbedding _ (isClosedEmbedding_pullback_to_prod (ofHom f) (ofHom g))

instance SpectralSpace.pullback [SpectralSpace X] [SpectralSpace Y] (f : C(X, S)) (g : C(Y, S)) :
    SpectralSpace (pullback (ofHom f) (ofHom g) : TopCat) :=
  let _ := (homeoOfIso (prodIsoProd (of X) (of Y))).symm.spectralSpace
  (isClosedEmbedding_pullback_to_prod (ofHom f) (ofHom g)).spectralSpace

end pullback


