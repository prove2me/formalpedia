-- Prove2me | Definitions.Def_N25_CanonicalSchemePoints
-- name    : N25_CanonicalSchemePoints
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:03:36.747528+00:00
-- url     : https://prove2.me/theorems/09a2093c-ef58-41cf-97e4-bd0852c92ad3
-- title:
--   Rational scheme sections of the canonical projective curve
-- statement:
--   For a field $K$, the file defines the carrier of canonical scheme points to be the sections $$\{s:\operatorname{Spec}K→X_K\mid s\circ\pi=\operatorname{id}_{\operatorname{Spec}K}\},$$ where $\pi:X_K→\operatorname{Spec}K$ is the canonical structure morphism. This is the intrinsic scheme-theoretic notion of a $K$-rational point used in the point/place equivalence.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalProjectiveCone
/-! Rational scheme sections of the selected literal canonical projective model. -/
noncomputable section
universe u
namespace N25.Endgame
open AlgebraicGeometry CategoryTheory N25

abbrev CanonicalSchemePoint25 (K : Type u) [Field K] :=
  {s : Spec (CommRingCat.of K) ⟶ CanonicalProjectiveCurve25 K //
    s ≫ canonicalProjectiveCurveToSpec25 K = 𝟙 _}

end N25.Endgame


