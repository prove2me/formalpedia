-- Prove2me | Definitions.Def_BundleGerbeStable_Iso
-- name    : BundleGerbeStable_Iso
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:44:55.259729+00:00
-- url     : https://prove2.me/theorems/5ab7fbe1-5e33-4c89-a796-47fdcf1873d1
-- title:
--   Isomorphisms of bundle gerbes
-- statement:
--   An **isomorphism** of bundle gerbes from $(P,Y)$ to $(Q,Z)$ is a diffeomorphism $f : Y\to Z$ commuting with the projections to $M$, together with a $\mathbb C^\times$-equivariant diffeomorphism $g : P\to Q$ covering $f^{[2]} : Y^{[2]}\to Z^{[2]}$ and commuting with the products. The two gerbes may lie over different locally split maps.
--
--   This is the equality meant in the definition of stable isomorphism.
-- source:
--   Murray, Stevenson, Bundle gerbes: stable isomorphism and local theory, arXiv:math/9908135v1, https://arxiv.org/abs/math/9908135v1, §2, p.3 (isomorphic bundle gerbes)

import Mathlib
import Definitions.Def_BundleGerbeStable_BundleGerbe

open Diffeology

namespace BundleGerbeStable

universe u

variable {M : Type u} [TopologicalSpace M] [DiffeologicalSpace M]

/-- An **isomorphism of bundle gerbes** `(P, Y) → (Q, Z)` (Murray, Stevenson, *Bundle gerbes: stable
isomorphism and local theory*, arXiv:math/9908135v1, §2, p.3): "an isomorphism f : Y → Z, commuting
with the projection to M and a bundle isomorphism g : P → Q covering the induced map f^[2] : Y^[2] →
Z^[2] and commuting with the bundle gerbe products". `P` and `Q` may lie over different locally split
maps.

**Formalization Note.** Isomorphisms in the diffeological category are diffeomorphisms: an equivalence
that is `DSmooth` in both directions. -/
structure Iso {S T : LocallySplit M} (P : BundleGerbe S) (Q : BundleGerbe T) where
  /-- The isomorphism `f : Y → Z`. -/
  f : S.Y ≃ T.Y
  f_smooth : DSmooth f
  f_symm_smooth : DSmooth f.symm
  f_π : ∀ y, T.π (f y) = S.π y
  /-- The bundle isomorphism `g : P → Q`. -/
  g : P.bdl.P ≃ Q.bdl.P
  g_smooth : DSmooth g
  g_symm_smooth : DSmooth g.symm
  g_smul : ∀ (z : ℂˣ) p, g (z • p) = z • g p
  g_src : ∀ p, Q.bdl.src (g p) = f (P.bdl.src p)
  g_tgt : ∀ p, Q.bdl.tgt (g p) = f (P.bdl.tgt p)
  g_mul : ∀ p q h h', g (P.mul p q h) = Q.mul (g p) (g q) h'

end BundleGerbeStable


