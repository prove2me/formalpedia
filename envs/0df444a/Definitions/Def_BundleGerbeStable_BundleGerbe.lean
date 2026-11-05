-- Prove2me | Definitions.Def_BundleGerbeStable_BundleGerbe
-- name    : BundleGerbeStable_BundleGerbe
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:44:03.175834+00:00
-- url     : https://prove2.me/theorems/ce01425a-443a-4588-af51-46a879042de5
-- title:
--   Bundle gerbes over $M$, and the dual bundle gerbe
-- statement:
--   A **bundle gerbe** over $M$ is a pair $(P,Y)$ where $\pi : Y\to M$ is locally split and $P\to Y^{[2]}$ is a principal $\mathbb C^\times$ bundle with a product: a smooth, $\mathbb C^\times$-equivariant, associative map
--   $$P_{(y_1,y_2)}\otimes P_{(y_2,y_3)}\to P_{(y_1,y_3)}.$$
--   Concretely, it is a smooth map $(p,q)\mapsto pq$ on pairs with $p$ over $(y_1,y_2)$ and $q$ over $(y_2,y_3)$, with $pq$ over $(y_1,y_3)$, $(zp)q=z(pq)=p(zq)$ and $(pq)r=p(qr)$.
--
--   The **dual** $(P^*,Y)$ is the same space and product with the action through $z\mapsto z^{-1}$.
--
--   This is the central object of the paper.
--
--   **Formalization Note.** A map out of the contracted product is, by its universal property, a balanced map on composable pairs. Identities and inverses are not fields, because the paper notes (p.3) that the product determines them uniquely.
-- source:
--   Murray, Stevenson, Bundle gerbes: stable isomorphism and local theory, arXiv:math/9908135v1, https://arxiv.org/abs/math/9908135v1, §2, pp.2–3 (definition of a bundle gerbe; dual)

import Mathlib
import Definitions.Def_BundleGerbeStable_CxBundle
import Definitions.Def_BundleGerbeStable_LocallySplit

open Diffeology

namespace BundleGerbeStable

universe u

variable {M : Type u} [TopologicalSpace M] [DiffeologicalSpace M] {S : LocallySplit M}

/-- The first point `y₁` of `(y₁, y₂) = proj p`, for `p` in a bundle over `Y^[2]`. -/
def CxBundle.src (B : CxBundle (FibreProd S S)) (p : B.P) : S.Y := (B.proj p).1.1

/-- The second point `y₂` of `(y₁, y₂) = proj p`, for `p` in a bundle over `Y^[2]`. -/
def CxBundle.tgt (B : CxBundle (FibreProd S S)) (p : B.P) : S.Y := (B.proj p).1.2

/-- A **bundle gerbe** over `M` (Murray, Stevenson, *Bundle gerbes: stable isomorphism and local
theory*, arXiv:math/9908135v1, §2, pp.2–3): a ℂ× bundle `P → Y^[2]`, for `π : Y → M` locally split,
with a smooth, ℂ×-equivariant, associative product `P_(y₁,y₂) ⊗ P_(y₂,y₃) → P_(y₁,y₃)`.

**Formalization Note.** A map out of the contracted product is, by its universal property, a map on
composable pairs `(p, q)` with `mul (z • p) q = z • mul p q = mul p (z • q)`. Smoothness of the product,
which the paper refers to [11] for, is `DSmooth` of `mul` on the subspace of composable pairs.
Identities and inverses are not fields: p.3 says the product determines them. The composability proof
is an argument of `mul`; the axioms quantify over all such proofs, which is harmless since a proposition
has at most one proof. -/
structure BundleGerbe (S : LocallySplit M) where
  /-- The ℂ× bundle `P → Y^[2]`. -/
  bdl : CxBundle (FibreProd S S)
  /-- The product `P_(y₁,y₂) ⊗ P_(y₂,y₃) → P_(y₁,y₃)`, as a balanced map on composable pairs. -/
  mul : (p q : bdl.P) → bdl.tgt p = bdl.src q → bdl.P
  mul_smooth : DSmooth (fun r : {r : bdl.P × bdl.P // bdl.tgt r.1 = bdl.src r.2} ↦
    mul r.1.1 r.1.2 r.2)
  src_mul : ∀ p q h, bdl.src (mul p q h) = bdl.src p
  tgt_mul : ∀ p q h, bdl.tgt (mul p q h) = bdl.tgt q
  mul_smul_left : ∀ (z : ℂˣ) p q h h', mul (z • p) q h' = z • mul p q h
  mul_smul_right : ∀ (z : ℂˣ) p q h h', mul p (z • q) h' = z • mul p q h
  mul_assoc : ∀ p q r h₁ h₂ h₃ h₄, mul (mul p q h₁) r h₂ = mul p (mul q r h₃) h₄

/-- The **dual** bundle gerbe `(P*, Y)` (arXiv:math/9908135v1, §2, p.3): "by taking the dual of P". The
space and the product are those of `P`, with the action through `z ↦ z⁻¹`. -/
def BundleGerbe.dual (P : BundleGerbe S) : BundleGerbe S where
  bdl := P.bdl.dual
  mul := P.mul
  mul_smooth := P.mul_smooth
  src_mul := P.src_mul
  tgt_mul := P.tgt_mul
  mul_smul_left := fun z p q h h' ↦ P.mul_smul_left z⁻¹ p q h h'
  mul_smul_right := fun z p q h h' ↦ P.mul_smul_right z⁻¹ p q h h'
  mul_assoc := P.mul_assoc

end BundleGerbeStable


