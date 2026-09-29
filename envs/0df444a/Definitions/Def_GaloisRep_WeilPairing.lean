-- Prove2me | Definitions.Def_GaloisRep_WeilPairing
-- name    : GaloisRep_WeilPairing
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/7b71ea6a-f13c-5a7c-a3fb-0980587d6a55
-- title:
--   Axiomatic mod-n Weil pairing on torsion points
-- statement:
--   The standing context is a Weierstrass curve `W'` in affine form over a commutative ring $R$, a commutative ring $S$ and a field $K$, with algebra maps $R \to S$, $R \to K$, $S \to K$ forming a scalar tower, so that the group $(W'⁄K).Point$ of affine points of the base change of `W'` to $K$ carries the action $\sigma \bullet P =$ `Point.map` $\sigma$ $P$ of the group $K \simeq_{\mathrm{alg}[S]} K$ of $S$-algebra automorphisms of $K$ introduced in the imported torsion/Galois-action module; the $n$-torsion is realised as `Submodule.torsionBy ℤ (W'⁄K).Point n`, the submodule of points annihilated by $n$, which is a $\mathbb{Z}/n$-module stable under that action.
--
--   The structure `IsWeilPairing S W' n B` is a `Prop`-valued predicate on an arbitrary function $B$ of two $n$-torsion variables with values in $K^\times$ (a bare two-variable function, not a bilinear map), carrying five axioms as fields: every value $B(P,Q)$ lies in `rootsOfUnity n K`, i.e. in $\mu_n(K)$; $B$ is additive in the first variable, $B(P+P',Q) = B(P,Q)\,B(P',Q)$; additive in the second variable, $B(P,Q+Q') = B(P,Q)\,B(P,Q')$; alternating in the strong sense $B(P,P) = 1$ for all $P$ (whence antisymmetry); equivariant, in the form that for every $\sigma : K \simeq_{\mathrm{alg}[S]} K$ and all $P,Q$ the image under $\sigma$ of $B(P,Q)$, viewed in $K$, equals $B(\sigma \bullet P, \sigma \bullet Q)$; and nondegenerate only in the weak sense that there exist $P,Q$ with $B(P,Q) \neq 1$, i.e. that $B$ is not identically trivial.
--
--   The definition `HasWeilPairing S K W' n` is the existential statement that some such $B$ exists, i.e. $\exists B,\$`IsWeilPairing S W' n B`.
--
--   **Relation to Mathlib.** Mathlib supplies the Weierstrass-curve point groups and `Submodule.torsionBy`, and `rootsOfUnity`, but no Weil pairing on the torsion of a Weierstrass curve; the predicate and its existential form are the project's own, and the Galois action used in the equivariance axiom is the project's action of $S$-algebra automorphisms of $K$ on points.
--
--   **Where it is used.** The intended application is the case $n = p$ for the Frey curve of a Frey package, with $S = \mathbb{Q}$ and $K$ an algebraic closure of $\mathbb{Q}$, where the existence of such a pairing is the input used to compute the determinant of the mod-$p$ representation on the $p$-torsion as the cyclotomic character, a hypothesis of the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GaloisRep_WeilPairing.lean

import Mathlib
import Definitions.Def_FreyPackage_GaloisRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace WeierstrassCurve.Affine.Point

open WeierstrassCurve

universe r s v

variable {R : Type r} {S : Type s} {K : Type v} [CommRing R] [CommRing S] [Field K]
  [DecidableEq K] {W' : Affine R} [Algebra R S] [Algebra R K] [Algebra S K]
  [IsScalarTower R S K]

variable (S) in

structure IsWeilPairing (W' : Affine R) (n : ℕ)
    (B : Submodule.torsionBy ℤ (W'⁄K).Point n → Submodule.torsionBy ℤ (W'⁄K).Point n → Kˣ) :
    Prop where

  mem_rootsOfUnity : ∀ P Q, B P Q ∈ rootsOfUnity n K

  add_left : ∀ P P' Q, B (P + P') Q = B P Q * B P' Q

  add_right : ∀ P Q Q', B P (Q + Q') = B P Q * B P Q'

  alternate : ∀ P, B P P = 1

  equivariant : ∀ (σ : K ≃ₐ[S] K) (P Q), σ ((B P Q : Kˣ) : K) = ((B (σ • P) (σ • Q) : Kˣ) : K)

  nondegenerate : ∃ P Q, B P Q ≠ 1

variable (S K) in

def HasWeilPairing (W' : Affine R) (n : ℕ) : Prop :=
  ∃ B : Submodule.torsionBy ℤ (W'⁄K).Point n → Submodule.torsionBy ℤ (W'⁄K).Point n → Kˣ,
    IsWeilPairing S W' n B

end WeierstrassCurve.Affine.Point


