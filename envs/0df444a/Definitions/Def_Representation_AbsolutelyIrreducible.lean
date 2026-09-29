-- Prove2me | Definitions.Def_Representation_AbsolutelyIrreducible
-- name    : Representation_AbsolutelyIrreducible
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/0154787f-b3d9-577a-a4ea-93ab3991a486
-- title:
--   Base change and absolute irreducibility of representations
-- statement:
--   Two notions are introduced for abstract representations of a group. First, for a commutative ring $R$, an $R$-module $V$, a group $G$ and a representation $\rho : G \to \mathrm{GL}_R(V)$ (in Mathlib's sense, a monoid homomorphism from $G$ to $V \to_{\ell} V$ units), and for any commutative $R$-algebra $R'$, [`Representation.baseChange R' ρ`](../def/Representation_AbsolutelyIrreducible.html#L17) is the representation of $G$ on $R' \otimes_R V$ which sends $g$ to the $R'$-linear extension $\mathrm{id}_{R'} \otimes \rho(g)$ of $\rho(g)$; multiplicativity and preservation of the identity are inherited from $\rho$. The scoped notation `R' ⊗ᵣ' ρ` denotes this representation. Second, for a field $k$ and a representation $\rho$ of $G$ on a $k$-module $W$, the class [`Representation.IsAbsolutelyIrreducible ρ`](../def/Representation_AbsolutelyIrreducible.html#L27) is a `Prop`-valued structure with a single field: for every type $k'$ in a fixed universe $u$ (a universe parameter of the class itself), every field structure on $k'$ and every $k$-algebra structure on $k'$, the base-changed representation $k' \otimes_k \rho$ of $G$ on $k' \otimes_k W$ is irreducible in the sense of Mathlib's `IsIrreducible`. Thus absolute irreducibility is phrased as stability of irreducibility under arbitrary field extensions of $k$, the field structure and the algebra structure being quantified over rather than fixed, so that a single type may be used with several $k$-algebra structures; the quantification ranges over fields whose carrier lies in the universe $u$.
--
--   **Relation to Mathlib.** Built on Mathlib's `Representation.IsIrreducible` and `LinearMap.baseChange`; the base change of a representation and the predicate of absolute irreducibility are defined here rather than taken from Mathlib.
--
--   **Where it is used.** These notions are the ambient form of absolute irreducibility used in the representation-theoretic parts of the argument, notably the Brauer–Nesbitt type results and the Taylor–Wiles patching input, where absolute irreducibility of a residual representation is the standing hypothesis; the two-dimensional residual Galois case is treated by a separate, specialised predicate.
--
--   *Attribution:* this file contains material adapted from third-party Apache-2.0 sources (whole file (82%): `FLT/Mathlib/RepresentationTheory/Basic.lean` — © 2024 Javier López-Contreras; authors: Javier López-Contreras, Kevin Buzzard; `FLT/Deformations/RepresentationTheory/Irreducible.lean` — © 2024 Javier López-Contreras; authors: Javier López-Contreras, Kevin Buzzard). See ATTRIBUTION.md and NOTICE in the source repository.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Representation_AbsolutelyIrreducible.lean

import Mathlib.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

section

open LinearMap
open scoped TensorProduct

namespace Representation

universe u

variable {R V G : Type*} [CommRing R] [AddCommMonoid V] [Module R V] [Group G]

noncomputable def baseChange (R' : Type*) [CommRing R'] [Algebra R R'] (ρ : Representation R G V)
    : Representation R' G (R' ⊗[R] V) where
  toFun g := LinearMap.baseChange R' (ρ g)
  map_one' := by aesop
  map_mul' := by aesop

scoped notation R' "⊗ᵣ'" ρ => baseChange R' ρ

variable {k : Type*} [Field k] {W : Type*} [AddCommMonoid W] [Module k W]

class IsAbsolutelyIrreducible (ρ : Representation k G W) : Prop where
  absolutelyIrreducible :
    ∀ k' : Type u, ∀ _ : Field k', ∀ _ : Algebra k k', IsIrreducible (k' ⊗ᵣ' ρ)

end Representation

end


