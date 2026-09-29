-- Prove2me | Definitions.Def_Mathlib_Topology_Algebra_UniformRing
-- name    : Mathlib_Topology_Algebra_UniformRing
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/19bbd97a-4acb-50db-a44a-11e8c05bfd6e
-- title:
--   Induced semialgebra homomorphism on completions of topological rings
-- statement:
--   The standing context is a pair of rings $\alpha,\beta$, each carrying a uniform space structure making it a topological ring with uniform additive group structure, together with a continuous ring homomorphism $f : \alpha \to \beta$. The Hausdorff completion $\widehat{\alpha} =$ `UniformSpace.Completion α` of a commutative such $\alpha$ is an $\alpha$-algebra via the canonical map $\alpha \to \widehat{\alpha}$, and likewise $\widehat{\beta}$ is a $\beta$-algebra. For commutative $\alpha$ and $\beta$ and continuous $f$, [`UniformSpace.Completion.mapSemialgHom f hf`](../def/Mathlib_Topology_Algebra_UniformRing.html#L14) packages the continuous extension of $f$ to the completions as an element of `Completion α →ₛₐ[f] Completion β`: that is, as a ring homomorphism $\psi : \widehat{\alpha} \to \widehat{\beta}$ which is semilinear over $f$, $\psi(a \cdot x) = f(a)\cdot \psi(x)$ for $a \in \alpha$ and $x \in \widehat{\alpha}$. Its underlying ring homomorphism is Mathlib's `UniformSpace.Completion.mapRingHom f hf`, and the semilinearity amounts to the compatibility of the extension with the canonical maps $\alpha \to \widehat{\alpha}$, $\beta \to \widehat{\beta}$.
--
--   Two lemmas record the values of this homomorphism. `mapSemialgHom_apply` states that, as a function, it is `UniformSpace.Completion.map f`. `mapSemialgHom_coe` states that when $f$ is in addition uniformly continuous, the homomorphism built from the resulting continuity sends the image of $a \in \alpha$ in $\widehat{\alpha}$ to the image of $f(a)$ in $\widehat{\beta}$.
--
--   **Relation to Mathlib.** Mathlib provides the ring homomorphism `UniformSpace.Completion.mapRingHom` on completions; this module upgrades it to a semialgebra homomorphism for the project's own notion [`SemialgHom φ A B`](../def/Mathlib_Algebra_Algebra_Hom.html#L11) (`A →ₛₐ[φ] B`) of a ring homomorphism semilinear over a ring homomorphism $\varphi$ of base rings, for which Mathlib has only the semilinear-map analogue.
--
--   **Where it is used.** This is part of the infrastructure for completions of topological rings, where a ring homomorphism of base rings must be tracked along with the induced map of completions; the semialgebra formulation is what allows the completion functor to be used when the base ring is allowed to vary, as in passing from a number field to its completions and to adelic rings.
--
--   *Attribution:* this file contains material adapted from third-party Apache-2.0 sources (whole file (100%): `FLT/Mathlib/Topology/Algebra/UniformRing.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard, Salvatore Mercuri). See ATTRIBUTION.md and NOTICE in the source repository.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Mathlib_Topology_Algebra_UniformRing.lean

import Mathlib
import Definitions.Def_Mathlib_Algebra_Algebra_Hom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

section

namespace UniformSpace.Completion

variable {α : Type*} [Ring α] [UniformSpace α] [IsTopologicalRing α] [IsUniformAddGroup α]
  {β : Type*} [UniformSpace β] [Ring β] [IsUniformAddGroup β] [IsTopologicalRing β]
  (f : α →+* β) (hf : Continuous f)

variable {f}

noncomputable def mapSemialgHom {α : Type*} [CommRing α] [UniformSpace α]
    [IsTopologicalRing α] [IsUniformAddGroup α] {β : Type*} [UniformSpace β] [CommRing β]
    [IsUniformAddGroup β] [IsTopologicalRing β] (f : α →+* β) (hf : Continuous f) :
    Completion α →ₛₐ[f] Completion β where
  __ := UniformSpace.Completion.mapRingHom f hf
  map_smul' m x := by
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe]
    rw [Algebra.smul_def, map_mul, Algebra.smul_def]
    congr
    exact extensionHom_coe _ _ m

theorem mapSemialgHom_apply {α : Type*} [CommRing α] [UniformSpace α]
    [IsTopologicalRing α] [IsUniformAddGroup α] {β : Type*} [UniformSpace β] [CommRing β]
    [IsUniformAddGroup β] [IsTopologicalRing β] (f : α →+* β) (hf : Continuous f)
    (x : UniformSpace.Completion α) :
    mapSemialgHom f hf x = UniformSpace.Completion.map f x := rfl

theorem mapSemialgHom_coe {α : Type*} [CommRing α] [UniformSpace α]
    [IsTopologicalRing α] [IsUniformAddGroup α] {β : Type*} [UniformSpace β] [CommRing β]
    [IsUniformAddGroup β] [IsTopologicalRing β] {f : α →+* β} (hf : UniformContinuous f)
    (a : α) :
    mapSemialgHom f hf.continuous a = f a := by
  rw [mapSemialgHom_apply, map_coe hf]

end UniformSpace.Completion


