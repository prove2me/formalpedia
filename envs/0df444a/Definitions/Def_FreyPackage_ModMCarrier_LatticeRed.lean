-- Prove2me | Definitions.Def_FreyPackage_ModMCarrier_LatticeRed
-- name    : FreyPackage_ModMCarrier_LatticeRed
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/55a59beb-9ebb-59a6-b06a-72c96a49f802
-- title:
--   Base change of a lattice in a complex vector space
-- statement:
--   Fix a field $k$ and two complex vector spaces $W$, $W'$, together with $\mathbb{Z}$-submodules $L \subseteq W$ and $L' \subseteq W'$ (the 'lattices'; no discreteness or spanning condition is imposed — $L$ is an arbitrary additive subgroup that is a $\mathbb{Z}$-submodule). The basic object is `latticeRed k L`, the tensor product $k \otimes_{\mathbb{Z}} L$, viewed as a $k$-vector space: the reduction of the lattice along $\mathbb{Z} \to k$. Alongside it, `latticeRed.mk` is the $\mathbb{Z}$-linear map $L \to k \otimes_{\mathbb{Z}} L$ sending $x$ to $1 \otimes x$; `latticeRed.mk_eq_tmul` records this value.
--
--   Functoriality is provided for $\mathbb{C}$-linear maps that preserve the lattices. Given $g : W \to W'$ linear over $\mathbb{C}$ and a hypothesis that $g x \in L'$ for every $x \in L$, `latticeRestrictMap` is the induced map $L \to L'$, $x \mapsto g x$, regarded as a homomorphism of $\mathbb{Z}$-modules (additivity and compatibility with integer scaling being inherited from $\mathbb{C}$-linearity of $g$). Its base change along $\mathbb{Z} \to k$ is `latticeRed.mapOf`, a $k$-linear map $k \otimes_{\mathbb{Z}} L \to k \otimes_{\mathbb{Z}} L'$. The lemma `latticeRed.mapOf_mk` states the expected compatibility: `latticeRed.mapOf` applied to $1 \otimes x$ is $1 \otimes g x$, where $g x$ is taken as an element of $L'$ via the preservation hypothesis. Note that nothing ties the characteristic of $k$ to the ambient $\mathbb{C}$-structure; $k$ enters only through the ring map $\mathbb{Z} \to k$ used for the tensor product.
--
--   **Relation to Mathlib.** Everything here is assembled from Mathlib's `TensorProduct` and `LinearMap.baseChange`; the module supplies names for the reduction $k \otimes_{\mathbb{Z}} L$ of a $\mathbb{Z}$-submodule of a complex vector space, for the restriction of a lattice-preserving $\mathbb{C}$-linear map, and for its base change, none of which Mathlib packages in this form.
--
--   **Where it is used.** This is the generic tensor-product layer underlying the construction of mod-$\mathfrak{m}$ coefficient spaces attached to integral lattices inside complex spaces of cusp forms, where the lattice-preserving $\mathbb{C}$-linear maps to be reduced are the degeneracy maps between spaces of different level. Such reductions supply the carrier on which the level-raising and level-lowering arguments of Ribet's theorem operate.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_FreyPackage_ModMCarrier_LatticeRed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
noncomputable section
open scoped TensorProduct

namespace FreyPackage.ModMCarrier

section LatticeRed
variable (k : Type*) [Field k] {W W' : Type*} [AddCommGroup W] [AddCommGroup W']
  [Module ℂ W] [Module ℂ W'] (L : Submodule ℤ W) (L' : Submodule ℤ W')

abbrev latticeRed : Type _ := k ⊗[ℤ] ↥L

def latticeRed.mk : ↥L →ₗ[ℤ] latticeRed k L := (TensorProduct.mk ℤ k (↥L)) 1

@[simp] lemma latticeRed.mk_eq_tmul (x : ↥L) : latticeRed.mk k L x = (1 : k) ⊗ₜ[ℤ] x := rfl

def latticeRestrictMap (g : W →ₗ[ℂ] W') (hg : ∀ x ∈ L, g x ∈ L') : ↥L →ₗ[ℤ] ↥L' where
  toFun x := ⟨g x, hg x x.2⟩
  map_add' x y := by simp [Subtype.ext_iff]
  map_smul' m x := by simp [Subtype.ext_iff, ← Int.cast_smul_eq_zsmul ℂ]

def latticeRed.mapOf (g : W →ₗ[ℂ] W') (hg : ∀ x ∈ L, g x ∈ L') :
    latticeRed k L →ₗ[k] latticeRed k L' :=
  LinearMap.baseChange k (latticeRestrictMap L L' g hg)

lemma latticeRed.mapOf_mk (g : W →ₗ[ℂ] W') (hg : ∀ x ∈ L, g x ∈ L') (x : ↥L) :
    latticeRed.mapOf k L L' g hg (latticeRed.mk k L x)
      = latticeRed.mk k L' ⟨g x, hg x x.2⟩ := rfl

end LatticeRed

end FreyPackage.ModMCarrier


