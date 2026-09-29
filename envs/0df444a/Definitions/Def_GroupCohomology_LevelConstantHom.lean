-- Prove2me | Definitions.Def_GroupCohomology_LevelConstantHom
-- name    : GroupCohomology_LevelConstantHom
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/663fa26f-e664-5209-90e5-5c706ffcad6c
-- title:
--   Level-constant additive characters and their conjugation-equivariant variant
-- statement:
--   Throughout, $G$ is a group equipped with a level map $r \colon G \to \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ (a monoid homomorphism into the group of $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`), $S$ is a finite set of rational primes, $k$ a commutative ring and $V$ a $k$-module.
--
--   The first definition, `levelConstantHom r S k V`, is the $k$-submodule of the function module $G \to V$ consisting of those $\varphi$ that are additive, $\varphi(gh) = \varphi(g) + \varphi(h)$ for all $g, h \in G$, and satisfy `IsLevelConstantSr₁ r S`, i.e. for which there is an intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ that is finite over $\mathbb{Q}$ and has the property that for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit in $A$ the inertia subgroup of $A$ over $\mathbb{Q}$ fixes $F$ pointwise, such that $\varphi(gs) = \varphi(g)$ whenever $r(s)$ fixes $F$ pointwise. Thus these are the additive $V$-valued characters of $G$ that are constant on cosets of $r^{-1}(\operatorname{Gal}(\overline{\mathbb{Q}}/F))$ for some such finite level $F$ unramified outside $S$. Additivity is imposed as a condition on plain functions, so that the collection is literally a submodule of $G \to V$.
--
--   The second definition, `eqLevelConstantHom r S Sg M`, is attached to a subgroup $Sg \le G$ and a representation $M$ of $G$ over $k$: it is the $k$-submodule of maps $\varphi \colon Sg \to M$ lying in `levelConstantHom (r.comp Sg.subtype) S k M` — additive and level-constant for the restricted level map — and in addition satisfying the conjugation-equivariance condition that for all $g \in G$ and $s, t \in Sg$ with $g^{-1} s g = t$ in $G$ one has $\rho_M(g)(\varphi(t)) = \varphi(s)$. No normality assumption on $Sg$ is needed to state this. Two membership lemmas record these descriptions as the definitions of the two submodules.
--
--   **Relation to Mathlib.** Mathlib has no notion of level-constancy of this kind; `IsLevelConstantSr₁` and the submodules built from it are the project's surrogate for continuity of Galois cochains, expressed through finite intermediate fields unramified outside $S$ rather than through a topology. Additivity is encoded as a predicate on functions instead of using Mathlib's bundled homomorphism types, so that the result is a `Submodule` of the $k$-module of all functions.
--
--   **Where it is used.** For coefficients on which the group acts trivially, the level-constant additive characters are exactly the level-$S$ $1$-cocycles, so these submodules provide a concrete model for the $S$-restricted first cohomology used in the project's Selmer-group formalism. The conjugation-equivariant variant is the shape in which characters of a subgroup (a Galois group of a subextension) appear in the inflation–restriction and Kummer-theoretic analysis of those Selmer groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_LevelConstantHom.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace groupCohomology

universe u

variable {G : Type u} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes)
  (k : Type u) [CommRing k] (V : Type u) [AddCommGroup V] [Module k V]

def levelConstantHom : Submodule k (G → V) where
  carrier := {φ | (∀ g h : G, φ (g * h) = φ g + φ h) ∧ IsLevelConstantSr₁ r S φ}
  add_mem' := fun {φ ψ} hφ hψ =>
    ⟨fun g h => by simp only [Pi.add_apply, hφ.1 g h, hψ.1 g h]; abel, hφ.2.add hψ.2⟩
  zero_mem' := ⟨fun _ _ => by simp, isLevelConstantSr₁_const r S (0 : V)⟩
  smul_mem' := fun c φ hφ =>
    ⟨fun g h => by simp only [Pi.smul_apply, hφ.1 g h, smul_add], hφ.2.comp (c • ·)⟩

variable {r S k V} in
theorem mem_levelConstantHom_iff (φ : G → V) :
    φ ∈ levelConstantHom r S k V ↔ (∀ g h : G, φ (g * h) = φ g + φ h) ∧ IsLevelConstantSr₁ r S φ := Iff.rfl

variable {k}

def eqLevelConstantHom (Sg : Subgroup G) (M : Rep k G) : Submodule k (↥Sg → M) where
  carrier := {φ | φ ∈ levelConstantHom (r.comp Sg.subtype) S k M ∧
    ∀ g : G, ∀ s t : ↥Sg, (g⁻¹ * s * g : G) = t → M.ρ g (φ t) = φ s}
  add_mem' := fun {φ ψ} hφ hψ =>
    ⟨add_mem hφ.1 hψ.1, fun g s t hst => by simp only [Pi.add_apply, map_add, hφ.2 g s t hst, hψ.2 g s t hst]⟩
  zero_mem' := ⟨zero_mem _, fun _ _ _ _ => by simp⟩
  smul_mem' := fun c φ hφ =>
    ⟨Submodule.smul_mem _ c hφ.1, fun g s t hst => by simp only [Pi.smul_apply, map_smul, hφ.2 g s t hst]⟩

variable {r S} in
theorem mem_eqLevelConstantHom_iff (Sg : Subgroup G) (M : Rep k G) (φ : ↥Sg → M) :
    φ ∈ eqLevelConstantHom r S Sg M ↔ φ ∈ levelConstantHom (r.comp Sg.subtype) S k M ∧
      ∀ g : G, ∀ s t : ↥Sg, (g⁻¹ * s * g : G) = t → M.ρ g (φ t) = φ s := Iff.rfl

end groupCohomology


