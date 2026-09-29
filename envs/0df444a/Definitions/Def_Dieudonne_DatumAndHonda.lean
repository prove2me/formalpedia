-- Prove2me | Definitions.Def_Dieudonne_DatumAndHonda
-- name    : Dieudonne_DatumAndHonda
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/acb128f3-743a-566a-ab9a-593c343b010f
-- title:
--   Dieudonné data and finite Honda systems
-- statement:
--   Fix a commutative ring $\mathcal{O}$, an element $\ell \in \mathcal{O}$ and an $\mathcal{O}$-module $D$. A [`Deformation.DieudonneDatum ℓ D`](../def/Dieudonne_DatumAndHonda.html#L14) is a structure carrying two $\mathcal{O}$-linear endomorphisms `F` and `V` of $D$ together with two fields asserting the equalities of linear maps $F \circ V = \ell \cdot \mathrm{id}_D$ and $V \circ F = \ell \cdot \mathrm{id}_D$; both maps are $\mathcal{O}$-linear, so no semilinear Frobenius twist is built into the notion. The pointwise forms $F(Vx) = \ell x$ and $V(Fx) = \ell x$ are recorded, as is the consequence $F \circ V = V \circ F$. Three predicates on such a datum are defined by unfolding to bijectivity or vanishing: `IsEtaleType` says $F$ is bijective, `IsMultiplicativeType` says $V$ is bijective, and `IsLocalLocal` says $F = 0$ and $V = 0$. If $F$ is bijective then $V$ is determined as $V x = \ell \cdot F^{-1}(x)$. Two one-dimensional examples on $D = \mathcal{O}$ are provided: `etaleOne` with $F = \mathrm{id}$, $V = \ell \cdot \mathrm{id}$, and `multOne` with $F = \ell \cdot \mathrm{id}$, $V = \mathrm{id}$, shown to be of étale and of multiplicative type respectively.
--
--   A [`Deformation.HondaSystem ℓ D`](../def/Dieudonne_DatumAndHonda.html#L73) extends a Dieudonné datum by an $\mathcal{O}$-submodule $L \subseteq D$ subject to four further fields: every $x \in L$ lying in the range of $F$ is of the form $\ell y$ with $y \in L$; conversely $\ell y$ lies in the range of $F$ for every $y \in L$; the range of $F$ together with $L$ spans $D$, i.e. $\mathrm{range}(F) \sqcup L = \top$; and $V$ is injective on $L$, in the sense that $x \in L$ with $V x = 0$ forces $x = 0$. Thus the Hodge-type submodule and the axioms governing it are carried as structure data, not derived.
--
--   **Relation to Mathlib.** Mathlib has no notion of Dieudonné module, $F$-$V$-module or Honda system; these structures are the project's own, formulated with Mathlib's `Module`, `LinearMap` and `Submodule` API.
--
--   **Where it is used.** These structures are the linear-algebra target of Fontaine's anti-equivalence: Dieudonné data classify finite commutative group schemes over the residue field, and Honda systems classify finite flat group schemes over the ring of integers of an unramified local field. They are used in the route to Fermat's Last Theorem to analyse finite flat group schemes of order $\ell$ attached to the Galois representations in play, underpinning the local flatness and finite-flat descent statements needed in the level-lowering and deformation-theoretic arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Dieudonne_DatumAndHonda.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open LinearMap Submodule Function

universe u v

namespace Deformation

variable {𝓞 : Type u} [CommRing 𝓞]

@[ext]
structure DieudonneDatum (ℓ : 𝓞) (D : Type v) [AddCommGroup D] [Module 𝓞 D] where

  F : D →ₗ[𝓞] D

  V : D →ₗ[𝓞] D

  fv : F ∘ₗ V = ℓ • LinearMap.id

  vf : V ∘ₗ F = ℓ • LinearMap.id

namespace DieudonneDatum

variable {ℓ : 𝓞} {D : Type v} [AddCommGroup D] [Module 𝓞 D] (M : DieudonneDatum ℓ D)

theorem F_V_apply (x : D) : M.F (M.V x) = ℓ • x := by
  have := LinearMap.congr_fun M.fv x; simpa using this

theorem V_F_apply (x : D) : M.V (M.F x) = ℓ • x := by
  have := LinearMap.congr_fun M.vf x; simpa using this

theorem F_V_comm : M.F ∘ₗ M.V = M.V ∘ₗ M.F := M.fv.trans M.vf.symm

def IsEtaleType : Prop := Function.Bijective M.F

def IsMultiplicativeType : Prop := Function.Bijective M.V

def IsLocalLocal : Prop := M.F = 0 ∧ M.V = 0

theorem V_eq_smul_of_isEtaleType (h : M.IsEtaleType) (x : D) :
    M.V x = ℓ • (Equiv.ofBijective M.F h).symm x := by
  apply h.injective
  rw [M.F_V_apply, map_smul]
  congr 1
  exact ((Equiv.ofBijective M.F h).apply_symm_apply x).symm

variable (ℓ) in

def etaleOne : DieudonneDatum ℓ 𝓞 where
  F := LinearMap.id
  V := ℓ • LinearMap.id
  fv := by ext; simp
  vf := by ext; simp

variable (ℓ) in

def multOne : DieudonneDatum ℓ 𝓞 where
  F := ℓ • LinearMap.id
  V := LinearMap.id
  fv := by ext; simp
  vf := by ext; simp

theorem etaleOne_isEtaleType : (etaleOne (𝓞 := 𝓞) ℓ).IsEtaleType :=
  Function.bijective_id

theorem multOne_isMultiplicativeType : (multOne (𝓞 := 𝓞) ℓ).IsMultiplicativeType :=
  Function.bijective_id

end DieudonneDatum

structure HondaSystem (ℓ : 𝓞) (D : Type v) [AddCommGroup D] [Module 𝓞 D] extends
    DieudonneDatum ℓ D where

  L : Submodule 𝓞 D

  sh1_le : ∀ x ∈ L, x ∈ LinearMap.range F → ∃ y ∈ L, x = ℓ • y

  sh1_ge : ∀ y ∈ L, ℓ • y ∈ LinearMap.range F

  sh2' : (LinearMap.range F) ⊔ L = ⊤

  sh3 : ∀ x ∈ L, V x = 0 → x = 0

end Deformation


