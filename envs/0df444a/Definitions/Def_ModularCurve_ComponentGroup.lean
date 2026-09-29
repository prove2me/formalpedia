-- Prove2me | Definitions.Def_ModularCurve_ComponentGroup
-- name    : ModularCurve_ComponentGroup
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/51600f2d-5f53-5b50-b6b9-c941a313b846
-- title:
--   Combinatorial component group of a weighted vertexless graph
-- statement:
--   Fix a finite index type $\iota$. The module sets up, in purely linear-algebraic terms, the degree-zero divisor lattice on $\iota$, a diagonal integral pairing weighted by natural numbers, and the cokernel of the associated Gram map.
--
--   [`ModularCurve.degreeOn ι`](../def/ModularCurve_ComponentGroup.html#L17) is the $\mathbb{Z}$-linear map $(\iota \to \mathbb{Z}) \to \mathbb{Z}$ obtained as the sum of the coordinate projections, so $D \mapsto \sum_{x} D_x$ (`degreeOn_apply`). [`ModularCurve.characterLattice ι`](../def/ModularCurve_ComponentGroup.html#L23) is its kernel, taken as a $\mathbb{Z}$-submodule of $\iota \to \mathbb{Z}$; `mem_characterLattice` records that $D$ lies in it exactly when $\sum_x D_x = 0$. For a weight function $e : \iota \to \mathbb{N}$, [`ModularCurve.widthPairing e`](../def/ModularCurve_ComponentGroup.html#L35) is the $\mathbb{Z}$-bilinear form on $\iota \to \mathbb{Z}$ given by $\langle D, D'\rangle = \sum_x (e_x) \, D_x D'_x$, with the integer casts of the weights; `widthPairing_apply` gives this formula and `widthPairing_comm` its symmetry. No positivity or boundedness is imposed on $e$ beyond its taking values in $\mathbb{N}$. [`ModularCurve.gramMap e`](../def/ModularCurve_ComponentGroup.html#L61) is this pairing restricted to `characterLattice ι` in both arguments, viewed as a map $X \to \operatorname{Hom}_{\mathbb{Z}}(X,\mathbb{Z}) =$ `Module.Dual ℤ (characterLattice ι)` with $X =$ `characterLattice ι`, and `gramMap_apply` evaluates it by the same weighted sum on the underlying functions. Finally [`ModularCurve.componentGroup e`](../def/ModularCurve_ComponentGroup.html#L69) is defined, as a reducible abbreviation, to be the quotient module $\operatorname{Hom}_{\mathbb{Z}}(X,\mathbb{Z}) / \operatorname{range}(\mathtt{gramMap}\ e)$, and [`ModularCurve.componentGroupProj e`](../def/ModularCurve_ComponentGroup.html#L72) is the canonical quotient map from the dual onto it. Thus the component group here is literally a quotient of the dual lattice by the image of the weighted diagonal pairing, not an abstractly characterised group; in particular it is defined for every $e$, with no finiteness or nondegeneracy hypothesis.
--
--   **Relation to Mathlib.** Built entirely from Mathlib's linear algebra (`LinearMap.proj`, `LinearMap.ker`, `LinearMap.mk₂`, `domRestrict₁₂`, `Module.Dual`, submodule quotients and `Submodule.mkQ`); the notions themselves — the degree map, character lattice, width pairing, Gram map and component group — are the project's own, Mathlib having no counterpart.
--
--   **Where it is used.** These are the combinatorial avatars of the character group $X$ of the toric part of the special fibre of the Néron model of $J_0(Mq)$ at a prime $q$ of multiplicative reduction, of Grothendieck's monodromy pairing $X \to \operatorname{Hom}(X,\mathbb{Z})$, and of the group of connected components $\Phi$ appearing as its cokernel; the index set is instantiated by the supersingular locus and the weights by the crossing widths. They feed the analysis of inertia at $q$ used in Mazur's principle and level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_ComponentGroup.lean

import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Algebra.Exact
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open Finset

section CharacterLattice
variable {ι : Type*} [Fintype ι]

def degreeOn (ι : Type*) [Fintype ι] : (ι → ℤ) →ₗ[ℤ] ℤ :=
  ∑ x : ι, LinearMap.proj x

@[simp] theorem degreeOn_apply (D : ι → ℤ) : degreeOn ι D = ∑ x : ι, D x := by
  simp [degreeOn]

def characterLattice (ι : Type*) [Fintype ι] : Submodule ℤ (ι → ℤ) :=
  LinearMap.ker (degreeOn ι)

theorem mem_characterLattice {D : ι → ℤ} :
    D ∈ characterLattice ι ↔ ∑ x : ι, D x = 0 := by
  simp [characterLattice, LinearMap.mem_ker]

end CharacterLattice

section Pairing
variable {ι : Type*} [Fintype ι]

def widthPairing (e : ι → ℕ) : (ι → ℤ) →ₗ[ℤ] (ι → ℤ) →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ (fun D D' => ∑ x : ι, (e x : ℤ) * (D x * D' x))
    (fun D₁ D₂ D' => by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by simp only [Pi.add_apply]; ring)
    (fun c D D' => by
      rw [smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by
        simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun D D'₁ D'₂ => by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by simp only [Pi.add_apply]; ring)
    (fun c D D' => by
      rw [smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by
        simp only [Pi.smul_apply, smul_eq_mul]; ring)

@[simp] theorem widthPairing_apply (e : ι → ℕ) (D D' : ι → ℤ) :
    widthPairing e D D' = ∑ x : ι, (e x : ℤ) * (D x * D' x) :=
  rfl

theorem widthPairing_comm (e : ι → ℕ) (D D' : ι → ℤ) :
    widthPairing e D D' = widthPairing e D' D := by
  simp only [widthPairing_apply]
  exact Finset.sum_congr rfl fun x _ => by ring

def gramMap (e : ι → ℕ) :
    characterLattice ι →ₗ[ℤ] Module.Dual ℤ (characterLattice ι) :=
  (widthPairing e).domRestrict₁₂ (characterLattice ι) (characterLattice ι)

@[simp] theorem gramMap_apply (e : ι → ℕ) (D D' : characterLattice ι) :
    gramMap e D D' = ∑ x : ι, (e x : ℤ) * (D.1 x * D'.1 x) :=
  rfl

abbrev componentGroup (e : ι → ℕ) :=
  Module.Dual ℤ (characterLattice ι) ⧸ LinearMap.range (gramMap e)

abbrev componentGroupProj (e : ι → ℕ) :
    Module.Dual ℤ (characterLattice ι) →ₗ[ℤ] componentGroup e :=
  (LinearMap.range (gramMap e)).mkQ

end Pairing

end ModularCurve


