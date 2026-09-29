-- Prove2me | Definitions.Def_Algebra_PointDerivations
-- name    : Algebra_PointDerivations
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/4ec00ab2-efbd-5f20-be8e-c5c64ec3e55b
-- title:
--   Point derivations of an algebra at a k-point
-- statement:
--   Fix a field $k$, a commutative $k$-algebra $A$, a ring homomorphism $\mathrm{ev} : A \to k$ and a $k$-module $M$. [`Algebra.PointDerivations k A ev M`](../def/Algebra_PointDerivations.html#L9) is defined to be the $k$-submodule of $\operatorname{Hom}_k(A,M)$ whose carrier consists of those $k$-linear maps $D : A \to M$ satisfying the Leibniz rule at the point $\mathrm{ev}$, namely $D(ab) = \mathrm{ev}(a)\,D(b) + \mathrm{ev}(b)\,D(a)$ for all $a, b \in A$; closure under addition, the vanishing of $0$ and closure under scalars from $k$ are part of the definition of the submodule. Note that $\mathrm{ev}$ is taken to be a bare ring homomorphism: no compatibility with the structure map $k \to A$ is imposed in the definition, and $M$ carries only its $k$-module structure.
--
--   The accompanying lemmas record the membership criterion (`mem_iff`, by definition) and its use (`apply_mul`), that every point derivation kills the unit, $D(1) = 0$ (`apply_one`), and hence kills constants, $D(\mathrm{algebraMap}_{k \to A}(c)) = 0$ for $c \in k$ (`apply_algebraMap`). The lemma `ev_smul` records that, under the additional hypothesis that $\mathrm{ev}$ composed with $k \to A$ is the identity of $k$, one has $\mathrm{ev}(c \cdot a) = c\,\mathrm{ev}(a)$, i.e. $\mathrm{ev}$ is then $k$-linear. Finally, [`Algebra.PointDerivations.map ev φ`](../def/Algebra_PointDerivations.html#L47), for a $k$-linear map $φ : M \to M'$, is post-composition $D \mapsto φ \circ D$, viewed as a $k$-linear map from the point derivations with values in $M$ to those with values in $M'$; `map_apply_coe` evaluates it, and `map_id`, `map_comp` state that this assignment is functorial in the coefficient module ($\mathrm{map}$ of the identity is the identity, and $\mathrm{map}$ of a composite is the composite of the maps).
--
--   **Relation to Mathlib.** Mathlib's `Derivation k A M` requires $M$ to be an $A$-module; this is a variant spelling of the same notion of tangent vector at a point, defined as a submodule of $\operatorname{Hom}_k(A,M)$ with $\mathrm{ev}$ a bare ring homomorphism, so that no $A$-module structure on $M$ (and no compatibility proof for $\mathrm{ev}$) has to be provided.
--
--   **Where it is used.** These modules of point derivations provide the vocabulary for tangent spaces at a $k$-point used in the square-zero/small-extension (deformation-theoretic) part of the development: a morphism out of a pointed square-zero thickening which is the given point on the closed part corresponds to the point derivation sending $a$ to the nilpotent part of its pullback.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Algebra_PointDerivations.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w w'

namespace Algebra

def PointDerivations (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A] (ev : A →+* k)
    (M : Type w) [AddCommGroup M] [Module k M] : Submodule k (A →ₗ[k] M) where
  carrier := {D | ∀ a b : A, D (a * b) = ev a • D b + ev b • D a}
  add_mem' := by
    intro D D' hD hD' a b
    simp only [LinearMap.add_apply, hD a b, hD' a b, smul_add]
    abel
  zero_mem' := by
    intro a b
    simp
  smul_mem' := by
    intro c D hD a b
    simp only [LinearMap.smul_apply, hD a b, smul_add, smul_comm c]

namespace PointDerivations

variable {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A] {ev : A →+* k}
  {M : Type w} [AddCommGroup M] [Module k M] {M' : Type w'} [AddCommGroup M'] [Module k M']

theorem mem_iff (D : A →ₗ[k] M) : D ∈ PointDerivations k A ev M ↔ ∀ a b : A, D (a * b) = ev a • D b + ev b • D a :=
  Iff.rfl

theorem apply_mul {D : A →ₗ[k] M} (hD : D ∈ PointDerivations k A ev M) (a b : A) :
    D (a * b) = ev a • D b + ev b • D a := hD a b

theorem apply_one {D : A →ₗ[k] M} (hD : D ∈ PointDerivations k A ev M) : D 1 = 0 := by
  have h := hD 1 1
  rw [mul_one, show ev 1 = 1 from map_one ev, one_smul] at h

  have h2 : D 1 + D 1 = D 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel h2

theorem apply_algebraMap {D : A →ₗ[k] M} (hD : D ∈ PointDerivations k A ev M) (c : k) : D (algebraMap k A c) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, LinearMap.map_smul, apply_one hD, smul_zero]

theorem ev_smul (hev : ev.comp (algebraMap k A) = RingHom.id k) (c : k) (a : A) : ev (c • a) = c * ev a := by
  rw [Algebra.smul_def, map_mul, ← RingHom.comp_apply, hev, RingHom.id_apply]

def map (ev : A →+* k) (φ : M →ₗ[k] M') : ↥(PointDerivations k A ev M) →ₗ[k] ↥(PointDerivations k A ev M') where
  toFun D := ⟨φ.comp D.1, fun a b => by simp only [LinearMap.comp_apply, D.2 a b, map_add, map_smul]⟩
  map_add' D D' := by ext a; simp
  map_smul' c D := by ext a; simp

@[simp] theorem map_apply_coe (ev : A →+* k) (φ : M →ₗ[k] M') (D : ↥(PointDerivations k A ev M)) (a : A) :
    (map ev φ D : A →ₗ[k] M') a = φ (D.1 a) := rfl

theorem map_id (ev : A →+* k) (D : ↥(PointDerivations k A ev M)) : map ev (LinearMap.id : M →ₗ[k] M) D = D := by
  ext a; rfl

theorem map_comp {M'' : Type w} [AddCommGroup M''] [Module k M''] (ev : A →+* k) (φ : M →ₗ[k] M') (ψ : M' →ₗ[k] M'')
    (D : ↥(PointDerivations k A ev M)) : map ev (ψ.comp φ) D = map ev ψ (map ev φ D) := by
  ext a; rfl

end PointDerivations

end Algebra


