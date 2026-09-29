-- Prove2me | Definitions.Def_WeierstrassCurve_MapPoint
-- name    : WeierstrassCurve_MapPoint
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:30.087021+00:00
-- url     : https://prove2.me/theorems/6959f4a5-aa3d-554d-a173-34d5cf33a00e
-- title:
--   Functoriality of affine Weierstrass points along a field homomorphism
-- statement:
--   For fields $F$ and $k$, a ring homomorphism $f \colon F \to k$ and a Weierstrass curve $W_0$ over $F$, this module defines the induced map on affine rational points [`WeierstrassCurve.mapPoint`](../def/WeierstrassCurve_MapPoint.html#L18) from the points of $W_0$ (in the sense of Mathlib's affine point type for a Weierstrass model) to the points of the base-changed curve $W_0.\mathrm{map}\,f$ over $k$. It sends the point at infinity to the point at infinity and an affine point $(x,y)$ to $(f(x), f(y))$, the required nonsingularity of the image being supplied by Mathlib's criterion that nonsingularity transfers along the injective map $f$. The accompanying lemmas record the two defining equations, injectivity of the map (from injectivity of $f$ on coordinates, together with the fact that an affine point never equals the point at infinity), and additivity: for all $P, Q$, $f_*(P+Q) = f_*(P) + f_*(Q)$, proved by separating the case $x_1 = x_2$, $y_1 = \mathrm{negY}(x_2,y_2)$, where both sides are zero, from the generic case, where the image coordinates are compared through the compatibility of slope, $\mathrm{addX}$ and $\mathrm{addY}$ with base change.
--
--   The additive map is packaged as the group homomorphism `mapPointHom`, from which the module derives its injectivity, the preservation of additive orders $\operatorname{addOrderOf}(f_*P) = \operatorname{addOrderOf}(P)$ (also stated in a variant taking an injectivity hypothesis on $f$ as an argument), and compatibility with $n \bullet$ and with negation. Finally, functoriality is recorded in the only form available when source and target types differ: `mapPoint_id_heq` states that $(\mathrm{id}_F)_*P$ is heterogeneously equal to $P$, and `mapPoint_comp_heq` that $(\tau \circ \sigma)_*P$ is heterogeneously equal to $\tau_*(\sigma_*P)$, transported along the identifications $W.\mathrm{map}\,\mathrm{id} = W$ and $(W.\mathrm{map}\,\sigma).\mathrm{map}\,\tau = W.\mathrm{map}(\tau \circ \sigma)$; two helper lemmas provide the corresponding heterogeneous equalities of zero points and of affine points along an equality of Weierstrass models, and `Affine.Point.some_congr'` identifies affine points with equal coordinates but different nonsingularity proofs.
--
--   **Relation to Mathlib.** Mathlib's `WeierstrassCurve.Affine.Point.map` handles algebra homomorphisms between base changes of a curve defined over a common base ring; the map defined here is the plain ring-homomorphism version $W_0(F) \to (W_0.\mathrm{map}\,f)(k)$, with $F$ and $k$ in arbitrary universes. The nonsingularity transfer `Affine.map_nonsingular` and the base-change identities for `negY`, `slope`, `addX`, `addY` it rests on are Mathlib's.
--
--   **Where it is used.** The map is what realises reduction maps, Frobenius and base change on points of Weierstrass models, in particular for comparing torsion of an elliptic curve over a number field with torsion over residue or larger fields; the order-preservation statement is the form in which injectivity on torsion is used.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_WeierstrassCurve_MapPoint.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace WeierstrassCurve

open WeierstrassCurve.Affine

universe u v

variable {F : Type u} {k : Type v} [Field F] [Field k] (f : F →+* k) {W₀ : WeierstrassCurve F}

theorem Affine.Point.some_congr' {V : Affine k} {x₁ y₁ x₂ y₂ : k} (hx : x₁ = x₂)
    (hy : y₁ = y₂) (h₁ : V.Nonsingular x₁ y₁) (h₂ : V.Nonsingular x₂ y₂) :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

def mapPoint : W₀.toAffine.Point → (W₀.map f).toAffine.Point
  | .zero => .zero
  | .some x y h => .some (f x) (f y) ((W₀.toAffine.map_nonsingular f.injective x y).mpr h)

@[simp]
lemma mapPoint_zero : mapPoint f (0 : W₀.toAffine.Point) = 0 :=
  rfl

lemma mapPoint_some {x y : F} (h : W₀.toAffine.Nonsingular x y) :
    mapPoint f (.some x y h)
      = .some (f x) (f y) ((W₀.toAffine.map_nonsingular f.injective x y).mpr h) :=
  rfl

lemma mapPoint_injective : Function.Injective (mapPoint f (W₀ := W₀)) := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · exact absurd h.symm (Affine.Point.some_ne_zero _)
  · exact absurd h (Affine.Point.some_ne_zero _)
  · rw [mapPoint_some, mapPoint_some, Affine.Point.some.injEq] at h
    exact Affine.Point.some_congr' (f.injective h.1) (f.injective h.2) _ _

theorem mapPoint_add [DecidableEq F] [DecidableEq k] (P Q : W₀.toAffine.Point) :
    mapPoint f (P + Q) = mapPoint f P + mapPoint f Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  any_goals rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = W₀.toAffine.negY x₂ y₂
  · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2, mapPoint_zero, mapPoint_some,
      mapPoint_some,
      Affine.Point.add_of_Y_eq (congrArg f hxy.1) (by rw [hxy.2, Affine.map_negY])]
  · have hxy' : ¬(f x₁ = f x₂ ∧ f y₁ = (W₀.map f).toAffine.negY (f x₂) (f y₂)) := by
      rintro ⟨hx, hy⟩
      rw [Affine.map_negY] at hy
      exact hxy ⟨f.injective hx, f.injective hy⟩
    rw [Affine.Point.add_some hxy, mapPoint_some, mapPoint_some, mapPoint_some,
      Affine.Point.add_some hxy']
    exact Affine.Point.some_congr' (by rw [Affine.map_slope, Affine.map_addX])
      (by rw [Affine.map_slope, Affine.map_addY]) _ _

@[simps]
def mapPointHom [DecidableEq F] [DecidableEq k] :
    W₀.toAffine.Point →+ (W₀.map f).toAffine.Point where
  toFun := mapPoint f
  map_zero' := rfl
  map_add' := mapPoint_add f

lemma mapPointHom_injective [DecidableEq F] [DecidableEq k] :
    Function.Injective (mapPointHom f (W₀ := W₀)) :=
  mapPoint_injective f

theorem addOrderOf_mapPoint [DecidableEq F] [DecidableEq k] (P : W₀.toAffine.Point) :
    addOrderOf (mapPoint f P) = addOrderOf P :=
  addOrderOf_injective (mapPointHom f (W₀ := W₀)) (mapPoint_injective f) P

theorem addOrderOf_mapPoint_of_injective [DecidableEq F] [DecidableEq k]
    (_hf : Function.Injective f) (P : W₀.toAffine.Point) :
    addOrderOf (mapPoint f P) = addOrderOf P :=
  addOrderOf_mapPoint f P

theorem mapPoint_nsmul [DecidableEq F] [DecidableEq k] (n : ℕ) (P : W₀.toAffine.Point) :
    mapPoint f (n • P) = n • mapPoint f P :=
  map_nsmul (mapPointHom f (W₀ := W₀)) n P

theorem mapPoint_neg [DecidableEq F] [DecidableEq k] (P : W₀.toAffine.Point) :
    mapPoint f (-P) = -mapPoint f P :=
  map_neg (mapPointHom f (W₀ := W₀)) P

theorem Affine.Point.zero_heq_zero {V V' : Affine k} (hV : V' = V) :
    HEq (0 : V'.Point) (0 : V.Point) := by
  subst hV
  rfl

theorem Affine.Point.some_heq_some {V V' : Affine k} (hV : V' = V) {x y x' y' : k}
    {h : V.Nonsingular x y} {h' : V'.Nonsingular x' y'} (hx : x' = x) (hy : y' = y) :
    HEq (Point.some x' y' h' : V'.Point) (Point.some x y h : V.Point) := by
  subst hV
  subst hx
  subst hy
  rfl

theorem mapPoint_id_heq (V : WeierstrassCurve F) (P : V.toAffine.Point) :
    HEq (mapPoint (RingHom.id F) (W₀ := V) P) P := by
  have hV : V.map (RingHom.id F) = V := WeierstrassCurve.map_id V
  cases P with
  | zero => exact Affine.Point.zero_heq_zero hV.symm
  | some x y h => exact Affine.Point.some_heq_some hV.symm rfl rfl

universe w in

theorem mapPoint_comp_heq {k' : Type w} [Field k'] (σ : F →+* k) (τ : k →+* k')
    (V : WeierstrassCurve F) (P : V.toAffine.Point) :
    HEq (mapPoint (τ.comp σ) (W₀ := V) P) (mapPoint τ (W₀ := V.map σ) (mapPoint σ (W₀ := V) P)) := by
  have hV : (V.map σ).map τ = V.map (τ.comp σ) := WeierstrassCurve.map_map V σ τ
  cases P with
  | zero => exact Affine.Point.zero_heq_zero hV
  | some x y h => exact Affine.Point.some_heq_some hV rfl rfl

end WeierstrassCurve


