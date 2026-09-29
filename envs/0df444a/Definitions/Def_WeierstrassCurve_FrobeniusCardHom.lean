-- Prove2me | Definitions.Def_WeierstrassCurve_FrobeniusCardHom
-- name    : WeierstrassCurve_FrobeniusCardHom
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:30.087021+00:00
-- url     : https://prove2.me/theorems/061d1286-4a04-59bd-bc21-e00b13ddc948
-- title:
--   Frobenius as an additive endomorphism of Weierstrass curve points
-- statement:
--   Let $k$ be a field and $V$ a Weierstrass curve over $k$. Given $q : \mathbb{N}$ and a proof `hfrob` that $(x,y)\mapsto(x^q,y^q)$ carries nonsingular affine points of $V$ to nonsingular affine points, `frobPoint q hfrob` is the map on Mathlib's group of affine points $V(k)$ defined by cases: the point at infinity goes to itself, and `.some x y h` goes to `.some (x ^ q) (y ^ q)`. Additivity is obtained under the hypotheses that some ring endomorphism $\varphi$ of $k$ satisfies $\varphi a = a^q$ for all $a$ and that $\varphi$ fixes the curve, $V.\mathrm{map}\,\varphi = V$: from Mathlib's compatibility of `negY`, `slope`, `addX`, `addY` with base change along $\varphi$ one gets `negY_pow`, `slope_pow`, `addX_slope_pow`, `addY_slope_pow`, hence `frobPoint_neg` and `frobPoint_add`, the latter by the usual split into the degenerate case $x_1=x_2$, $y_1=\mathrm{negY}(x_2,y_2)$ and the generic case; injectivity of $a\mapsto a^q$ comes from injectivity of $\varphi$ (`pow_injective_of_ringHom`).
--
--   These hypotheses are then supplied in the arithmetic situation: $F$ a finite field, $f : F \to k$ a ring homomorphism into a field, $W_0$ a Weierstrass curve over $F$, and $q = \#F$. Writing $\#F = p^n$, the $n$-fold Frobenius `iterateFrobenius k p n` raises to the $q$-th power and fixes $W_0.\mathrm{map}\,f$, since the coefficients lie in the image of $f$ (`exists_ringHom_pow_card_fixing`); this also yields `nonsingular_pow_card_map`. Consequently `frobCardHom f` is the additive monoid homomorphism $(x,y)\mapsto(x^q,y^q)$ on the affine points of $W_0.\mathrm{map}\,f$ over $k$, with `frobCardHom_injective` always, and `frobCardHom_surjective`, hence `frobCardHom_bijective`, when $k$ is algebraically closed (using $q$-th roots in $k$). An auxiliary finite-field lemma, [`FiniteField.mem_range_iff_pow_card_eq_self`](../def/WeierstrassCurve_FrobeniusCardHom.html#L9), states that $x \in k$ lies in the image of $f$ if and only if $x^{\#F}=x$, proved by comparing the image of $F$ with the root set of $X^{\#F}-X$.
--
--   **Relation to Mathlib.** Built on Mathlib's `WeierstrassCurve`, its base change `map`, the affine point group `Affine.Point` and the compatibilities `Affine.map_negY`, `Affine.map_slope`, `Affine.map_addX`, `Affine.map_addY`, `Affine.map_nonsingular`, together with `iterateFrobenius`. Mathlib has no Frobenius endomorphism of the group of points of a Weierstrass curve; `frobPoint` and `frobCardHom` are the project's own, and only the additive group structure is produced here (no isogeny, degree or fixed-point statement).
--
--   **Where it is used.** This provides the $q$-power Frobenius acting on the points of an elliptic curve over a finite field, in the form of an additive endomorphism of the affine point group that is bijective over an algebraically closed base. It is the starting point for the development of the geometric Frobenius on torsion points, where the Frobenius trace of a curve over a finite field is compared with Hecke eigenvalues.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_WeierstrassCurve_FrobeniusCardHom.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

namespace FiniteField

theorem mem_range_iff_pow_card_eq_self {F k : Type*} [Field F] [Fintype F] [Field k]
    (f : F →+* k) (x : k) : x ∈ Set.range f ↔ x ^ Fintype.card F = x := by
  classical
  constructor
  · rintro ⟨a, rfl⟩
    rw [← map_pow, FiniteField.pow_card]
  · intro hx
    have h1 : (1 : ℕ) < Fintype.card F := Fintype.one_lt_card
    have hg0 : (X ^ Fintype.card F - X : k[X]) ≠ 0 :=
      FiniteField.X_pow_card_sub_X_ne_zero k h1
    have hdeg : (X ^ Fintype.card F - X : k[X]).natDegree = Fintype.card F :=
      FiniteField.X_pow_card_sub_X_natDegree_eq k h1
    have hSroots : Finset.univ.image f ⊆ (X ^ Fintype.card F - X : k[X]).roots.toFinset := by
      intro a ha
      rw [Finset.mem_image] at ha
      obtain ⟨b, -, rfl⟩ := ha
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hg0]
      simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
      rw [← map_pow, FiniteField.pow_card, sub_self]
    have hScard : (Finset.univ.image f).card = Fintype.card F := by
      rw [Finset.card_image_of_injective _ f.injective, Finset.card_univ]
    have hcardroots : (X ^ Fintype.card F - X : k[X]).roots.toFinset.card ≤ Fintype.card F :=
      le_trans (Multiset.toFinset_card_le _) (le_trans (Polynomial.card_roots' _) hdeg.le)
    have hSeq : Finset.univ.image f = (X ^ Fintype.card F - X : k[X]).roots.toFinset :=
      Finset.eq_of_subset_of_card_le hSroots (hcardroots.trans hScard.symm.le)
    have hxroot : x ∈ (X ^ Fintype.card F - X : k[X]).roots.toFinset := by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hg0]
      simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
      rw [hx, sub_self]
    rw [← hSeq, Finset.mem_image] at hxroot
    obtain ⟨a, -, ha⟩ := hxroot
    exact ⟨a, ha⟩

end FiniteField

namespace WeierstrassCurve

open WeierstrassCurve.Affine

section FrobPoint

variable {k : Type*} [Field k] {V : WeierstrassCurve k}

def frobPoint (q : ℕ)
    (hfrob : ∀ {x y : k}, V.toAffine.Nonsingular x y → V.toAffine.Nonsingular (x ^ q) (y ^ q)) :
    V.toAffine.Point → V.toAffine.Point
  | .zero => .zero
  | .some x y h => .some (x ^ q) (y ^ q) (hfrob h)

variable {q : ℕ}
  {hfrob : ∀ {x y : k}, V.toAffine.Nonsingular x y → V.toAffine.Nonsingular (x ^ q) (y ^ q)}

@[simp]
lemma frobPoint_zero : frobPoint q hfrob (0 : V.toAffine.Point) = 0 :=
  rfl

lemma frobPoint_some {x y : k} (h : V.toAffine.Nonsingular x y) :
    frobPoint q hfrob (.some x y h) = .some (x ^ q) (y ^ q) (hfrob h) :=
  rfl

lemma frobPoint_zero' :
    frobPoint q hfrob (Affine.Point.zero : V.toAffine.Point) = Affine.Point.zero :=
  rfl

end FrobPoint

section PowHelpers

variable {k : Type*} [Field k] {V : WeierstrassCurve k} {q : ℕ} {φ : k →+* k}

private lemma some_congr {R : Type*} [CommRing R] {V' : Affine R} {x₁ x₂ y₁ y₂ : R}
    (hx : x₁ = x₂) (hy : y₁ = y₂) (h₁ : V'.Nonsingular x₁ y₁) (h₂ : V'.Nonsingular x₂ y₂) :
    Affine.Point.some x₁ y₁ h₁ = Affine.Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

lemma pow_injective_of_ringHom (hφ : ∀ a : k, φ a = a ^ q) {a b : k} (hab : a ^ q = b ^ q) :
    a = b :=
  φ.injective (by rw [hφ, hφ]; exact hab)

lemma negY_pow (hφ : ∀ a : k, φ a = a ^ q) (hfix : V.map φ = V) (x y : k) :
    V.toAffine.negY (x ^ q) (y ^ q) = V.toAffine.negY x y ^ q := by
  have hfix' : V.toAffine.map φ = V.toAffine := hfix
  have h := Affine.map_negY (W' := V.toAffine) φ x y
  rw [hfix'] at h
  simpa only [hφ] using h

lemma slope_pow [DecidableEq k] (hφ : ∀ a : k, φ a = a ^ q) (hfix : V.map φ = V)
    (x₁ x₂ y₁ y₂ : k) :
    V.toAffine.slope (x₁ ^ q) (x₂ ^ q) (y₁ ^ q) (y₂ ^ q)
      = V.toAffine.slope x₁ x₂ y₁ y₂ ^ q := by
  have hfix' : V.toAffine.map φ = V.toAffine := hfix
  have h := Affine.map_slope (W := V.toAffine) φ x₁ x₂ y₁ y₂
  rw [hfix'] at h
  simpa only [hφ] using h

lemma addX_slope_pow [DecidableEq k] (hφ : ∀ a : k, φ a = a ^ q) (hfix : V.map φ = V)
    (x₁ x₂ y₁ y₂ : k) :
    V.toAffine.addX (x₁ ^ q) (x₂ ^ q) (V.toAffine.slope (x₁ ^ q) (x₂ ^ q) (y₁ ^ q) (y₂ ^ q))
      = V.toAffine.addX x₁ x₂ (V.toAffine.slope x₁ x₂ y₁ y₂) ^ q := by
  have hfix' : V.toAffine.map φ = V.toAffine := hfix
  have h := Affine.map_addX (W' := V.toAffine) φ x₁ x₂ (V.toAffine.slope x₁ x₂ y₁ y₂)
  rw [hfix'] at h
  rw [slope_pow hφ hfix x₁ x₂ y₁ y₂]
  simpa only [hφ] using h

lemma addY_slope_pow [DecidableEq k] (hφ : ∀ a : k, φ a = a ^ q) (hfix : V.map φ = V)
    (x₁ x₂ y₁ y₂ : k) :
    V.toAffine.addY (x₁ ^ q) (x₂ ^ q) (y₁ ^ q)
        (V.toAffine.slope (x₁ ^ q) (x₂ ^ q) (y₁ ^ q) (y₂ ^ q))
      = V.toAffine.addY x₁ x₂ y₁ (V.toAffine.slope x₁ x₂ y₁ y₂) ^ q := by
  have hfix' : V.toAffine.map φ = V.toAffine := hfix
  have h := Affine.map_addY (W' := V.toAffine) (f := φ) (x₁ := x₁) (x₂ := x₂) (y₁ := y₁)
    (ℓ := V.toAffine.slope x₁ x₂ y₁ y₂)
  rw [hfix'] at h
  rw [slope_pow hφ hfix x₁ x₂ y₁ y₂]
  simpa only [hφ] using h

variable {hfrob : ∀ {x y : k}, V.toAffine.Nonsingular x y → V.toAffine.Nonsingular (x ^ q) (y ^ q)}

theorem frobPoint_neg (hφ : ∀ a : k, φ a = a ^ q) (hfix : V.map φ = V)
    (P : V.toAffine.Point) :
    frobPoint q hfrob (-P) = -frobPoint q hfrob P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · simp only [Affine.Point.neg_some, frobPoint_some]
    exact some_congr rfl (negY_pow hφ hfix x y).symm _ _

theorem frobPoint_add [DecidableEq k] (hφ : ∀ a : k, φ a = a ^ q) (hfix : V.map φ = V)
    (P Q : V.toAffine.Point) :
    frobPoint q hfrob (P + Q) = frobPoint q hfrob P + frobPoint q hfrob Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  any_goals rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = V.toAffine.negY x₂ y₂
  · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2, frobPoint_zero, frobPoint_some, frobPoint_some,
      Affine.Point.add_of_Y_eq (by rw [hxy.1]) (by rw [hxy.2, negY_pow hφ hfix])]
  · have hxy' : ¬(x₁ ^ q = x₂ ^ q ∧ y₁ ^ q = V.toAffine.negY (x₂ ^ q) (y₂ ^ q)) := by
      rintro ⟨hx, hy⟩
      rw [negY_pow hφ hfix] at hy
      exact hxy ⟨pow_injective_of_ringHom hφ hx, pow_injective_of_ringHom hφ hy⟩
    rw [Affine.Point.add_some hxy]
    simp only [frobPoint_some]
    rw [Affine.Point.add_some hxy']
    exact some_congr (addX_slope_pow hφ hfix x₁ x₂ y₁ y₂).symm
      (addY_slope_pow hφ hfix x₁ x₂ y₁ y₂).symm _ _

end PowHelpers

section FrobCardHom

variable {F : Type*} [Field F] [Fintype F] {k : Type*} [Field k] (f : F →+* k)
variable {W₀ : WeierstrassCurve F}

theorem nonsingular_pow_card_map {x y : k} (h : (W₀.map f).toAffine.Nonsingular x y) :
    (W₀.map f).toAffine.Nonsingular (x ^ Fintype.card F) (y ^ Fintype.card F) := by
  obtain ⟨p, hcharF, n, hp, hcard⟩ := FiniteField.card' (K := F)
  haveI : CharP F p := hcharF
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP k p := charP_of_injective_ringHom f.injective p
  haveI : ExpChar k p := ExpChar.prime hp
  have hfix : (W₀.map f).map (iterateFrobenius k p n) = W₀.map f := by
    rw [map_map]
    congr 1
    ext a
    simp only [RingHom.comp_apply, iterateFrobenius_def]
    rw [← map_pow, ← hcard, FiniteField.pow_card]
  have hmap : ((W₀.map f).map (iterateFrobenius k p n)).toAffine.Nonsingular
      (iterateFrobenius k p n x) (iterateFrobenius k p n y) :=
    ((W₀.map f).toAffine.map_nonsingular (iterateFrobenius k p n).injective x y).mpr h
  rw [hfix] at hmap
  simpa only [iterateFrobenius_def, hcard] using hmap

theorem exists_ringHom_pow_card_fixing :
    ∃ φ : k →+* k, (∀ a : k, φ a = a ^ Fintype.card F) ∧ (W₀.map f).map φ = W₀.map f := by
  obtain ⟨p, hcharF, n, hp, hcard⟩ := FiniteField.card' (K := F)
  haveI : CharP F p := hcharF
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP k p := charP_of_injective_ringHom f.injective p
  haveI : ExpChar k p := ExpChar.prime hp
  refine ⟨iterateFrobenius k p n, fun a => by rw [iterateFrobenius_def, hcard], ?_⟩
  rw [map_map]
  congr 1
  ext a
  simp only [RingHom.comp_apply, iterateFrobenius_def]
  rw [← map_pow, ← hcard, FiniteField.pow_card]

variable [DecidableEq k]

theorem frobPoint_card_add (P Q : (W₀.map f).toAffine.Point) :
    frobPoint (Fintype.card F) (fun {_ _} h => nonsingular_pow_card_map f h) (P + Q)
      = frobPoint (Fintype.card F) (fun {_ _} h => nonsingular_pow_card_map f h) P
        + frobPoint (Fintype.card F) (fun {_ _} h => nonsingular_pow_card_map f h) Q := by
  obtain ⟨φ, hφ, hfix⟩ := exists_ringHom_pow_card_fixing f (W₀ := W₀)
  exact frobPoint_add hφ hfix P Q

noncomputable def frobCardHom :
    (W₀.map f).toAffine.Point →+ (W₀.map f).toAffine.Point where
  toFun := frobPoint (Fintype.card F) (fun {_ _} h => nonsingular_pow_card_map f h)
  map_zero' := rfl
  map_add' := frobPoint_card_add f

@[simp]
lemma frobCardHom_apply (P : (W₀.map f).toAffine.Point) :
    frobCardHom f P
      = frobPoint (Fintype.card F) (fun {_ _} h => nonsingular_pow_card_map f h) P :=
  rfl

theorem frobCardHom_injective :
    Function.Injective (frobCardHom f (W₀ := W₀)) := by
  obtain ⟨φ, hφ, hfix⟩ := exists_ringHom_pow_card_fixing f (W₀ := W₀)
  intro P Q hPQ
  simp only [frobCardHom_apply] at hPQ
  cases P with
  | zero =>
    cases Q with
    | zero => rfl
    | some x y h =>
      rw [frobPoint_zero', frobPoint_some] at hPQ
      simp at hPQ
  | some x y h =>
    cases Q with
    | zero =>
      rw [frobPoint_zero', frobPoint_some] at hPQ
      simp at hPQ
    | some x' y' h' =>
      rw [frobPoint_some, frobPoint_some, Affine.Point.some.injEq] at hPQ
      exact some_congr (pow_injective_of_ringHom hφ hPQ.1) (pow_injective_of_ringHom hφ hPQ.2)
        h h'

theorem frobCardHom_surjective [IsAlgClosed k] :
    Function.Surjective (frobCardHom f (W₀ := W₀)) := by
  obtain ⟨φ, hφ, hfix⟩ := exists_ringHom_pow_card_fixing f (W₀ := W₀)
  intro P
  cases P with
  | zero => exact ⟨0, map_zero _⟩
  | some x' y' h' =>
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq x' (n := Fintype.card F) Fintype.card_pos
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq y' (n := Fintype.card F) Fintype.card_pos
    have hns : (W₀.map f).toAffine.Nonsingular x y := by
      have hmap : ((W₀.map f).map φ).toAffine.Nonsingular (φ x) (φ y) := by
        rw [hfix, hφ x, hφ y, hx, hy]
        exact h'
      exact ((W₀.map f).toAffine.map_nonsingular φ.injective x y).mp hmap
    refine ⟨.some x y hns, ?_⟩
    rw [frobCardHom_apply, frobPoint_some]
    exact some_congr hx hy _ h'

theorem frobCardHom_bijective [IsAlgClosed k] :
    Function.Bijective (frobCardHom f (W₀ := W₀)) :=
  ⟨frobCardHom_injective f, frobCardHom_surjective f⟩

end FrobCardHom

end WeierstrassCurve


