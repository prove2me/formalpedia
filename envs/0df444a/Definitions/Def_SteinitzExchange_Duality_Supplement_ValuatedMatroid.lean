-- Prove2me | Definitions.Def_SteinitzExchange_Duality_Supplement_ValuatedMatroid
-- name    : SteinitzExchange_Duality_Supplement_ValuatedMatroid
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T04:26:09.873714+00:00
-- url     : https://prove2.me/theorems/a7fc25ec-375b-4cf0-93a7-b4033de5b46f
-- title:
--   Matroid base families and valuations (MV)
-- statement:
--   Let $E$ be a finite set. A family $\mathcal B\subseteq 2^E$ is the **base family of a matroid** $(E,\mathcal B)$ if it is nonempty and satisfies the Steinitz exchange property: for $X,Y\in\mathcal B$ and $u\in X- Y$ there is $v\in Y- X$ with $X-u+v\in\mathcal B$.
--
--   A **valuation** of $(E,\mathcal B)$ is a function $\omega:\mathcal B\to\mathbb R$ such that
--
--   (MV) for $X,Y\in\mathcal B$ and $u\in X- Y$ there is $v\in Y- X$ with $X-u+v\in\mathcal B$, $Y+u-v\in\mathcal B$ and
--   $$\omega(X)+\omega(Y)\le\omega(X-u+v)+\omega(Y+u-v).$$
--
--   A matroid equipped with a valuation is a **valuated matroid** (Dress and Wenzel). Here $X-u+v=(X\setminus\{u\})\cup\{v\}$ and $Y+u-v=(Y\cup\{u\})\setminus\{v\}$.
--
--   **Formalization Note.** Base families are `Finset (Finset E)`; a valuation is a total function `Finset E → ℝ` of which only the values on $\mathcal B$ are used. `IsValuation ℬ ω` is (MV); `IsValuatedMatroid ℬ ω` is `IsMatroidBases ℬ ∧ IsValuation ℬ ω` (nonemptiness of $\mathcal B$ is part of being a matroid).
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), pp. 274–275, Section 1 (Steinitz exchange property and (MV))

import Mathlib

namespace SteinitzExchange.Duality.Supplement

/-- A matroid on a ground set `E`, given by its family of bases `ℬ ⊆ 2^E` (Murota 1996, p. 274):
`ℬ` is nonempty and satisfies the Steinitz exchange property: for `X, Y ∈ ℬ` and `u ∈ X − Y`
there is `v ∈ Y − X` with `X − u + v ∈ ℬ`. -/
def IsMatroidBases {E : Type*} [DecidableEq E] (ℬ : Finset (Finset E)) : Prop :=
  ℬ.Nonempty ∧ ∀ X ∈ ℬ, ∀ Y ∈ ℬ, ∀ u ∈ X \ Y, ∃ v ∈ Y \ X, insert v (X.erase u) ∈ ℬ

/-- The valuation axiom (MV) (Murota 1996, p. 275): for `X, Y ∈ ℬ` and `u ∈ X − Y` there is
`v ∈ Y − X` with `X − u + v ∈ ℬ`, `Y + u − v ∈ ℬ` and
`ω(X) + ω(Y) ≤ ω(X − u + v) + ω(Y + u − v)`. A function on `ℬ` is modelled as a total function
`Finset E → ℝ` of which only the values on `ℬ` are used. -/
def IsValuation {E : Type*} [DecidableEq E] (ℬ : Finset (Finset E)) (ω : Finset E → ℝ) : Prop :=
  ∀ X ∈ ℬ, ∀ Y ∈ ℬ, ∀ u ∈ X \ Y, ∃ v ∈ Y \ X,
    insert v (X.erase u) ∈ ℬ ∧ (insert u Y).erase v ∈ ℬ ∧
      ω X + ω Y ≤ ω (insert v (X.erase u)) + ω ((insert u Y).erase v)

/-- `ω` is a valuation of the matroid `(E, ℬ)`: `ℬ` is a matroid base family and `ω` satisfies
(MV) (a valuated matroid, Murota 1996, p. 275). -/
def IsValuatedMatroid {E : Type*} [DecidableEq E] (ℬ : Finset (Finset E))
    (ω : Finset E → ℝ) : Prop :=
  IsMatroidBases ℬ ∧ IsValuation ℬ ω

end SteinitzExchange.Duality.Supplement


