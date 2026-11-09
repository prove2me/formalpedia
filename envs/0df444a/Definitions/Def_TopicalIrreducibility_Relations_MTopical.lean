-- Prove2me | Definitions.Def_TopicalIrreducibility_Relations_MTopical
-- name    : TopicalIrreducibility_Relations_MTopical
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:04:34.080352+00:00
-- url     : https://prove2.me/theorems/fb60052c-b1ac-4080-9d85-7dd6f2a35b3a
-- title:
--   p. 1, p. 3 — m-topical maps on $\mathbb R^n_{\ge0}$, subadditivity and m-convexity
-- statement:
--   Fix a dimension $n\ge 0$. The **standard cone** is $\mathbb R^n_{\ge0}=[0,\infty)^n$, the set of real vectors with nonnegative entries, with the coordinatewise order ($x\le y$ iff $x_i\le y_i$ for all $i\in[n]$) and the usual (product) topology. Its interior is $\mathbb R^n_{>0}$, the vectors all of whose entries are positive.
--
--   A map $f:\mathbb R^n_{\ge0}\to\mathbb R^n_{\ge0}$ is **multiplicatively topical** (**m-topical**) if
--
--   1. $f$ is continuous on the whole closed cone;
--   2. $f$ is order-preserving: $x\le y$ implies $f(x)\le f(y)$;
--   3. $f$ is homogeneous: $f(\lambda x)=\lambda f(x)$ for all $x\in\mathbb R^n_{\ge0}$ and all real $\lambda>0$;
--   4. $f$ leaves the interior invariant: $f(\mathbb R^n_{>0})\subseteq\mathbb R^n_{>0}$.
--
--   The map $f$ is **subadditive** if $f(x+y)\le f(x)+f(y)$ for all $x,y\in\mathbb R^n_{\ge0}$, and **multiplicatively convex** (**m-convex**) if
--   $$
--   f\bigl(x^{\lambda}y^{1-\lambda}\bigr)\le f(x)^{\lambda}f(y)^{1-\lambda}\qquad\text{for all }x,y\in\mathbb R^n_{>0},\ 0<\lambda<1,
--   $$
--   where powers and products are taken entrywise.
--
--   These are the standing objects of nonlinear Perron–Frobenius theory used throughout the paper; subadditivity and m-convexity are separate, optional properties of an m-topical map, not part of its definition.
--
--   **Formalization Note** The cone is the type `Fin n → ℝ≥0` of nonnegative real vectors, whose order, topology, addition and scalar multiplication are the coordinatewise ones of $\mathbb R^n$ restricted to the cone. Positive real scalars are positive elements of `ℝ≥0`. Entrywise real powers are `NNReal.rpow`; m-convexity is only required at interior points, where every entry involved is positive.
-- source:
--   Brian Lins, Irreducibility for Topical Maps, STOC 2027 submission #201 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/201.pdf, p. 1 (definition of m-topical maps) and p. 3 (subadditive, m-convex); PDF page = printed page

import Mathlib

open scoped NNReal

namespace TopicalIrreducibility.Relations

/-- The standard cone `ℝⁿ_{≥0} = [0, ∞)ⁿ`, as the type of nonnegative real vectors with the
coordinatewise order and the product (= subspace) topology. -/
abbrev StdCone (n : ℕ) : Type := Fin n → ℝ≥0

/-- A vector lies in the interior `ℝⁿ_{>0}` of the standard cone: all entries are positive. -/
def IsInterior {n : ℕ} (x : StdCone n) : Prop := ∀ i, 0 < x i

/-- Multiplicatively topical (m-topical) map, p. 1: continuous, order-preserving, homogeneous
(`f (c • x) = c • f x` for every real `c > 0`) and leaving the interior invariant. -/
structure IsMTopical {n : ℕ} (f : StdCone n → StdCone n) : Prop where
  continuous : Continuous f
  monotone : Monotone f
  homogeneous : ∀ c : ℝ≥0, 0 < c → ∀ x : StdCone n, f (c • x) = c • f x
  interior : ∀ x : StdCone n, IsInterior x → IsInterior (f x)

/-- Subadditivity, p. 3: `f (x + y) ≤ f x + f y` (coordinatewise) for all `x, y ∈ ℝⁿ_{≥0}`. -/
def IsSubadditive {n : ℕ} (f : StdCone n → StdCone n) : Prop :=
  ∀ x y : StdCone n, f (x + y) ≤ f x + f y

/-- Multiplicative convexity (m-convexity), p. 3: for all `x, y ∈ ℝⁿ_{>0}` and real
`0 < λ < 1`, `f (x^λ y^(1-λ)) ≤ f(x)^λ f(y)^(1-λ)`, powers and products taken entrywise. -/
def IsMConvex {n : ℕ} (f : StdCone n → StdCone n) : Prop :=
  ∀ x y : StdCone n, IsInterior x → IsInterior y → ∀ l : ℝ, 0 < l → l < 1 →
    ∀ i, f (fun k => x k ^ l * y k ^ (1 - l)) i ≤ f x i ^ l * f y i ^ (1 - l)

end TopicalIrreducibility.Relations


