-- Prove2me | Definitions.Def_WeilConjectures_zetaFunction
-- name    : WeilConjectures_zetaFunction
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-12T14:56:28.256855+00:00
-- url     : https://prove2.me/theorems/59682f8d-573f-420e-8598-69b390007cf9
-- title:
--   Point counts $N_m$ and the zeta function $Z(X,T)$ over a finite field
-- statement:
--   Let $k=\mathbb F_q$ be a finite field of characteristic $p$ and $f:X\to\operatorname{Spec}k$ a $k$-scheme.
--
--   1. For a $k$-algebra $L$, the number of **$L$-points** of $X$ is the number of morphisms $\operatorname{Spec}L\to X$ over $\operatorname{Spec}k$.
--   2. For $m\ge1$, $N_m$ is the number of $\mathbb F_{q^m}$-points of $X$, where $\mathbb F_{q^m}$ is a fixed extension of $k$ of degree $m$; by convention $N_0=0$.
--   3. For any sequence $(N_m)_{m\ge1}$ of natural numbers, its zeta function is the formal power series
--
--   $$\exp\Big(\sum_{m\ge1}\frac{N_m}{m}T^m\Big)\in\mathbb Q[[T]],$$
--
--   and the **zeta function of $X$** is $Z(X,T)$, this series for the point counts of $X$. With $T=q^{-s}$ it is the function $\zeta(X,s)$ of the source.
--
--   **Formalization Note** The extension of degree $m$ is `FiniteField.Extension k p m`; the number of points does not depend on this choice up to isomorphism. The cardinality is `Nat.card`, which is $0$ for an infinite set; for schemes of finite type over $k$ the set is finite. The exponential of a series without constant term is `PowerSeries.subst` into `PowerSeries.exp ℚ`. Definitions: `zetaOfCounts`, `pointsOver`, `pointCount`, `zetaFunction`.
-- source:
--   Wikipedia, "Weil conjectures", https://en.wikipedia.org/wiki/Weil_conjectures (PDF snapshot supplied by the proposer, 14 pp.), section "Statement of the Weil conjectures", definition of $\zeta(X,s)$ and of $N_m$

import Mathlib

/-!
Point counts of a scheme over a finite field and its (Hasse–Weil) zeta function
`Z(X, T) = exp(∑_{m ≥ 1} N_m T^m / m)` as a formal power series in `T = q^{-s}`.
-/

namespace WeilConjectures

open AlgebraicGeometry CategoryTheory

/-- The zeta function attached to a sequence of point counts `N : ℕ → ℕ`:
the formal power series `exp(∑_{m ≥ 1} (N m / m) T^m) ∈ ℚ⟦T⟧` (the value `N 0` is ignored). -/
noncomputable def zetaOfCounts (N : ℕ → ℕ) : PowerSeries ℚ :=
  PowerSeries.subst
    (PowerSeries.mk fun m => if m = 0 then (0 : ℚ) else (N m : ℚ) / (m : ℚ))
    (PowerSeries.exp ℚ)

/-- The set of `L`-valued points of a `k`-scheme `f : X ⟶ Spec k`, for a `k`-algebra `L`:
morphisms `Spec L ⟶ X` over `Spec k`; `pointsOver f L` is its cardinality (as `Nat.card`). -/
noncomputable def pointsOver {k : Type} [Field k] {X : Scheme} (f : X ⟶ Spec (.of k))
    (L : Type) [CommRing L] [Algebra k L] : ℕ :=
  Nat.card {x : Spec (.of L) ⟶ X // x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k L))}

/-- `pointCount p f m = N_m`, the number of points of `X` defined over the degree-`m`
extension `𝔽_{q^m}` of the finite field `k = 𝔽_q` (of characteristic `p`), for `m ≥ 1`;
by convention `N_0 = 0`. -/
noncomputable def pointCount (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [Finite k] [CharP k p]
    {X : Scheme} (f : X ⟶ Spec (.of k)) (m : ℕ) : ℕ :=
  if h : m = 0 then 0 else
    haveI : NeZero m := ⟨h⟩
    pointsOver f (FiniteField.Extension k p m)

/-- The zeta function `Z(X, T) = exp(∑_{m ≥ 1} N_m T^m / m) ∈ ℚ⟦T⟧` of a scheme `X` over
the finite field `k = 𝔽_q`; with `T = q^{-s}` this is `ζ(X, s)`. -/
noncomputable def zetaFunction (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [Finite k]
    [CharP k p] {X : Scheme} (f : X ⟶ Spec (.of k)) : PowerSeries ℚ :=
  zetaOfCounts (pointCount p f)

end WeilConjectures


