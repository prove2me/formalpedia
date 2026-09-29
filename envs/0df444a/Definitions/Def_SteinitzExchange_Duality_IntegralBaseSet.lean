-- Prove2me | Definitions.Def_SteinitzExchange_Duality_IntegralBaseSet
-- name    : SteinitzExchange_Duality_IntegralBaseSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:53:13.214009+00:00
-- url     : https://prove2.me/theorems/0719ceca-ea42-4d69-a79f-b6e3753ad8ee
-- title:
--   Finite integral base sets (B1), their convex hulls, and the notation of §2.1
-- statement:
--   Let $V$ be a finite nonempty set. For $u\in V$ let $\chi_u\in\mathbb Z^V$ be its characteristic vector ($\chi_u(v)=1$ if $v=u$ and $0$ otherwise). For $x\in\mathbb R^V$ write $\operatorname{supp}^+(x)=\{v\mid x(v)>0\}$, $\operatorname{supp}^-(x)=\{v\mid x(v)<0\}$ and $x(X)=\sum_{v\in X}x(v)$ for $X\subseteq V$; for $p,b\in\mathbb R^V$ let $\langle p,b\rangle=\sum_{v\in V}p(v)\,b(v)$.
--
--   A **finite integral base set** is a finite nonempty set $B\subseteq\mathbb Z^V$ satisfying the exchange axiom
--
--   $$\text{(B1)}\quad x,y\in B,\ u\in\operatorname{supp}^+(x-y)\ \Longrightarrow\ \exists\,v\in\operatorname{supp}^-(x-y):\ x-\chi_u+\chi_v\in B.$$
--
--   For a finite $B\subseteq\mathbb Z^V$, $\overline B\subseteq\mathbb R^V$ denotes its convex hull.
--
--   Finite integral base sets are exactly the sets of integer points of integral base polytopes (Theorem 2.1 of the paper); they are the domains $B_1,B_2$ of the two functions in the Fenchel-type duality.
--
--   **Formalization Note.** Integer vectors are `V → ℤ`, real vectors `V → ℝ`, and `toReal` is the coordinatewise embedding $\mathbb Z^V\to\mathbb R^V$. `chi u` is `Pi.single u 1`; `sumOn x X` is $x(X)$ for an integer vector; `hull B` is Mathlib's `convexHull ℝ` of the image of $B$ in $\mathbb R^V$. Nonemptiness is part of `IsIntegralBaseSet`.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 276 (Section 2.1, notation), p. 277 (B1), p. 285 (Eq. (4.4))

import Mathlib

namespace SteinitzExchange.Duality

/-- The characteristic vector `χ_u ∈ ℤ^V` of `u ∈ V`: `χ_u(v) = 1` if `v = u`, else `0`
(Murota 1996, p. 276, §2.1). -/
def chi {V : Type*} [DecidableEq V] (u : V) : V → ℤ :=
  Pi.single u 1

/-- The embedding `ℤ^V → ℝ^V`, `x ↦ (x(v) : ℝ)_{v ∈ V}`. -/
def toReal {V : Type*} (x : V → ℤ) : V → ℝ :=
  fun v => (x v : ℝ)

/-- The pairing `⟨p, b⟩ = ∑_{v ∈ V} p(v) b(v)` on `ℝ^V` (Murota 1996, p. 276, §2.1). -/
def pairing {V : Type*} [Fintype V] (p b : V → ℝ) : ℝ :=
  ∑ v, p v * b v

/-- `x(X) = ∑_{v ∈ X} x(v)` for an integer vector `x` and `X ⊆ V` (Murota 1996, p. 276, §2.1). -/
def sumOn {V : Type*} (x : V → ℤ) (X : Finset V) : ℤ :=
  ∑ v ∈ X, x v

/-- `B̄`: the convex hull in `ℝ^V` of a finite set `B ⊆ ℤ^V` (Murota 1996, p. 285, Eq. (4.4)). -/
def hull {V : Type*} (B : Finset (V → ℤ)) : Set (V → ℝ) :=
  convexHull ℝ (toReal '' (B : Set (V → ℤ)))

/-- A finite integral base set (Murota 1996, p. 277, (B1)): a finite nonempty `B ⊆ ℤ^V` such that
for `x, y ∈ B` and `u ∈ supp⁺(x − y)` there is `v ∈ supp⁻(x − y)` with `x − χ_u + χ_v ∈ B`. -/
def IsIntegralBaseSet {V : Type*} [DecidableEq V] (B : Finset (V → ℤ)) : Prop :=
  B.Nonempty ∧
    ∀ x ∈ B, ∀ y ∈ B, ∀ u : V, 0 < (x - y) u →
      ∃ v : V, (x - y) v < 0 ∧ x - chi u + chi v ∈ B

end SteinitzExchange.Duality


