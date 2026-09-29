-- Prove2me | Definitions.Def_SteinitzExchange_LocalSupermod_IntegralBaseSet
-- name    : SteinitzExchange_LocalSupermod_IntegralBaseSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:46:39.100754+00:00
-- url     : https://prove2.me/theorems/1206571a-4276-4561-8e48-12a8c2949e22
-- title:
--   Finite integral base sets (B1), characteristic vectors and the pairing on ℝ^V
-- statement:
--   Let $V$ be a finite nonempty set. For $u\in V$ let $\chi_u\in\mathbb Z^V$ be its characteristic vector ($\chi_u(v)=1$ if $v=u$, $0$ otherwise), and for a subset $X\subseteq V$ let $\chi_X\in\mathbb R^V$ be its characteristic vector ($\chi_X(v)=1$ if $v\in X$, $0$ otherwise). For $x\in\mathbb R^V$ write $\operatorname{supp}^+(x)=\{v\mid x(v)>0\}$, $\operatorname{supp}^-(x)=\{v\mid x(v)<0\}$ and $x(X)=\sum_{v\in X}x(v)$; for $p,b\in\mathbb R^V$ let $\langle p,b\rangle=\sum_{v\in V}p(v)\,b(v)$. For a finite $B\subseteq\mathbb Z^V$, $\overline B\subseteq\mathbb R^V$ denotes its convex hull.
--
--   A **finite integral base set** is a finite nonempty set $B\subseteq\mathbb Z^V$ satisfying the exchange axiom
--
--   $$\text{(B1)}\quad x,y\in B,\ u\in\operatorname{supp}^+(x-y)\ \Longrightarrow\ \exists\,v\in\operatorname{supp}^-(x-y):\ x-\chi_u+\chi_v\in B.$$
--
--   Finite integral base sets are the sets of integer points of integral base polytopes (Theorem 2.1 of the paper); they are the domains of all functions in this mission.
--
--   **Formalization Note.** Integer vectors are `V → ℤ`, real vectors `V → ℝ`, and the embedding is `toReal`. `chi u` is `Pi.single u 1`, `charVec X` is $\chi_X$ (real-valued), `sumOn x X` is $x(X)$ for an integer vector, and `hull B` is Mathlib's `convexHull ℝ` of the image of $B$ in $\mathbb R^V$. The bodies coincide with those of the first mission of this series.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 276 (Section 2.1, notation), p. 277 (B1), p. 285 (Eq. (4.4)), p. 290 (χ_X in (C1), (C2))

import Mathlib

namespace SteinitzExchange.LocalSupermod

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

/-- The characteristic vector `χ_X ∈ ℝ^V` of a subset `X ⊆ V`: `χ_X(v) = 1` if `v ∈ X`, else `0`
(used in (C1), (C2), Murota 1996, p. 290). -/
def charVec {V : Type*} [DecidableEq V] (X : Finset V) : V → ℝ :=
  fun v => if v ∈ X then 1 else 0

/-- `B̄`: the convex hull in `ℝ^V` of a finite set `B ⊆ ℤ^V` (Murota 1996, p. 285, Eq. (4.4)). -/
def hull {V : Type*} (B : Finset (V → ℤ)) : Set (V → ℝ) :=
  convexHull ℝ (toReal '' (B : Set (V → ℤ)))

/-- A finite integral base set (Murota 1996, p. 277, (B1)): a finite nonempty `B ⊆ ℤ^V` such that
for `x, y ∈ B` and `u ∈ supp⁺(x − y)` there is `v ∈ supp⁻(x − y)` with `x − χ_u + χ_v ∈ B`. -/
def IsIntegralBaseSet {V : Type*} [DecidableEq V] (B : Finset (V → ℤ)) : Prop :=
  B.Nonempty ∧
    ∀ x ∈ B, ∀ y ∈ B, ∀ u : V, 0 < (x - y) u →
      ∃ v : V, (x - y) v < 0 ∧ x - chi u + chi v ∈ B

end SteinitzExchange.LocalSupermod


