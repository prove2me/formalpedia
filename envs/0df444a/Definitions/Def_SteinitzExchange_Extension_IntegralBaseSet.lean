-- Prove2me | Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet
-- name    : SteinitzExchange_Extension_IntegralBaseSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:39:23.257595+00:00
-- url     : https://prove2.me/theorems/8fa28ba9-6678-4c45-8861-7bdaf606c914
-- title:
--   Finite integral base sets (B1) and integral base polytopes
-- statement:
--   Let $V$ be a finite nonempty set. For $u\in V$ let $\chi_u\in\mathbb Z^V$ be its characteristic vector ($\chi_u(v)=1$ if $v=u$, $0$ otherwise), and for $x\in\mathbb R^V$ write $\operatorname{supp}^+(x)=\{v\mid x(v)>0\}$ and $\operatorname{supp}^-(x)=\{v\mid x(v)<0\}$. For $p,b\in\mathbb R^V$ let $\langle p,b\rangle=\sum_{v\in V}p(v)\,b(v)$.
--
--   A **finite integral base set** is a finite nonempty set $B\subseteq\mathbb Z^V$ satisfying the exchange axiom
--
--   $$\text{(B1)}\quad x,y\in B,\ u\in\operatorname{supp}^+(x-y)\ \Longrightarrow\ \exists\,v\in\operatorname{supp}^-(x-y):\ x-\chi_u+\chi_v\in B.$$
--
--   For a finite $B\subseteq\mathbb Z^V$, $\overline B\subseteq\mathbb R^V$ denotes its convex hull. An **integral base polytope** is a set $P\subseteq\mathbb R^V$ of the form $P=\overline{B'}$ for some finite integral base set $B'$; in particular it is nonempty.
--
--   These are the domains of all functions in the mission. By the folklore Theorem 2.1 of the paper, (B1) characterizes the integer points of the base polytope of an integral submodular system, which is why the convex hull of such a set is called an integral base polytope.
--
--   **Formalization Note.** Integer vectors are `V → ℤ`, real vectors `V → ℝ`, and the embedding is `toReal`. `chi u` is `Pi.single u 1`. `hull B` is Mathlib's `convexHull ℝ` of the image of `B` in $\mathbb R^V$. `IsIntegralBasePolytope P` is defined as "$P$ is the convex hull of a finite set satisfying (B1)", not as "a polytope with integer vertices" (the unit square has integer vertices but is not a base polytope).
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 276 (Section 2.1, notation), p. 277 (B1), pp. 277-278 (integral base polytope, Eq. (2.3)), p. 285 (Eq. (4.4))

import Mathlib

namespace SteinitzExchange.Extension

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

/-- `B̄`: the convex hull in `ℝ^V` of a finite set `B ⊆ ℤ^V` (Murota 1996, p. 285, Eq. (4.4)). -/
def hull {V : Type*} (B : Finset (V → ℤ)) : Set (V → ℝ) :=
  convexHull ℝ (toReal '' (B : Set (V → ℤ)))

/-- A finite integral base set (Murota 1996, p. 277, (B1)): a finite nonempty `B ⊆ ℤ^V` such that
for `x, y ∈ B` and `u ∈ supp⁺(x − y)` there is `v ∈ supp⁻(x − y)` with `x − χ_u + χ_v ∈ B`. -/
def IsIntegralBaseSet {V : Type*} [DecidableEq V] (B : Finset (V → ℤ)) : Prop :=
  B.Nonempty ∧
    ∀ x ∈ B, ∀ y ∈ B, ∀ u : V, 0 < (x - y) u →
      ∃ v : V, (x - y) v < 0 ∧ x - chi u + chi v ∈ B

/-- An integral base polytope: the convex hull `B̄'` of some finite integral base set `B'`
(Murota 1996, pp. 277–278, after Theorem 2.1). It is nonempty and contains no integer points
besides those of `B'` (Eq. (2.3)). -/
def IsIntegralBasePolytope {V : Type*} [DecidableEq V] (P : Set (V → ℝ)) : Prop :=
  ∃ B' : Finset (V → ℤ), IsIntegralBaseSet B' ∧ P = hull B'

end SteinitzExchange.Extension


