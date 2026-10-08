-- Prove2me | Definitions.Def_TalagrandConc_QPoints_Basic
-- name    : TalagrandConc_QPoints_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:38:38.661283+00:00
-- url     : https://prove2.me/theorems/8d5a6dbd-bc2f-4837-97fb-bf8d32f50cba
-- title:
--   The q-point control functional $f(A_1,\dots,A_q,x)$ of (3.1.1), sections and projections
-- statement:
--   Let $(\Omega,\mu)$ be a probability space, $N\ge 0$ and $q\ge 1$ integers, and write points of $\Omega^N$ as $x=(x_1,\dots,x_N)$. For $q$ points $y^1,\dots,y^q\in\Omega^N$ we count the coordinates of $x$ that none of them **captures**:
--   $$\#\{\,i\le N:\ x_i\notin\{y^1_i,\dots,y^q_i\}\,\}.$$
--   For subsets $A_1,\dots,A_q\subseteq\Omega^N$, Talagrand's **control by $q$ points** (Eq. (3.1.1)) is
--   $$f(A_1,\dots,A_q,x)=\inf\big\{\#\{i\le N: x_i\notin\{y^1_i,\dots,y^q_i\}\};\ y^1\in A_1,\dots,y^q\in A_q\big\},$$
--   the smallest number of coordinates of $x$ left uncaptured when one point is chosen in each $A_j$. It takes values in $\{0,1,\dots,N\}\cup\{+\infty\}$, with the value $+\infty$ exactly when some $A_j$ is empty.
--
--   The module also fixes the power $a^{n}$ of a number $a\in[0,\infty]$ with an exponent $n\in\{0,1,2,\dots\}\cup\{+\infty\}$, setting $a^{+\infty}=+\infty$ (the limit of $a^n$ for $a>1$, the only case used), and, for $A\subseteq\Omega^{N+1}$ and $\omega\in\Omega$, the section and the projection of Eq. (2.1.5):
--   $$A(\omega)=\{x\in\Omega^N:(x,\omega)\in A\},\qquad B=\{x\in\Omega^N:\exists\,\omega\in\Omega,\ (x,\omega)\in A\}.$$
--
--   These are the objects of Section 3 of Talagrand's paper: $f$ measures how far $x$ is from the family $(A_1,\dots,A_q)$ when several points may cooperate to capture its coordinates.
--
--   **Formalization Note** $\Omega^N$ is `Fin N → Ω` (coordinates indexed $0,\dots,N-1$) and $\Omega^{N+1}\ni(x,\omega)$ is `Fin.snoc x ω`, the last coordinate being $\omega$. The infimum is taken in `ℕ∞`, so an empty $A_j$ gives $\top$ rather than a junk value $0$.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 113, Eq. (3.1.1); p. 83, Eq. (2.1.5)

import Mathlib

namespace TalagrandConc.QPoints

open scoped ENNReal

/-- For `x ∈ Ω^N` and `q` points `y 0, …, y (q-1) ∈ Ω^N`, the number of coordinates
`i` with `x i ∉ {y 0 i, …, y (q-1) i}`: the coordinates of `x` not captured by the `y j`. -/
noncomputable def uncaptured {Ω : Type*} {N q : ℕ} (y : Fin q → Fin N → Ω)
    (x : Fin N → Ω) : ℕ :=
  Nat.card {i : Fin N // ∀ j : Fin q, x i ≠ y j i}

/-- Talagrand's (3.1.1): `f(A_1, …, A_q, x)`, the infimum of `uncaptured y x` over all
choices `y j ∈ A j`. Computed in `ℕ∞`, so it is `⊤` when some `A j` is empty. -/
noncomputable def qDist {Ω : Type*} {N q : ℕ} (A : Fin q → Set (Fin N → Ω))
    (x : Fin N → Ω) : ℕ∞ :=
  ⨅ (y : Fin q → Fin N → Ω) (_ : ∀ j, y j ∈ A j), (uncaptured y x : ℕ∞)

/-- `a ^ n` for an extended natural exponent: `a ^ ⊤ := ⊤` (the limit of `a ^ n` for
`a > 1`, the only bases used in this chapter). -/
noncomputable def epow (a : ℝ≥0∞) : ℕ∞ → ℝ≥0∞ :=
  ENat.recTopCoe ⊤ (fun m : ℕ => a ^ m)

/-- The section `A(ω) = {x ∈ Ω^N : (x, ω) ∈ A}` of `A ⊆ Ω^{N+1}` (Talagrand (2.1.5));
`(x, ω)` is `Fin.snoc x ω`, the last coordinate being `ω`. -/
def sliceAt {Ω : Type*} {N : ℕ} (A : Set (Fin (N + 1) → Ω)) (ω : Ω) : Set (Fin N → Ω) :=
  {x | (Fin.snoc x ω : Fin (N + 1) → Ω) ∈ A}

/-- The projection `B = {x ∈ Ω^N : ∃ ω, (x, ω) ∈ A}` of `A ⊆ Ω^{N+1}` on `Ω^N`. -/
def projLast {Ω : Type*} {N : ℕ} (A : Set (Fin (N + 1) → Ω)) : Set (Fin N → Ω) :=
  {x | ∃ ω : Ω, (Fin.snoc x ω : Fin (N + 1) → Ω) ∈ A}

end TalagrandConc.QPoints


