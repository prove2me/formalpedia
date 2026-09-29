-- Prove2me | Definitions.Def_RobustLP_Counterpart_UncertainLP
-- name    : RobustLP_Counterpart_UncertainLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T19:24:15.98405+00:00
-- url     : https://prove2.me/theorems/f44936d4-6bde-4983-9430-91f94e10d454
-- title:
--   Uncertain linear program: data $(E,e,A,b,\ell,u)$ and uncertain-entry sets $J_i$; tolerance $b_i^+$ and nominal feasibility
-- statement:
--   Consider a linear program in the form
--   $$
--   \text{minimize } c^T x \quad\text{s.t.}\quad Ex = e,\qquad Ax \le b,\qquad \ell \le x \le u, \tag{LP}
--   $$
--   with $n$ variables $x \in \mathbb{R}^n$, $p$ equality constraints ($E \in \mathbb{R}^{p\times n}$, $e\in\mathbb{R}^p$) and $m$ inequality constraints ($A = (a_{ij}) \in \mathbb{R}^{m\times n}$, $b \in \mathbb{R}^m$). The bounds $\ell_j$ and $u_j$ may be infinite: $\ell_j \in \mathbb{R}\cup\{-\infty\}$, $u_j\in\mathbb{R}\cup\{+\infty\}$. For each inequality row $i$, a set $J_i \subseteq \{1,\dots,n\}$ records the indices of the **uncertain** entries $a_{ij}$, $j \in J_i$; all other data ($E$, $e$, $b$, $\ell$, $u$, and $a_{ij}$ for $j\notin J_i$) are exact.
--
--   This definition bundles the data $(E, e, A, b, \ell, u, (J_i)_i)$ and defines two derived notions.
--
--   1. For a tolerance $\delta$, the **tolerated right-hand side** of row $i$ is
--   $$
--   b_i^+ = b_i + \delta\max[1, |b_i|].
--   $$
--   2. A vector $x\in\mathbb{R}^n$ is **feasible for the nominal problem** if $Ex = e$, $Ax\le b$ (componentwise) and $\ell_j \le x_j \le u_j$ for every $j$.
--
--   The objective $c$ plays no role in any feasibility or reliability statement and is not part of the data.
--
--   **Formalization Note** Indices are 0-based: rows are `Fin m`, columns `Fin n`. The sets $J_i$ are `Finset (Fin n)` and are arbitrary (the paper's NETLIB rule for choosing them is a case-study device). The bounds are `EReal`-valued, so $\ell_j=-\infty$ and $u_j=+\infty$ are expressible, and $\ell\le x\le u$ is read coordinatewise after coercing $x_j$ to `EReal`. $Ax \le b$ is the pointwise order on `Fin m → ℝ`.
-- source:
--   Ben-Tal and Nemirovski, Robust solutions of Linear Programming problems contaminated with uncertain data, Math. Program. Ser. A 88 (2000) 411–424, p. 413, §2.1, (LP); p. 414, §2.2 (only A uncertain); pp. 417–420, §3.1 (tolerance b_i + δ max[1,|b_i|], named b_i^+ on pp. 419–420; condition (i))

import Mathlib

namespace RobustLP.Counterpart

/-- An LP with uncertain inequality coefficients (Ben-Tal–Nemirovski 2000, §2.1, p. 413, (LP)):
`minimize cᵀx s.t. E x = e, A x ≤ b, ℓ ≤ x ≤ u`, with `n` variables, `p` equality rows and
`m` inequality rows. The objective `c` plays no role in the feasibility statements and is omitted.
The box bounds are extended reals, so `ℓ j = ⊥` (no lower bound) and `u j = ⊤` (no upper bound)
are allowed. `J i` is the set of indices of the uncertain entries of the `i`-th inequality row;
only the entries of `A` are uncertain (§2.2, p. 414). -/
structure UncertainLP (n p m : ℕ) where
  /-- equality constraint matrix `E` -/
  E : Matrix (Fin p) (Fin n) ℝ
  /-- equality right-hand side `e` -/
  e : Fin p → ℝ
  /-- nominal inequality constraint matrix `A = (a_{ij})` -/
  A : Matrix (Fin m) (Fin n) ℝ
  /-- inequality right-hand side `b` -/
  b : Fin m → ℝ
  /-- lower bounds `ℓ` (possibly `-∞`) -/
  ℓ : Fin n → EReal
  /-- upper bounds `u` (possibly `+∞`) -/
  u : Fin n → EReal
  /-- `J i` : indices of the uncertain entries of row `i` of `A` -/
  J : Fin m → Finset (Fin n)

namespace UncertainLP

variable {n p m : ℕ}

/-- The tolerated right-hand side `b_i^+ = b_i + δ · max[1, |b_i|]` (§3.1, pp. 417–420). -/
def bPlus (L : UncertainLP n p m) (δ : ℝ) (i : Fin m) : ℝ :=
  L.b i + δ * max 1 |L.b i|

/-- The box constraint `ℓ ≤ x ≤ u`, read coordinatewise in `EReal`. -/
def InBox (L : UncertainLP n p m) (x : Fin n → ℝ) : Prop :=
  ∀ j, L.ℓ j ≤ (x j : EReal) ∧ (x j : EReal) ≤ L.u j

/-- `x` is feasible for the nominal problem (LP): `E x = e`, `A x ≤ b`, `ℓ ≤ x ≤ u`
(condition (i), §3.1, p. 417). -/
def NominalFeasible (L : UncertainLP n p m) (x : Fin n → ℝ) : Prop :=
  L.E.mulVec x = L.e ∧ L.A.mulVec x ≤ L.b ∧ L.InBox x

end UncertainLP

end RobustLP.Counterpart


