-- Prove2me | Definitions.Def_StochasticProg_Recourse_Instance
-- name    : StochasticProg_Recourse_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T04:45:24.763692+00:00
-- url     : https://prove2.me/theorems/a982ca27-30d6-4eca-a866-e86e07ded193
-- title:
--   Two-stage recourse instance with a finite scenario set
-- statement:
--   Let $n_1, n_2, m_1, m_2, K$ be natural numbers. A **two-stage recourse instance**
--   consists of first-stage data $A \in \mathbb{R}^{m_1 \times n_1}$, $b \in \mathbb{R}^{m_1}$,
--   $c \in \mathbb{R}^{n_1}$, a fixed recourse matrix $W \in \mathbb{R}^{m_2 \times n_2}$, and $K$
--   scenarios indexed by $k = 1,\dots,K$, each carrying a cost vector $q_k \in \mathbb{R}^{n_2}$, a
--   right-hand side $h_k \in \mathbb{R}^{m_2}$, a technology matrix $T_k \in \mathbb{R}^{m_2 \times
--   n_1}$, and a probability $p_k \ge 0$ with $\sum_k p_k = 1$.
--
--   From this data the definitions build the objects of Birge & Louveaux, Chapter 3, Section 3.1:
--   $K_1 = \{x \mid Ax = b,\ x \ge 0\}$; the second-stage value
--   $$Q(x,\xi_k) = \min_y \{q_k^{\mathsf T} y \mid Wy = h_k - T_k x,\ y \ge 0\}$$
--   as an extended real (`sInf` of the empty feasible set is $+\infty$, and `sInf` of a set unbounded
--   below is $-\infty$); the expected second-stage value $Q(x) = \sum_k p_k\,Q(x,\xi_k)$; the
--   second-stage feasibility set $K_2 = \{x \mid Q(x) < \infty\}$; and the deterministic-equivalent
--   objective $z(x) = c^{\mathsf T}x + Q(x)$.
--
--   **Formalization Note.** The book aggregates $Q(x) = \sum_k p_k Q(x,\xi_k)$ with the explicit
--   convention $+\infty + (-\infty) = +\infty$ (p. 109): infeasibility of one scenario overrides
--   unboundedness of another. Mathlib's `EReal` addition uses the opposite convention
--   ($\bot + \top = \top + \bot = \bot$), so the aggregation here is built from a bespoke `bookAdd`
--   operation matching the book, rather than from `EReal`'s own `+`. The finite scenario set `Fin K`
--   models the book's discrete-random-variable treatment (Section 3.1b); under it, "finite second
--   moments" (the standing hypothesis of Theorems 4-11) is automatic.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, p. 103-109, Chapter 3, Section 3.1a-c, Eq. (1.1)-(1.6)

import Mathlib

namespace StochasticProg.Recourse

/-- A two-stage stochastic linear program with fixed recourse and a finite scenario
set (Birge & Louveaux, Ch. 3, Section 3.1a-b, Eq. (1.1)-(1.4)): first-stage data
`A, b, c` and fixed recourse matrix `W`, together with `K` equally-indexed
realisations of the random data `(q, h, T)` and their probabilities `p`. -/
structure Instance (n1 n2 m1 m2 K : ℕ) where
  A : Matrix (Fin m1) (Fin n1) ℝ
  b : Fin m1 → ℝ
  c : Fin n1 → ℝ
  W : Matrix (Fin m2) (Fin n2) ℝ
  q : Fin K → Fin n2 → ℝ
  h : Fin K → Fin m2 → ℝ
  T : Fin K → Matrix (Fin m2) (Fin n1) ℝ
  p : Fin K → ℝ
  hp_nonneg : ∀ k, 0 ≤ p k
  hp_sum : ∑ k, p k = 1

variable {n1 n2 m1 m2 K : ℕ}

/-- `K1 = {x | Ax = b, x ≥ 0}` (p. 105), the first-stage feasible region. -/
def K1 (inst : Instance n1 n2 m1 m2 K) : Set (Fin n1 → ℝ) :=
  {x | Matrix.mulVec inst.A x = inst.b ∧ ∀ i, 0 ≤ x i}

/-- The second-stage value `Q(x,ξ_k) = min_y {q(ω)ᵀy | Wy = h(ω) - T(ω)x, y ≥ 0}`
(Eq. (1.6), p. 106), as an extended real: `sInf` of the empty set is `⊤` (infeasible)
and `sInf` of a set unbounded below is `⊥` (unbounded), matching the book's stated
conventions for these two failure modes (p. 109). -/
noncomputable def QVal (inst : Instance n1 n2 m1 m2 K) (x : Fin n1 → ℝ) (k : Fin K) : EReal :=
  sInf {z : EReal | ∃ y : Fin n2 → ℝ, (∀ i, 0 ≤ y i) ∧
    Matrix.mulVec inst.W y = inst.h k - Matrix.mulVec (inst.T k) x ∧
    z = ((dotProduct (inst.q k) y : ℝ) : EReal)}

/-- Addition of extended second-stage values under the book's explicit convention
`+∞ + (-∞) = +∞` (p. 109): infeasibility of any scenario dominates unboundedness of
another. This is the opposite convention from Mathlib's `EReal` addition
(`⊥ + ⊤ = ⊤ + ⊥ = ⊥`), so the aggregate recourse value below is built from this
operation rather than from `EReal`'s own `+`. -/
noncomputable def bookAdd (a b : EReal) : EReal := if a = ⊤ ∨ b = ⊤ then ⊤ else a + b

/-- The expected second-stage value `Q(x) = E_ξ Q(x,ξ) = Σ_k p_k Q(x,ξ_k)` for a
finite scenario set (Eq. (1.3) together with p. 106), combined via `bookAdd`. -/
noncomputable def Q (inst : Instance n1 n2 m1 m2 K) (x : Fin n1 → ℝ) : EReal :=
  (List.ofFn (fun k : Fin K => (inst.p k : EReal) * QVal inst x k)).foldr bookAdd 0

/-- `K2 = {x | Q(x) < ∞}` (p. 109), the second-stage feasibility set. -/
def K2 (inst : Instance n1 n2 m1 m2 K) : Set (Fin n1 → ℝ) :=
  {x | Q inst x ≠ ⊤}

/-- The deterministic-equivalent objective `z(x) = cᵀx + Q(x)` (Eq. (1.2), p. 104). -/
noncomputable def obj (inst : Instance n1 n2 m1 m2 K) (x : Fin n1 → ℝ) : EReal :=
  ((dotProduct inst.c x : ℝ) : EReal) + Q inst x

end StochasticProg.Recourse


