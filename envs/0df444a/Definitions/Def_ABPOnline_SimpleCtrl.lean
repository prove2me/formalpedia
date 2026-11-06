-- Prove2me | Definitions.Def_ABPOnline_SimpleCtrl
-- name    : ABPOnline_SimpleCtrl
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:53:42.511204+00:00
-- url     : https://prove2.me/theorems/d1bebe70-a9b3-4a00-a50e-8372628dc6e7
-- title:
--   Bounded simple predictable controls of the form in Definition 4.2
-- statement:
--   Let $0=s_0<\dots<s_L=T$. A **bounded simple predictable control** on $[0,T]$ is a process
--   $$
--   \beta_t=\xi_j,\qquad t\in(s_j,s_{j+1}],
--   $$
--   where $\xi_j$ is bounded and $\mathcal F^B_{s_j}$-measurable. The controls used by the paper have
--   $$
--   \xi_j=F_j(B_{r_{j,1}},\dots,B_{r_{j,m_j}}),\qquad r_{j,\ell}\le s_j,
--   $$
--   with rational times $r_{j,\ell}$, $s_j$, and bounded, nonnegative, globally Lipschitz, rational piecewise-polynomial functions $F_j$. Here $F:\mathbb R^m\to\mathbb R$ is **rational piecewise-polynomial** if finitely many closed polyhedra $\{x:\langle a_\ell,x\rangle\le c_\ell\}$ with rational data cover $\mathbb R^m$ and $F$ agrees on each with a polynomial with rational coefficients.
--
--   These controls can be evaluated from finitely many past Brownian values, which is what Algorithm 1 needs.
--
--   **Formalization Note** A control is stored as its data $(L,s,m,r,F)$ with a validity predicate; the process is $0$ outside $(0,s_L]$. Observation times are nonnegative (Brownian time). "Rational piecewise-polynomial" is not spelled out in the paper; the reading above covers the piecewise-affine approximants of the proof of Proposition 4.3.
-- source:
--   Jo, Lee, The Exact Online Threshold for the Asymmetric Binary Perceptron, arXiv:2609.02124 (artifact sha256 bd5e2bdb18a47b7e806191ae9b888a6e4e7e150a9bd50e541b7587007d07a7a2), Definition 4.2, p.12 (PDF p.13)

import Mathlib

set_option autoImplicit false

open MeasureTheory
open scoped NNReal

namespace ABPOnline

/-- One piece of a rational piecewise-polynomial function on `ℝ^m`: a closed polyhedron
`{x : ⟨aₗ, x⟩ ≤ cₗ for all listed (aₗ, cₗ)}` with rational data, and a polynomial with rational
coefficients. -/
structure RatPiece (m : ℕ) where
  ineqs : List ((Fin m → ℚ) × ℚ)
  poly : MvPolynomial (Fin m) ℚ

/-- The polyhedron of a `RatPiece`. -/
def RatPiece.carrier {m : ℕ} (p : RatPiece m) : Set (Fin m → ℝ) :=
  {x | ∀ c ∈ p.ineqs, ∑ i, (c.1 i : ℝ) * x i ≤ (c.2 : ℝ)}

/-- `F : ℝ^m → ℝ` is **rational piecewise-polynomial** (arXiv:2609.02124, Definition 4.2, printed
p.12, PDF p.13): finitely many closed polyhedra with rational data cover `ℝ^m`, and on each of
them `F` agrees with a polynomial with rational coefficients.

**Formalization Note** The paper does not spell the notion out; this is its standard reading
(the approximants built in the proof of Proposition 4.3 are piecewise affine on a triangulated
rational grid, tapered outside a rational box). -/
def IsRatPiecewisePoly {m : ℕ} (F : (Fin m → ℝ) → ℝ) : Prop :=
  ∃ pieces : List (RatPiece m), (∀ x, ∃ p ∈ pieces, x ∈ p.carrier) ∧
    ∀ p ∈ pieces, ∀ x ∈ p.carrier,
      F x = MvPolynomial.eval x (MvPolynomial.map (algebraMap ℚ ℝ) p.poly)

/-- The data of a simple predictable control of the form in Definition 4.2 (arXiv:2609.02124,
p.12): block times `s_0, …, s_L`, and for each block `j < L` the observation times
`r_{j,1}, …, r_{j,m_j}` and the coefficient function `F_j`. The control is
`β_t = F_j(B_{r_{j,1}}, …, B_{r_{j,m_j}})` for `t ∈ (s_j, s_{j+1}]`. -/
structure SimpleCtrl where
  L : ℕ
  s : ℕ → ℚ
  m : ℕ → ℕ
  r : (j : ℕ) → Fin (m j) → ℚ
  F : (j : ℕ) → (Fin (m j) → ℝ) → ℝ

/-- `β` is a **bounded simple predictable control on `[0,T]` of the form in Definition 4.2**
(arXiv:2609.02124, Definition 4.2, p.12): `0 = s_0 < ⋯ < s_L = T` with rational `s_j`, rational
observation times `0 ≤ r_{j,ℓ} ≤ s_j`, and each `F_j` bounded, nonnegative, globally Lipschitz and
rational piecewise-polynomial.

**Formalization Note** Brownian time is `[0, ∞)`, so the observation times are taken
nonnegative. The coefficients `ξ_j = F_j(B_{r_{j,·}})` are then bounded and `F^B_{s_j}`-measurable,
as Definition 4.2 requires. -/
def SimpleCtrl.IsValidOn (β : SimpleCtrl) (T : ℚ) : Prop :=
  β.s 0 = 0 ∧ (∀ j < β.L, β.s j < β.s (j + 1)) ∧ β.s β.L = T ∧
    ∀ j < β.L, (∀ ℓ : Fin (β.m j), 0 ≤ β.r j ℓ ∧ β.r j ℓ ≤ β.s j) ∧
      (∃ K : ℝ, ∀ x, |β.F j x| ≤ K) ∧ (∀ x, 0 ≤ β.F j x) ∧
      (∃ K : ℝ≥0, LipschitzWith K (β.F j)) ∧ IsRatPiecewisePoly (β.F j)

/-- The process `β_t = ξ_j = F_j(B_{r_{j,1}}, …, B_{r_{j,m_j}})` for `t ∈ (s_j, s_{j+1}]`, driven by
a real process `B` (arXiv:2609.02124, (16), p.12). It is `0` outside `(0, s_L]`. -/
noncomputable def SimpleCtrl.proc {Ω : Type*} (β : SimpleCtrl) (B : ℝ≥0 → Ω → ℝ) :
    ℝ≥0 → Ω → ℝ :=
  fun t ω => ∑ j ∈ Finset.range β.L,
    if (β.s j : ℝ) < t ∧ (t : ℝ) ≤ β.s (j + 1) then
      β.F j (fun ℓ => B (Real.toNNReal (β.r j ℓ)) ω) else 0

end ABPOnline


