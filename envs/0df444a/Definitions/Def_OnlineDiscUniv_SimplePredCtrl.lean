-- Prove2me | Definitions.Def_OnlineDiscUniv_SimplePredCtrl
-- name    : OnlineDiscUniv_SimplePredCtrl
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:12:07.132059+00:00
-- url     : https://prove2.me/theorems/8b414c14-d61d-4180-b974-250dd3eebf4c
-- title:
--   Bounded simple predictable controls with a finite rational description (Definition 4.3)
-- statement:
--   For a partition $0=t_0<t_1<\dots<t_J=T$, a **bounded simple predictable control** has the form
--   $$
--   \beta_t=F_j\big(B_{r_{j,1}},\dots,B_{r_{j,m_j}}\big),\qquad t\in(t_j,t_{j+1}],\quad 0\le j<J,
--   $$
--   with observation times $0\le r_{j,\ell}\le t_j$ and functions $F_j:\mathbb R^{m_j}\to\mathbb R$ that are bounded and globally Lipschitz. The drift on each block is determined by observations available at its left endpoint. The control has a **finite rational description** if all times are rational and each $F_j$ is affine on the cells of a finite rational polyhedral partition of $\mathbb R^{m_j}$, with rational affine coefficients.
--
--   These are the controls the online algorithm can evaluate coordinate by coordinate; Propositions 4.4 and 4.5 approximate optimal Brownian controls by them.
--
--   **Formalization Note** The times are rational from the start (every use in the paper asks for a finite rational description). The cells are closed polyhedra $\{x:\langle a_\ell,x\rangle\le c_\ell\}$ with rational data covering $\mathbb R^{m}$. The process is $0$ outside $(0,t_J]$, in particular at $t=0$, a Lebesgue-null time the paper leaves unspecified.
-- source:
--   Jo, Lee, Exact Universality of Online Discrepancy, arXiv:2610.00103 (artifact sha256 cb190f127dea2c038b4a22a4787862f82356a983593dfdc3dc3fe3c7c8264ad5), Definition 4.3, (4.5), pp.13–14 (PDF pp.14–15)

import Mathlib

set_option autoImplicit false

open MeasureTheory
open scoped NNReal

namespace OnlineDiscUniv

/-- One cell of a finite rational polyhedral partition of `ℝ^m`, with an affine function on it:
the closed polyhedron `{x : ⟨a_ℓ, x⟩ ≤ c_ℓ for every listed (a_ℓ, c_ℓ)}` with rational data, and
the affine map `x ↦ ⟨w, x⟩ + b` with rational coefficients. -/
structure RatAffPiece (m : ℕ) where
  ineqs : List ((Fin m → ℚ) × ℚ)
  w : Fin m → ℚ
  b : ℚ

/-- The polyhedron of a `RatAffPiece`. -/
def RatAffPiece.carrier {m : ℕ} (p : RatAffPiece m) : Set (Fin m → ℝ) :=
  {x | ∀ c ∈ p.ineqs, ∑ i, (c.1 i : ℝ) * x i ≤ (c.2 : ℝ)}

/-- The affine function of a `RatAffPiece`. -/
def RatAffPiece.eval {m : ℕ} (p : RatAffPiece m) (x : Fin m → ℝ) : ℝ :=
  ∑ i, (p.w i : ℝ) * x i + (p.b : ℝ)

/-- `F : ℝ^m → ℝ` is **affine on the cells of a finite rational polyhedral partition, with
rational affine coefficients** (Jo–Lee, arXiv:2610.00103, artifact sha256 cb190f12…,
Definition 4.3, printed p.14, PDF p.15): finitely many closed polyhedra with rational data cover
`ℝ^m`, and on each of them `F` agrees with an affine function with rational coefficients. -/
def IsRatPiecewiseAffine {m : ℕ} (F : (Fin m → ℝ) → ℝ) : Prop :=
  ∃ pieces : List (RatAffPiece m), (∀ x, ∃ p ∈ pieces, x ∈ p.carrier) ∧
    ∀ p ∈ pieces, ∀ x ∈ p.carrier, F x = p.eval x

/-- The data of a simple predictable control of the form (4.5) (Jo–Lee, arXiv:2610.00103,
Definition 4.3, printed pp.13–14, PDF pp.14–15): partition times `t_0, …, t_J`, and for each block
`j < J` the observation times `r_{j,1}, …, r_{j,m_j}` and the function `F_j`. The control is
`β_t = F_j(B_{r_{j,1}}, …, B_{r_{j,m_j}})` for `t ∈ (t_j, t_{j+1}]`.

**Formalization Note** The times are rational from the start: every use of Definition 4.3 in the
paper (Propositions 4.4 and 4.5) asks for a finite rational description. Observation `ℓ` of
block `j` is indexed `0, …, m_j − 1`. -/
structure SimplePredCtrl where
  J : ℕ
  t : ℕ → ℚ
  m : ℕ → ℕ
  r : (j : ℕ) → Fin (m j) → ℚ
  F : (j : ℕ) → (Fin (m j) → ℝ) → ℝ

/-- `β` is a **bounded simple predictable control on `[0,T]` of the form (4.5), with a finite
rational description** (Jo–Lee, arXiv:2610.00103, Definition 4.3, pp.13–14, PDF pp.14–15):
`0 = t_0 < t_1 < ⋯ < t_J = T`, observation times `0 ≤ r_{j,ℓ} ≤ t_j`, and each `F_j` bounded,
globally Lipschitz and affine on the cells of a finite rational polyhedral partition with
rational affine coefficients (all times are rational by construction). -/
def SimplePredCtrl.IsValidOn (β : SimplePredCtrl) (T : ℚ) : Prop :=
  β.t 0 = 0 ∧ (∀ j < β.J, β.t j < β.t (j + 1)) ∧ β.t β.J = T ∧
    ∀ j < β.J, (∀ ℓ : Fin (β.m j), 0 ≤ β.r j ℓ ∧ β.r j ℓ ≤ β.t j) ∧
      (∃ K : ℝ, ∀ x, |β.F j x| ≤ K) ∧ (∃ K : ℝ≥0, LipschitzWith K (β.F j)) ∧
      IsRatPiecewiseAffine (β.F j)

/-- The process `β_t = F_j(B_{r_{j,1}}, …, B_{r_{j,m_j}})` for `t ∈ (t_j, t_{j+1}]` driven by a real
process `B` (Jo–Lee, arXiv:2610.00103, (4.5), p.13, PDF p.14).

**Formalization Note** The process is `0` outside `(0, t_J]`; in particular `β_0 = 0`, a single
time of Lebesgue measure zero that the paper leaves unspecified. -/
noncomputable def SimplePredCtrl.proc {Ω : Type*} (β : SimplePredCtrl) (B : ℝ≥0 → Ω → ℝ) :
    ℝ≥0 → Ω → ℝ :=
  fun s ω => ∑ j ∈ Finset.range β.J,
    if (β.t j : ℝ) < s ∧ (s : ℝ) ≤ β.t (j + 1) then
      β.F j (fun ℓ => B (Real.toNNReal (β.r j ℓ)) ω) else 0

end OnlineDiscUniv


