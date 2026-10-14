-- Prove2me | Definitions.Def_BudgetedAffine_Budget_Construction
-- name    : BudgetedAffine_Budget_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T20:25:54.605593+00:00
-- url     : https://prove2.me/theorems/eedcddff-ea45-412c-8c40-aab30cd9bf92
-- title:
--   Sec. 3.1, (3.3)–(3.5); (4.5)–(4.6) — α, β, the threshold set I, the linear part y_Lin and the static problem
-- statement:
--   The ingredients of the affine solution of Section 3.1, built from a first-stage decision $x^*$, a number $\mathrm{OPT}$ and the weights $w$ of the budget set.
--
--   1. $\alpha_i=1-(Ax^*)_i$ for $i\in[m]$; when $\alpha_i\le0$ the first stage already covers row $i$.
--   2. $\beta=\dfrac{4\log n}{\log\log n}$, with the natural logarithm, where $n$ is the number of decision variables.
--   3. The threshold set
--   $$\mathcal I=\Big\{i\in[m]\ :\ \alpha_i>0\ \text{ and }\ \alpha_i\,z(e_i)\le w_i\,\beta\,\mathrm{OPT}\Big\},$$
--   the paper's condition $\alpha_iz(e_i)/w_i\le\beta\cdot\mathrm{OPT}$ multiplied through by $w_i$.
--   4. The linear part (3.3): given vectors $v_i\in\mathbb R^n$,
--   $$y_{Lin}(h)=\sum_{i\in\mathcal I}\alpha_ih_iv_i,$$
--   and the matrix $P\in\mathbb R^{n\times m}$ whose $i$-th column is $\alpha_iv_i$ for $i\in\mathcal I$ and $0$ otherwise, so that $Ph=y_{Lin}(h)$.
--   5. The static problem (3.4) with right-hand side $r=\sum_{i\in\mathcal I^c}e_i+\sum_{i\in\mathcal I}(1-\alpha_i)^+e_i$:
--   $$z_{Sta}=\min_{x\in\mathcal X,\ y\ge0}\big\{c^Tx+d^Ty\ :\ Ax+By\ge r\big\},$$
--   and an optimal solution $(x_{Sta},y_{Sta})$ of it (a feasible point attaining $z_{Sta}$).
--
--   The candidate affine solution (3.5) of the paper is $x=x_{Sta}$, $y(h)=Ph+y_{Sta}$.
--
--   Items 1, 4 and 5 are reused verbatim in Section 4.2 for disjoint constrained budgeted sets ((4.5)–(4.7), p. 18), where the threshold set is built differently; items 2 and 3 ($\beta=4\log n/\log\log n$ and $\mathcal I$) belong to Section 3 only.
--
--   **Formalization Note** The threshold is in multiplied form because Lean's division by $w_i=0$ returns $0$, which would put every such component into $\mathcal I$; with $w_i>0$ the two forms agree. $z(e_i)$ is the extended-real covering value, so a row that cannot be covered ($z(e_i)=+\infty$) with $\alpha_i>0$ falls in $\mathcal I^c$. $z_{Sta}$ is $+\infty$ when (3.4) is infeasible.
-- source:
--   El Housni, Goyal, On the Optimality of Affine Policies for Budgeted Uncertainty Sets, arXiv:1807.00163v2, Sec. 3.1, (3.3), (3.4), (3.5), pp. 7–8; Sec. 4.2, (4.5), (4.6), (4.7), p. 18

import Mathlib
import Definitions.Def_BudgetedAffine_Budget_Model

namespace BudgetedAffine.Budget

open Matrix

/-- `αᵢ = 1 − (A x)ᵢ`, the part of the unit requirement in row `i` left uncovered by `x`. -/
def alpha {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) (i : Fin m) : ℝ :=
  1 - (A *ᵥ x) i

/-- `β = 4 log n / log log n` (natural logarithm). -/
noncomputable def beta (n : ℕ) : ℝ :=
  4 * Real.log n / Real.log (Real.log n)

open Classical in
/-- The set `I = {i | αᵢ > 0 and αᵢ z(eᵢ) / wᵢ ≤ β · OPT}` of Sec. 3.1, in the multiplied form
`αᵢ z(eᵢ) ≤ wᵢ β OPT` (with `z(eᵢ)` the `EReal` covering value), where `α` is computed from the
first-stage decision `x` and `β = beta n`. -/
noncomputable def Iset {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (d : Fin n → ℝ)
    (w : Fin m → ℝ) (x : Fin n → ℝ) (OPT : ℝ) : Finset (Fin m) :=
  Finset.univ.filter fun i =>
    0 < alpha A x i ∧
      ((alpha A x i : ℝ) : EReal) * coverCost B d (Pi.single i 1) ≤
        ((w i * beta n * OPT : ℝ) : EReal)

/-- The linear part (3.3): `y_Lin(h) = ∑_{i ∈ I} αᵢ hᵢ vᵢ`. -/
def yLin {m n : ℕ} (I : Finset (Fin m)) (α : Fin m → ℝ) (v : Fin m → Fin n → ℝ)
    (h : Fin m → ℝ) : Fin n → ℝ :=
  ∑ i ∈ I, (α i * h i) • v i

/-- The matrix `P` of the linear part: column `i` is `αᵢ vᵢ` for `i ∈ I` and `0` otherwise, so
`P h = y_Lin(h)`. -/
def linMatrix {m n : ℕ} (I : Finset (Fin m)) (α : Fin m → ℝ) (v : Fin m → Fin n → ℝ) :
    Matrix (Fin n) (Fin m) ℝ :=
  Matrix.of fun j i => if i ∈ I then α i * v i j else 0

/-- The right-hand side of the static problem (3.4):
`∑_{i ∈ Iᶜ} eᵢ + ∑_{i ∈ I} (1 − αᵢ)⁺ eᵢ`. -/
noncomputable def staRhs {m : ℕ} (I : Finset (Fin m)) (α : Fin m → ℝ) : Fin m → ℝ :=
  fun i => if i ∈ I then max (1 - α i) 0 else 1

/-- The value of the static problem (3.4) with right-hand side `r`:
`min_{x ∈ X, y ≥ 0} {cᵀx + dᵀy | A x + B y ≥ r}`, in `EReal` (`+∞` when infeasible). -/
noncomputable def staticValue {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (c d : Fin n → ℝ)
    (X : Set (Fin n → ℝ)) (r : Fin m → ℝ) : EReal :=
  ⨅ (x : Fin n → ℝ) (_ : x ∈ X) (y : Fin n → ℝ) (_ : 0 ≤ y ∧ r ≤ A *ᵥ x + B *ᵥ y),
    ((c ⬝ᵥ x + d ⬝ᵥ y : ℝ) : EReal)

/-- `(x, y)` is an optimal solution (an argmin) of the static problem (3.4) with right-hand
side `r`. -/
def IsStaticOpt {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (c d : Fin n → ℝ)
    (X : Set (Fin n → ℝ)) (r : Fin m → ℝ) (x y : Fin n → ℝ) : Prop :=
  x ∈ X ∧ 0 ≤ y ∧ r ≤ A *ᵥ x + B *ᵥ y ∧
    ((c ⬝ᵥ x + d ⬝ᵥ y : ℝ) : EReal) = staticValue A B c d X r

end BudgetedAffine.Budget


