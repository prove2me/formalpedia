-- Prove2me | Definitions.Def_IteratedLP_Gaussian_RegularKKT
-- name    : IteratedLP_Gaussian_RegularKKT
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:21:30.121507+00:00
-- url     : https://prove2.me/theorems/adf29e2b-a730-4234-a73f-9e1b96edc95f
-- title:
--   KKT pairs and regular KKT pairs of a round LP (Definition 4.1)
-- statement:
--   Consider the round-$t$ LP of ITERATED-LP with matrix $A$, objective $v$, margin $\kappa$ and entering iterate $x^{(t-1)}$; the coordinates entering free are $F_{t-1}=\{j:|x^{(t-1)}_j|\ne1\}$. For a primal point $x$ and row multipliers $\lambda\in\mathbb R^M$ write $u=Ax$, $r=A^\top\lambda$.
--
--   $(x,\lambda)$ is a **KKT pair** if $x$ is feasible, $\lambda\ge0$, $\lambda_i(u_i-\kappa)=0$ for all $i$, and there are box multipliers $\lambda^\pm_{\mathrm{box}}\ge0$ on $F_{t-1}$ with
--   $$v_j+r_j-\lambda^+_{\mathrm{box},j}+\lambda^-_{\mathrm{box},j}=0,\qquad \lambda^+_{\mathrm{box},j}(1-x_j)=\lambda^-_{\mathrm{box},j}(1+x_j)=0\qquad(j\in F_{t-1}).$$
--
--   With $I_t=\{i:\lambda_i>0\}$, $F_t=\{j\in F_{t-1}:|x_j|<1\}$ and $C_t=F_{t-1}\setminus F_t$, the pair is **regular** (Definition 4.1) if
--   1. the row constraints are strictly complementary: $u_i=\kappa,\ \lambda_i>0$ for $i\in I_t$ and $u_i>\kappa,\ \lambda_i=0$ for $i\notin I_t$;
--   2. $|x_j|<1$ and $(v+r)_j=0$ for $j\in F_t$, and $x_j(v+r)_j>0$ for $j\in C_t$;
--   3. $|I_t|=|F_t|$ and $A_{I_t,F_t}$ is invertible (the determinant of the empty block is $1$).
--
--   Regular pairs are the nondegenerate vertices with which Lemma 4.2 works.
--
--   **Formalization Note.** Invertibility of $A_{I_t,F_t}$ is written as bijectivity of $y\mapsto(\sum_{j\in F_t}A_{ij}y_j)_{i\in I_t}$ from $\mathbb R^{F_t}$ to $\mathbb R^{I_t}$, which does not depend on an ordering of the two index sets and holds for empty blocks. Cardinalities are `Nat.card` of subtypes.
-- source:
--   Zhang, Li, State Evolution and Universality of Iterated Linear Programs for the Binary Perceptron, arXiv:2611.04294v1, pp. 16–17, §4.3 and Definition 4.1

import Mathlib
import Definitions.Def_IteratedLP_Gaussian_Model

open MeasureTheory

namespace IteratedLP.Gaussian

/-- A primal–dual KKT pair `(x, λ)` of the round LP with matrix `A`, objective `v`, margin `κ` and
entering iterate `xprev` (§4.3, p. 16). The coordinates entering free are
`F_{t-1} = {j : |xprev_j| ≠ 1}`; `u = A x`, `r = A⊤ λ`. Conditions: `x` is feasible;
`λ ≥ 0` and `λ_i (u_i - κ) = 0`; and on `F_{t-1}` there are box multipliers
`λ⁺_box, λ⁻_box ≥ 0` with `v_j + r_j - λ⁺_j + λ⁻_j = 0`,
`λ⁺_j (1 - x_j) = λ⁻_j (1 + x_j) = 0`. -/
def IsKKTPair {M N : ℕ} (A : Fin M → Fin N → ℝ) (v : Fin N → ℝ) (κ : ℝ) (xprev : Fin N → ℝ)
    (x : Fin N → ℝ) (lam : Fin M → ℝ) : Prop :=
  x ∈ feasibleSet A κ xprev ∧ (∀ i, 0 ≤ lam i) ∧
  (∀ i, lam i * (∑ j, A i j * x j - κ) = 0) ∧
  ∃ lp lm : Fin N → ℝ, ∀ j, |xprev j| ≠ 1 →
    0 ≤ lp j ∧ 0 ≤ lm j ∧ v j + (∑ i, A i j * lam i) - lp j + lm j = 0 ∧
    lp j * (1 - x j) = 0 ∧ lm j * (1 + x j) = 0

open scoped Classical in
/-- A regular KKT pair (Definition 4.1, pp. 16–17). With `I_t = {i : λ_i > 0}`,
`F_t = {j ∈ F_{t-1} : |x_j| < 1}` and `C_t = F_{t-1} \ F_t`:
(i) strict complementarity: `u_i = κ, λ_i > 0` for `i ∈ I_t` and `u_i > κ, λ_i = 0` otherwise;
(ii) `|x_j| < 1`, `(v + r)_j = 0` on `F_t`, and `x_j (v + r)_j > 0` on `C_t`;
(iii) `|I_t| = |F_t|` and `A_{I_t, F_t}` is invertible (the map `y ↦ (A_{I_t,F_t} y)` from
`ℝ^{F_t}` to `ℝ^{I_t}` is bijective; for empty blocks this holds, matching `det = 1`). -/
def IsRegularKKT {M N : ℕ} (A : Fin M → Fin N → ℝ) (v : Fin N → ℝ) (κ : ℝ)
    (xprev : Fin N → ℝ) (x : Fin N → ℝ) (lam : Fin M → ℝ) : Prop :=
  IsKKTPair A v κ xprev x lam ∧
  (∀ i, (0 < lam i ∧ ∑ j, A i j * x j = κ) ∨ (lam i = 0 ∧ κ < ∑ j, A i j * x j)) ∧
  (∀ j, |xprev j| ≠ 1 →
    (|x j| < 1 → v j + ∑ i, A i j * lam i = 0) ∧
    (|x j| = 1 → 0 < x j * (v j + ∑ i, A i j * lam i))) ∧
  Nat.card {i // 0 < lam i} = Nat.card {j // |xprev j| ≠ 1 ∧ |x j| < 1} ∧
  Function.Bijective (fun (y : {j // |xprev j| ≠ 1 ∧ |x j| < 1} → ℝ) =>
    fun (i : {i // 0 < lam i}) => ∑ j, A i.1 j.1 * y j)

end IteratedLP.Gaussian


