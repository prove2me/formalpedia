-- Prove2me | Definitions.Def_PlotkinShmoysTardos_relaxedOptimality
-- name    : PlotkinShmoysTardos_relaxedOptimality
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:50:49.385238+00:00
-- url     : https://prove2.me/theorems/0bed6f07-3436-4a44-bbc2-d5535bec96a7
-- title:
--   The value $\lambda(x)$, the dual $y$, the potential $\Phi$ and the relaxed optimality conditions G1, G2
-- statement:
--   Fix $A$, $b$ and a positive vector $d$ as in the GENERAL problem, with $m\ge 1$ rows.
--
--   1. The **value** of a point $x$ is
--   $$
--   \lambda(x)=\max_i \frac{a_ix-b_i}{d_i},
--   $$
--   the least $\lambda$ with $Ax\le b+\lambda d$.
--   2. For a parameter $\alpha$, the **dual solution corresponding to $x$** is $y_i=\frac1{d_i}e^{\alpha(a_ix-b_i)/d_i}$, and the **potential** is
--   $$
--   \Phi = y^t d=\sum_i e^{\alpha(a_ix-b_i)/d_i}.
--   $$
--   3. For a point $x$, a number $\lambda$ and a vector $y\ge 0$, the relaxed optimality conditions are
--   $$
--   (\mathcal G1)\quad \lambda\, y^td\le 4\,y^t(Ax-b),\qquad (\mathcal G2)\quad y^t(Ax-b)-C_{\mathcal G}(y)\le \tfrac{\lambda}{5}\,y^td,
--   $$
--   where $C_{\mathcal G}(y)=\min(y^tAx'-y^tb : x'\in P)$.
--
--   Lemma 4.1 shows that G1 and G2 together certify that the GENERAL problem has no exact solution; the procedure IMPROVE-GENERAL drives $\lambda(x)$ down by decreasing $\Phi$.
--
--   **Formalization Note** $\lambda(x)$ is `Finset.sup'` over the rows, which needs `[NeZero m]`. Condition G2 is stated against every competitor $x'\in P$, $y^t(Ax-b)-y^t(Ax'-b)\le\frac{\lambda}{5}y^td$, so no infimum (with Lean's junk value on unbounded sets) is used; this is the paper's G2 whenever the minimum $C_{\mathcal G}(y)$ is attained.
-- source:
--   Plotkin, Shmoys, Tardos, Fast Approximation Algorithms for Fractional Packing and Covering Problems, Cornell ORIE Technical Report No. 999 (Feb. 1992), §4, (11), p. 24 (λ as minimum value; C_G(y); G1, G2), p. 25 (dual solution corresponding to x), p. 26 (potential Φ)

import Mathlib

namespace PlotkinShmoysTardos

/-! # Relaxed optimality for GENERAL (Plotkin–Shmoys–Tardos, TR 999, 1992, §4, pp. 24–26) -/

/-- **The value `λ` of a point.** §4, p. 24: "For each `x ∈ P`, there is a corresponding minimum
value `λ` such that `A x ≤ b + λ d`"; Figure 4 computes it as `maxᵢ (aᵢ x − bᵢ)/dᵢ`.
The maximum is over the `m ≥ 1` rows (`[NeZero m]`). -/
noncomputable def lam {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => (A.mulVec x i - b i) / d i)

/-- **The dual solution corresponding to `x`.** §4, p. 25:
`yᵢ = (1/dᵢ) e^{α (aᵢ x − bᵢ)/dᵢ}`. -/
noncomputable def dual {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ) (α : ℝ)
    (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i => (1 / d i) * Real.exp (α * (A.mulVec x i - b i) / d i)

/-- **The potential function.** §4, p. 26: `Φ = yᵗd = Σᵢ e^{α (aᵢ x − bᵢ)/dᵢ}` for the dual `y`
corresponding to `x`. -/
noncomputable def potential {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ) (α : ℝ)
    (x : Fin n → ℝ) : ℝ :=
  dual A b d α x ⬝ᵥ d

/-- **Condition (G1).** §4, p. 24: `λ yᵗd ≤ 4 yᵗ(A x − b)`. -/
def G1 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ) (x : Fin n → ℝ) (l : ℝ)
    (y : Fin m → ℝ) : Prop :=
  l * (y ⬝ᵥ d) ≤ 4 * (y ⬝ᵥ (A.mulVec x - b))

/-- **Condition (G2).** §4, p. 24: `yᵗ(A x − b) − C_G(y) ≤ (λ/5) yᵗd`, where
`C_G(y) = min(yᵗA x' − yᵗb : x' ∈ P)`. The minimum is not written as an infimum; instead the
inequality is required against every competitor `x' ∈ P`, which is the same condition whenever
the minimum is attained. -/
def G2 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ) (P : Set (Fin n → ℝ))
    (x : Fin n → ℝ) (l : ℝ) (y : Fin m → ℝ) : Prop :=
  ∀ x' ∈ P, y ⬝ᵥ (A.mulVec x - b) - y ⬝ᵥ (A.mulVec x' - b) ≤ l / 5 * (y ⬝ᵥ d)

end PlotkinShmoysTardos


