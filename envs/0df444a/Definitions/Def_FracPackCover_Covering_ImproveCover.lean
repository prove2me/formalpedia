-- Prove2me | Definitions.Def_FracPackCover_Covering_ImproveCover
-- name    : FracPackCover_Covering_ImproveCover
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:47:25.488401+00:00
-- url     : https://prove2.me/theorems/e5dc4153-a3aa-4748-9f90-570c230fd3cf
-- title:
--   Procedure IMPROVE-COVER (Figure 3), run with its oracle-call count
-- statement:
--   Procedure IMPROVE-COVER$(x,\varepsilon)$ of Figure 3 takes a point $x\in P$ with $\lambda_0=\lambda(x)>0$ and an error parameter $\varepsilon$, and sets
--   $$\alpha=\frac{4}{\lambda_0\,\varepsilon}\ln\frac{4m}{\varepsilon},\qquad \sigma=\frac{\varepsilon}{4\alpha\rho}.$$
--   While $\lambda(x)\le 2\lambda_0$ and $x$ with its dual solution $y$ (parameter $\alpha$) does not satisfy $\mathcal C2$, it sets $y_i=\frac1{b_i}e^{-\alpha a_ix/b_i}$, takes the maximizer $\tilde x\in P$ of $y^tAx$ returned by subroutine (7), and updates
--   $$x\leftarrow(1-\sigma)x+\sigma\tilde x .$$
--   It returns the current $x$ when the while-test fails.
--
--   The module defines one loop body (the update above), the while-test, the run of the loop with a bound on the number of evaluations of the while-test, and the point reached after $t$ updates. The run returns the final point together with the number of calls to subroutine (7) it made, or reports that it did not stop within the given number of tests. A point after $t$ updates is **reached by the execution** when the while-test held at each of the $t$ earlier points.
--
--   **Formalization Note** Each evaluation of the while-test that gets past $\lambda(x)\le2\lambda_0$ needs $C_{\mathcal C}(y)=y^tA\tilde x$, so it costs one oracle call, and the loop body reuses that $\tilde x$; a test failing on its first clause costs none. Lean functions must terminate, so the loop is run with fuel (a bound on the number of tests); the result is `some (x, k)` exactly when the procedure stops within the fuel, with `k` oracle calls. Theorems about the procedure assert that it stops; they do not assume it. The width bound $\rho$ enters only through $\sigma$.
-- source:
--   Plotkin, Shmoys, Tardos, Fast Approximation Algorithms for Fractional Packing and Covering Problems, Cornell ORIE Tech. Rep. 999 (1992), p. 18, Figure 3 (Procedure IMPROVE-COVER)

import Mathlib
import Definitions.Def_FracPackCover_Covering_Basic

namespace FracPackCover.Covering

/-! # Procedure IMPROVE-COVER (Figure 3, p. 18)

```
IMPROVE-COVER(x, ε)
λ0 ← min_i a_i x/b_i;  α ← 4 λ0⁻¹ ε⁻¹ ln(4 m ε⁻¹);  σ ← ε/(4αρ).
While min_i a_i x/b_i ≤ 2λ0 and x and y do not satisfy 𝒞2
    For each i = 1, …, m: set y_i ← (1/b_i) e^{−α a_i x/b_i}.
    Find a maximum-cost point x̃ ∈ P for costs c = yᵗA.
    Update x ← (1 − σ)x + σx̃.
Return x.
```

Oracle-call accounting: an evaluation of the while-test that reaches the 𝒞2 test needs
`C_𝒞(y) = yᵗ A x̃` with `x̃ = orc y`, which is one oracle call; the loop body reuses that `x̃`. A test
that fails on `min_i a_i x / b_i > 2λ0` makes no call. -/

/-- `α = 4 λ0⁻¹ ε⁻¹ ln(4 m ε⁻¹)` (Figure 3). -/
noncomputable def coverAlpha (m : ℕ) (ε l0 : ℝ) : ℝ :=
  4 * l0⁻¹ * ε⁻¹ * Real.log (4 * m * ε⁻¹)

/-- `σ = ε / (4 α ρ)` (Figure 3). -/
noncomputable def coverSigma (m : ℕ) (ρ ε l0 : ℝ) : ℝ :=
  ε / (4 * coverAlpha m ε l0 * ρ)

/-- One loop body of Figure 3 with fixed `α, σ`: `y` is the dual solution of `x`, `x̃ = orc y`, and the
new point is `(1 − σ) x + σ x̃`. -/
noncomputable def coverStep {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (orc : (Fin m → ℝ) → (Fin n → ℝ)) (α σ : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  (1 - σ) • x + σ • orc (dualY A b α x)

/-- The while-test of Figure 3 at the current point `x`: `min_i a_i x/b_i ≤ 2λ0` and `x` with its
dual solution `y` does not satisfy 𝒞2, where `C_𝒞(y) = yᵗ A (orc y)`. -/
def coverTest {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (orc : (Fin m → ℝ) → (Fin n → ℝ)) (ε l0 α : ℝ) (x : Fin n → ℝ) : Prop :=
  lam A b x ≤ 2 * l0 ∧
    ¬ C2 A b ε (dualY A b α x) x (yAx A (dualY A b α x) (orc (dualY A b α x)))

open Classical in
/-- The while loop of Figure 3 run with `fuel` evaluations of the while-test. It returns
`some (x, k)` when the loop test fails within `fuel` evaluations, `x` being the returned point and `k`
the number of oracle calls made, and `none` when the fuel runs out first. -/
noncomputable def coverLoop {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (orc : (Fin m → ℝ) → (Fin n → ℝ)) (ε l0 α σ : ℝ) :
    ℕ → (Fin n → ℝ) → Option ((Fin n → ℝ) × ℕ)
  | 0, _ => none
  | fuel + 1, x =>
    if lam A b x ≤ 2 * l0 then
      if C2 A b ε (dualY A b α x) x (yAx A (dualY A b α x) (orc (dualY A b α x))) then
        some (x, 1)
      else
        (coverLoop A b orc ε l0 α σ fuel (coverStep A b orc α σ x)).map
          (fun p => (p.1, p.2 + 1))
    else
      some (x, 0)

/-- IMPROVE-COVER(x, ε) of Figure 3 with width bound `ρ`, run with `fuel` evaluations of the
while-test: `λ0 = λ(x)`, `α = coverAlpha m ε λ0`, `σ = coverSigma m ρ ε λ0`. The result is
`some (x', k)` (returned point, oracle calls) if the procedure stops within `fuel` tests. -/
noncomputable def improveCover {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (orc : (Fin m → ℝ) → (Fin n → ℝ)) (ρ ε : ℝ) (x : Fin n → ℝ) (fuel : ℕ) :
    Option ((Fin n → ℝ) × ℕ) :=
  coverLoop A b orc ε (lam A b x) (coverAlpha m ε (lam A b x)) (coverSigma m ρ ε (lam A b x))
    fuel x

/-- The current point of IMPROVE-COVER(x, ε) after `t` updates (Figure 3), ignoring the stopping
rule: `(coverStep …)^[t] x`. It is a state of the run exactly when the while-test held at the
`t` earlier states, see `IsReachedCover`. -/
noncomputable def coverIterate {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (orc : (Fin m → ℝ) → (Fin n → ℝ)) (ρ ε : ℝ) (x : Fin n → ℝ) (t : ℕ) :
    Fin n → ℝ :=
  (coverStep A b orc (coverAlpha m ε (lam A b x)) (coverSigma m ρ ε (lam A b x)))^[t] x

/-- The point after `t` updates is reached by the execution of IMPROVE-COVER(x, ε): the while-test
held at each of the `t` earlier points. -/
def IsReachedCover {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (orc : (Fin m → ℝ) → (Fin n → ℝ)) (ρ ε : ℝ) (x : Fin n → ℝ) (t : ℕ) : Prop :=
  ∀ s < t, coverTest A b orc ε (lam A b x) (coverAlpha m ε (lam A b x))
    (coverIterate A b orc ρ ε x s)

end FracPackCover.Covering


