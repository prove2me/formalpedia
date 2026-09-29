-- Prove2me | Definitions.Def_Roberts1997_RWM_ProofObjects
-- name    : Roberts1997_RWM_ProofObjects
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:45:42.014921+00:00
-- url     : https://prove2.me/theorems/0d8f2bdd-606c-4f17-904b-f57901bea5d6
-- title:
--   Proof objects of §2: discrete generator G_nV, R_n, S_n, the sets F_n, and W_n
-- statement:
--   The proof of Theorem 1.1 (§2, pp. 113–115) uses the following objects on $\mathbb R^n$, with $Y\sim N(x,\sigma_n^2I_n)$ the proposal from $x$.
--
--   1. The **discrete-time generator** of $X^n$:
--   $$ G_nV(x) = n\,\mathbb E\Big[(V(Y)-V(x))\Big(1\wedge\frac{\pi_n(Y)}{\pi_n(x)}\Big)\Big]. $$
--   2. The averages over the components $i=2,\dots,n$:
--   $$ R_n(x_2,\dots,x_n)=\frac1{n-1}\sum_{i=2}^n\big[(\log f(x_i))'\big]^2,\qquad S_n(x_2,\dots,x_n)=\frac{-1}{n-1}\sum_{i=2}^n(\log f(x_i))''. $$
--   3. The sets
--   $$ F_n=\{|R_n-I|<n^{-1/8}\}\cap\{|S_n-I|<n^{-1/8}\}\subseteq\mathbb R^n. $$
--   4. The quantity of Lemma 2.3, a function of the state $x$ and the proposal $y$:
--   $$ W_n=\sum_{i=2}^n\Big[\frac{(\log f(x_i))''}{2}(y_i-x_i)^2+\frac{l^2}{2(n-1)}\big((\log f(x_i))'\big)^2\Big]. $$
--
--   Here $(\log f(x_i))'$ and $(\log f(x_i))''$ are the first and second derivatives of $\log f$ at $x_i$.
--
--   **Formalization Note** The paper's components $2,\dots,n$ are the Lean indices $i\neq0$. $n-1$ is computed in $\mathbb R$ and $n^{-1/8}$ is a real power. The derivatives of $\log f$ are taken literally as `deriv` of `fun y => Real.log (f y)`; with $f>0$ and $f\in C^2$ they equal $f'/f$ and $f''/f-(f'/f)^2$. The integrand of $G_nV$ is bounded for bounded measurable $V$, so the expectation is a genuine integral.
-- source:
--   Roberts, Gelman, Gilks, Weak convergence and optimal scaling of random walk Metropolis algorithms, Ann. Appl. Probab. 7(1), 1997, p. 113 (G_nV), p. 114 (F_n, R_n, S_n), p. 115 (W_n, Lemma 2.3)

import Definitions.Def_Roberts1997_RWM_Target
import Definitions.Def_Roberts1997_RWM_Speed

open MeasureTheory ProbabilityTheory

namespace Roberts1997.RWM

/-- The discrete-time generator (p. 113)
`G_n V(x) = n 𝔼[(V(Y) - V(x)) (1 ∧ π_n(Y)/π_n(x))]`, `Y ~ N(x, σ_n² I_n)`. -/
noncomputable def discGen (f : ℝ → ℝ) (n : ℕ) (l : ℝ) (V : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  n * ∫ y, (V y - V x) * accept f n x y ∂(proposal n l x)

/-- `R_n(x_2, …, x_n) = (1/(n-1)) ∑_{i=2}^n [(log f(x_i))']²` (paper indices `2..n` are the
Lean indices `i ≠ 0`). -/
noncomputable def Rn (f : ℝ → ℝ) (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  (1 / ((n : ℝ) - 1)) *
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ≠ 0),
      (deriv (fun y => Real.log (f y)) (x i)) ^ 2

/-- `S_n(x_2, …, x_n) = (-1/(n-1)) ∑_{i=2}^n (log f(x_i))''`. -/
noncomputable def Sn (f : ℝ → ℝ) (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  (-1 / ((n : ℝ) - 1)) *
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ≠ 0),
      deriv (deriv (fun y => Real.log (f y))) (x i)

/-- `F_n = {|R_n - I| < n^{-1/8}} ∩ {|S_n - I| < n^{-1/8}} ⊆ ℝ^n`. -/
def Fn (f : ℝ → ℝ) (n : ℕ) : Set (Fin n → ℝ) :=
  {x | |Rn f n x - fisherI f| < (n : ℝ) ^ (-(1 : ℝ) / 8) ∧
       |Sn f n x - fisherI f| < (n : ℝ) ^ (-(1 : ℝ) / 8)}

/-- `W_n = ∑_{i=2}^n [ (log f(x_i))''/2 (y_i - x_i)² + l²/(2(n-1)) ((log f(x_i))')² ]`
(Lemma 2.3), as a function of the current state `x` and the proposal `y`. -/
noncomputable def Wn (f : ℝ → ℝ) (n : ℕ) (l : ℝ) (x y : Fin n → ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ≠ 0),
    (deriv (deriv (fun z => Real.log (f z))) (x i) / 2 * (y i - x i) ^ 2 +
      l ^ 2 / (2 * ((n : ℝ) - 1)) * (deriv (fun z => Real.log (f z)) (x i)) ^ 2)

end Roberts1997.RWM


