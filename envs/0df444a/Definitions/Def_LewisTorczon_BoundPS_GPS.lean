-- Prove2me | Definitions.Def_LewisTorczon_BoundPS_GPS
-- name    : LewisTorczon_BoundPS_GPS
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:42:10.098552+00:00
-- url     : https://prove2.me/theorems/ef9bd47c-860d-49ae-8059-4a8ec5293bc2
-- title:
--   Generalized pattern search for bound constrained problems: patterns, exploratory moves, Algorithms 1–2
-- statement:
--   This file encodes a run of the **generalized pattern search method for bound constrained problems** (Algorithm 1 with the step-length update of Algorithm 2).
--
--   **Fixed data of the method.**
--   1. A nonsingular **basis matrix** $B\in\mathbb R^{n\times n}$.
--   2. A finite set $\mathcal M\subset\mathbb Z^{n\times n}$ of nonsingular integer matrices.
--   3. A rational $\tau>1$, an integer $w_0<0$, and a finite nonempty set $\{w_1,\dots,w_L\}$ of nonnegative integers; put $\theta=\tau^{w_0}$ and $\Lambda=\{\tau^{w_1},\dots,\tau^{w_L}\}$.
--
--   **A run** consists of iterates $x_k\in\mathbb R^n$, step-length parameters $\Delta_k$, steps $s_k$, and generating matrices $C_k=[M_k\ \ {-M_k}\ \ L_k]=[\Gamma_k\ \ L_k]$ with $M_k\in\mathbb Z^{n\times n}$ and $L_k\in\mathbb Z^{n\times(p-2n)}$. A **trial step** is $\Delta_k B c$ for a column $c$ of $C_k$. The run satisfies, for every $k$:
--   1. $x_0\in\Omega$ and $\Delta_0>0$;
--   2. $M_k\in\mathcal M$, $L_k$ has a column of zeroes, and $BM_k$ is diagonal;
--   3. (exploratory moves) $s_k=\Delta_k Bc$ for some column $c$ of $C_k$, $x_k+s_k\in\Omega$, and
--   $$\min\{f(x_k+y) : y\in\Delta_k B\Gamma_k,\ x_k+y\in\Omega\}<f(x_k)\ \Longrightarrow\ f(x_k+s_k)<f(x_k);$$
--   4. (Algorithm 1 (d)) $x_{k+1}=x_k+s_k$ if $f(x_k+s_k)<f(x_k)$, and $x_{k+1}=x_k$ otherwise;
--   5. (Algorithm 2) $\Delta_{k+1}=\lambda_k\Delta_k$ with $\lambda_k\in\Lambda$ after a successful iteration, and $\Delta_{k+1}=\theta\Delta_k$ otherwise.
--
--   **Strong Hypotheses.** A run satisfies the third Strong Hypothesis if, whenever the minimum above is below $f(x_k)$, the step satisfies $f(x_k+s_k)\le f(x_k+y)$ for every feasible core trial step $y\in\Delta_k B\Gamma_k$.
--
--   **Bounded columns.** There is $C>0$ with $\|c\|<C$ for every column $c$ of every $C_k$ (Euclidean norm).
--
--   These are the objects about which the paper's convergence theory (Theorems 3.2 and 3.3) is stated.
--
--   **Formalization Note** The number of columns of $L_k$ is a parameter $m$ (the paper's $p-2n$); "$L_k$ has a zero column" forces $m\ge1$. Lean column $i$ is the paper's column $i+1$. The minimum over the finite set of feasible core trial points is encoded as "some feasible core trial step strictly decreases $f$", which is exactly when the minimum exists and is below $f(x_k)$. The acceptance test $\rho_k>0$ is $f(x_k+s_k)<f(x_k)$. The update of $C_k$ is otherwise free, as in the paper. The nonemptiness of $\{w_1,\dots,w_L\}$ is implicit in the paper's "$\lambda_k\in\Lambda$". The page prints the third Strong Hypothesis with a strict inequality $f(x_k+s_k)<\min\{\cdots\}$, which no core step can satisfy and which excludes the coordinate search methods the paper says satisfy it; the proof of Proposition 4.3 uses only $\le$, the form of Torczon (1997), and that is what is encoded. $\le$ is the weaker hypothesis, so every theorem using it is at least as strong as with the printed $<$.
-- source:
--   Lewis & Torczon, Pattern Search Algorithms for Bound Constrained Minimization, ICASE Report No. 96-20 (NASA CR-198306), March 1996, pp. 2–3, §2.1 (pattern, eqs. (2)–(3), trial steps), §2.2 (Hypotheses on Bound Constrained Exploratory Moves), §2.3 (Algorithm 1), §2.4 (Algorithm 2); p. 7, §3 (bounded columns, Strong Hypotheses)

import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box

namespace LewisTorczon.BoundPS

/-- The fixed data of a generalized pattern search method (§2.1 and Algorithm 2, pp. 2–3):
* a nonsingular basis matrix `B ∈ ℝ^{n×n}`;
* a finite set `𝕄 ⊂ ℤ^{n×n}` of nonsingular integer matrices (nonzero integer determinant),
  from which every `M_k` is drawn;
* the rational `τ > 1`, the exponent `w₀ < 0` (so `θ = τ^{w₀}`) and the finite nonempty set
  `W = {w_1, …, w_L}` of exponents `w_i ≥ 0` (so `Λ = {τ^{w_i}}`; `L ≥ 1` is implicit in
  "`λ_k ∈ Λ`"). -/
structure GPSParams (n : ℕ) where
  B : Matrix (Fin n) (Fin n) ℝ
  B_det_ne_zero : B.det ≠ 0
  𝕄 : Finset (Matrix (Fin n) (Fin n) ℤ)
  𝕄_det_ne_zero : ∀ M ∈ 𝕄, M.det ≠ 0
  τ : ℚ
  one_lt_τ : 1 < τ
  w₀ : ℤ
  w₀_neg : w₀ < 0
  W : Finset ℤ
  W_nonneg : ∀ w ∈ W, 0 ≤ w
  W_nonempty : W.Nonempty

/-- The sequences of one run of Algorithm 1: iterates `x_k`, step-length parameters `Δ_k`,
steps `s_k`, and the generating matrices `C_k = [M_k  −M_k  L_k]` through their blocks
`M_k ∈ ℤ^{n×n}` and `L_k ∈ ℤ^{n×m}` (the paper's `m = p − 2n`). -/
structure GPSRun (n m : ℕ) where
  x : ℕ → EuclideanSpace ℝ (Fin n)
  Δ : ℕ → ℝ
  s : ℕ → EuclideanSpace ℝ (Fin n)
  M : ℕ → Matrix (Fin n) (Fin n) ℤ
  L : ℕ → Matrix (Fin n) (Fin m) ℤ

/-- The columns of `Γ_k = [M_k  −M_k]` (the core of the generating matrix, (2)). -/
def coreCols {n m : ℕ} (R : GPSRun n m) (k : ℕ) : Set (Fin n → ℤ) :=
  {c | ∃ i, c = (R.M k).transpose i ∨ c = -((R.M k).transpose i)}

/-- The columns of `C_k = [M_k  −M_k  L_k]` (2). -/
def cols {n m : ℕ} (R : GPSRun n m) (k : ℕ) : Set (Fin n → ℤ) :=
  coreCols R k ∪ {c | ∃ j, c = (R.L k).transpose j}

/-- An integer vector viewed as a point of Euclidean `ℝⁿ`. -/
noncomputable def intVec {n : ℕ} (c : Fin n → ℤ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun r => (c r : ℝ))

/-- The trial step `Δ B c` defined by a column `c` of the generating matrix (p. 2). -/
noncomputable def stepOf {n : ℕ} (P : GPSParams n) (Δ : ℝ) (c : Fin n → ℤ) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (Δ • (P.B.mulVec (fun r => (c r : ℝ))))

/-- `R` is a run of the generalized pattern search method for bound constrained problems
(Algorithm 1, p. 3) with the pattern of §2.1, bound constrained exploratory moves satisfying the
Hypotheses of §2.2, and the `Δ_k` update of Algorithm 2 (§2.4). "min{f(x_k+y) | y ∈ Δ_k BΓ_k,
x_k + y ∈ Ω} < f(x_k)" (a minimum over a finite set) is encoded as "some feasible core trial step
decreases `f`". `ρ_k > 0` is `f(x_k + s_k) < f(x_k)`. -/
structure IsGPSRun {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (R : GPSRun n m) : Prop where
  /-- Algorithm 1: `x_0 ∈ Ω`. -/
  x_zero_mem : R.x 0 ∈ box lo hi
  /-- Algorithm 1: `Δ_0 > 0`. -/
  Δ_zero_pos : 0 < R.Δ 0
  /-- §2.1: `M_k ∈ 𝕄`. -/
  M_mem : ∀ k, R.M k ∈ P.𝕄
  /-- §2.1: `L_k` contains a column of zeroes. -/
  L_zero_col : ∀ k, ∃ j, (R.L k).transpose j = 0
  /-- (3): `B M_k` is diagonal. -/
  diag : ∀ k, (P.B * (R.M k).map (fun a : ℤ => (a : ℝ))).IsDiag
  /-- Hypothesis 1: `s_k ∈ Δ_k B C_k`. -/
  step_mem : ∀ k, ∃ c ∈ cols R k, R.s k = stepOf P (R.Δ k) c
  /-- Hypothesis 2: `x_k + s_k ∈ Ω`. -/
  step_feasible : ∀ k, R.x k + R.s k ∈ box lo hi
  /-- Hypothesis 3: simple decrease is found whenever a feasible core step gives it. -/
  simple_decrease : ∀ k,
    (∃ c ∈ coreCols R k, R.x k + stepOf P (R.Δ k) c ∈ box lo hi ∧
        f (R.x k + stepOf P (R.Δ k) c) < f (R.x k)) →
      f (R.x k + R.s k) < f (R.x k)
  /-- Algorithm 1 (d). -/
  x_succ : ∀ k, R.x (k + 1) = if f (R.x k + R.s k) < f (R.x k) then R.x k + R.s k else R.x k
  /-- Algorithm 2 (b): after a successful iteration `Δ_{k+1} = λ_k Δ_k`, `λ_k ∈ Λ`. -/
  Δ_succ_success : ∀ k, f (R.x k + R.s k) < f (R.x k) →
    ∃ w ∈ P.W, R.Δ (k + 1) = (P.τ : ℝ) ^ w * R.Δ k
  /-- Algorithm 2 (a): after an unsuccessful iteration `Δ_{k+1} = θ Δ_k`. -/
  Δ_succ_failure : ∀ k, ¬ f (R.x k + R.s k) < f (R.x k) →
    R.Δ (k + 1) = (P.τ : ℝ) ^ P.w₀ * R.Δ k

/-- Clause 3 of the Strong Hypotheses on Bound Constrained Exploratory Moves (p. 7), with "≤":
if some feasible core trial step decreases `f`, then `f(x_k + s_k)` is at most `f` at every
feasible core trial point (i.e. at most the minimum). Clauses 1–2 are those of `IsGPSRun`.
The page prints "<"; see the mission notes. -/
def StrongHyp {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (R : GPSRun n m) : Prop :=
  ∀ k, (∃ c ∈ coreCols R k, R.x k + stepOf P (R.Δ k) c ∈ box lo hi ∧
        f (R.x k + stepOf P (R.Δ k) c) < f (R.x k)) →
    ∀ c ∈ coreCols R k, R.x k + stepOf P (R.Δ k) c ∈ box lo hi →
      f (R.x k + R.s k) ≤ f (R.x k + stepOf P (R.Δ k) c)

/-- The columns of the generating matrices are uniformly bounded in (Euclidean) norm:
`∃ C > 0, ∀ k, ∀ i, C > ‖c_k^i‖` (p. 7). -/
def BoundedCols {n m : ℕ} (R : GPSRun n m) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ k, ∀ c ∈ cols R k, ‖intVec c‖ < C

end LewisTorczon.BoundPS


