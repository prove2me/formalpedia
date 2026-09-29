-- Prove2me | Definitions.Def_Roberts1997_RWM_Chain
-- name    : Roberts1997_RWM_Chain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:44:27.869331+00:00
-- url     : https://prove2.me/theorems/1da5abad-0cea-4f64-8e2a-52529c4f355c
-- title:
--   The random walk Metropolis chain X^n started from π_n, and the speeded-up paths Z^n_t = X^n_{⌊nt⌋} and U^n_t = X^n_{⌊nt⌋,1}
-- statement:
--   The random walk Metropolis algorithm (p. 111) produces a Markov chain $X^n=(X^n_0,X^n_1,\dots)$ on $\mathbb R^n$: given $X^n_{m-1}$, generate $Y^n\sim q_n(X^n_{m-1},\cdot)=N(X^n_{m-1},\sigma_n^2 I_n)$ and set $X^n_m=Y^n$ with probability $\alpha(X^n_{m-1},Y^n)$, otherwise $X^n_m=X^n_{m-1}$.
--
--   The chain is realised on an explicit probability space. A sample point is $\omega=(x_0,(\xi_m,u_m)_{m\ge0})$ with $x_0\in\mathbb R^n$, $\xi_m\in\mathbb R^n$ and $u_m\in[0,1]$; under the law $P_n$, $x_0\sim\pi_n$ (the chain starts in stationarity), the $\xi_m$ are i.i.d. $N(0,I_n)$, the $u_m$ are i.i.d. uniform on $[0,1]$, and all are independent. Then
--
--   $$ X^n_0=x_0,\qquad X^n_{m+1}=\begin{cases} X^n_m+\sigma_n\xi_m & \text{if } u_m<\alpha(X^n_m,X^n_m+\sigma_n\xi_m),\ X^n_m & \text{otherwise},\end{cases} $$
--
--   with $\sigma_n=\sqrt{l^2/(n-1)}$. The speeded-up processes are $Z^n_t = X^n_{\lfloor nt\rfloor}$ (p. 114) and its first component $U^n_t = X^n_{\lfloor nt\rfloor,1}$ (p. 111), for $t\ge0$.
--
--   **Formalization Note** The random-mapping construction is literally the paper's algorithm: the proposal is $N(X^n_m,\sigma_n^2I_n)$ and acceptance occurs with probability $\alpha$. Theorem 1.1's initial condition ("all components distributed according to $f$", with the chains of different dimensions sharing their first coordinates) is read as "the $n$-th chain starts from $\pi_n$"; weak convergence depends only on the law of each $U^n$, so the coupling across dimensions is immaterial, and the paper's proof uses exactly $Z^n_0\sim\pi_n$ (p. 114). Time is `ℝ≥0` and $\lfloor nt\rfloor$ is `Nat.floor`; the time factor is $n$.
-- source:
--   Roberts, Gelman, Gilks, Weak convergence and optimal scaling of random walk Metropolis algorithms, Ann. Appl. Probab. 7(1), 1997, p. 111 (the algorithm and U^n_t = X^n_{[nt],1}), p. 112 (Theorem 1.1, initial condition), p. 114 (Z^n_t)

import Definitions.Def_Roberts1997_RWM_Target

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Roberts1997.RWM

/-- The randomness of the `n`-dimensional chain: an initial state in `ℝ^n` and, for each step
`m`, a standard normal vector in `ℝ^n` and a uniform variable in `[0, 1]`. -/
abbrev Omega (n : ℕ) : Type := (Fin n → ℝ) × (ℕ → (Fin n → ℝ) × unitInterval)

/-- The law of one step's innovation: `N(0, I_n) ⊗ Uniform[0, 1]`. -/
noncomputable def innovLaw (n : ℕ) : Measure ((Fin n → ℝ) × unitInterval) :=
  (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).prod volume

/-- The law of the randomness: initial state `~ π_n` (stationary start), independent of an
i.i.d. sequence of innovations. -/
noncomputable def chainLaw (f : ℝ → ℝ) (n : ℕ) : Measure (Omega n) :=
  (target f n).prod (Measure.infinitePi (fun _ : ℕ => innovLaw n))

/-- The random walk Metropolis chain `X^n_m` with proposal `N(X_{m-1}, σ_n² I_n)`,
`σ_n = √(l²/(n-1))`: propose `Y = X_{m-1} + σ_n ξ_m`, and accept (`X_m = Y`) iff the uniform
`U_m < α(X_{m-1}, Y)`, i.e. with probability `α`; otherwise `X_m = X_{m-1}`. -/
noncomputable def chain (f : ℝ → ℝ) (n : ℕ) (l : ℝ) : ℕ → Omega n → (Fin n → ℝ)
  | 0, ω => ω.1
  | m + 1, ω =>
    if ((ω.2 m).2 : ℝ) < accept f n (chain f n l m ω)
        (chain f n l m ω + Real.sqrt (sigmaSq n l) • (ω.2 m).1)
    then chain f n l m ω + Real.sqrt (sigmaSq n l) • (ω.2 m).1
    else chain f n l m ω

/-- The speeded-up vector process `Z^n_t = X^n_{⌊n t⌋}`. -/
noncomputable def Zproc (f : ℝ → ℝ) (n : ℕ) (l : ℝ) (t : ℝ≥0) (ω : Omega n) : Fin n → ℝ :=
  chain f n l (Nat.floor ((n : ℝ≥0) * t)) ω

/-- The path of the first component, `U^n_t = X^n_{⌊n t⌋, 1}`. -/
noncomputable def Upath (f : ℝ → ℝ) (n : ℕ) (l : ℝ) (ω : Omega n) : ℝ≥0 → ℝ :=
  fun t => first (Zproc f n l t ω)

end Roberts1997.RWM


