-- Prove2me | Definitions.Def_NaiveFS_Multinomial_Model
-- name    : NaiveFS_Multinomial_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:14:13.526799+00:00
-- url     : https://prove2.me/theorems/7ad4a6b3-6f86-4305-bb9a-12a90721b92b
-- title:
--   §2.2, §3.1, §3.3–3.4, pp. 2–8 — sparse multinomial naive Bayes (SMNB), its value ϕ(k), the top-k sum s_k, and the relaxation (USMNB) with C, C̃, h(α), ψ(k)
-- statement:
--   The sparse multinomial naive Bayes problem and its one-dimensional convex relaxation.
--
--   **Data.** There are $m$ features. A nonnegative data matrix $X\in\mathbb R_+^{n\times m}$ with labels $y\in\{-1,1\}^n$ enters only through the class sums $f^\pm=\sum_{i:\,y_i=\pm1}x^{(i)}\in\mathbb R^m$; throughout, $f^+_i,f^-_i>0$. Write $g=f^++f^-$ and $S=\mathbf 1^\top(f^++f^-)$.
--
--   1. **Feasible set.** For an integer $k$, a pair $(\theta^+,\theta^-)$ is feasible for (SMNB) when $\theta^\pm\in(0,1]^m$, $\mathbf 1^\top\theta^+=\mathbf 1^\top\theta^-=1$ and $\|\theta^+-\theta^-\|_0=\#\{i:\theta^+_i\ne\theta^-_i\}\le k$.
--   2. **Objective and value.** The log-likelihood is $f^{+\top}\log\theta^++f^{-\top}\log\theta^-$, and
--   $$\phi(k)=\sup\Big\{f^{+\top}\log\theta^++f^{-\top}\log\theta^-\ :\ (\theta^+,\theta^-)\ \text{feasible}\Big\}.$$
--   3. **Top-$k$ sum.** For $c\in\mathbb R^n$, $s_k(c)$ is the sum of its $\min(k,n)$ largest entries. For $c\ge0$ it also equals $\max_{u\in\{0,1\}^n,\ \mathbf 1^\top u\le k}u^\top c$, as on p. 6.
--   4. **Relaxation (USMNB).** With
--   $$\tilde C=f^+\circ\log f^++f^-\circ\log f^--(f^++f^-)\circ\log(f^++f^-),\qquad h(\alpha)=\tilde C-f^+\log\alpha-f^-\log(1-\alpha)\quad(0<\alpha<1),$$
--   and the constant $C=(f^++f^-)^\top\log(f^++f^-)-S\log S$,
--   $$\psi(k)=C+\inf_{\alpha\in(0,1)}s_k\big(h(\alpha)\big).$$
--
--   These objects are shared by every statement of the mission: Theorem 3.2 compares $\phi(k)$ with $\psi(k)$, and Theorem 3.6 shows the two agree up to a shift of four in $k$.
--
--   **Formalization Note** Features are indexed by `Fin m`. $\theta^\pm$ are required to be strictly positive: since $f^\pm>0$, the paper's objective equals $-\infty$ whenever some $\theta_i=0$, so the supremum is unchanged, whereas Lean's convention $\log 0=0$ would otherwise inflate it. $\phi$ is a real `sSup` of a set that is nonempty (uniform $\theta^\pm$) and bounded above by $0$. $s_k$ is the supremum over subsets of exactly $\min(k,n)$ indices, a nonempty finite set; it is the sum of the largest entries even for signed vectors. On the nonnegative inputs used in the paper's relaxation it equals the $\mathcal C_k$ form of p. 6. The paper writes $\min_{\alpha\in[0,1]}$; $h$ is only defined on $(0,1)$ and $s_k(h(\alpha))\to+\infty$ at both ends when $k\ge1$, so the infimum is taken over the open interval. The constant $C$ is the one fixed on p. 8, built into $\psi$; Theorem 3.2 only says "$C$ is a constant", and Theorem 3.6 is false for any other value.
-- source:
--   Askari, d'Aspremont & El Ghaoui, Naive Feature Selection, arXiv:1905.09884v4, pp. 2–8, §2.2 (f±), §3.1, Theorem 3.2 (USMNB), §3.4 (SMNB) and the constant C (p. 8)

import Mathlib

namespace NaiveFS.Multinomial

open Finset

/-- Feasible set of (SMNB) at sparsity level `k` (Askari–d'Aspremont–El Ghaoui, §3.4, p. 7):
`θ⁺, θ⁻ ∈ (0,1]ᵐ`, `1ᵀθ⁺ = 1ᵀθ⁻ = 1`, `‖θ⁺ − θ⁻‖₀ = #{i : θ⁺ᵢ ≠ θ⁻ᵢ} ≤ k`.
Entries are taken strictly positive: with `f± > 0` the paper's objective is `−∞` as soon as
some `θᵢ = 0`, so this does not change the optimal value, while Lean's `Real.log 0 = 0`
would otherwise inflate it. -/
def Feasible {m : ℕ} (k : ℕ) (θp θm : Fin m → ℝ) : Prop :=
  (∀ i, 0 < θp i ∧ θp i ≤ 1) ∧ (∀ i, 0 < θm i ∧ θm i ≤ 1) ∧
    ∑ i, θp i = 1 ∧ ∑ i, θm i = 1 ∧
    (univ.filter (fun i => θp i ≠ θm i)).card ≤ k

/-- The log-likelihood objective `f⁺ᵀ log θ⁺ + f⁻ᵀ log θ⁻` of (SMNB). -/
noncomputable def objective {m : ℕ} (fp fm θp θm : Fin m → ℝ) : ℝ :=
  ∑ i, (fp i * Real.log (θp i) + fm i * Real.log (θm i))

/-- `ϕ(k)`, the optimal value of (SMNB) (Theorem 3.2, p. 6; §3.4, p. 7): the supremum of the
objective over the feasible set. For `m ≥ 1` the set is nonempty (uniform `θ±`) and, since
`f± > 0` and `log θ ≤ 0` on `(0,1]`, bounded above by `0`. -/
noncomputable def phi {m : ℕ} (fp fm : Fin m → ℝ) (k : ℕ) : ℝ :=
  sSup {v | ∃ θp θm : Fin m → ℝ, Feasible k θp θm ∧ v = objective fp fm θp θm}

/-- `s_k(c)`, the sum of the top `k` entries (p. 2). For `k ≥ n` all entries are summed.
The page 6 formula using `C_k = {u ∈ {0,1}ⁿ : 1ᵀu ≤ k}` agrees with this definition when
`c ≥ 0`, as in every use of that formula here. -/
noncomputable def topSum {n : ℕ} (k : ℕ) (c : Fin n → ℝ) : ℝ :=
  sSup {v | ∃ T : Finset (Fin n), T.card = min k n ∧ v = ∑ i ∈ T, c i}

/-- `S := 1ᵀ(f⁺ + f⁻)` (p. 7). -/
def S {m : ℕ} (fp fm : Fin m → ℝ) : ℝ := ∑ i, (fp i + fm i)

/-- The constant `C := (f⁺ + f⁻)ᵀ log(f⁺ + f⁻) − S log S` of (USMNB) (p. 8). -/
noncomputable def C {m : ℕ} (fp fm : Fin m → ℝ) : ℝ :=
  ∑ i, (fp i + fm i) * Real.log (fp i + fm i) - S fp fm * Real.log (S fp fm)

/-- `C̃ = f⁺ ∘ log f⁺ + f⁻ ∘ log f⁻ − (f⁺ + f⁻) ∘ log(f⁺ + f⁻)` (Theorem 3.2, p. 6). -/
noncomputable def Ctil {m : ℕ} (fp fm : Fin m → ℝ) : Fin m → ℝ := fun i =>
  fp i * Real.log (fp i) + fm i * Real.log (fm i) - (fp i + fm i) * Real.log (fp i + fm i)

/-- `h(α) = C̃ − f⁺ log α − f⁻ log(1 − α)`, meaningful for `α ∈ (0,1)` (Theorem 3.2, p. 6). -/
noncomputable def h {m : ℕ} (fp fm : Fin m → ℝ) (α : ℝ) : Fin m → ℝ := fun i =>
  Ctil fp fm i - fp i * Real.log α - fm i * Real.log (1 - α)

/-- `ψ(k) := C + min_α s_k(h(α))`, the value of the relaxation (USMNB) (Theorem 3.2, p. 6;
constant `C` from p. 8). The minimum is taken over the open interval `(0,1)`, where `h` is
defined; the set is nonempty and bounded below by `0` because `h(α) ≥ 0` there. -/
noncomputable def psi {m : ℕ} (fp fm : Fin m → ℝ) (k : ℕ) : ℝ :=
  C fp fm + sInf ((fun α => topSum k (h fp fm α)) '' Set.Ioo (0 : ℝ) 1)

end NaiveFS.Multinomial


