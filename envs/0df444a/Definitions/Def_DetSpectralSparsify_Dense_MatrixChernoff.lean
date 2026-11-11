-- Prove2me | Definitions.Def_DetSpectralSparsify_Dense_MatrixChernoff
-- name    : DetSpectralSparsify_Dense_MatrixChernoff
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:58:08.20864+00:00
-- url     : https://prove2.me/theorems/d28a7071-c67c-4a49-92c6-8d3727a3e4d1
-- title:
--   Algorithm 1 (MatrixChernoffSelect), its inexact-score variant, and the exponent recurrence (40)
-- statement:
--   **Algorithm 1** (p.6). Let $A_1,\dots,A_q$ be positive semidefinite $r\times r$ matrices, $R\ge1$, $0<\varepsilon\le1/2$ and $k\ge1$. Put $X_i=A_i/R$,
--   $$\theta_+=\log(1+\varepsilon),\quad\theta_-=-\log(1-\varepsilon),\quad\rho_+=1+\varepsilon/R,\quad\rho_-=1-\varepsilon/R .$$
--   At iteration $j=1,\dots,k$, with $S=X_{i_1}+\dots+X_{i_{j-1}}$ and
--   $$u_j=e^{-\theta_+(1+\varepsilon)k/R}\rho_+^{\,k-j},\qquad \ell_j=e^{\theta_-(1-\varepsilon)k/R}\rho_-^{\,k-j},$$
--   the **score** of candidate $i$ is
--   $$\sigma_j(i)=u_j\,\langle e^{\theta_+S},A_i\rangle-\ell_j\,\langle e^{-\theta_-S},A_i\rangle,\qquad\langle E,A\rangle=\mathrm{Tr}(EA),$$
--   and Algorithm 1 chooses $i_j$ minimizing $\sigma_j$. A sequence $(i_1,\dots,i_k)$ **is chosen by Algorithm 1** if every $i_j$ minimizes the score of its iteration (ties broken in any way).
--
--   **Inexact scores** (Lemma 6). A sequence is **chosen with inexact scores** if there are real numbers $\tilde\sigma_j(i)$ with $|\tilde\sigma_j(i)-\sigma_j(i)|\le\zeta:=R/(16\varepsilon k)$ for all $i$ and $j$, and every $i_j$ minimizes $\tilde\sigma_j$.
--
--   **Exponent recurrence** (40), p.28: for a real starting value $\alpha_0$,
--   $$\alpha_{r+1}=3-\frac{1}{\alpha_r-1}.$$
--   The paper starts it at $\alpha_0=\omega$.
--
--   **Formalization Note** Iterations are indexed from $0$ in Lean: `j : Fin k` is iteration $j+1$, so $S$ is the sum over the first $j$ selections and the coefficients use the exponent $k-(j+1)$. Matrix exponentials are `NormedSpace.exp`. The recurrence is defined by recursion on $r$, never by its closed form.
-- source:
--   Trevor Vaughn, Jason Li, Deterministic Spectral Sparsification in Almost-Linear Time for Dense Graphs, STOC 2027 submission #370 (October 2026), source.pdf SHA-256 b88d92728f937730b7e9664f482778048c0b667d4376e0488686c9708e5d8467, p.6 (Algorithm 1, Lemma 5 setting), p.8 (Lemma 6, ζ), p.28 (recurrence (40))

import Mathlib

set_option autoImplicit false

namespace DetSpectralSparsify.Dense

open Matrix

/-! ## Algorithm 1 (MatrixChernoffSelect, p.6)

Inputs: PSD `r × r` matrices `A₁,…,A_q`, a bound `R`, an accuracy `ε` and a length `k`.
With `X_i = A_i / R`, `θ₊ = log(1+ε)`, `θ₋ = -log(1-ε)`, `ρ₊ = 1 + ε/R`, `ρ₋ = 1 - ε/R`,
iteration `j = 1,…,k` uses `S = X_{i_1} + ⋯ + X_{i_{j-1}}`,
`u_j = e^{-θ₊(1+ε)k/R} ρ₊^{k-j}`, `ℓ_j = e^{θ₋(1-ε)k/R} ρ₋^{k-j}`, and chooses `i_j`
minimizing `u_j ⟨e^{θ₊ S}, A_i⟩ - ℓ_j ⟨e^{-θ₋ S}, A_i⟩`, where `⟨E, A⟩ = Tr(E A)`.
Indices are `0`-based in Lean: `j : Fin k` is iteration `j + 1`. -/

/-- `θ₊ = log(1 + ε)`. -/
noncomputable def thetaPlus (ε : ℝ) : ℝ := Real.log (1 + ε)

/-- `θ₋ = -log(1 - ε)`. -/
noncomputable def thetaMinus (ε : ℝ) : ℝ := -Real.log (1 - ε)

/-- `u_j = e^{-θ₊(1+ε)k/R} (1 + ε/R)^{k-j}` (`j` is the 1-based iteration number). -/
noncomputable def uCoef (R ε : ℝ) (k j : ℕ) : ℝ :=
  Real.exp (-(thetaPlus ε) * (1 + ε) * k / R) * (1 + ε / R) ^ (k - j)

/-- `ℓ_j = e^{θ₋(1-ε)k/R} (1 - ε/R)^{k-j}` (`j` is the 1-based iteration number). -/
noncomputable def lCoef (R ε : ℝ) (k j : ℕ) : ℝ :=
  Real.exp (thetaMinus ε * (1 - ε) * k / R) * (1 - ε / R) ^ (k - j)

variable {r q k : ℕ}

/-- `S` before iteration `j + 1`: the sum of `X_{i_h} = A_{i_h} / R` over the first `j`
selected indices. -/
noncomputable def selectedSum (A : Fin q → Matrix (Fin r) (Fin r) ℝ) (R : ℝ)
    (idx : Fin k → Fin q) (j : ℕ) : Matrix (Fin r) (Fin r) ℝ :=
  ∑ h ∈ Finset.univ.filter (fun h : Fin k => h.val < j), R⁻¹ • A (idx h)

/-- The exact score of candidate `i` at iteration `j + 1`, given the earlier selections `idx`:
`u_{j+1} Tr(e^{θ₊ S} A_i) - ℓ_{j+1} Tr(e^{-θ₋ S} A_i)` with `S = selectedSum A R idx j`. -/
noncomputable def chernoffScore (A : Fin q → Matrix (Fin r) (Fin r) ℝ) (R ε : ℝ)
    (idx : Fin k → Fin q) (j : Fin k) (i : Fin q) : ℝ :=
  let S := selectedSum A R idx j.val
  uCoef R ε k (j.val + 1) * Matrix.trace (NormedSpace.exp (thetaPlus ε • S) * A i) -
    lCoef R ε k (j.val + 1) * Matrix.trace (NormedSpace.exp (-(thetaMinus ε) • S) * A i)

/-- `idx` is a sequence chosen by Algorithm 1: at every iteration the chosen index minimizes the
exact score (ties broken arbitrarily). -/
def IsAlg1Selection (A : Fin q → Matrix (Fin r) (Fin r) ℝ) (R ε : ℝ) (idx : Fin k → Fin q) :
    Prop :=
  ∀ j : Fin k, ∀ i : Fin q, chernoffScore A R ε idx j (idx j) ≤ chernoffScore A R ε idx j i

/-- `idx` is chosen by Algorithm 1 with inexact scores (Lemma 6): there are approximate scores,
within additive `ζ = R / (16 ε k)` of the exact scores for every candidate at every iteration,
and each chosen index minimizes the approximate score. The approximate scores are arbitrary
reals and may depend on the run. -/
def IsApproxAlg1Selection (A : Fin q → Matrix (Fin r) (Fin r) ℝ) (R ε : ℝ)
    (idx : Fin k → Fin q) : Prop :=
  ∃ σ : Fin k → Fin q → ℝ,
    (∀ j i, |σ j i - chernoffScore A R ε idx j i| ≤ R / (16 * ε * k)) ∧
    ∀ j i, σ j (idx j) ≤ σ j i

/-! ## The exponent recurrence (40), p.28 -/

/-- `α_0 = α₀`, `α_{r+1} = 3 - 1/(α_r - 1)`. The paper takes `α₀ = ω`; here `α₀` is a real
parameter. -/
noncomputable def alphaSeq (α₀ : ℝ) : ℕ → ℝ
  | 0 => α₀
  | r + 1 => 3 - 1 / (alphaSeq α₀ r - 1)

end DetSpectralSparsify.Dense


