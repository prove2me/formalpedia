-- Prove2me | Definitions.Def_MultiperiodRisk_Bellman_Psi
-- name    : MultiperiodRisk_Bellman_Psi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T18:02:15.687522+00:00
-- url     : https://prove2.me/theorems/c00f7620-24af-445d-a837-0cd7effe5a27
-- title:
--   The risk-adjusted values $\Psi_\sigma(X)$ (Theorem 4.2) and $\bar\Psi_n(X)$ (Theorem 4.1)
-- statement:
--   Fix a set $\mathcal P$ of test probabilities with density set $D$ and a value process $X$ on $0,\dots,N$.
--
--   1. For a stopping time $\sigma$, the **risk-adjusted value at $\sigma$** is
--   $$
--   \Psi_\sigma(X)=\operatorname*{ess.inf}\bigl\{\mathbb E_{\mathbb Q}[X_\tau\mid\mathcal F_\sigma]\ \bigm|\ \tau\ge\sigma \text{ a stopping time with } \tau\le N,\ \mathbb Q\in\mathcal P^e\bigr\},
--   $$
--   the essential infimum being taken $\mathbb P_0$-a.s. among $\mathcal F_\sigma$-measurable functions. The process $n\mapsto\Psi_n(X)$ is $\Psi$ at the constant stopping times $\sigma\equiv n$.
--   2. The **generalized Snell envelope** $\bar\Psi(X)$ is defined by backward recursion:
--   $$
--   \bar\Psi_N(X)=X_N,\qquad \bar\Psi_n(X)=X_n\wedge\operatorname*{ess.inf}_{\mathbb Q\in\mathcal P^e}\mathbb E_{\mathbb Q}\bigl[\bar\Psi_{n+1}(X)\mid\mathcal F_n\bigr]\quad(0\le n<N).
--   $$
--
--   These are the two multiperiod measurements of risk that Section 4 compares; Theorem 4.2 shows that they coincide exactly when $\mathcal P$ is stable.
--
--   **Formalization Note** $\mathbb E_{\mathbb Q}[\,\cdot\mid\mathcal F_\sigma]$ is the conditional expectation under the measure $\mathbb Q_f=f\cdot\mathbb P_0$, with $\mathcal F_\sigma$ the σ-algebra of the stopping time. The essential infimum is the chosen one of the `EssInf` file (junk value $0$ if none exists; it exists whenever $\mathcal P^e\neq\emptyset$ and $X$ is bounded). The recursion is written with the index $k=N-n$; for $n>N$ the value of $\bar\Psi_n$ is frozen at $X_N$ and $\Psi_n$ is an infimum over an empty family — neither is ever used.
-- source:
--   Artzner, Delbaen, Eber, Heath, Ku, Coherent Multiperiod Risk Adjusted Values and Bellman's Principle, Ann. Oper. Res. 152 (2007); manuscript of Nov. 16, 2004, p. 11, Theorem 4.1 (formula for Ψ̄) and Theorem 4.2 (definition of Ψ_σ)

import Mathlib
import Definitions.Def_MultiperiodRisk_Bellman_TestSet
import Definitions.Def_MultiperiodRisk_Bellman_EssInf

namespace MultiperiodRisk.Bellman

open MeasureTheory

variable {Ω : Type*} {m : MeasurableSpace Ω} {P₀ : Measure Ω} {ℱ : Filtration ℕ m} {N : ℕ}

/-- The family `{𝐄_ℚ[X_τ | ℱ_σ] | τ ≥ σ a stopping time (bounded by N), ℚ ∈ 𝒫ᵉ}`. -/
def psiFamily (D : TestSet P₀ ℱ N) (X : ℕ → Ω → ℝ) (σ : Ω → WithTop ℕ)
    (hσ : IsStoppingTime ℱ σ) : Set (Ω → ℝ) :=
  {h | ∃ τ : Ω → WithTop ℕ, IsBddStoppingTime ℱ N τ ∧ (∀ ω, σ ω ≤ τ ω) ∧
    ∃ f ∈ Pe D, h = (Q P₀ f)[stoppedValue X τ | hσ.measurableSpace]}

/-- Theorem 4.2: `Ψ_σ(X) = ess.inf {𝐄_ℚ[X_τ | ℱ_σ] | τ ≥ σ, ℚ ∈ 𝒫ᵉ}`, the essential
infimum being taken `P₀`-a.s. among `ℱ_σ`-measurable functions. -/
noncomputable def Psi (D : TestSet P₀ ℱ N) (X : ℕ → Ω → ℝ) (σ : Ω → WithTop ℕ)
    (hσ : IsStoppingTime ℱ σ) : Ω → ℝ :=
  essInfFamily P₀ hσ.measurableSpace (psiFamily D X σ hσ)

/-- The process `n ↦ Ψ_n(X)`: `Ψ` at the constant stopping time `n` (read for `n ≤ N`). -/
noncomputable def PsiN (D : TestSet P₀ ℱ N) (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  Psi D X (fun _ => (n : WithTop ℕ)) (isStoppingTime_const ℱ (n : ℕ))

/-- Backward recursion of Theorem 4.1, indexed by `k = N - n`:
`psiBarAux 0 = X_N`, and `psiBarAux (k+1) = X_{N-k-1} ∧ ess.inf_{ℚ∈𝒫ᵉ} 𝐄_ℚ[psiBarAux k | ℱ_{N-k-1}]`. -/
noncomputable def psiBarAux (D : TestSet P₀ ℱ N) (X : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => X N
  | k + 1 => fun ω => min (X (N - (k + 1)) ω)
      (essInfFamily P₀ (ℱ (N - (k + 1)))
        {h | ∃ f ∈ Pe D, h = (Q P₀ f)[psiBarAux D X k | ℱ (N - (k + 1))]} ω)

/-- Theorem 4.1: the generalized Snell envelope `Ψ̄(X)`, with `Ψ̄_N(X) = X_N` and
`Ψ̄_n(X) = X_n ∧ ess.inf_{ℚ∈𝒫ᵉ} 𝐄_ℚ[Ψ̄_{n+1}(X) | ℱ_n]` for `0 ≤ n < N`.
For `n > N` the value is frozen at `X_N` (never read). -/
noncomputable def PsiBar (D : TestSet P₀ ℱ N) (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  if n ≤ N then psiBarAux D X (N - n) else X N

end MultiperiodRisk.Bellman


