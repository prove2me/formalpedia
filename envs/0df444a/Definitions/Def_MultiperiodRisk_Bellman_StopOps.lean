-- Prove2me | Definitions.Def_MultiperiodRisk_Bellman_StopOps
-- name    : MultiperiodRisk_Bellman_StopOps
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T18:02:57.302609+00:00
-- url     : https://prove2.me/theorems/f55bc95e-335b-42cf-b425-58c19832c6ae
-- title:
--   The processes $X^{\tau-}$, ${}^{\tau}X$ and $X^{\tau-}+\Psi_\tau({}^\tau X)\mathbf 1_{[\tau,N]}$
-- statement:
--   Let $X$ be a process and $\tau$ a stopping time with values in $\{0,\dots,N\}$. Write $X_{\tau-1}(\omega)=X_{\tau(\omega)-1}(\omega)$, with the convention $X_{-1}=0$.
--
--   1. The **process stopped just before $\tau$** is $X^{\tau-}_n=X_n$ for $n<\tau$ and $X^{\tau-}_n=X_{\tau-1}$ for $n\ge\tau$.
--   2. The **process started at $\tau$** is ${}^\tau X_n=0$ for $n<\tau$ and ${}^\tau X_n=X_n-X_{\tau-1}$ for $n\ge\tau$.
--   3. The process appearing in Bellman's principle is
--   $$
--   X^{\tau-}+\Psi_\tau({}^\tau X)\,\mathbf 1_{[\tau,N]},
--   $$
--   that is, at time $n$ it equals $X^{\tau-}_n$ plus $\Psi_\tau({}^\tau X)$ when $\tau\le n$.
--
--   The third process replaces the part of $X$ after $\tau$ by its risk-adjusted value at $\tau$; Bellman's principle (Theorem 4.2 (iii)) says that $\Psi_\sigma$ does not change under this replacement.
--
--   **Formalization Note** The paper does not define $X_{-1}$; the convention $X_{-1}=0$ is chosen here (the paper sets $A_{-1}=0$ in the same way on p. 7). With natural-number subtraction, $\tau-1$ would be $0$ at $\tau=0$; the definition avoids this by an explicit case split.
-- source:
--   Artzner, Delbaen, Eber, Heath, Ku, Coherent Multiperiod Risk Adjusted Values and Bellman's Principle, Ann. Oper. Res. 152 (2007); manuscript of Nov. 16, 2004, p. 11, Remark after Theorem 4.2 and Theorem 4.2 (iii)

import Mathlib
import Definitions.Def_MultiperiodRisk_Bellman_Psi

namespace MultiperiodRisk.Bellman

open MeasureTheory

variable {Ω : Type*} {m : MeasurableSpace Ω} {P₀ : Measure Ω} {ℱ : Filtration ℕ m} {N : ℕ}

/-- `X_{τ-1}`, with the convention `X_{-1} = 0` (i.e. the value `0` where `τ = 0`). -/
noncomputable def Xprev (X : ℕ → Ω → ℝ) (τ : Ω → WithTop ℕ) : Ω → ℝ :=
  fun ω => if τ ω = 0 then 0 else X ((τ ω).untopA - 1) ω

/-- `X^{τ-}`: `X^{τ-}_n = X_n` for `n < τ`, `X^{τ-}_n = X_{τ-1}` for `n ≥ τ`. -/
noncomputable def preStop (X : ℕ → Ω → ℝ) (τ : Ω → WithTop ℕ) : ℕ → Ω → ℝ :=
  fun n ω => if (n : WithTop ℕ) < τ ω then X n ω else Xprev X τ ω

/-- `^τX`: `^τX_n = 0` for `n < τ`, `^τX_n = X_n - X_{τ-1}` for `n ≥ τ`. -/
noncomputable def fromStop (X : ℕ → Ω → ℝ) (τ : Ω → WithTop ℕ) : ℕ → Ω → ℝ :=
  fun n ω => if τ ω ≤ (n : WithTop ℕ) then X n ω - Xprev X τ ω else 0

/-- The process `X^{τ-} + Ψ_τ(^τX) 1_{[τ,N]}` of Bellman's principle. -/
noncomputable def bellmanProcess (D : TestSet P₀ ℱ N) (X : ℕ → Ω → ℝ) (τ : Ω → WithTop ℕ)
    (hτ : IsStoppingTime ℱ τ) : ℕ → Ω → ℝ :=
  fun n ω => preStop X τ n ω +
    if τ ω ≤ (n : WithTop ℕ) then Psi D (fromStop X τ) τ hτ ω else 0

end MultiperiodRisk.Bellman


