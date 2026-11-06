-- Prove2me | Definitions.Def_SymNormLoad_IsCompetitive
-- name    : SymNormLoad_IsCompetitive
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:29.750084+00:00
-- url     : https://prove2.me/theorems/232a7d7e-9302-4abd-985d-2c69f75fb9cd
-- title:
--   $\rho$-competitive online algorithm for the objective $\Psi$
-- statement:
--   A deterministic online algorithm $A$ is **$\rho$-competitive** for the objective $\Psi$ if on every finite job sequence $p_0,\dots,p_{N-1}$ with $p_j\in\mathbb R^M_{\ge0}$, its load vector $L_A$ satisfies
--   $$
--   \Psi(L_A)\le\rho\cdot\mathrm{OPT},\qquad \mathrm{OPT}=\min_{\sigma}\Psi(L_\sigma),
--   $$
--   the minimum taken over all integral offline assignments $\sigma$ of the same jobs.
--
--   **Formalization Note** Since OPT is a minimum over finitely many assignments, the condition is stated as $\Psi(L_A)\le\rho\,\Psi(L_\sigma)$ for every $\sigma$. There is no additive constant, and zero processing times are allowed.
-- source:
--   Chen–Im–Sirri, Online Load Balancing under Symmetric Norms, manuscript (STOC 2027 submission), footnote 1, p.2; Section 1.1, pp.2–3

import Mathlib
import Definitions.Def_SymNormLoad_loadVec
import Definitions.Def_SymNormLoad_OnlineAlgorithm

namespace SymNormLoad

/-- **`ρ`-competitive online algorithm for the objective `Ψ`.** Chen–Im–Sirri, *Online Load
Balancing under Symmetric Norms*, manuscript (STOC 2027 submission), footnote 1, p.2: the
competitive ratio is the worst-case ratio of an algorithm's cost to the offline optimum OPT. A
deterministic algorithm `A` is `ρ`-competitive when, on every finite job sequence with
processing-time vectors in `ℝ^M_{≥0}`, `Ψ(L_A) ≤ ρ · OPT`.

**Formalization Note** OPT is the minimum of `Ψ(L_σ)` over the finitely many integral offline
assignments `σ`, so "`Ψ(L_A) ≤ ρ · OPT`" is stated as "`Ψ(L_A) ≤ ρ · Ψ(L_σ)` for every `σ`".
There is no additive constant. Zero processing times are allowed. -/
def IsCompetitive {M : ℕ} (Ψ : (Fin M → ℝ) → ℝ) (A : OnlineAlgorithm M) (ρ : ℝ) : Prop :=
  ∀ (N : ℕ) (p : Fin N → Fin M → ℝ), (∀ j i, 0 ≤ p j i) →
    ∀ σ : Fin N → Fin M, Ψ (loadVec p (runAssign A p)) ≤ ρ * Ψ (loadVec p σ)

end SymNormLoad


