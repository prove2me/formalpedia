-- Prove2me | Definitions.Def_QDSGibbs_tmix
-- name    : QDSGibbs_tmix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:34:52.529238+00:00
-- url     : https://prove2.me/theorems/ee0801cd-5143-4f9a-920a-428bd515662d
-- title:
--   Mixing times $t_{\mathrm{mix}}(\mathcal L,\varepsilon)$ and $k_{\mathrm{mix}}(P,\varepsilon)$
-- statement:
--   For a generator $\mathcal L$ and a channel $P$ with stationary state $\sigma$, the trace-norm **mixing times** are
--
--   $$
--   t_{\mathrm{mix}}(\mathcal L,\varepsilon)=\inf\Big\{t\ge0:\sup_\rho\|e^{t\mathcal L}(\rho)-\sigma\|_1\le\varepsilon\Big\},\qquad k_{\mathrm{mix}}(P,\varepsilon)=\min\Big\{k\in\mathbb N_0:\sup_\rho\|P^k(\rho)-\sigma\|_1\le\varepsilon\Big\},
--   $$
--
--   the suprema running over density matrices on the full system.
--
--   **Formalization Note** $t_{\mathrm{mix}}$ takes values in $[0,\infty]$ and $k_{\mathrm{mix}}$ in $\mathbb N\cup\{\infty\}$; an empty set gives $\infty$.
-- source:
--   Rouzé–Stilck França, Rapid mixing of Gibbs samplers via quantum Dobrushin–Shlosman conditions, arXiv:2610.03578 (held file sha256 ede55815…), (4.15), p.30

import Mathlib
import Definitions.Def_QDSGibbs_IsChannel

open scoped Matrix ENNReal

namespace QDSGibbs

/-- The **continuous-time mixing time** `t_mix(L, ε) = inf{t ≥ 0 : sup_ρ ‖e^{tL}(ρ) − σ‖₁ ≤ ε}`
(arXiv:2610.03578, held file sha256 ede55815…, (4.15), p.30); the supremum is over density matrices
on the full system.

**Formalization Note** `ℝ≥0∞`-valued (`inf ∅ = ⊤`); "`sup_ρ … ≤ ε`" is "for every state `ρ`, … ≤ ε". -/
noncomputable def tmix {n : Type} [Fintype n] [DecidableEq n] (L : Matrix n n ℂ → Matrix n n ℂ)
    (σ : Matrix n n ℂ) (ε : ℝ) : ℝ≥0∞ :=
  ⨅ (t : ℝ) (_ : 0 ≤ t ∧ ∀ ρ, IsState ρ → traceNorm (sexp L t ρ - σ) ≤ ε), ENNReal.ofReal t

/-- The **discrete-time mixing time** `k_mix(P, ε) = min{k ∈ ℕ₀ : sup_ρ ‖P^k(ρ) − σ‖₁ ≤ ε}`
(arXiv:2610.03578, (4.15), p.30).

**Formalization Note** `ℕ∞`-valued (`⊤` if no such `k`). -/
noncomputable def kmix {n : Type} [Fintype n] [DecidableEq n] (P : Matrix n n ℂ → Matrix n n ℂ)
    (σ : Matrix n n ℂ) (ε : ℝ) : ℕ∞ :=
  ⨅ (k : ℕ) (_ : ∀ ρ, IsState ρ → traceNorm (P^[k] ρ - σ) ≤ ε), (k : ℕ∞)

end QDSGibbs


