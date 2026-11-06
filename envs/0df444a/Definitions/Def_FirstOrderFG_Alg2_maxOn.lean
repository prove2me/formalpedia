-- Prove2me | Definitions.Def_FirstOrderFG_Alg2_maxOn
-- name    : FirstOrderFG_Alg2_maxOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:53:32.797074+00:00
-- url     : https://prove2.me/theorems/5dba7284-f649-4aca-b478-22c42c481342
-- title:
--   Maximum over a predictable interval of rounds $\max_{t\in I}F_t$
-- statement:
--   As for the interval sum, this returns $\max_{t\in I}F_t$; e.g. $\bar\rho_I=\max_{t\in I}1/x_{t,0}$.
--
--   **Formalization Note** The maximum over an empty interval is $0$.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Lemma B.1, p.22

import Mathlib
import Definitions.Def_FirstOrderFG_Alg2_step

namespace FirstOrderFG

open Classical in
/-- **`max_{t ∈ I} F_t` over a predictable interval of rounds.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Lemma B.1, p.22
(`ρ̄_I ≜ max_{t ∈ I} 1/x_{t,0}`).

Same walk as `Alg2.sumOn`, returning the maximum of `F t st_t` over the rounds of the interval.

**Formalization Note.** The maximum over the empty interval is `0`; for `F = 1/x_{t,0} ≥ 1` this is
the paper's maximum whenever `I ≠ ∅`, and makes `r_I = E_τ[ρ̄_I] ≥ 0`. -/
noncomputable def Alg2.maxOn {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (T : ℕ) (ℓ : ℕ → Fin K → ℝ)
    (q₀ : (Fin K → ℝ) → ℝ → Fin K → ℝ) (cont : List (Fin K) → Prop)
    (F : ℕ → Alg2.State K → ℝ) : ℕ → Alg2.State K → List (Fin K) → List (Fin K) → ℝ
  | _, _, _, [] => 0
  | t, st, done, I :: rest =>
    if t ≤ T ∧ cont done then
      max (F t st) (Alg2.maxOn E T ℓ q₀ cont F (t + 1) (Alg2.step E T ℓ q₀ t st I) (done ++ [I]) rest)
    else 0

end FirstOrderFG


