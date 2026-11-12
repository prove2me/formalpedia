-- Prove2me | Definitions.Def_QSampVerif_IsSubexpQFHE
-- name    : QSampVerif_IsSubexpQFHE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:38:26.158058+00:00
-- url     : https://prove2.me/theorems/2fe678e9-184e-4fd2-8d2c-e0fba73375a1
-- title:
--   Assumption 3.21: subexponentially secure QFHE
-- statement:
--   A QFHE scheme $S$ is **subexponentially secure** when it is efficient (Definition 3.20) and there are constants $a\in(0,1)$, $c_1,c_2>0$ and a threshold $\kappa_0$ such that for every $\kappa\ge\kappa_0$ and every depth bound $L$:
--
--   1. every well-formed adversary of size at most $e^{c_1\kappa^a}$ has IND-CPA advantage at most $e^{-c_2\kappa^a}$;
--   2. $S$ is correct within $e^{-c_2\kappa^a}$ for circuits of size at most $e^{c_1\kappa^a}$.
--
--   Adversaries are nonuniform quantum circuits with classical advice (§3.11).
--
--   **Formalization Note** The threshold $\kappa_0$ does not appear in print; it weakens the hypothesis and is equivalent to the printed form under $\kappa\mapsto\kappa+\kappa_0$. The size bound on the correctness clause also weakens the hypothesis.
-- source:
--   Chung, Cojocaru, Lee, Lin, Classical Verification of Quantum Sampling with Negligible Error, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7), Assumption 3.21, p.24 (PDF 25); paper.md decision 13

import Definitions.Def_QSampVerif_CorrectWithin
import Definitions.Def_QSampVerif_indcpaAdvantage

set_option autoImplicit false

namespace QSampVerif

open QAlgorithms QAlgorithms.Complexity

/-- Chung, Cojocaru, Lee, Lin, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7),
Assumption 3.21 (Subexponentially secure QFHE), p.24 (PDF 25), for one scheme `S`: `S` is a QFHE
scheme as in Definition 3.20 (efficient), and there are constants `a ∈ (0, 1)`, `c₁, c₂ > 0` such
that, for every `κ` beyond a threshold `κ₀` and every depth bound `L`,
1. every (well-formed) adversary of size at most `e^{c₁κ^a}` has IND-CPA advantage at most
   `e^{−c₂κ^a}`;
2. the correctness error is at most `e^{−c₂κ^a}` (for circuits of size at most `e^{c₁κ^a}`).

**Formalization Note.** The threshold `κ₀` does not appear in print; it makes the hypothesis
weaker and is equivalent to the printed one under `κ ↦ κ + κ₀` (paper.md decision 13). The size
bound on the correctness clause also weakens the hypothesis (decision 12). Adversaries are
nonuniform circuits with classical advice (§3.11, p.23). -/
def IsSubexpQFHE (S : QFHEScheme) : Prop :=
  S.Efficient ∧
    ∃ (a c₁ c₂ : ℝ) (κ₀ : ℕ), 0 < a ∧ a < 1 ∧ 0 < c₁ ∧ 0 < c₂ ∧
      ∀ κ : ℕ, κ₀ ≤ κ → ∀ L : ℕ,
        (∀ A : Prover, A.Valid → (A.size : ℝ) ≤ Real.exp (c₁ * (κ : ℝ) ^ a) →
          indcpaAdvantage S κ L A ≤ Real.exp (-(c₂ * (κ : ℝ) ^ a))) ∧
        S.CorrectWithin κ L (Real.exp (c₁ * (κ : ℝ) ^ a)) (Real.exp (-(c₂ * (κ : ℝ) ^ a)))

end QSampVerif


