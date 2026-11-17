-- Prove2me | Definitions.Def_FairReplay_Supplement_Qsuite
-- name    : FairReplay_Supplement_Qsuite
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:47:05.584857+00:00
-- url     : https://prove2.me/theorems/90a031ac-16a6-4323-8d2c-27d53ac5b1f0
-- title:
--   Optimal suite-replay complexities $Q^{\mathrm{rounds}}_{\mathrm{suite}}$, $Q^{\mathrm{exec}}_{\mathrm{suite}}$
-- statement:
--   A suite tester is **$\delta$-correct** if its type-I error under the null is at most $\delta$ and its type-II error is at most $\delta$ under every single-changed-endpoint alternative $x\in V_+(H)$. Then
--   $$Q^{\mathrm{rounds}}_{\mathrm{suite}}=\inf\{\mathbb E_0[T]:\ \text{suite tester }\delta\text{-correct}\},\qquad Q^{\mathrm{exec}}_{\mathrm{suite}}=2n_+\,Q^{\mathrm{rounds}}_{\mathrm{suite}},$$
--   the optimal null expected number of suite rounds and of concrete program executions.
--
--   **Formalization Note** Infima in $[0,\infty]$; non-stopping counts as an error under an alternative.
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), Theorem 10.6, eq. (57), p.17 (PDF p.19)

import Mathlib
import Definitions.Def_BanditTrajectory
import Definitions.Def_FairReplay_expectedRounds
import Definitions.Def_FairReplay_Supplement_activeVertices
import Definitions.Def_FairReplay_Supplement_suiteModel

open MeasureTheory

namespace FairReplay.Supplement

/-- **δ-correctness against every single-changed-endpoint alternative** (Sah, Zhang, Lian, *Testing
Fairness of Evolving Software under Uncertainty*, STOC 2027 submission, manuscript of 2026-11-03,
sha256 e23940a0…, Theorem 10.6, pp.16–17 (PDF pp.18–19): "type-II error at most δ for every
alternative").

A suite tester `(π, T, ψ)` is δ-correct if it stops and rejects with probability at most `δ` under
the null, and, for every active vertex `x`, fails to stop-and-reject with probability at most `δ`
under the alternative changing `x`.

**Formalization Note** A run that never stops counts as an error under an alternative. -/
def IsSuiteDeltaCorrect {n : ℕ} (δ : ℝ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (p s d : ℝ) (π : BanditAlgorithm.BanditPolicy 1) (T : (ℕ → Fin 1 × ℝ) → ℕ∞)
    (ψ : (ℕ → Fin 1 × ℝ) → Bool) : Prop :=
  BanditAlgorithm.banditTrajMeasure (suiteModel H p s d none) π {ω | T ω < ⊤ ∧ ψ ω = true} ≤
      ENNReal.ofReal δ ∧
    ∀ x ∈ activeVertices H,
      BanditAlgorithm.banditTrajMeasure (suiteModel H p s d (some x)) π
        {ω | ¬ (T ω < ⊤ ∧ ψ ω = true)} ≤ ENNReal.ofReal δ

/-- **`Q^rounds_suite`** (Theorem 10.6, eq. (57), p.17): the infimum of the null expected number of
suite rounds over suite testers that are δ-correct against every single-changed-endpoint
alternative. The infimum is in `[0, ∞]`. -/
noncomputable def QsuiteRounds {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (p s d δ : ℝ) : ENNReal :=
  ⨅ (π : BanditAlgorithm.BanditPolicy 1) (T : (ℕ → Fin 1 × ℝ) → ℕ∞)
    (ψ : (ℕ → Fin 1 × ℝ) → Bool) (hT : BanditAlgorithm.IsBanditStoppingTime T)
    (_ : Measurable[hT.measurableSpace] ψ) (_ : IsSuiteDeltaCorrect δ H p s d π T ψ),
    expectedRounds (suiteModel H p s d none) π T

/-- **`Q^exec_suite`** (Theorem 10.6, eq. (57), p.17): the optimal null expected number of concrete
program executions, `2 n+` per suite round, `n+ = |V+(H)|`. -/
noncomputable def QsuiteExec {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (p s d δ : ℝ) : ENNReal :=
  (2 * (activeVertices H).card : ENNReal) * QsuiteRounds H p s d δ

end FairReplay.Supplement


