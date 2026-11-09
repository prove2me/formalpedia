-- Prove2me | Definitions.Def_GevreyGibbsSep_runAnswers
-- name    : GevreyGibbsSep_runAnswers
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:38:01.303022+00:00
-- url     : https://prove2.me/theorems/12e13d33-e699-45de-a195-c204436e2825
-- title:
--   The run of a sampling algorithm (answers $O_1,\dots,O_n$)
-- statement:
--   The run of an algorithm $A$ with the order-$k$ oracle on the instance with potential $V$ and seed $\omega$: the answers $O_1,\dots,O_n$, defined recursively by $X_1=Q_1(\omega)$, $O_m=\phi_k(p,X_m)$, $X_{m+1}=Q_{m+1}(\omega,O_1,\dots,O_m)$ as in (B4).
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Definition B.3, Eq. (B4), p.35

import Mathlib
import Definitions.Def_GevreyGibbsSep_Answer
import Definitions.Def_GevreyGibbsSep_oracle
import Definitions.Def_GevreyGibbsSep_SamplingAlg

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- The run of a sampling algorithm on an instance, Eq. (B4), p.35 of arXiv:2608.24527
(sha256 d4fd40eb…): `runAnswers A k V ω n = (O₁, …, Oₙ)`, the first `n` answers of the order-`k`
oracle, with `X₁ = Q 0 ω ()`, `Oₙ = ϕ_k(p, Xₙ)` and `X_{n+1} = Q n ω (O₁, …, Oₙ)`. -/
noncomputable def runAnswers {d : ℕ} (A : SamplingAlg d) (k : ℕ∞) (V : (Fin d → ℝ) → ℝ)
    (ω : A.Ω) : (n : ℕ) → Fin n → Answer d
  | 0 => Fin.elim0
  | n + 1 => Fin.snoc (α := fun _ => Answer d) (runAnswers A k V ω n)
      (oracle k V (A.Q n ω (runAnswers A k V ω n)))

end GevreyGibbsSep


