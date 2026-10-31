-- Prove2me | Definitions.Def_MayersBC_guessError
-- name    : MayersBC_guessError
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:56:10.051759+00:00
-- url     : https://prove2.me/theorems/ca9b440e-1250-4da5-9ddb-5510b9216d5f
-- title:
--   Probability of error $\mathrm{PE}$ of a binary guess
-- statement:
--   Let $\rho_0, \rho_1$ be the states of Bob's system when Alice's bit is $0$ or $1$, and suppose the bit is uniformly random. Bob guesses the bit with a two-outcome measurement $\{Q, I - Q\}$, where $0 \le Q \le I$: outcome $Q$ means "guess $0$" and outcome $I - Q$ means "guess $1$". His probability of error is
--
--   $$
--   \mathrm{PE} = \tfrac12 \operatorname{Tr}\big((I - Q)\rho_0\big) + \tfrac12 \operatorname{Tr}(Q \rho_1),
--   $$
--
--   which is the paper's $\mathrm{PE} = \sum_{b=0}^{1} \Pr(\mathbf b = b) \Pr(X = \bar b \mid \mathbf b = b)$ with $\Pr(\mathbf b = b) = \tfrac12$.
--
--   **Formalization Note** Probabilities are real parts of traces; for an effect $Q$ and density matrices the traces are real.
-- source:
--   Mayers, The Trouble with Quantum Bit Commitment, arXiv:quant-ph/9603015v3, section d, p.7

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
open QAlgorithms

namespace MayersBC

/-- Mayers, arXiv:quant-ph/9603015v3, section d, p.7: the probability of error
`PE = Σ_{b=0}^{1} Pr(b = b) Pr(X = b̄ | b = b)` of a guess `X` of Alice's bit made by Bob, for a
perfectly random bit (`Pr(b = b) = 1/2`), when Bob's photons are in state `ρ_0` or `ρ_1` and he
guesses with the two-outcome measurement `{Q, I − Q}`: outcome `Q` is the guess `0`, outcome
`I − Q` the guess `1`. So `PE = ½ Tr((I − Q)ρ_0) + ½ Tr(Q ρ_1)`.

**Formalization Note.** Probabilities are real parts of traces (`QAlgorithms.effectProb`), which
are the traces themselves for an effect `Q` and density matrices. -/
noncomputable def guessError {ι : Type} [Fintype ι] [DecidableEq ι]
    (ρ0 ρ1 Q : Matrix ι ι ℂ) : ℝ :=
  1 / 2 * effectProb (1 - Q) ρ0 + 1 / 2 * effectProb Q ρ1

end MayersBC


