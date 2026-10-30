-- Prove2me | Definitions.Def_HolevoCQ_randomCodeError
-- name    : HolevoCQ_randomCodeError
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:17:28.511807+00:00
-- url     : https://prove2.me/theorems/e0f0defa-ff61-441e-9957-6e251fdb8820
-- title:
--   Expected error $\mathsf MP_{er}$ of a random code with decision rule (11)
-- statement:
--   Choose the code words $u_1,\dots,u_N\in A^n$ independently, each with the product law (9), and decode with the operators (11) built from $P$ (6) and $P_{u_k}$ (8). The expected average error probability is
--
--   $$
--   \mathsf MP_{er}=\sum_{u_1,\dots,u_N}\Big(\prod_{k=1}^N\pi_{u_k}\Big)\,\frac1N\sum_{k=1}^N\big[1-\mathrm{Tr}\,S_{u_k}X_k\big],
--   $$
--
--   where $\pi_u=\pi_{i_1}\cdots\pi_{i_n}$.
--
--   **Formalization Note** The expectation is a finite sum over codebooks `Fin N → Fin n → A`; no probability space is introduced.
-- source:
--   Holevo, The Capacity of Quantum Channel with General Signal States, arXiv:quant-ph/9611023v1, §6, p.6

import Mathlib
import Definitions.Def_HolevoCQ_wordState
import Definitions.Def_HolevoCQ_wordProb
import Definitions.Def_HolevoCQ_avgError
import Definitions.Def_HolevoCQ_typProj
import Definitions.Def_HolevoCQ_condTypProj
import Definitions.Def_HolevoCQ_sqrtMeas

namespace HolevoCQ

/-- Holevo, *The Capacity of Quantum Channel with General Signal States*,
arXiv:quant-ph/9611023v1, §6, p.6: `M P_er`, the expected average error probability of the
decision rule (11) (with `P` from (6) and `P_u` from (8)) when the words `u₁, …, u_N` are chosen
independently, each with the law (9).

**Formalization Note.** The expectation is the finite sum over codebooks
`c : Fin N → Fin n → A` weighted by `∏_k π(c_k)` (product of the word laws (9)); no
probability space is introduced. -/
noncomputable def randomCodeError {A D : Type} [Fintype A] [DecidableEq A] [Fintype D]
    [DecidableEq D] (S : A → Matrix D D ℂ) (π : A → ℝ) (n N : ℕ) (δ : ℝ) : ℝ :=
  ∑ c : Fin N → Fin n → A, (∏ k, wordProb π n (c k)) *
    avgError (fun k => wordState S n (c k))
      (sqrtMeas fun k => typProj S π n δ * condTypProj S π n δ (c k) * typProj S π n δ)

end HolevoCQ


