-- Prove2me | Definitions.Def_BauerleRiederMDP_Indifference_Market_VH
-- name    : BauerleRiederMDP_Indifference_Market_VH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:28:42.096205+00:00
-- url     : https://prove2.me/theorems/8ceeed2a-9fe4-4b2d-9c72-e9a1e6735f0a
-- title:
--   Value function $V^H_n$ of problem (4.38)
-- statement:
--   For a claim $H$ with maturity $N$ and $n\le N$,
--   $$
--   V^H_n(x,s,\hat s):=\sup_\pi \mathbb E^\pi_{n,x,s,\hat s}\Bigl[-e^{-\gamma(X_N-H)}\Bigr],
--   $$
--   the maximal expected utility of an investor who has wealth $x$ at time $n$, sees the prices $(s,\hat s)$ and is short in $H$. The supremum is over the Markov policies of the model of Section 4.9. For $H\equiv 0$ this is $V^0_n$.
--
--   **Formalization Note** This is the value function of the published framework applied to the model above: an extended-real supremum over the nonempty type of policies, with extended-real expectations. The maturity is an argument because part c) of Theorem 4.9.4 prices a claim with maturity $n+1$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), eq. (4.38), p.138

import Mathlib
import Definitions.Def_MDPFinance_Bellman_ValueFunction
import Definitions.Def_BauerleRiederMDP_Indifference_Market_model

namespace BauerleRiederMDP.Indifference

namespace Market

/-- The value function `V^H_n(x, s, ŝ) := sup_π 𝔼^π_{n,x,s,ŝ}[-e^{-γ(X_N - H)}]` of problem (4.38)
(Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), eq. (4.38), p.138,
PDF 152), for the claim `H` with maturity `N`.

**Formalization Note.** This is the value function `V_n` of the book's Markov Decision Model
`M.model N H` (`MDPFinance.Bellman.V`): an `EReal`-valued supremum over the Markov policies
`(f_0, …, f_{N-1})` of measurable decision rules. The supremum is indexed by the type of policies,
which is nonempty, and the expectation is an extended-real integral with respect to the
finitely supported kernel, so neither a real `sSup` nor a Bochner integral can return a default
value here. The maturity `N` is an argument because part c) of Theorem 4.9.4 prices a claim with
maturity `n + 1`. -/
noncomputable def VH (M : Market) (N : ℕ) (H : Claim) (n : ℕ) (x s ŝ : ℝ) : EReal :=
  MDPFinance.Bellman.V (M.model N H) n (x, s, ŝ)

end Market

end BauerleRiederMDP.Indifference


