-- Prove2me | Definitions.Def_LightningNetwork_RateBounds_onChainCost
-- name    : LightningNetwork_RateBounds_onChainCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:46:49.576689+00:00
-- url     : https://prove2.me/theorems/72787c70-ce6b-4c42-9990-14bc967245ad
-- title:
--   On-chain cost of a payment stream, Lemma 1
-- statement:
--   If every payment of a Poisson stream of rate $\lambda$ is settled on the blockchain at cost $C$ per transaction, and costs are discounted at the continuously compounded rate $r > 0$, the total discounted cost is (Lemma 1 of the paper)
--
--   $$
--   \frac{C\lambda}{r}.
--   $$
--
--   Two streams of rate $\lambda$ (a symmetric bidirectional flow) cost $2C\lambda/r$. This is the benchmark against which Theorem 2 compares channel costs.
--
--   **Formalization Note** The value of Lemma 1 is taken as the definition; the lemma's stochastic content is not formalized here.
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Channels, Management Science (2023), doi:10.1287/mnsc.2022.01664, Lemma 1, p. 6

import Mathlib

namespace LightningNetwork.RateBounds

/-- **On-chain cost of a payment stream**, Lemma 1.
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Channels*, Management Science (2023),
doi:10.1287/mnsc.2022.01664, Lemma 1, p. 6: "The on-chain cost for a transaction stream with rate
λ is Cλ/r."

`onChainCost C r lam = C · lam / r`, the discounted cost of settling every payment of a stream of
rate `lam` on-chain, each at cost `C`, with interest rate `r`.

**Formalization Note.** This is the value of Lemma 1, taken as the definition; the lemma's
stochastic content (expected discounted cost over Poisson arrival times) is not formalized. Two
streams of rate `lam` cost `2 * onChainCost C r lam` (proof of Theorem 2(ii), p. 11: "which is
2Cλ/r"). -/
noncomputable def onChainCost (C r lam : ℝ) : ℝ :=
  C * lam / r

end LightningNetwork.RateBounds


