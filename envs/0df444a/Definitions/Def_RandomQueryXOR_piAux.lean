-- Prove2me | Definitions.Def_RandomQueryXOR_piAux
-- name    : RandomQueryXOR_piAux
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:08:39.33763+00:00
-- url     : https://prove2.me/theorems/1dab856c-1e81-47e4-8140-6287fb8da3b0
-- title:
--   Auxiliary protocol with transcript $\Pi'$ (no FAIL)
-- statement:
--   The **auxiliary transcript** $\Pi'$ is that of the protocol which runs $\pi_{\rm two}$ without ever declaring FAIL: it always simulates the first $k$ blocks, and if there is a $(k+1)$-th occurrence of $h$, the last block ends just before it, so the last player writes the state $\hat P_k$ reached just before that occurrence. On the event that $h$ occurs at most $k$ times, $\Pi'$ coincides with the transcript of $\pi_{\rm two}$.
--
--   **Formalization Note** Same public and private randomness as `piTwo` (so both transcripts live on one probability space). The printed "$\hat P_k=P_{\hat t_{k+1}}$" is read as the state just before the $(k+1)$-th occurrence, $P_{\hat t_{k+1}-1}$, as the preceding sentence says. The answer of this protocol is not used and is set to $0$.
-- source:
--   Garg, Sundaresan, Velusamy, XOR-Functions and Beyond in the Random Query Model, arXiv:2611.04353, §4.3, p.24 (PDF p.26)

import Mathlib
import Definitions.Def_ShallowShadows_ShadowNorm_uniformDist
import Definitions.Def_RandomQueryXOR_piTwo

set_option autoImplicit false
set_option synthInstance.maxSize 2048

namespace RandomQueryXOR

open WildeQIT
open ShallowShadows.ShadowNorm (uniformDist)

variable {n S T : ℕ}

/-- The auxiliary protocol whose transcript is `Π′` (Garg, Sundaresan, Velusamy, *XOR-Functions
and Beyond in the Random Query Model*, arXiv:2611.04353, p.24 = PDF p.26): "Let Π′ be the
auxiliary transcript which always simulates the first k blocks without declaring FAIL. If there
is a (k + 1)th occurrence of h, the last block ends just before this occurrence, and the last
player outputs P̂_k = P_{t̂_{k+1}}. We use P′_a to denote its a-th message."

**Formalization Note** Same public and private randomness as `piTwo` (so `gameLaw` is the same
and `Π′` is jointly distributed with `Π^two`); every active player `Q_a`, `a < k`, writes the
state at the end of its block, the last block ending at the state just before the `(k + 1)`-th
occurrence of `h` (the printed `P_{t̂_{k+1}}` read as `P_{t̂_{k+1} − 1}`, the state "just before
this occurrence"). The answer is irrelevant (`0`): only the transcript `Π′` is used. -/
noncomputable def piAux (f : (Fin n → Bool) → Bool) (xs : Fin n → Bool) (k : ℕ)
    (hZ : (sensZeros f xs).Nonempty) (μP : FinDist (DetBP (2 ^ S) (GateSample (Fin (2 * n))) T)) :
    TwoBitProtocol k (Option (Fin (2 ^ S))) (TwoPub n S T) (Fin T → Bool) where
  pub := twoPubLaw f xs hZ μP
  priv := fun _ => uniformDist (Fin T → Bool)
  msg := embedMsg f xs true
  out _ _ := false

end RandomQueryXOR


