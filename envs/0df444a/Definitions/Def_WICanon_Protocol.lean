-- Prove2me | Definitions.Def_WICanon_Protocol
-- name    : WICanon_Protocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:01:29.54609+00:00
-- url     : https://prove2.me/theorems/4f976dee-1591-487c-a65b-136154535d54
-- title:
--   Interactive protocols, transcripts and views
-- statement:
--   An **interactive protocol** with $k=k(|x|)$ rounds has a transcript $(\rho_1,m_1,\dots,\rho_k,m_k)$: in round $i$ the verifier sends $\rho_i$ and the prover replies $m_i$. The verifier's output is computed at the end. For uniform independent coins $r_P,r_V$, the **view** of the verifier is
--
--   $$\mathrm{View}^P_V(x,w)=(r_V,\langle P(x,w;r_P),V(x;r_V)\rangle).$$
--
--   This item defines the raw data of a protocol, the run against any reply function, the law of the view and the acceptance probabilities.
--
--   **Formalization Note** Efficiency is a separate predicate (`WICanon.ProtocolProps`). The states $st_{V,i},st_{P,i}$ are replaced by the message history: a state is computed from the coins and the messages so far. The verifier's fields do not take the witness. The prover's coin count depends on $|x|$ only, since witnesses are polynomially bounded and a machine may ignore coins.
-- source:
--   Arnon, Mazor, Pass, Silbak, Does Witness Indistinguishability Require Cryptography?, STOC 2027 submission manuscript (sha256 3f78ec3d…), §2.3, p.13

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_QiOPoQ_pair
import Definitions.Def_QiOPoQ_UPPT
import Definitions.Def_WICanon_Law

set_option autoImplicit false

namespace WICanon

open QAlgorithms.Complexity QAdvFew.PoQOracle QiOPoQ

/-- **Interactive protocol as raw data** (Arnon, Mazor, Pass, Silbak, *Does Witness
Indistinguishability Require Cryptography?*, STOC 2027 submission manuscript, sha256 3f78ec3d…,
§2.3, p.13): "tr = (ρ1, m1, …, ρk, mk), where for i = 1, …, k: (ρi, stV,i) = Vi(y, stV,i−1, mi−1;
rV,i), (mi, stP,i) = Pi(x, stP,i−1, ρi; rP,i)".

* `rounds n` is `k(|x|)` for `|x| = n`.
* `coinsP n`, `coinsV n` are the lengths of the coin tapes `r_P`, `r_V`.
* `verMsg x rV ms` is the verifier's next message `ρ_i` after the replies `ms = (m_1, …, m_{i−1})`.
* `proverMsg x w rP ρs` is the reply `m_i` to `ρs = (ρ_1, …, ρ_i)`.
* `accept x rV tr` is the verifier's output `V*`, on the flat transcript `tr`.

**Formalization Note.** Efficiency is the separate predicate `Protocol.IsEfficient`, so that the
sanity checks can run on raw data. The states `st` are replaced by the history: a state is computed
from the coins and the messages so far, and a machine may keep whatever it needs. The verifier's
fields do not take the witness. The prover's coin count depends on `|x|` only: witnesses are
polynomially bounded and a machine that reads fewer coins ignores the rest. -/
structure Protocol where
  rounds : ℕ → ℕ
  coinsP : ℕ → ℕ
  coinsV : ℕ → ℕ
  verMsg : Str → Str → List Str → Str
  proverMsg : Str → Str → Str → List Str → Str
  accept : Str → Str → List Str → Bool

namespace Protocol

/-- The messages `(ρ_1, …, ρ_i)` and `(m_1, …, m_i)` after `i` rounds between the verifier of `pv`
on `(x; rV)` and a prover replying by `respond` to the verifier's messages so far. -/
def interact (pv : Protocol) (x rV : Str) (respond : List Str → Str) :
    ℕ → List Str × List Str
  | 0 => ([], [])
  | i + 1 =>
    let prev := interact pv x rV respond i
    let ρs := prev.1 ++ [pv.verMsg x rV prev.2]
    (ρs, prev.2 ++ [respond ρs])

/-- The flat transcript `(ρ_1, m_1, …, ρ_k, m_k)` against the prover `respond`, `k = k(|x|)`. -/
def transcriptWith (pv : Protocol) (x rV : Str) (respond : List Str → Str) : List Str :=
  let run := pv.interact x rV respond (pv.rounds x.length)
  (List.zip run.1 run.2).flatMap fun p => [p.1, p.2]

/-- `⟨P(x, w; rP), V(x; rV)⟩` (§2.3, p.13). -/
def transcript (pv : Protocol) (x w rP rV : Str) : List Str :=
  pv.transcriptWith x rV (pv.proverMsg x w rP)

/-- The replies `(m_1, …, m_k)` of the honest prover. -/
def proverReplies (pv : Protocol) (x w rP rV : Str) : List Str :=
  (pv.interact x rV (pv.proverMsg x w rP) (pv.rounds x.length)).2

/-- The verifier's view `(r_V, ⟨P(x, w; r_P), V(x; r_V)⟩)` as one string (§2.3, p.13). -/
def encodeView (rV : Str) (tr : List Str) : Str := pair rV (tup tr)

/-- The law of `View^P_V(x, w)` for uniform independent `r_P`, `r_V` (§2.3, p.13). -/
noncomputable def viewLaw (pv : Protocol) (x w : Str) : Law :=
  coinLaw (pv.coinsP x.length + pv.coinsV x.length) fun r =>
    let rP := r.take (pv.coinsP x.length)
    let rV := r.drop (pv.coinsP x.length)
    encodeView rV (pv.transcript x w rP rV)

/-- `Pr[Out(⟨P(x, w), V(x)⟩) = 1]` (§2.3, p.13). -/
noncomputable def acceptProb (pv : Protocol) (x w : Str) : ℝ :=
  avgCoins (pv.coinsP x.length) fun rP =>
    avgCoins (pv.coinsV x.length) fun rV =>
      if pv.accept x rV (pv.transcript x w rP rV) = true then 1 else 0

/-- `Pr_{r_V}[Out(⟨P̂, V(x)⟩) = 1]` for a fixed reply function `respond`. -/
noncomputable def acceptProbAgainst (pv : Protocol) (x : Str) (respond : List Str → Str) : ℝ :=
  avgCoins (pv.coinsV x.length) fun rV =>
    if pv.accept x rV (pv.transcriptWith x rV respond) = true then 1 else 0

end Protocol

end WICanon


