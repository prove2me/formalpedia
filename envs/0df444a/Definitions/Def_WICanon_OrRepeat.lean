-- Prove2me | Definitions.Def_WICanon_OrRepeat
-- name    : WICanon_OrRepeat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:02:57.456178+00:00
-- url     : https://prove2.me/theorems/08f5ebcd-3a87-4f28-a3fa-4719b72742ec
-- title:
--   OR-parallel repetition of a protocol
-- statement:
--   The **$t$-fold independent parallel repetition with OR accepting condition**: $t(|x|)$ independent copies of the protocol run in parallel, with independent coins; each message is the tuple of the copies' messages; the verifier accepts if at least one copy accepts. It is the standard amplification of completeness used in the proof of Theorem 3.3 (with $t=\lceil\log n\rceil$).
--
--   **Formalization Note** Coins are concatenated tapes and tuples are the published injective `tup`. A prover message that does not parse gives empty messages in all copies.
-- source:
--   Arnon, Mazor, Pass, Silbak, Does Witness Indistinguishability Require Cryptography?, STOC 2027 submission manuscript (sha256 3f78ec3d…), Claim 2.12, p.14

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_QiOPoQ_pair
import Definitions.Def_WICanon_Protocol

set_option autoImplicit false

namespace WICanon

open QAlgorithms.Complexity QAdvFew.PoQOracle QiOPoQ

/-- The `j`-th of the copies inside a parallel message `tup (s_1, …, s_t)`; empty if there is none. -/
noncomputable def copyOf (j : ℕ) (s : Str) : Str := ((untuple s).getD []).getD j []

/-- The `j`-th block of length `c` of a concatenated coin tape. -/
def coinChunk (c j : ℕ) (r : Str) : Str := (r.drop (j * c)).take c

/-- **The `t`-fold parallel repetition with OR accepting condition** (Arnon, Mazor, Pass, Silbak, STOC
2027 submission manuscript, sha256 3f78ec3d…, Claim 2.12, p.14): `t(|x|)` independent copies run in
parallel, each message is the tuple of the copies' messages, and the verifier accepts if at least one
copy accepts. `t` may depend on `|x|` (the proof of Theorem 3.3 takes `t = ⌈log n⌉`, p.17). -/
noncomputable def orRepeat (pv : Protocol) (t : ℕ → ℕ) : Protocol where
  rounds := pv.rounds
  coinsP n := t n * pv.coinsP n
  coinsV n := t n * pv.coinsV n
  verMsg x rV ms := tup ((List.range (t x.length)).map fun j =>
    pv.verMsg x (coinChunk (pv.coinsV x.length) j rV) (ms.map (copyOf j)))
  proverMsg x w rP ρs := tup ((List.range (t x.length)).map fun j =>
    pv.proverMsg x w (coinChunk (pv.coinsP x.length) j rP) (ρs.map (copyOf j)))
  accept x rV tr := (List.range (t x.length)).any fun j =>
    pv.accept x (coinChunk (pv.coinsV x.length) j rV) (tr.map (copyOf j))

end WICanon


