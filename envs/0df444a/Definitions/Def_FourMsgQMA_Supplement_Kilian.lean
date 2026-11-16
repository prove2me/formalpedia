-- Prove2me | Definitions.Def_FourMsgQMA_Supplement_Kilian
-- name    : FourMsgQMA_Supplement_Kilian
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:19:29.75911+00:00
-- url     : https://prove2.me/theorems/e4c8ad23-a7b8-42db-8642-accf56b849ac
-- title:
--   Kilian's argument from a Merkle commitment and a nonadaptive PCP (§3.12)
-- statement:
--   **Kilian's argument** $\Sigma$ for a relation $R$, built from a keyed hash family $H$ and a nonadaptive PCP for $R$ with proof length $M$, has four messages $vk,\beta,q,a$:
--
--   1. $vk\leftarrow\mathrm{Setup}(1^\lambda,M)$ is a Merkle key for $M$ one-bit blocks, independent of the instance;
--   2. $(\beta,\mathrm{st}_P)\leftarrow\mathrm{Commit}(vk,u,w)$ computes $\pi=\mathrm{Prove}(1^\lambda,u,w)$ and its Merkle root $\beta$;
--   3. the verifier sends a uniform seed $q$;
--   4. $a\leftarrow\mathrm{Respond}(\mathrm{st}_P,q)$ gives, for each queried position $j\in Q$, the bit $\pi_j$ and its authentication path.
--
--   $\mathrm{Verify}(vk,u,\beta,q,a)$ recomputes $(Q,\mathrm{st}_V)$, checks the seed length and every opening under $\beta$, and applies Decide to the opened bits; it returns one exactly when every check accepts. The public instance $u$ may be chosen together with $\beta$.
--
--   This is the argument of Theorem 3.26, of the authorization proof of §5.1 (Theorem 5.1) and of Construction 7.4 (Theorem 7.5).
--
--   **Formalization Note** The Merkle commitment is the balanced tree of `FourMsgQMA.Supplement.merkleCommit` over $H$.
-- source:
--   Goyal, Koppula, Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from LWE, STOC 2027 submission (sha256 6c523d45…), §3.12, p.23 (PDF 25)

import Mathlib
import Definitions.Def_FourMsgQMA_Supplement_Merkle
import Definitions.Def_FourMsgQMA_Supplement_PCP

namespace FourMsgQMA

/-!
Goyal, Koppula, STOC 2027 submission (sha256 6c523d45…), §3.12 (p.23, PDF 25): Kilian's argument
`Σ = (Setup, Commit, Respond, Verify)` for a relation `R`, built from a Merkle commitment with
one-bit blocks (§3.8) and a nonadaptive PCP. "The four messages are `vk, β, q, a`, with a uniform
verifier seed `q`. The public instance may be chosen together with `β`."

The Merkle commitment is the balanced tree of `Supplement.merkleCommit` over the hash family, for
`M(λ)` one-bit blocks.
-/

namespace Supplement

open QAlgorithms QAlgorithms.Complexity TightPQRepetition.Main

/-- Kilian's argument instantiated with the hash family `hash` and the PCP `pcp`. -/
structure Kilian where
  /-- The hash family of the Merkle commitment. -/
  hash : HashFamily
  /-- The PCP. -/
  pcp : PCP

/-- The proof as a vector of one-bit blocks. -/
def bitBlocks (π : Bits) : List Bits := π.map fun b => [b]

/-- The coins of `Setup(1^λ, M)`. -/
def Kilian.setupCoins (K : Kilian) (lam : ℕ) : ℕ := merkleCoins K.hash lam (K.pcp.proofLen lam) 1

/-- `vk ← Setup(1^λ, M)`: a Merkle key for `M` one-bit blocks, independent of the instance. -/
def Kilian.setup (K : Kilian) (lam : ℕ) (r : Bits) : Bits := merkleGen K.hash lam (K.pcp.proofLen lam) 1 r

/-- `(β, st_P) ← Commit(vk, u, w)` with the PCP prover's coins `c`: the Merkle root of
`π = Prove(1^λ, u, w)` and the retained state `st_P = (vk, u, π)`. -/
def Kilian.commit (K : Kilian) (lam : ℕ) (vk u w c : Bits) : Bits × Bits :=
  let π := K.pcp.prove lam u w c
  (merkleCommit K.hash (K.pcp.proofLen lam) 1 vk (bitBlocks π), pack [vk, u, π])

/-- `a ← Respond(st_P, q)`: for each queried position `j ∈ Q` (in order), the bit `π_j` and its
Merkle authentication path. -/
def Kilian.respond (K : Kilian) (lam : ℕ) (st q : Bits) : Bits :=
  let l := unpack st
  let vk := l.getD 0 []
  let u := l.getD 1 []
  let π := l.getD 2 []
  pack ((K.pcp.query lam u q).1.map fun j =>
    pack [[π.getD j false], merkleOpen K.hash (K.pcp.proofLen lam) 1 vk (bitBlocks π) j])

/-- `Verify(vk, u, β, q, a)`: recompute `(Q, st_V) := Query(1^λ, u, q)`, check that the seed has the
prescribed length and that `a` holds one opening per queried position, check every opening under
`β`, and apply `Decide` to the opened bits. Returns one exactly when every check accepts. -/
def Kilian.verify (K : Kilian) (lam : ℕ) (vk u β q a : Bits) : Bool :=
  let Q := (K.pcp.query lam u q).1
  let st := (K.pcp.query lam u q).2
  let ans := (unpack a).map unpack
  decide (q.length = K.pcp.seedLen lam u.length) && decide (ans.length = Q.length) &&
    ((List.range Q.length).all fun i =>
      merkleVerify K.hash lam (K.pcp.proofLen lam) 1 vk β (Q.getD i 0) ((ans.getD i []).getD 0 [])
        ((ans.getD i []).getD 1 [])) &&
    K.pcp.decision lam u st (ans.map fun e => (e.getD 0 []).getD 0 false)

end Supplement

end FourMsgQMA


